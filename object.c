// object.c — Content-addressable object store
//
// Every piece of data (file contents, directory listings, commits) is stored
// as an "object" named by its SHA-256 hash. Objects are stored under
// .pes/objects/XX/YYYYYY... where XX is the first two hex characters of the
// hash (directory sharding).
//
// PROVIDED functions: compute_hash, object_path, object_exists, hash_to_hex, hex_to_hash
// TODO functions:     object_write, object_read

#include "pes.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

// Self-contained SHA-256 implementation to avoid external OpenSSL dependency.
// Public domain implementation adapted for this repository.

static inline uint32_t rotr(uint32_t x, unsigned int n) {
    return (x >> n) | (x << (32 - n));
}

static void sha256_transform(uint32_t state[8], const uint8_t block[64]) {
    static const uint32_t k[64] = {
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
        0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
        0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
        0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
        0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
        0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
        0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
        0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
    };

    uint32_t w[64];
    for (int i = 0; i < 16; i++) {
        w[i] = ((uint32_t)block[i * 4] << 24) |
               ((uint32_t)block[i * 4 + 1] << 16) |
               ((uint32_t)block[i * 4 + 2] << 8) |
               ((uint32_t)block[i * 4 + 3]);
    }
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >> 3);
        uint32_t s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16] + s0 + w[i - 7] + s1;
    }

    uint32_t a = state[0];
    uint32_t b = state[1];
    uint32_t c = state[2];
    uint32_t d = state[3];
    uint32_t e = state[4];
    uint32_t f = state[5];
    uint32_t g = state[6];
    uint32_t h = state[7];

    for (int i = 0; i < 64; i++) {
        uint32_t S1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25);
        uint32_t ch = (e & f) ^ (~e & g);
        uint32_t temp1 = h + S1 + ch + k[i] + w[i];
        uint32_t S0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22);
        uint32_t maj = (a & b) ^ (a & c) ^ (b & c);
        uint32_t temp2 = S0 + maj;

        h = g;
        g = f;
        f = e;
        e = d + temp1;
        d = c;
        c = b;
        b = a;
        a = temp1 + temp2;
    }

    state[0] += a;
    state[1] += b;
    state[2] += c;
    state[3] += d;
    state[4] += e;
    state[5] += f;
    state[6] += g;
    state[7] += h;
}

void compute_hash(const void *data, size_t len, ObjectID *id_out) {
    uint64_t bit_len = (uint64_t)len * 8;
    uint8_t buffer[64];
    uint32_t state[8] = {
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
    };

    size_t processed = 0;
    while (len - processed >= 64) {
        sha256_transform(state, (const uint8_t *)data + processed);
        processed += 64;
    }

    size_t remaining = len - processed;
    memcpy(buffer, (const uint8_t *)data + processed, remaining);
    buffer[remaining] = 0x80;
    size_t pad_len = (remaining < 56) ? (56 - remaining) : (120 - remaining);
    memset(buffer + remaining + 1, 0, pad_len);

    buffer[56] = (uint8_t)(bit_len >> 56);
    buffer[57] = (uint8_t)(bit_len >> 48);
    buffer[58] = (uint8_t)(bit_len >> 40);
    buffer[59] = (uint8_t)(bit_len >> 32);
    buffer[60] = (uint8_t)(bit_len >> 24);
    buffer[61] = (uint8_t)(bit_len >> 16);
    buffer[62] = (uint8_t)(bit_len >> 8);
    buffer[63] = (uint8_t)(bit_len);

    sha256_transform(state, buffer);
    if (remaining + 1 + pad_len > 64) {
        // Process second block when padding didn't fit in first block
        uint8_t second_block[64];
        memset(second_block, 0, sizeof(second_block));
        second_block[56] = (uint8_t)(bit_len >> 56);
        second_block[57] = (uint8_t)(bit_len >> 48);
        second_block[58] = (uint8_t)(bit_len >> 40);
        second_block[59] = (uint8_t)(bit_len >> 32);
        second_block[60] = (uint8_t)(bit_len >> 24);
        second_block[61] = (uint8_t)(bit_len >> 16);
        second_block[62] = (uint8_t)(bit_len >> 8);
        second_block[63] = (uint8_t)(bit_len);
        sha256_transform(state, second_block);
    }

    for (int i = 0; i < 8; i++) {
        id_out->hash[i * 4]     = (uint8_t)(state[i] >> 24);
        id_out->hash[i * 4 + 1] = (uint8_t)(state[i] >> 16);
        id_out->hash[i * 4 + 2] = (uint8_t)(state[i] >> 8);
        id_out->hash[i * 4 + 3] = (uint8_t)(state[i]);
    }
}

// ─── PROVIDED ────────────────────────────────────────────────────────────────

void hash_to_hex(const ObjectID *id, char *hex_out) {
    for (int i = 0; i < HASH_SIZE; i++) {
        sprintf(hex_out + i * 2, "%02x", id->hash[i]);
    }
    hex_out[HASH_HEX_SIZE] = '\0';
}

int hex_to_hash(const char *hex, ObjectID *id_out) {
    if (strlen(hex) < HASH_HEX_SIZE) return -1;
    for (int i = 0; i < HASH_SIZE; i++) {
        unsigned int byte;
        if (sscanf(hex + i * 2, "%2x", &byte) != 1) return -1;
        id_out->hash[i] = (uint8_t)byte;
    }
    return 0;
}

// Get the filesystem path where an object should be stored.
// Format: .pes/objects/XX/YYYYYYYY...
// The first 2 hex chars form the shard directory; the rest is the filename.
void object_path(const ObjectID *id, char *path_out, size_t path_size) {
    char hex[HASH_HEX_SIZE + 1];
    hash_to_hex(id, hex);
    snprintf(path_out, path_size, "%s/%.2s/%s", OBJECTS_DIR, hex, hex + 2);
}

int object_exists(const ObjectID *id) {
    char path[512];
    object_path(id, path, sizeof(path));
    return access(path, F_OK) == 0;
}

// ─── TODO: Implement these ──────────────────────────────────────────────────

// Write an object to the store.
//
// Object format on disk:
//   "<type> <size>\0<data>"
//   where <type> is "blob", "tree", or "commit"
//   and <size> is the decimal string of the data length
//
// Steps:
//   1. Build the full object: header ("blob 16\0") + data
//   2. Compute SHA-256 hash of the FULL object (header + data)
//   3. Check if object already exists (deduplication) — if so, just return success
//   4. Create shard directory (.pes/objects/XX/) if it doesn't exist
//   5. Write to a temporary file in the same shard directory
//   6. fsync() the temporary file to ensure data reaches disk
//   7. rename() the temp file to the final path (atomic on POSIX)
//   8. Open and fsync() the shard directory to persist the rename
//   9. Store the computed hash in *id_out

// HINTS - Useful syscalls and functions for this phase:
//   - sprintf / snprintf : formatting the header string
//   - compute_hash       : hashing the combined header + data
//   - object_exists      : checking for deduplication
//   - mkdir              : creating the shard directory (use mode 0755)
//   - open, write, close : creating and writing to the temp file
//                          (Use O_CREAT | O_WRONLY | O_TRUNC, mode 0644)
//   - fsync              : flushing the file descriptor to disk
//   - rename             : atomically moving the temp file to the final path
//

//
// Returns 0 on success, -1 on error.
int object_write(ObjectType type, const void *data, size_t len, ObjectID *id_out) {
    // Step 1: Build the full object: header ("blob 16\0") + data
    const char *type_str;
    switch (type) {
        case OBJ_BLOB:   type_str = "blob"; break;
        case OBJ_TREE:   type_str = "tree"; break;
        case OBJ_COMMIT: type_str = "commit"; break;
        default: return -1;
    }

    // Build header string
    char header[256];
    snprintf(header, sizeof(header), "%s %lu", type_str, (unsigned long)len);
    size_t header_len = strlen(header);

    // Create full object: header + '\0' + data
    size_t full_len = header_len + 1 + len;
    void *full_obj = malloc(full_len);
    if (!full_obj) return -1;

    memcpy(full_obj, header, header_len);
    ((char *)full_obj)[header_len] = '\0';
    if (len > 0) memcpy((char *)full_obj + header_len + 1, data, len);

    // Step 2: Compute SHA-256 hash of the FULL object
    compute_hash(full_obj, full_len, id_out);

    // Step 3: Check if object already exists (deduplication)
    if (object_exists(id_out)) {
        free(full_obj);
        return 0;
    }

    // Step 4: Create shard directory if it doesn't exist
    char shard_dir[512];
    char hex[HASH_HEX_SIZE + 1];
    hash_to_hex(id_out, hex);
    snprintf(shard_dir, sizeof(shard_dir), "%s/%.2s", OBJECTS_DIR, hex);
    mkdir(shard_dir, 0755);

    // Step 5: Write to a temporary file
    char path[512];
    object_path(id_out, path, sizeof(path));
    
    char tmp_path[520];
    if (snprintf(tmp_path, sizeof(tmp_path), "%s.tmp", path) >= (int)sizeof(tmp_path)) {
        free(full_obj);
        return -1;
    }

    int fd = open(tmp_path, O_CREAT | O_WRONLY | O_TRUNC, 0644);
    if (fd < 0) {
        free(full_obj);
        return -1;
    }

    if (write(fd, full_obj, full_len) != (ssize_t)full_len) {
        close(fd);
        unlink(tmp_path);
        free(full_obj);
        return -1;
    }

    // Step 6: fsync() the temporary file to ensure data reaches disk
    if (fsync(fd) != 0) {
        close(fd);
        unlink(tmp_path);
        free(full_obj);
        return -1;
    }
    close(fd);

    // Step 7: rename() the temp file to the final path (atomic on POSIX)
    if (rename(tmp_path, path) != 0) {
        free(full_obj);
        return -1;
    }

    // Step 8: fsync() the shard directory to persist the rename
    fd = open(shard_dir, O_RDONLY);
    if (fd >= 0) {
        fsync(fd);
        close(fd);
    }

    free(full_obj);
    return 0;
}

// Read an object from the store.
//
// Steps:
//   1. Build the file path from the hash using object_path()
//   2. Open and read the entire file
//   3. Parse the header to extract the type string and size
//   4. Verify integrity: recompute the SHA-256 of the file contents
//      and compare to the expected hash (from *id). Return -1 if mismatch.
//   5. Set *type_out to the parsed ObjectType
//   6. Allocate a buffer, copy the data portion (after the \0), set *data_out and *len_out
//
// HINTS - Useful syscalls and functions for this phase:
//   - object_path        : getting the target file path
//   - fopen, fread, fseek: reading the file into memory
//   - memchr             : safely finding the '\0' separating header and data
//   - strncmp            : parsing the type string ("blob", "tree", "commit")
//   - compute_hash       : re-hashing the read data for integrity verification
//   - memcmp             : comparing the computed hash against the requested hash
//   - malloc, memcpy     : allocating and returning the extracted data
//
// The caller is responsible for calling free(*data_out).
// Returns 0 on success, -1 on error (file not found, corrupt, etc.).
int object_read(const ObjectID *id, ObjectType *type_out, void **data_out, size_t *len_out) {
    char path[512];
    object_path(id, path, sizeof(path));

    // Step 1: Open and read the entire file
    FILE *f = fopen(path, "rb");
    if (!f) return -1;

    // Read file into memory
    fseek(f, 0, SEEK_END);
    long file_size = ftell(f);
    if (file_size < 0) {
        fclose(f);
        return -1;
    }
    fseek(f, 0, SEEK_SET);

    void *file_data = malloc(file_size);
    if (!file_data) {
        fclose(f);
        return -1;
    }

    if (fread(file_data, 1, file_size, f) != (size_t)file_size) {
        free(file_data);
        fclose(f);
        return -1;
    }
    fclose(f);

    // Step 2 & 3: Parse the header and verify integrity
    // Find the null terminator that separates header and data
    void *null_ptr = memchr(file_data, '\0', file_size);
    if (!null_ptr) {
        free(file_data);
        return -1;
    }

    size_t header_len = (char *)null_ptr - (char *)file_data;
    char header_str[256];
    if (header_len >= sizeof(header_str)) {
        free(file_data);
        return -1;
    }
    memcpy(header_str, file_data, header_len);
    header_str[header_len] = '\0';

    // Parse type and size from header
    char type_name[32];
    size_t parsed_size;
    if (sscanf(header_str, "%31s %zu", type_name, &parsed_size) != 2) {
        free(file_data);
        return -1;
    }

    // Map type string to ObjectType
    ObjectType type;
    if (strcmp(type_name, "blob") == 0)       type = OBJ_BLOB;
    else if (strcmp(type_name, "tree") == 0)  type = OBJ_TREE;
    else if (strcmp(type_name, "commit") == 0) type = OBJ_COMMIT;
    else {
        free(file_data);
        return -1;
    }

    // Verify that the parsed size matches actual data
    size_t data_len = file_size - header_len - 1;
    if (data_len != parsed_size) {
        free(file_data);
        return -1;
    }

    // Verify integrity: recompute SHA-256 and compare
    ObjectID computed_id;
    compute_hash(file_data, file_size, &computed_id);
    if (memcmp(&computed_id, id, sizeof(ObjectID)) != 0) {
        free(file_data);
        return -1;  // Hash mismatch - corruption detected
    }

    // Step 5 & 6: Extract data portion and return it
    void *data_out_buf = malloc(data_len + 1);
    if (!data_out_buf) {
        free(file_data);
        return -1;
    }
    if (data_len > 0) {
        memcpy(data_out_buf, (char *)file_data + header_len + 1, data_len);
    }
    ((char *)data_out_buf)[data_len] = '\0';

    *type_out = type;
    *data_out = data_out_buf;
    *len_out = data_len;

    free(file_data);
    return 0;
}
