// Everest OpenSSL crypto engine for SHA256
// Allows OpenSSL to call the Everest SHA256 code

// gcc does not support the __cdecl notation
#include "gcc_compat.h"

// For uint?_t
#include <stdint.h>

// Set this to 1 to build the everest engine DLL, but calling back to OpenSSL's
// SHA256 code.  This helps isolate performance overhead due to EVP_Digest()
// allocating and freeing heap on every inner loop in the "speed" test.
#define USE_OPENSSL 0

#define _WINDLL 1
#pragma warning(disable:4090) // from openssl lhash.h
#include <openssl/engine.h>
#include <openssl/aes.h>
static const char *engine_Everest_id = "Everest";
#if USE_OPENSSL
static const char *engine_Everest_name = "Everest engine (OPENSSL crypto)";
#else
static const char *engine_Everest_name = "Everest engine (Everest crypto)";
#endif

IMPLEMENT_DYNAMIC_CHECK_FN();
IMPLEMENT_DYNAMIC_BIND_FN(bind_helper);

int Everest_init(ENGINE *e) {
    return 1;
}

#if USE_OPENSSL
int __cdecl OpenSSL_SHA256_Init(void *evpctx)
{
    SHA256_CTX *ctx = (SHA256_CTX *)EVP_MD_CTX_md_data(evpctx);

    return SHA256_Init(ctx);
}

int __cdecl  OpenSSL_SHA256_Update(EVP_MD_CTX *evpctx, const void *data, size_t count)
{
    SHA256_CTX *ctx = (SHA256_CTX *)EVP_MD_CTX_md_data(evpctx);
    return SHA256_Update(ctx, data, count);
}

int  __cdecl OpenSSL_SHA256_Final(EVP_MD_CTX *evpctx, unsigned char *md)
{
    SHA256_CTX *ctx = (SHA256_CTX *)EVP_MD_CTX_md_data(evpctx);
    return SHA256_Final(md, ctx);
}

typedef struct {
    union {
        double align;
        AES_KEY ks;
    } ks;
    //block128_f block;
    //union {
    //    cbc128_f cbc;
    //    ctr128_f ctr;
    //} stream;
} EVP_AES_KEY;

int __cdecl OpenSSL_AES128_InitKey(EVP_CIPHER_CTX *evpctx, const unsigned char *key, const unsigned char *iv, int enc)
{
    EVP_AES_KEY *ctx = (EVP_AES_KEY*)EVP_CIPHER_CTX_get_cipher_data(evpctx);
    // EVP_CIPHER_CTX_MODE(evpctx) should be EVP_CIPH_CBC_MODE here
    if (enc) {
        return AES_set_encrypt_key(key, 128, &ctx->ks.ks);
    } else {
        return AES_set_decrypt_key(key, 128, &ctx->ks.ks);
    }
}

int __cdecl OpenSSL_AES128_Cipher(EVP_CIPHER_CTX *evpctx, unsigned char *out, const unsigned char *in, size_t inl)
{
    // Note:  This calls the non-engine version of AES, which does not use AESNI.

    EVP_AES_KEY *ctx = (EVP_AES_KEY*)EVP_CIPHER_CTX_get_cipher_data(evpctx);
    AES_cbc_encrypt(in, out, inl, &ctx->ks.ks, EVP_CIPHER_CTX_iv_noconst(evpctx), EVP_CIPHER_CTX_encrypting(evpctx));
    return 1;
}

int __cdecl OpenSSL_AES128_Cleanup(EVP_CIPHER_CTX *evpctx)
{
    return 1;
}

#define Everest_SHA256_Init     OpenSSL_SHA256_Init
#define Everest_SHA256_Update   OpenSSL_SHA256_Update
#define Everest_SHA256_Final    OpenSSL_SHA256_Final
#define Everest_AES128_InitKey  OpenSSL_AES128_InitKey
#define Everest_AES128_Cipher   OpenSSL_AES128_Cipher
#define Everest_AES128_Cleanup  OpenSSL_AES128_Cleanup
#else
// These are __cdecl calling convention, but implemented in a separate file.
extern int Everest_SHA256_Init(EVP_MD_CTX *evpctx);
extern int Everest_SHA256_Update(EVP_MD_CTX *evpctx, const void *data, size_t count);
extern int Everest_SHA256_Final(EVP_MD_CTX *evpctx, unsigned char *md);
extern int Everest_AES128_InitKey(EVP_CIPHER_CTX *ctx, const unsigned char *key, const unsigned char *iv, int enc);
extern int Everest_AES128_Cipher(EVP_CIPHER_CTX *ctx, unsigned char *out, const unsigned char *in, size_t inl);
extern int Everest_AES128_Cleanup(EVP_CIPHER_CTX *ctx);
#ifdef _M_X64
extern int Everest_Poly1305_Init(EVP_MD_CTX *evpctx);
extern int Everest_Poly1305_Update(EVP_MD_CTX *evpctx, const void *data, size_t count);
extern int Everest_Poly1305_Final(EVP_MD_CTX *evpctx, unsigned char *md);
#endif // _M_X64

#ifndef _M_X64
// These are the Vale entrypoints
extern void __stdcall aes_main_i_KeyExpansionStdcall(const void * key_ptr, void *expanded_key_ptr);
extern void __stdcall CBCEncryptStdcall(const void* input_ptr, void* output_ptr, const void* expanded_key_ptr, const void* input_end_ptr, const void* IV_ptr, uint32_t scratch1);

typedef struct {
    uint8_t iv[16];
    uint8_t expanded_key[176];
} EVEREST_AES128_CONTEXT;

int __cdecl Everest_AES128_InitKey(EVP_CIPHER_CTX *evpctx, const unsigned char *key, const unsigned char *iv, int enc)
{
    EVEREST_AES128_CONTEXT *ctx = (EVEREST_AES128_CONTEXT*)EVP_CIPHER_CTX_get_cipher_data(evpctx);
    // EVP_CIPHER_CTX_MODE(evpctx) should be EVP_CIPH_CBC_MODE here
    if (enc) {
        memcpy(ctx->iv, iv, sizeof(ctx->iv));
        aes_main_i_KeyExpansionStdcall(key, ctx->expanded_key);
        return 1;
    } else {
        // bugbug: implement decryption
        __debugbreak();
        return 0;
    }
}

int Everest_AES128_Cipher(EVP_CIPHER_CTX *evpctx, unsigned char *out, const unsigned char *in, size_t inl)
{
    EVEREST_AES128_CONTEXT *ctx = (EVEREST_AES128_CONTEXT*)EVP_CIPHER_CTX_get_cipher_data(evpctx);
    CBCEncryptStdcall(in, out, ctx->expanded_key, in+inl, ctx->iv, 0);
    return 1;
}

int Everest_AES128_Cleanup(EVP_CIPHER_CTX *evpctx)
{
    EVEREST_AES128_CONTEXT *ctx = (EVEREST_AES128_CONTEXT*)EVP_CIPHER_CTX_get_cipher_data(evpctx);
    OPENSSL_cleanse(ctx->expanded_key, sizeof(ctx->expanded_key));
    return 1;
}
#endif // !_M_X64

#endif

static EVP_MD *sha256_md = NULL;
static EVP_MD *poly1305_md = NULL;
static int Everest_digest_nids(const int **nids)
{
    static int digest_nids[2];
    static int init = 0;
    int count = 0;

    if (!init) {
        //
        // Initialize SHA256
        //
        EVP_MD *md = EVP_MD_meth_new(NID_sha256, NID_sha256WithRSAEncryption);
        EVP_MD_meth_set_init(md, Everest_SHA256_Init);
        EVP_MD_meth_set_update(md, Everest_SHA256_Update);
        EVP_MD_meth_set_final(md, Everest_SHA256_Final);
        EVP_MD_meth_set_app_datasize(md, 4096); // much more than an Everest SHA256Context
        EVP_MD_meth_set_input_blocksize(md, 512/8);
        EVP_MD_meth_set_result_size(md, 256/8);
        EVP_MD_meth_set_flags(md, EVP_MD_FLAG_DIGALGID_ABSENT);
        sha256_md = md;
        digest_nids[count++] = EVP_MD_type(md);

#ifdef _M_X64
        //
        // Initialize Poly1305
        //
        md = EVP_MD_meth_new(NID_chacha20_poly1305, NID_sha256WithRSAEncryption); // somewhat arbitrary choices
        EVP_MD_meth_set_init(md, Everest_Poly1305_Init);
        EVP_MD_meth_set_update(md, Everest_Poly1305_Update);
        EVP_MD_meth_set_final(md, Everest_Poly1305_Final);
        EVP_MD_meth_set_app_datasize(md, 4096); // more than needed
        EVP_MD_meth_set_input_blocksize(md, 1);
        EVP_MD_meth_set_result_size(md, 16);
        EVP_MD_meth_set_flags(md, EVP_MD_FLAG_DIGALGID_ABSENT | EVP_MD_FLAG_ONESHOT);
        poly1305_md = md;
        digest_nids[count++] = EVP_MD_type(md);
#endif // _M_X64

        //
        // NULL-terminate the lst
        //
        digest_nids[count] = 0;
        init = 1;
    }
    *nids = digest_nids;
    return 1;
}

static EVP_CIPHER *aes128_cbc_md = NULL;
static int Everest_ciphers_nids(const int **nids)
{
    static int cipher_nids[3];
    static int init = 0;
    int count = 0;

    if (!init) {
#ifndef _M_X64
        //
        // Initialize AES 128 CBC
        //
        EVP_CIPHER *cipher = EVP_CIPHER_meth_new(NID_aes_128_cbc, 16, 16);
        EVP_CIPHER_meth_set_iv_length(cipher, 16);
        EVP_CIPHER_meth_set_flags(cipher, EVP_CIPH_CBC_MODE);
        EVP_CIPHER_meth_set_init(cipher, Everest_AES128_InitKey);
        EVP_CIPHER_meth_set_do_cipher(cipher, Everest_AES128_Cipher);
        EVP_CIPHER_meth_set_cleanup(cipher, Everest_AES128_Cleanup);
        EVP_CIPHER_meth_set_impl_ctx_size(cipher, 4096); // much more than Everest SHA128 requires
        aes128_cbc_md = cipher;
        cipher_nids[count++] = EVP_CIPHER_type(cipher);
#endif // !_M_X64

        //
        // NULL-terminate the lst
        //
        cipher_nids[count] = 0;
        init = 1;
    }
    *nids = cipher_nids;
    return 1;
}


int Everest_digest(ENGINE *e, const EVP_MD **digest, const int **nids, int nid)
{
    if (digest == NULL) {
        return Everest_digest_nids(nids);
    } else if (nid == NID_sha256) {
        *digest = sha256_md;
        return 1;
#ifdef _M_X64
    } else if (nid == NID_chacha20_poly1305) {
        *digest = poly1305_md;
        return 1;
#endif // !_M_X64
    } else {
        return 0;
    }
}

int Everest_ciphers(ENGINE *e, const EVP_CIPHER **cipher, const int **nids, int nid)
{
    if (cipher == NULL) {
        return Everest_ciphers_nids(nids);
#ifndef _M_X64
    } else if (nid == NID_aes_128_cbc) {
        *cipher = aes128_cbc_md;
        return 1;
#endif // !_M_X64
    } else {
        return 0;
    }
}

// See https://wiki.openssl.org/index.php/Creating_an_OpenSSL_Engine_to_use_indigenous_ECDH_ECDSA_and_HASH_Algorithms

int bind_helper(ENGINE * e, const char *id)
{
    if (!ENGINE_set_id(e, engine_Everest_id) ||
        !ENGINE_set_name(e, engine_Everest_name) ||
        !ENGINE_set_init_function(e,Everest_init) ||
        !ENGINE_set_digests(e, Everest_digest) ||
        !ENGINE_set_ciphers(e, Everest_ciphers)
    )
        return 0;

    return 1;
}
