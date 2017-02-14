// Everest OpenSSL crypto engine for SHA256
// Allows OpenSSL to call the Everest SHA256 code

// This fils is compiled __stdcall, so it can call Vale code.
// But its functions are __cdecl so OpenSSL can call them.
// In this file, you can reference OpenSSL types, but not call OpenSSL functions

#ifndef _MSV_VER
#define __int32 int
#define __int8  char
#endif

#define _WINDLL 1
#pragma warning(disable:4090) // from openssl lhash.h
#define EVP_MD_CTX_md_data EVP_MD_CTX_md_data_cdecl
#include <openssl/engine.h>
#undef EVP_MD_CTX_md_data
extern void *__cdecl EVP_MD_CTX_md_data(const EVP_MD_CTX *ctx);

#if __arm__
#define sha256_main_i_SHA256Context SHA256_CTX
int E_SHA256_Init(SHA256_CTX *c);
int E_SHA256_Update(SHA256_CTX *c, const void *data, size_t len);
int E_SHA256_Final(unsigned char *md, SHA256_CTX *c);
#else
#include <sha256_main_i.h>

#define DECLARE_SHA256Context     sha256_main_i_SHA256Context * ctx = ((sha256_main_i_SHA256Context *)EVP_MD_CTX_md_data(evpctx))

struct KremlinWorkaround {
    sha256_main_i_SHA256Context ctx_value;
    uint32_t H_value[8];
    uint8_t unprocessed_bytes_value[64];
};
#endif

int __cdecl Everest_SHA256_Init(void *evpctx)
{
#if __arm__
    DECLARE_SHA256Context;
    E_SHA256_Init(ctx);
#else    
    struct KremlinWorkaround *k = (struct KremlinWorkaround*)EVP_MD_CTX_md_data(evpctx);
    memset(k, 0, sizeof(*k));
    k->ctx_value.H = k->H_value;
    k->ctx_value.unprocessed_bytes = k->unprocessed_bytes_value;

    DECLARE_SHA256Context;
    sha256_main_i_SHA256_Init(ctx);
#endif
    return 1;
}

int __cdecl  Everest_SHA256_Update(EVP_MD_CTX *evpctx, const void *data, size_t count)
{
    DECLARE_SHA256Context;
#if __arm__
    return E_SHA256_Update(ctx, data, count);
#else
    sha256_main_i_SHA256_Update(ctx, (uint8_t*)data, 0, count);
#endif
    return 1;
}

int  __cdecl Everest_SHA256_Final(EVP_MD_CTX *evpctx, unsigned char *md)
{
    DECLARE_SHA256Context;
#if __arm__
    return E_SHA256_Final(md, ctx);
#else
    sha256_main_i_SHA256_Final(ctx, (uint32_t*)md);
#endif    
    return 1;
}

