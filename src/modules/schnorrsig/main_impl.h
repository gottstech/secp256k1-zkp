/**********************************************************************
 * Copyright (c) 2018 Andrew Poelstra                                 *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef _SECP256K1_MODULE_SCHNORRSIG_MAIN_
#define _SECP256K1_MODULE_SCHNORRSIG_MAIN_

#include "include/secp256k1.h"
#include "include/secp256k1_schnorrsig.h"
#include "hash.h"

/* Generator point for the value in Pedersen Commitment.
 * Created as NUMS (Nothing-Up-My-Sleeve) curve point from SHA256 hash of secp256k1 generator.
 * Details: Calculate sha256 of uncompressed serialization format of G, treat the
 * result as x-coordinate, find the first point on curve with this x-coordinate
 * (which happens to exist on the curve)
 *
 * Check it:
 * $ echo "0479be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8" | xxd -r -p > G.bin
 * $ openssl dgst -sha256 G.bin
 *
 * The output will be "50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0".
 */
static const secp256k1_ge secp256k1_ge_const_h = SECP256K1_GE_CONST(
        0x50929b74UL, 0xc1a04954UL, 0xb78b4b60UL, 0x35e97a5eUL,
        0x078a5a0fUL, 0x28ec96d5UL, 0x47bfee9aUL, 0xce803ac0UL,
        0x31d3c686UL, 0x3973926eUL, 0x049e637cUL, 0xb1b5f40aUL,
        0x36dac28aUL, 0xf1766968UL, 0xc30c2313UL, 0xf3a38904UL
);

int secp256k1_schnorrsig_serialize(const secp256k1_context* ctx, unsigned char *out64, const secp256k1_schnorrsig* sig) {
    (void) ctx;
    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(out64 != NULL);
    ARG_CHECK(sig != NULL);
    memcpy(out64, sig->data, 64);
    return 1;
}

int secp256k1_schnorrsig_parse(const secp256k1_context* ctx, secp256k1_schnorrsig* sig, const unsigned char *in64) {
    (void) ctx;
    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(sig != NULL);
    ARG_CHECK(in64 != NULL);
    memcpy(sig->data, in64, 64);
    return 1;
}

int secp256k1_comsig_serialize(
    const secp256k1_context* ctx,
    unsigned char* out96,
    const secp256k1_comsig* sig
) {
    (void) ctx;
    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(out96 != NULL);
    ARG_CHECK(sig != NULL);
    memcpy(out96, sig->data, 96);
    return 1;
}

int secp256k1_comsig_parse(
    const secp256k1_context* ctx,
    secp256k1_comsig* sig,
    const unsigned char* in96
) {
    (void) ctx;
    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(sig != NULL);
    ARG_CHECK(in96 != NULL);
    memcpy(sig->data, in96, 96);
    return 1;
}

int secp256k1_schnorrsig_sign(const secp256k1_context* ctx, secp256k1_schnorrsig *sig, int *nonce_is_negated, const unsigned char *msg32, const unsigned char *seckey, secp256k1_nonce_function noncefp, void *ndata) {
    secp256k1_scalar x;
    secp256k1_scalar e;
    secp256k1_scalar k;
    secp256k1_gej pkj;
    secp256k1_gej rj;
    secp256k1_ge pk;
    secp256k1_ge r;
    secp256k1_sha256 sha;
    int overflow;
    unsigned char buf[33];
    size_t buflen = sizeof(buf);

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(secp256k1_ecmult_gen_context_is_built(&ctx->ecmult_gen_ctx));
    ARG_CHECK(sig != NULL);
    ARG_CHECK(msg32 != NULL);
    ARG_CHECK(seckey != NULL);

    if (noncefp == NULL) {
        noncefp = secp256k1_nonce_function_bipschnorr;
    }
    secp256k1_scalar_set_b32(&x, seckey, &overflow);
    /* Fail if the secret key is invalid. */
    if (overflow || secp256k1_scalar_is_zero(&x)) {
        memset(sig, 0, sizeof(*sig));
        return 0;
    }

    secp256k1_ecmult_gen(&ctx->ecmult_gen_ctx, &pkj, &x);
    secp256k1_ge_set_gej(&pk, &pkj);

    if (!noncefp(buf, msg32, seckey, NULL, (void*)ndata, 0)) {
        return 0;
    }
    secp256k1_scalar_set_b32(&k, buf, NULL);
    if (secp256k1_scalar_is_zero(&k)) {
        return 0;
    }

    secp256k1_ecmult_gen(&ctx->ecmult_gen_ctx, &rj, &k);
    secp256k1_ge_set_gej(&r, &rj);

    if (nonce_is_negated != NULL) {
        *nonce_is_negated = 0;
    }
    if (!secp256k1_fe_is_quad_var(&r.y)) {
        secp256k1_scalar_negate(&k, &k);
        if (nonce_is_negated != NULL) {
            *nonce_is_negated = 1;
        }
    }
    secp256k1_fe_normalize(&r.x);
    secp256k1_fe_get_b32(&sig->data[0], &r.x);

    secp256k1_sha256_initialize(&sha);
    secp256k1_sha256_write(&sha, &sig->data[0], 32);
    secp256k1_eckey_pubkey_serialize(&pk, buf, &buflen, 1);
    secp256k1_sha256_write(&sha, buf, buflen);
    secp256k1_sha256_write(&sha, msg32, 32);
    secp256k1_sha256_finalize(&sha, buf);

    secp256k1_scalar_set_b32(&e, buf, NULL);
    secp256k1_scalar_mul(&e, &e, &x);
    secp256k1_scalar_add(&e, &e, &k);

    secp256k1_scalar_get_b32(&sig->data[32], &e);
    secp256k1_scalar_clear(&k);
    secp256k1_scalar_clear(&x);

    return 1;
}

int secp256k1_comsig_sign(
    const secp256k1_context* ctx,
    secp256k1_comsig *sig,
    secp256k1_pubkey* pubkey,
    int *nonce_is_negated,
    const unsigned char *msg32,
    const unsigned char *seckey,
    const unsigned char *value,
    secp256k1_nonce_function noncefp,
    const unsigned char* algo16) {

    secp256k1_scalar x,vs;
    secp256k1_scalar e,u,v;
    secp256k1_scalar k1,k2;
    secp256k1_gej pkj;
    secp256k1_gej rj;
    secp256k1_ge pk1,pk;
    secp256k1_ge r1,r;
    secp256k1_sha256 sha;
    int overflow;
    unsigned char buf[33];
    size_t buflen = sizeof(buf);

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(secp256k1_ecmult_gen_context_is_built(&ctx->ecmult_gen_ctx));
    ARG_CHECK(sig != NULL);
    ARG_CHECK(msg32 != NULL);
    ARG_CHECK(seckey != NULL);

    if (noncefp == NULL) {
        noncefp = secp256k1_nonce_function_bipschnorr;
        ARG_CHECK(algo16 != NULL);
    }
    secp256k1_scalar_set_b32(&x, seckey, &overflow);
    /* Fail if the secret key is invalid. */
    if (overflow || secp256k1_scalar_is_zero(&x)) {
        memset(sig, 0, sizeof(*sig));
        return 0;
    }

    secp256k1_ecmult_gen(&ctx->ecmult_gen_ctx, &pkj, &x);
    {
        secp256k1_ge_set_gej(&pk1, &pkj);

        secp256k1_scalar_set_b32(&vs, value, &overflow);
        /* Fail if the value is invalid. */
        if (overflow || secp256k1_scalar_is_zero(&vs)) {
            memset(sig, 0, sizeof(*sig));
            return 0;
        }
        secp256k1_ecmult_const(&pkj, &secp256k1_ge_const_h, &vs, 256);

        /* calculate Commitment P=P1+P2 */
        secp256k1_gej_add_ge(&pkj, &pkj, &pk1);
    }
    secp256k1_ge_set_gej(&pk, &pkj);
    if (pubkey != NULL) {
        secp256k1_pubkey_save(pubkey, &pk);
    }

    /* generate nonce k1. k1 = Hash256(seckey || msg32 || seed) as default */
    if (!noncefp(buf, msg32, seckey, algo16, (void*)NULL, 0)) {
        return 0;
    }
    secp256k1_scalar_set_b32(&k1, buf, NULL);
    if (secp256k1_scalar_is_zero(&k1)) {
        return 0;
    }

    /* generate nonce k2. k2 = Hash256(value || msg32 || seed) as default  */
    if (!noncefp(buf, msg32, value, algo16, (void *)NULL, 0)) {
        return 0;
    }
    secp256k1_scalar_set_b32(&k2, buf, NULL);
    if (secp256k1_scalar_is_zero(&k2)) {
        return 0;
    }

    /* calculate R=R1+R2, where R1=k1*G, R2=k2*H */
    secp256k1_ecmult_gen(&ctx->ecmult_gen_ctx, &rj, &k1);
    {
        secp256k1_ge_set_gej(&r1, &rj);
        secp256k1_ecmult_const(&rj, &secp256k1_ge_const_h, &k2, 256);
        secp256k1_gej_add_ge(&rj, &rj, &r1);
    }
    secp256k1_ge_set_gej(&r, &rj);

    if (nonce_is_negated != NULL) {
        *nonce_is_negated = 0;
    }
    if (!secp256k1_fe_is_quad_var(&r.y)) {
        secp256k1_scalar_negate(&k1, &k1);
        secp256k1_scalar_negate(&k2, &k2);
        if (nonce_is_negated != NULL) {
            *nonce_is_negated = 1;
        }
    }
    secp256k1_fe_normalize(&r.x);
    secp256k1_fe_get_b32(&sig->data[0], &r.x);

    /* e = Hash( R.x || P || m ) */
    secp256k1_sha256_initialize(&sha);
    secp256k1_sha256_write(&sha, &sig->data[0], 32);
    secp256k1_eckey_pubkey_serialize(&pk, buf, &buflen, 1);
    secp256k1_sha256_write(&sha, buf, buflen);
    secp256k1_sha256_write(&sha, msg32, 32);
    secp256k1_sha256_finalize(&sha, buf);
    secp256k1_scalar_set_b32(&e, buf, NULL);

    /* u = k1 + e*x, where x is the 'x' in Pedersen Commitment 'x*G+a*H' */
    secp256k1_scalar_mul(&u, &e, &x);
    secp256k1_scalar_add(&u, &u, &k1);
    /* v = k2 + e*a, where a is the 'a' in Pedersen Commitment 'x*G+a*H' */
    secp256k1_scalar_mul(&v, &e, &vs);
    secp256k1_scalar_add(&v, &v, &k2);

    secp256k1_scalar_get_b32(&sig->data[32], &u);
    secp256k1_scalar_get_b32(&sig->data[64], &v);
    secp256k1_scalar_clear(&k1);
    secp256k1_scalar_clear(&k2);
    secp256k1_scalar_clear(&x);
    secp256k1_scalar_clear(&vs);

    return 1;
}

/* Helper function for verification and batch verification.
 * Computes R = sG - eP. */
static int secp256k1_schnorrsig_real_verify(const secp256k1_context* ctx, secp256k1_gej *rj, const secp256k1_scalar *s, const secp256k1_scalar *e, const secp256k1_pubkey *pk) {
    secp256k1_scalar nege;
    secp256k1_ge pkp;
    secp256k1_gej pkj;

    secp256k1_scalar_negate(&nege, e);

    if (!secp256k1_pubkey_load(ctx, &pkp, pk)) {
        return 0;
    }
    secp256k1_gej_set_ge(&pkj, &pkp);

    /* rj =  s*G + (-e)*pkj */
    secp256k1_ecmult(&ctx->ecmult_ctx, rj, &pkj, &nege, s);
    return 1;
}

int secp256k1_schnorrsig_verify(const secp256k1_context* ctx, const secp256k1_schnorrsig *sig, const unsigned char *msg32, const secp256k1_pubkey *pk) {
    secp256k1_scalar s;
    secp256k1_scalar e;
    secp256k1_gej rj;
    secp256k1_fe rx;
    secp256k1_sha256 sha;
    unsigned char buf[33];
    size_t buflen = sizeof(buf);
    int overflow;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(secp256k1_ecmult_context_is_built(&ctx->ecmult_ctx));
    ARG_CHECK(sig != NULL);
    ARG_CHECK(msg32 != NULL);
    ARG_CHECK(pk != NULL);

    if (!secp256k1_fe_set_b32(&rx, &sig->data[0])) {
        return 0;
    }

    secp256k1_scalar_set_b32(&s, &sig->data[32], &overflow);
    if (overflow) {
        return 0;
    }

    secp256k1_sha256_initialize(&sha);
    secp256k1_sha256_write(&sha, &sig->data[0], 32);
    secp256k1_ec_pubkey_serialize(ctx, buf, &buflen, pk, SECP256K1_EC_COMPRESSED);
    secp256k1_sha256_write(&sha, buf, buflen);
    secp256k1_sha256_write(&sha, msg32, 32);
    secp256k1_sha256_finalize(&sha, buf);
    secp256k1_scalar_set_b32(&e, buf, NULL);

    if (!secp256k1_schnorrsig_real_verify(ctx, &rj, &s, &e, pk)
        || !secp256k1_gej_has_quad_y_var(&rj) /* fails if rj is infinity */
        || !secp256k1_gej_eq_x_var(&rx, &rj)) {
        return 0;
    }

    return 1;
}

/* Helper function for ComSig signature verification and batch verification.
 * Computes R = (u*G + v*H) - eP. */
static int secp256k1_comsig_real_verify(
    const secp256k1_context* ctx,
    secp256k1_gej *rj,
    const secp256k1_scalar *u,
    const secp256k1_scalar *v,
    const secp256k1_scalar *e,
    const secp256k1_pubkey *pk) {

    secp256k1_scalar nege;
    secp256k1_ge pkp;
    secp256k1_ge s2h;
    secp256k1_gej pkj;

    secp256k1_scalar_negate(&nege, e);

    if (!secp256k1_pubkey_load(ctx, &pkp, pk)) {
        return 0;
    }
    secp256k1_gej_set_ge(&pkj, &pkp);

    /* rj = (u*G+v*H) + (-e)*pkj */
    secp256k1_ecmult_const(rj, &secp256k1_ge_const_h, v, 256);
    secp256k1_ge_set_gej(&s2h, rj);
    secp256k1_ecmult(&ctx->ecmult_ctx, rj, &pkj, &nege, u);
    secp256k1_gej_add_ge(rj, rj, &s2h);

    return 1;
}

int secp256k1_comsig_verify(
    const secp256k1_context* ctx,
    const secp256k1_comsig *sig,
    const unsigned char *msg32,
    const secp256k1_pubkey *pk) {

    secp256k1_scalar u,v;
    secp256k1_scalar e;
    secp256k1_gej rj;
    secp256k1_fe rx;
    secp256k1_sha256 sha;
    unsigned char buf[33];
    size_t buflen = sizeof(buf);
    int overflow;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(secp256k1_ecmult_context_is_built(&ctx->ecmult_ctx));
    ARG_CHECK(sig != NULL);
    ARG_CHECK(msg32 != NULL);
    ARG_CHECK(pk != NULL);

    if (!secp256k1_fe_set_b32(&rx, &sig->data[0])) {
        return 0;
    }

    secp256k1_scalar_set_b32(&u, &sig->data[32], &overflow);
    if (overflow) {
        return 0;
    }
    secp256k1_scalar_set_b32(&v, &sig->data[64], &overflow);
    if (overflow) {
        return 0;
    }

    secp256k1_sha256_initialize(&sha);
    secp256k1_sha256_write(&sha, &sig->data[0], 32);
    secp256k1_ec_pubkey_serialize(ctx, buf, &buflen, pk, SECP256K1_EC_COMPRESSED);
    secp256k1_sha256_write(&sha, buf, buflen);
    secp256k1_sha256_write(&sha, msg32, 32);
    secp256k1_sha256_finalize(&sha, buf);
    secp256k1_scalar_set_b32(&e, buf, NULL);

    if (!secp256k1_comsig_real_verify(ctx, &rj, &u, &v, &e, pk)
        || !secp256k1_gej_has_quad_y_var(&rj) /* fails if rj is infinity */
        || !secp256k1_gej_eq_x_var(&rx, &rj)) {
        return 0;
    }

    return 1;
}

/* Data that is used by the batch verification ecmult callback */
typedef struct {
    const secp256k1_context *ctx;
    /* Seed for the random number generator */
    unsigned char chacha_seed[32];
    /* Caches randomizers generated by the PRNG which returns two randomizers per call. Caching
     * avoids having to call the PRNG twice as often. The very first randomizer will be set to 1 and
     * the PRNG is called at every odd indexed schnorrsig to fill the cache. */
    secp256k1_scalar randomizer_cache[2];
    /* Signature, message, public key tuples to verify */
    const secp256k1_schnorrsig *const *sig;
    const unsigned char *const *msg32;
    const secp256k1_pubkey *const *pk;
    size_t n_sigs;
} secp256k1_schnorrsig_verify_ecmult_context;

/* Callback function which is called by ecmult_multi in order to convert the ecmult_context
 * consisting of signature, message and public key tuples into scalars and points. */
static int secp256k1_schnorrsig_verify_batch_ecmult_callback(secp256k1_scalar *sc, secp256k1_ge *pt, size_t idx, void *data) {
    secp256k1_schnorrsig_verify_ecmult_context *ecmult_context = (secp256k1_schnorrsig_verify_ecmult_context *) data;

    if (idx % 4 == 2) {
        /* Every idx corresponds to a (scalar,point)-tuple. So this callback is called with 4
         * consecutive tuples before we need to call the RNG for new randomizers:
         * (-randomizer_cache[0], R1)
         * (-randomizer_cache[0]*e1, P1)
         * (-randomizer_cache[1], R2)
         * (-randomizer_cache[1]*e2, P2) */
        secp256k1_scalar_chacha20(&ecmult_context->randomizer_cache[0], &ecmult_context->randomizer_cache[1], ecmult_context->chacha_seed, idx / 4);
    }

    /* R */
    if (idx % 2 == 0) {
        secp256k1_fe rx;
        *sc = ecmult_context->randomizer_cache[(idx / 2) % 2];
        if (!secp256k1_fe_set_b32(&rx, &ecmult_context->sig[idx / 2]->data[0])) {
            return 0;
        }
        if (!secp256k1_ge_set_xquad(pt, &rx)) {
            return 0;
        }
    /* eP */
    } else {
        unsigned char buf[33];
        size_t buflen = sizeof(buf);
        secp256k1_sha256 sha;
        secp256k1_sha256_initialize(&sha);
        secp256k1_sha256_write(&sha, &ecmult_context->sig[idx / 2]->data[0], 32);
        secp256k1_ec_pubkey_serialize(ecmult_context->ctx, buf, &buflen, ecmult_context->pk[idx / 2], SECP256K1_EC_COMPRESSED);
        secp256k1_sha256_write(&sha, buf, buflen);
        secp256k1_sha256_write(&sha, ecmult_context->msg32[idx / 2], 32);
        secp256k1_sha256_finalize(&sha, buf);

        secp256k1_scalar_set_b32(sc, buf, NULL);
        secp256k1_scalar_mul(sc, sc, &ecmult_context->randomizer_cache[(idx / 2) % 2]);

        if (!secp256k1_pubkey_load(ecmult_context->ctx, pt, ecmult_context->pk[idx / 2])) {
            return 0;
        }
    }
    return 1;
}

/** Helper function for batch verification. Hashes signature verification data into the
 *  randomization seed and initializes ecmult_context.
 *
 *  Returns 1 if the randomizer was successfully initialized.
 *
 *  Args:    ctx: a secp256k1 context object
 *  Out: ecmult_context: context for batch_ecmult_callback
 *  In/Out   sha: an initialized sha256 object which hashes the schnorrsig input in order to get a
 *                seed for the randomizer PRNG
 *  In:      sig: array of signatures, or NULL if there are no signatures
 *         msg32: array of messages, or NULL if there are no signatures
 *            pk: array of public keys, or NULL if there are no signatures
 *        n_sigs: number of signatures in above arrays (must be 0 if they are NULL)
 */
int secp256k1_schnorrsig_verify_batch_init_randomizer(const secp256k1_context *ctx, secp256k1_schnorrsig_verify_ecmult_context *ecmult_context, secp256k1_sha256 *sha, const secp256k1_schnorrsig *const *sig, const unsigned char *const *msg32, const secp256k1_pubkey *const *pk, size_t n_sigs) {
    size_t i;

    if (n_sigs > 0) {
        ARG_CHECK(sig != NULL);
        ARG_CHECK(msg32 != NULL);
        ARG_CHECK(pk != NULL);
    }

    for (i = 0; i < n_sigs; i++) {
        unsigned char buf[33];
        size_t buflen = sizeof(buf);
        secp256k1_sha256_write(sha, sig[i]->data, 64);
        secp256k1_sha256_write(sha, msg32[i], 32);
        secp256k1_ec_pubkey_serialize(ctx, buf, &buflen, pk[i], SECP256K1_EC_COMPRESSED);
        secp256k1_sha256_write(sha, buf, 32);
    }
    ecmult_context->ctx = ctx;
    ecmult_context->sig = sig;
    ecmult_context->msg32 = msg32;
    ecmult_context->pk = pk;
    ecmult_context->n_sigs = n_sigs;

    return 1;
}

/** Helper function for batch verification. Sums the s part of all signatures multiplied by their
 *  randomizer.
 *
 *  Returns 1 if s is successfully summed.
 *
 *  In/Out: s: the s part of the input sigs is added to this s argument
 *  In:  chacha_seed: PRNG seed for computing randomizers
 *        sig: array of signatures, or NULL if there are no signatures
 *     n_sigs: number of signatures in above array (must be 0 if they are NULL)
 */
int secp256k1_schnorrsig_verify_batch_sum_s(secp256k1_scalar *s, unsigned char *chacha_seed, const secp256k1_schnorrsig *const *sig, size_t n_sigs) {
    secp256k1_scalar randomizer_cache[2];
    size_t i;

    secp256k1_scalar_set_int(&randomizer_cache[0], 1);
    for (i = 0; i < n_sigs; i++) {
        int overflow;
        secp256k1_scalar term;
        if (i % 2 == 1) {
            secp256k1_scalar_chacha20(&randomizer_cache[0], &randomizer_cache[1], chacha_seed, i / 2);
        }

        secp256k1_scalar_set_b32(&term, &sig[i]->data[32], &overflow);
        if (overflow) {
            return 0;
        }
        secp256k1_scalar_mul(&term, &term, &randomizer_cache[i % 2]);
        secp256k1_scalar_add(s, s, &term);
    }
    return 1;
}

/* schnorrsig batch verification.
 * Seeds a random number generator with the inputs and derives a random number ai for every
 * signature i. Fails if y-coordinate of any R is not a quadratic residue or if
 * 0 != -(s1 + a2*s2 + ... + au*su)G + R1 + a2*R2 + ... + au*Ru + e1*P1 + (a2*e2)P2 + ... + (au*eu)Pu. */
int secp256k1_schnorrsig_verify_batch(const secp256k1_context *ctx, secp256k1_scratch *scratch, const secp256k1_schnorrsig *const *sig, const unsigned char *const *msg32, const secp256k1_pubkey *const *pk, size_t n_sigs) {
    secp256k1_schnorrsig_verify_ecmult_context ecmult_context;
    secp256k1_sha256 sha;
    secp256k1_scalar s;
    secp256k1_gej rj;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(secp256k1_ecmult_context_is_built(&ctx->ecmult_ctx));
    ARG_CHECK(scratch != NULL);
    /* Check that n_sigs is less than half of the maximum size_t value. This is necessary because
     * the number of points given to ecmult_multi is 2*n_sigs. */
    ARG_CHECK(n_sigs <= SIZE_MAX / 2);
    /* Check that n_sigs is less than 2^31 to ensure the same behavior of this function on 32-bit
     * and 64-bit platforms. */
    ARG_CHECK(n_sigs < (size_t)(1 << 31));

    secp256k1_sha256_initialize(&sha);
    if (!secp256k1_schnorrsig_verify_batch_init_randomizer(ctx, &ecmult_context, &sha, sig, msg32, pk, n_sigs)) {
        return 0;
    }
    secp256k1_sha256_finalize(&sha, ecmult_context.chacha_seed);
    secp256k1_scalar_set_int(&ecmult_context.randomizer_cache[0], 1);

    secp256k1_scalar_clear(&s);
    if (!secp256k1_schnorrsig_verify_batch_sum_s(&s, ecmult_context.chacha_seed, sig, n_sigs)) {
        return 0;
    }
    secp256k1_scalar_negate(&s, &s);

    return secp256k1_ecmult_multi_var(&ctx->ecmult_ctx, scratch, &rj, &s, secp256k1_schnorrsig_verify_batch_ecmult_callback, (void *) &ecmult_context, 2 * n_sigs)
            && secp256k1_gej_is_infinity(&rj);
}

#endif
