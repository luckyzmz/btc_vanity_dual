// eth_vanity_bip39.cu
// BIP39 mnemonic -> PBKDF2 -> BIP32/44 m/44'/60'/0'/0/0 -> 真 secp256k1 -> keccak256 -> ETH 地址
// vanity 前缀比对生成器（真链路，非 BitCrack）
// 字段算术：8x32 位小端 limb，p = 2^256 - 2^32 - 977

#include <cuda_runtime.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <thread>
#include <chrono>

typedef uint32_t u32;
typedef uint64_t u64;
typedef uint8_t u8;
typedef uint16_t u16;
typedef u32 fe[ 8];

#include "bip39_words.h"

#define CUDA_CHECK(call) do { cudaError_t err = call; if(err != cudaSuccess) { fprintf(stderr, "CUDA Err: %s\n", cudaGetErrorString(err)); exit(err); } } while(0)

// ==========================================
// secp256k1 常数（LE 32 位 limb）
// ==========================================
__constant__ u32 P_FE[ 8] = {0xFFFFFC2Fu,0xFFFFFFFEu,0xFFFFFFFFu,0xFFFFFFFFu,0xFFFFFFFFu,0xFFFFFFFFu,0xFFFFFFFFu,0xFFFFFFFFu};
__constant__ u32 N_FE[ 8] = {0xD0364141u,0xBFD25E8Cu,0xAF48A03Bu,0xBAAEDCE6u,0xFFFFFFFEu,0xFFFFFFFFu,0xFFFFFFFFu,0xFFFFFFFFu};
__constant__ u32 C2P256MN[ 8] = {0x2FC9BEBFu,0x402DA173u,0x50B75FC4u,0x45512319u,0x00000001u,0,0,0};
__constant__ u32 GX_FE[ 8] = {0x16F81798u,0x59F2815Bu,0x2DCE28D9u,0x029BFCDBu,0xCE870B07u,0x55A06295u,0xF9DCBBACu,0x79BE667Eu};
__constant__ u32 GY_FE[ 8] = {0xFB10D4B8u,0x9C47D08Fu,0xA6855419u,0xFD17B448u,0x0E1108A8u,0x5DA4FBFCu,0x26A3C465u,0x483ADA77u};

// ==========================================
// 字段算术（8x32 位，p = 2^256 - 2^32 - 977）
// ==========================================
__device__ __forceinline__ void fe_cpy(u32 r[ 8], const u32 a[ 8]) { for (int i=0;i<8;i++) r[i]=a[i]; }
__device__ __forceinline__ void fe_set0(u32 r[ 8]) { for (int i=0;i<8;i++) r[i]=0; }
__device__ __forceinline__ void fe_set1(u32 r[ 8]) { fe_set0(r); r[ 0]=1; }
__device__ __forceinline__ int fe_iszero(const u32 a[ 8]) { int z=1; for (int i=0;i<8;i++) z &= (a[i]==0); return z; }
__device__ __forceinline__ int fe_isone(const u32 a[ 8]) { int z=(a[ 0]==1); for (int i=1;i<8;i++) z &= (a[i]==0); return z; }
__device__ __forceinline__ int fe_ge(const u32 a[ 8], const u32 b[ 8]) {
    for (int i=7;i>=0;i--) { if (a[i]!=b[i]) return a[i]>b[i]; }
    return 1;
}
__device__ __forceinline__ void fe_sub(u32 r[ 8], const u32 a[ 8], const u32 b[ 8]) {
    u64 bo=0;
    for (int i=0;i<8;i++){ u64 s=(u64)a[i]-b[i]-bo; r[i]=(u32)s; bo=(s>>32)?1:0; }
    if (bo) {
        u64 c=0;
        for (int i=0;i<8;i++){ u64 s=(u64)r[i]+P_FE[i]+c; r[i]=(u32)s; c=s>>32; }
    }
}
// 折叠 10-limb v 的高位 v[8],v[9]（2^256 ≡ 2^32+977），至多 3 次
__device__ __forceinline__ void fe_fold_hi(u32 v[ 10]) {
    for (int it=0; it<3; it++) {
        if ((v[ 8] | v[ 9]) == 0) return;
        u32 h0 = v[ 8], h1 = v[ 9];
        v[ 8] = 0; v[ 9] = 0;
        u64 c = 0;
        for (int i=0;i<10;i++){
            u64 s = c + (i<8 ? (u64)v[i] : 0);
            if (i>=1) {
                if (i-1==0) s += (u64)h0;
                else if (i-1==1) s += (u64)h1;
            }
            if (i==0) s += (u64)h0 * 977u;
            if (i==1) s += (u64)h1 * 977u;
            v[i] = (u32)s;
            c = s >> 32;
        }
        if (c) { u64 s = (u64)v[ 9] + c; v[ 9] = (u32)s; }
    }
}
// r = t mod p，t 为 9 limbs（< 2^257）
__device__ __forceinline__ void fe_reduce9(u32 r[ 8], const u32 t[ 9]) {
    u32 v[ 10];
    u64 c=0;
    for (int i=0;i<10;i++){
        u64 s = c + (i<8 ? (u64)t[i] : 0);
        if (i==1) s += (u64)t[ 8];
        if (i==0) s += (u64)t[ 8]*977u;
        v[i]=(u32)s; c=s>>32;
    }
    if (c){ u64 s=(u64)v[ 9]+c; v[ 9]=(u32)s; }
    fe_fold_hi(v);
    for (int i=0;i<8;i++) r[i]=v[i];
    if (fe_ge(r, P_FE)) fe_sub(r, r, P_FE);
}
__device__ __forceinline__ void fe_add(u32 r[ 8], const u32 a[ 8], const u32 b[ 8]) {
    u64 c=0; u32 t[ 9];
    for (int i=0;i<8;i++){ u64 s=(u64)a[i]+b[i]+c; t[i]=(u32)s; c=s>>32; }
    t[ 8]=(u32)c;
    fe_reduce9(r, t);
}
// r = a * b mod p（32 位 limb 学校式 + 进位链，无 __int128）
__device__ __noinline__ void fe_mul(u32 r[ 8], const u32 a[ 8], const u32 b[ 8]) {
    u32 t[ 16];
    for (int i=0;i<16;i++) t[i]=0;
    for (int i=0;i<8;i++)
        for (int j=0;j<8;j++) {
            u64 p = (u64)a[i]*b[j];
            u64 s = (u64)t[i+j] + (u32)p;
            t[i+j] = (u32)s;
            u64 c = s >> 32;
            int k = i+j+1;
            while (c && k < 16) { u64 s2=(u64)t[k]+c; t[k]=(u32)s2; c=s2>>32; k++; }
            s = (u64)t[i+j+1] + (u32)(p>>32);
            t[i+j+1] = (u32)s;
            c = s >> 32;
            k = i+j+2;
            while (c && k < 16) { u64 s2=(u64)t[k]+c; t[k]=(u32)s2; c=s2>>32; k++; }
        }
    u32 v[ 10];
    u64 c=0;
    for (int i=0;i<10;i++){
        u64 s = c + (i<8 ? (u64)t[i] : 0);
        if (i>=1 && (i-1)<8) s += (u64)t[ 8+(i-1)];
        if (i<8) s += (u64)t[ 8+i]*977u;
        v[i]=(u32)s; c=s>>32;
    }
    if (c){ u64 s=(u64)v[ 9]+c; v[ 9]=(u32)s; }
    fe_fold_hi(v);
    for (int i=0;i<8;i++) r[i]=v[i];
    if (fe_ge(r, P_FE)) fe_sub(r, r, P_FE);
}
__device__ __forceinline__ void fe_sqr(u32 r[ 8], const u32 a[ 8]) { fe_mul(r, a, a); }
// 费马求逆 a^(p-2)
__device__ __forceinline__ void fe_inv(u32 r[ 8], const u32 a[ 8]) {
    u32 e[ 8] = {0xFFFFFC2Du,0xFFFFFFFEu,0xFFFFFFFFu,0xFFFFFFFFu,0xFFFFFFFFu,0xFFFFFFFFu,0xFFFFFFFFu,0xFFFFFFFFu};
    u32 res[ 8]; fe_set1(res);
    u32 base[ 8]; fe_cpy(base, a);
    for (int i=255;i>=0;i--){
        fe_sqr(res, res);
        if ((e[i>>5] >> (i&31)) & 1) fe_mul(res, res, base);
    }
    fe_cpy(r, res);
}
// 标量加法 mod n（BIP32 CKD：k_new = (IL + k) mod n）
__device__ __forceinline__ void sc_add_mod_n(u32 r[ 8], const u32 a[ 8], const u32 b[ 8]) {
    u64 c=0; u32 t[ 9];
    for (int i=0;i<8;i++){ u64 s=(u64)a[i]+b[i]+c; t[i]=(u32)s; c=s>>32; }
    t[ 8]=(u32)c;
    if (t[ 8]) {
        u64 cc=0;
        for (int i=0;i<8;i++){ u64 s=(u64)t[i]+C2P256MN[i]+cc; r[i]=(u32)s; cc=s>>32; }
    } else if (fe_ge(t, N_FE)) {
        u64 bo=0;
        for (int i=0;i<8;i++){ u64 s=(u64)t[i]-N_FE[i]-bo; r[i]=(u32)s; bo=(s>>32)?1:0; }
    } else {
        for (int i=0;i<8;i++) r[i]=t[i];
    }
}

// ==========================================
// 雅可比坐标点运算
// ==========================================
struct Jacobian { fe X, Y, Z; };
__device__ __forceinline__ void jac_set_inf(Jacobian& P) { fe_set0(P.X); fe_set0(P.Y); fe_set0(P.Z); }
__device__ __forceinline__ int jac_is_inf(const Jacobian& P) { return fe_iszero(P.Z); }

__device__ __forceinline__ void jac_double(Jacobian& R, const Jacobian& P) {
    if (jac_is_inf(P)) { jac_set_inf(R); return; }
    fe A, B, C, D, E, F, t, t2;
    fe_sqr(A, P.X);
    fe_sqr(B, P.Y);
    fe_sqr(C, B);
    fe_add(t, P.X, B); fe_sqr(t, t);
    fe_sub(t, t, A); fe_sub(t, t, C);
    fe_add(D, t, t);
    fe_add(E, A, A); fe_add(E, E, A);
    fe_sqr(F, E);
    fe_add(t, D, D);
    fe_sub(t, F, t);
    fe_sub(t2, D, t);
    fe_mul(t2, t2, E);
    fe_add(F, C, C); fe_add(F, F, F); fe_add(F, F, F);
    fe_sub(t2, t2, F);
    fe_mul(F, P.Y, P.Z); fe_add(F, F, F);
    fe_cpy(R.X, t); fe_cpy(R.Y, t2); fe_cpy(R.Z, F);
}

__device__ __forceinline__ void jac_add_affine(Jacobian& R, const Jacobian& P, const u32 qx[ 8], const u32 qy[ 8]) {
    if (jac_is_inf(P)) { fe_cpy(R.X, qx); fe_cpy(R.Y, qy); fe_set1(R.Z); return; }
    fe Z1Z1, U2, S2, H, Rr, HH, HHH, V, X3, Y3, Z3, t, t2;
    fe_sqr(Z1Z1, P.Z);
    fe_mul(U2, qx, Z1Z1);
    fe_mul(t, P.Z, Z1Z1);
    fe_mul(S2, qy, t);
    fe_sub(H, U2, P.X);
    fe_sub(Rr, S2, P.Y);
    if (fe_iszero(H)) {
        if (fe_iszero(Rr)) { jac_double(R, P); return; }
        else { jac_set_inf(R); return; }
    }
    fe_sqr(HH, H);
    fe_mul(HHH, H, HH);
    fe_mul(V, P.X, HH);
    fe_sqr(X3, Rr);
    fe_sub(X3, X3, HHH);
    fe_add(t, V, V);
    fe_sub(X3, X3, t);
    fe_sub(t, V, X3);
    fe_mul(t, t, Rr);
    fe_mul(t2, P.Y, HHH);
    fe_sub(Y3, t, t2);
    fe_mul(Z3, P.Z, H);
    fe_cpy(R.X, X3); fe_cpy(R.Y, Y3); fe_cpy(R.Z, Z3);
}

// k * G（从 MSB 到 LSB 的 double-and-add）
__device__ void scalar_mult_base(Jacobian& R, const u32 k[ 8]) {
    jac_set_inf(R);
    for (int i=255;i>=0;i--){
        jac_double(R, R);
        if ((k[i>>5] >> (i&31)) & 1) jac_add_affine(R, R, GX_FE, GY_FE);
    }
}


__device__ void jac_to_affine(u32 x[ 8], u32 y[ 8], const Jacobian& P) {
    fe zi, zi2, zi3;
    fe_inv(zi, P.Z);
    fe_sqr(zi2, zi);
    fe_mul(zi3, zi2, zi);
    fe_mul(x, P.X, zi2);
    fe_mul(y, P.Y, zi3);
}
__device__ const u32* g_comb;

// ==========================================
// 4-tooth comb 固定基点标量乘
// T[t][j] = j * 2^(64t) * G, t=0..3, j=1..15 （仿射坐标，16 u32/点）
// 256 次 double -> 64 次 double + ~64 次 affine add
// ==========================================
__global__ void precompute_comb_kernel(u32* d_table) {
    int t = threadIdx.x;      // 0..3
    int j = blockIdx.x + 1;   // 1..15
    if (t > 3) return;
    u32 kf[ 8] = {0,0,0,0,0,0,0,0};
    // k = j * 2^(64t)：j 放入 limb 2t（j<16 不溢出）
    kf[ 2*t] = (u32)j;
    Jacobian P;
    jac_set_inf(P);
    for (int i=255;i>=0;i--){
        jac_double(P, P);
        if ((kf[i>>5]>>(i&31))&1) jac_add_affine(P, P, GX_FE, GY_FE);
    }
    u32 x[ 8], y[ 8];
    jac_to_affine(x, y, P);
    u32* dst = d_table + ((t*15 + (j-1)) * 16);
    for (int i=0;i<8;i++){ dst[i]=x[i]; dst[8+i]=y[i]; }
}

__device__ __forceinline__ void scalar_mult_base_comb(Jacobian& R, const u32 k[ 8]) {
    jac_set_inf(R);
    const u32* T = g_comb;
    for (int r=15; r>=0; r--) {
        jac_double(R,R); jac_double(R,R); jac_double(R,R); jac_double(R,R);
        for (int t=0;t<4;t++) {
            int shift = 64*t + 4*r;
            int d = (k[shift>>5] >> (shift&31)) & 0xF;
            if (d) {
                const u32* p = T + ((t*15 + (d-1)) * 16);
                jac_add_affine(R, R, p, p+8);
            }
        }
    }
}


// ==========================================
// 字节 / limb 转换
// ==========================================
__device__ __forceinline__ void bytes32_to_fe(u32 f[ 8], const u8 b[ 32]) {
    for (int i=0;i<8;i++) f[i] = ((u32)b[28-4*i]<<24)|((u32)b[29-4*i]<<16)|((u32)b[30-4*i]<<8)|b[31-4*i];
}
__device__ __forceinline__ void fe_to_bytes32(u8 b[ 32], const u32 f[ 8]) {
    for (int i=0;i<8;i++){ u32 v=f[i]; b[28-4*i]=(u8)(v>>24); b[29-4*i]=(u8)(v>>16); b[30-4*i]=(u8)(v>>8); b[31-4*i]=(u8)v; }
}
__device__ __forceinline__ int device_strlen(const char* s) { int l=0; while (s[l]) l++; return l; }

// ==========================================
// SHA-256（BIP39 校验和 / vanity 熵）
// ==========================================
__constant__ u32 K256[ 64] = {
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
};
__device__ __forceinline__ u32 rotr32(u32 x, int n) { return (x >> n) | (x << (32 - n)); }
__device__ __forceinline__ void sha256_block(u32 h[ 8], const u8 blk[ 64]) {
    u32 w[ 64];
    for (int i=0;i<16;i++) w[i] = ((u32)blk[i*4]<<24)|((u32)blk[i*4+1]<<16)|((u32)blk[i*4+2]<<8)|blk[i*4+3];
    for (int i=16;i<64;i++){
        u32 s0 = rotr32(w[i-15],7)^rotr32(w[i-15],18)^(w[i-15]>>3);
        u32 s1 = rotr32(w[i-2],17)^rotr32(w[i-2],19)^(w[i-2]>>10);
        w[i] = w[i-16] + s0 + w[i-7] + s1;
    }
    u32 a=h[ 0],b=h[ 1],c=h[ 2],d=h[ 3],e=h[ 4],f=h[ 5],g=h[ 6],hh=h[ 7];
    for (int i=0;i<64;i++){
        u32 S1 = rotr32(e,6)^rotr32(e,11)^rotr32(e,25);
        u32 ch = (e&f)^((~e)&g);
        u32 t1 = hh + S1 + ch + K256[i] + w[i];
        u32 S0 = rotr32(a,2)^rotr32(a,13)^rotr32(a,22);
        u32 maj = (a&b)^(a&c)^(b&c);
        u32 t2 = S0 + maj;
        hh=g; g=f; f=e; e=d+t1; d=c; c=b; b=a; a=t1+t2;
    }
    h[ 0]+=a; h[ 1]+=b; h[ 2]+=c; h[ 3]+=d; h[ 4]+=e; h[ 5]+=f; h[ 6]+=g; h[ 7]+=hh;
}
__device__ void sha256(const u8* data, int len, u8 out[ 32]) {
    u32 h[ 8] = {0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19};
    u8 blk[ 64];
    int off = 0;
    while (len - off >= 64) { for (int i=0;i<64;i++) blk[i]=data[off+i]; sha256_block(h, blk); off += 64; }
    for (int i=0;i<64;i++) blk[i]=0;
    int rem = len - off;
    for (int i=0;i<rem;i++) blk[i]=data[off+i];
    blk[rem] = 0x80;
    u64 bits = (u64)len * 8;
    for (int i=0;i<8;i++) blk[56+i] = (u8)((bits >> (56-8*i)) & 0xFF);
    sha256_block(h, blk);
    for (int i=0;i<8;i++){ out[i*4]=(u8)(h[i]>>24); out[i*4+1]=(u8)(h[i]>>16); out[i*4+2]=(u8)(h[i]>>8); out[i*4+3]=(u8)h[i]; }
}

// ==========================================
// SHA-512 / HMAC-SHA512（移植自优化版）
// ==========================================
__device__ __constant__ u64 sha512_k[ 80] = {
    0x428a2f98d728ae22ULL, 0x7137449123ef65cdULL, 0xb5c0fbcfec4d3b2fULL, 0xe9b5dba58189dbbcULL,
    0x3956c25bf348b538ULL, 0x59f111f1b605d019ULL, 0x923f82a4af194f9bULL, 0xab1c5ed5da6d8118ULL,
    0xd807aa98a3030242ULL, 0x12835b0145706fbeULL, 0x243185be4ee4b28cULL, 0x550c7dc3d5ffb4e2ULL,
    0x72be5d74f27b896fULL, 0x80deb1fe3b1696b1ULL, 0x9bdc06a725c71235ULL, 0xc19bf174cf692694ULL,
    0xe49b69c19ef14ad2ULL, 0xefbe4786384f25e3ULL, 0x0fc19dc68b8cd5b5ULL, 0x240ca1cc77ac9c65ULL,
    0x2de92c6f592b0275ULL, 0x4a7484aa6ea6e483ULL, 0x5cb0a9dcbd41fbd4ULL, 0x76f988da831153b5ULL,
    0x983e5152ee66dfabULL, 0xa831c66d2db43210ULL, 0xb00327c898fb213fULL, 0xbf597fc7beef0ee4ULL,
    0xc6e00bf33da88fc2ULL, 0xd5a79147930aa725ULL, 0x06ca6351e003826fULL, 0x142929670a0e6e70ULL,
    0x27b70a8546d22ffcULL, 0x2e1b21385c26c926ULL, 0x4d2c6dfc5ac42aedULL, 0x53380d139d95b3dfULL,
    0x650a73548baf63deULL, 0x766a0abb3c77b2a8ULL, 0x81c2c92e47edaee6ULL, 0x92722c851482353bULL,
    0xa2bfe8a14cf10364ULL, 0xa81a664bbc423001ULL, 0xc24b8b70d0f89791ULL, 0xc76c51a30654be30ULL,
    0xd192e819d6ef5218ULL, 0xd69906245565a910ULL, 0xf40e35855771202aULL, 0x106aa07032bbd1b8ULL,
    0x19a4c116b8d2d0c8ULL, 0x1e376c085141ab53ULL, 0x2748774cdf8eeb99ULL, 0x34b0bcb5e19b48a8ULL,
    0x391c0cb3c5c95a63ULL, 0x4ed8aa4ae3418acbULL, 0x5b9cca4f7763e373ULL, 0x682e6ff3d6b2b8a3ULL,
    0x748f82ee5defb2fcULL, 0x78a5636f43172f60ULL, 0x84c87814a1f0ab72ULL, 0x8cc702081a6439ecULL,
    0x90befffa23631e28ULL, 0xa4506cebde82bde9ULL, 0xbef9a3f7b2c67915ULL, 0xc67178f2e372532bULL,
    0xca273eceea26619cULL, 0xd186b8c721c0c207ULL, 0xeada7dd6cde0eb1eULL, 0xf57d4f7fee6ed178ULL,
    0x06f067aa72176fbaULL, 0x0a637dc5a2c898a6ULL, 0x113f9804bef90daeULL, 0x1b710b35131c471bULL,
    0x28db77f523047d84ULL, 0x32caab7b40c72493ULL, 0x3c9ebe0a15c9bebcULL, 0x431d67c49c100d4cULL,
    0x4cc5d4becb3e42b6ULL, 0x597f299cfc657e2aULL, 0x5fcb6fab3ad6faecULL, 0x6c44198c4a475817ULL
};
__device__ __forceinline__ u64 rotr64(u64 x, int n) { return (x >> n) | (x << (64 - n)); }
__device__ __forceinline__ u64 Ch(u64 x, u64 y, u64 z) { return (x & y) ^ (~x & z); }
__device__ __forceinline__ u64 Maj(u64 x, u64 y, u64 z) { return (x & y) ^ (x & z) ^ (y & z); }
__device__ __forceinline__ u64 Sigma0(u64 x) { return rotr64(x, 28) ^ rotr64(x, 34) ^ rotr64(x, 39); }
__device__ __forceinline__ u64 Sigma1(u64 x) { return rotr64(x, 14) ^ rotr64(x, 18) ^ rotr64(x, 41); }
__device__ __forceinline__ u64 sigma0(u64 x) { return rotr64(x, 1) ^ rotr64(x, 8) ^ (x >> 7); }
__device__ __forceinline__ u64 sigma1(u64 x) { return rotr64(x, 19) ^ rotr64(x, 61) ^ (x >> 6); }
__device__ __forceinline__ void sha512_init(u64 st[ 8]) {
    st[ 0]=0x6a09e667f3bcc908ULL; st[ 1]=0xbb67ae8584caa73bULL;
    st[ 2]=0x3c6ef372fe94f82bULL; st[ 3]=0xa54ff53a5f1d36f1ULL;
    st[ 4]=0x510e527fade682d1ULL; st[ 5]=0x9b05688c2b3e6c1fULL;
    st[ 6]=0x1f83d9abfb41bd6bULL; st[ 7]=0x5be0cd19137e2179ULL;
}
__device__ __forceinline__ void sha512_block_words(u64 st[ 8], const u64 blockW[ 16]) {
    u64 W[ 80];
    #pragma unroll
    for (int i = 0; i < 16; i++) W[i] = blockW[i];
    #pragma unroll
    for (int i = 16; i < 80; i++) W[i] = sigma1(W[i-2]) + W[i-7] + sigma0(W[i-15]) + W[i-16];
    u64 a=st[ 0], b=st[ 1], c=st[ 2], d=st[ 3], e=st[ 4], f=st[ 5], g=st[ 6], h=st[ 7];
    #pragma unroll
    for (int i = 0; i < 80; i++) {
        u64 T1 = h + Sigma1(e) + Ch(e,f,g) + sha512_k[i] + W[i];
        u64 T2 = Sigma0(a) + Maj(a,b,c);
        h=g; g=f; f=e; e=d + T1; d=c; c=b; b=a; a=T1 + T2;
    }
    st[ 0]+=a; st[ 1]+=b; st[ 2]+=c; st[ 3]+=d; st[ 4]+=e; st[ 5]+=f; st[ 6]+=g; st[ 7]+=h;
}
__device__ __forceinline__ void load_be_words(const u8 blk[ 128], u64 W[ 16]) {
    #pragma unroll
    for (int i = 0; i < 16; i++) {
        u64 v = 0;
        #pragma unroll
        for (int j = 0; j < 8; j++) v = (v << 8) | blk[i*8 + j];
        W[i] = v;
    }
}
__device__ __forceinline__ void hmac_sha512_precompute(const u8* key, int key_len,
                                                       u64 ipad_st[ 8], u64 opad_st[ 8]) {
    u8 real_key[ 128] = {0};
    u8 kblk[ 128];
    if (key_len > 128) {
        u64 st[ 8]; sha512_init(st);
        int off = 0;
        while (off + 128 <= key_len) {
            u64 W[ 16]; load_be_words(key + off, W);
            sha512_block_words(st, W); off += 128;
        }
        u8 pad[ 128] = {0};
        int rem = key_len - off;
        for (int i = 0; i < rem; i++) pad[i] = key[off + i];
        pad[rem] = 0x80;
        u64 bits = (u64)key_len * 8;
        for (int i = 0; i < 8; i++) pad[ 120 + i] = (bits >> (56 - 8*i)) & 0xFF;
        u64 W2[ 16]; load_be_words(pad, W2);
        sha512_block_words(st, W2);
        for (int i = 0; i < 8; i++) for (int j = 0; j < 8; j++) real_key[i*8+j] = (st[i] >> (56 - 8*j)) & 0xFF;
    } else {
        for (int i = 0; i < key_len; i++) real_key[i] = key[i];
    }
    u64 W[ 16];
    for (int i = 0; i < 128; i++) kblk[i] = real_key[i] ^ 0x36;
    load_be_words(kblk, W);
    sha512_init(ipad_st); sha512_block_words(ipad_st, W);
    for (int i = 0; i < 128; i++) kblk[i] = real_key[i] ^ 0x5c;
    load_be_words(kblk, W);
    sha512_init(opad_st); sha512_block_words(opad_st, W);
}
// 通用 HMAC-SHA512（msg_len <= 64，key_len <= 128）
__device__ __forceinline__ void hmac_sha512_gen(const u8* key, int key_len, const u8* msg, int msg_len, u8 out[ 64]) {
    u64 ipad_st[ 8], opad_st[ 8];
    hmac_sha512_precompute(key, key_len, ipad_st, opad_st);
    u8 blk[ 128];
    for (int i=0;i<128;i++) blk[i]=0;
    for (int i=0;i<msg_len && i<128;i++) blk[i]=msg[i];
    blk[msg_len]=0x80;
    u64 bits=(u64)(128+msg_len)*8;
    for (int i=0;i<8;i++) blk[120+i]=(u8)((bits>>(56-8*i))&0xFF);
    u64 W[ 16], st[ 8], ih[ 8];
    load_be_words(blk, W);
    for (int i=0;i<8;i++) st[i]=ipad_st[i];
    sha512_block_words(st, W);
    for (int i=0;i<8;i++) ih[i]=st[i];
    for (int i=0;i<128;i++) blk[i]=0;
    for (int i=0;i<64;i++) blk[i]=(u8)((ih[i>>3]>>(56-8*(i&7)))&0xFF);
    blk[64]=0x80;
    bits=(128+64)*8;
    for (int i=0;i<8;i++) blk[120+i]=(u8)((bits>>(56-8*i))&0xFF);
    load_be_words(blk, W);
    for (int i=0;i<8;i++) st[i]=opad_st[i];
    sha512_block_words(st, W);
    for (int i=0;i<8;i++) for (int j=0;j<8;j++) out[i*8+j]=(u8)((st[i]>>(56-8*j))&0xFF);
}
// PBKDF2 首次迭代：salt = "mnemonic" + 0x00000001
__device__ __forceinline__ void hmac_sha512_salt(const u64 ipad_st[ 8], const u64 opad_st[ 8], u64 out[ 8]) {
    const u64 saltW[ 16] = {
        0x6D6E656D6F6E6963ULL, 0x0000000180000000ULL,
        0,0,0,0,0,0,0,0,0,0,0,0, 0, 0x0000000000000460ULL
    };
    u64 st[ 8], W[ 16], ih[ 8];
    for (int i = 0; i < 8; i++) st[i] = ipad_st[i];
    for (int i = 0; i < 16; i++) W[i] = saltW[i];
    sha512_block_words(st, W);
    for (int i = 0; i < 8; i++) ih[i] = st[i];
    for (int i = 0; i < 8; i++) st[i] = opad_st[i];
    for (int i = 0; i < 8; i++) W[i] = ih[i];
    W[ 8]  = 0x8000000000000000ULL;
    W[ 9]  = 0; W[ 10] = 0; W[ 11] = 0; W[ 12] = 0; W[ 13] = 0; W[ 14] = 0;
    W[ 15] = 0x0000000000000600ULL;
    sha512_block_words(st, W);
    for (int i = 0; i < 8; i++) out[i] = st[i];
}
// HMAC 一步：消息 = 完整 64B 块 msg
__device__ __forceinline__ void hmac_sha512_64(const u64 ipad_st[ 8], const u64 opad_st[ 8],
                                               const u64 msg[ 8], u64 out[ 8]) {
    u64 st[ 8], W[ 16], ih[ 8];
    for (int i = 0; i < 8; i++) st[i] = ipad_st[i];
    for (int i = 0; i < 8; i++) W[i] = msg[i];
    W[ 8]  = 0x8000000000000000ULL;
    W[ 9]  = 0; W[ 10] = 0; W[ 11] = 0; W[ 12] = 0; W[ 13] = 0; W[ 14] = 0;
    W[ 15] = 0x0000000000000600ULL;
    sha512_block_words(st, W);
    for (int i = 0; i < 8; i++) ih[i] = st[i];
    for (int i = 0; i < 8; i++) st[i] = opad_st[i];
    for (int i = 0; i < 8; i++) W[i] = ih[i];
    W[ 8]  = 0x8000000000000000ULL;
    W[ 9]  = 0; W[ 10] = 0; W[ 11] = 0; W[ 12] = 0; W[ 13] = 0; W[ 14] = 0;
    W[ 15] = 0x0000000000000600ULL;
    sha512_block_words(st, W);
    for (int i = 0; i < 8; i++) out[i] = st[i];
}
// 完整 BIP39 Seed 派生（2048 次 PBKDF2-HMAC-SHA512）
__device__ void device_bip39_seed(const char* mnemonic, u8 seed[ 64]) {
    int pass_len = device_strlen(mnemonic);
    u64 ipad_st[ 8], opad_st[ 8];
    hmac_sha512_precompute((const u8*)mnemonic, pass_len, ipad_st, opad_st);
    u64 U[ 8], T[ 8];
    hmac_sha512_salt(ipad_st, opad_st, U);
    for (int i = 0; i < 8; i++) T[i] = U[i];
    for (int i = 1; i < 2048; i++) {
        hmac_sha512_64(ipad_st, opad_st, U, U);
        for (int j = 0; j < 8; j++) T[j] ^= U[j];
    }
    for (int i = 0; i < 8; i++)
        for (int j = 0; j < 8; j++) seed[i*8 + j] = (T[i] >> (56 - 8*j)) & 0xFF;
}

// ==========================================
// Keccak-256（地址）
// ==========================================
__device__ __constant__ u64 keccak_rc[ 24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808aULL, 0x8000000080008000ULL,
    0x000000000000808bULL, 0x0000000080000001ULL, 0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008aULL, 0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL, 0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL, 0x000000000000800aULL, 0x800000008000000aULL,
    0x8000000080008081ULL, 0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL
};
__device__ __forceinline__ u64 rotl64b(u64 x, int n) { n &= 63; return n ? ((x << n) | (x >> (64 - n))) : x; }
__device__ void keccak_f1600(u64 state[ 25]) {
    u64 C[ 5], D[ 5], B[ 25];
    for (int round=0; round<24; round++) {
        for (int i=0;i<5;i++) C[i]=state[i]^state[i+5]^state[i+10]^state[i+15]^state[i+20];
        for (int i=0;i<5;i++) { D[i]=C[(i+4)%5]^rotl64b(C[(i+1)%5],1); for (int j=0;j<25;j+=5) state[j+i]^=D[i]; }
        for (int i=0;i<25;i++) B[i]=state[i];
        int x=1, y=0; u64 cur=B[ 1];
        for (int t=0;t<24;t++) {
            int tmp=x; x=y; y=(2*tmp+3*y)%5;
            u64 tv=B[x+5*y]; B[x+5*y]=rotl64b(cur,(t+1)*(t+2)/2); cur=tv;
        }
        for (int i=1;i<25;i++) state[i]=B[i];
        for (int j=0;j<25;j+=5) {
            for (int i=0;i<5;i++) B[j+i]=state[j+i];
            for (int i=0;i<5;i++) state[j+i]^=(~B[j+(i+1)%5])&B[j+(i+2)%5];
        }
        state[ 0]^=keccak_rc[round];
    }
}
__device__ void device_keccak256(const u8* data, int len, u8 hash[ 32]) {
    u64 state[ 25] = {0}; int rate=136; int off=0;
    while (off+rate<=len) {
        for (int i=0;i<rate/8;i++) {
            u64 val=0;
            for (int j=0;j<8;j++) val |= ((u64)data[off+i*8+j])<<(8*j);
            state[i]^=val;
        }
        keccak_f1600(state); off+=rate;
    }
    u8 blk[ 136] = {0}; int rem=len-off;
    if (rem>0) for (int i=0;i<rem;i++) blk[i]=data[off+i];
    blk[rem]=0x01; blk[rate-1]|=0x80;
    for (int i=0;i<rate/8;i++) {
        u64 val=0;
        for (int j=0;j<8;j++) val |= ((u64)blk[i*8+j])<<(8*j);
        state[i]^=val;
    }
    keccak_f1600(state);
    for (int i=0;i<4;i++) for (int j=0;j<8;j++) hash[i*8+j]=(u8)((state[i]>>(8*j))&0xFF);
}

// ==========================================
// BIP39 编码：128bit 熵 + 4bit 校验和 -> 12 词
// ==========================================
__device__ void entropy_to_mnemonic(const u8 ent[ 16], char* mnem, int* mnem_len) {
    u8 h[ 32];
    sha256(ent, 16, h);
    u16 idx[ 12];
    for (int w=0;w<12;w++) {
        int bp = w*11; u32 val=0;
        for (int b=0;b<11;b++) {
            int p=bp+b; int byte=p>>3, sh=7-(p&7);
            int bit = (byte<16) ? ((ent[byte]>>sh)&1) : ((h[ 0]>>sh)&1);
            val=(val<<1)|bit;
        }
        idx[w]=(u16)val;
    }
    int pos=0;
    for (int w=0;w<12;w++) {
        const char* word = BIP39_WORDS[idx[w]];
        int len=0; while (word[len]) len++;
        for (int i=0;i<len;i++) mnem[pos++]=word[i];
        if (w<11) mnem[pos++]=' ';
    }
    mnem[pos]=0;
    if (mnem_len) *mnem_len=pos;
}

// ==========================================
// BIP32 / BIP44 派生：m/44'/60'/0'/0/0
// ==========================================
__device__ void ckd_priv(u8 k[ 32], u8 c[ 32], u32 index, int hardened) {
    u8 data[ 37], out[ 64];
    if (hardened) {
        data[ 0]=0;
        for (int i=0;i<32;i++) data[1+i]=k[i];
    } else {
        u32 kf[ 8]; bytes32_to_fe(kf, k);
        Jacobian P; scalar_mult_base_comb(P, kf);
        u32 x[ 8], y[ 8]; jac_to_affine(x, y, P);
        u8 xb[ 32]; fe_to_bytes32(xb, x);
        data[ 0] = (y[ 0]&1) ? 0x03 : 0x02;
        for (int i=0;i<32;i++) data[1+i]=xb[i];
    }
    data[33]=(u8)(index>>24); data[34]=(u8)(index>>16); data[35]=(u8)(index>>8); data[36]=(u8)index;
    hmac_sha512_gen(c, 32, data, 37, out);
    u32 il[ 8], kf[ 8], kf2[ 8];
    bytes32_to_fe(il, out);
    bytes32_to_fe(kf, k);
    sc_add_mod_n(kf2, il, kf);
    fe_to_bytes32(k, kf2);
    for (int i=0;i<32;i++) c[i]=out[32+i];
}
__device__ void bip32_derive(u8 privk[ 32], const u8 seed[ 64]) {
    u8 k[ 32], c[ 32], out[ 64];
    hmac_sha512_gen((const u8*)"Bitcoin seed", 12, seed, 64, out);
    for (int i=0;i<32;i++){ k[i]=out[i]; c[i]=out[32+i]; }
    ckd_priv(k, c, 0x80000000u+44u, 1);
    ckd_priv(k, c, 0x80000000u+0u, 1);
    ckd_priv(k, c, 0x80000000u+0u, 1);
    ckd_priv(k, c, 0u, 0);
    ckd_priv(k, c, 0u, 0);
    for (int i=0;i<32;i++) privk[i]=k[i];
}
__device__ void derive_address(const u8 privk[ 32], u8 addr[ 20]) {
    u32 kf[ 8]; bytes32_to_fe(kf, privk);
    Jacobian P; scalar_mult_base_comb(P, kf);
    u32 x[ 8], y[ 8]; jac_to_affine(x, y, P);
    u8 pub[ 64];
    fe_to_bytes32(pub, x);
    fe_to_bytes32(pub+32, y);
    u8 h[ 32];
    device_keccak256(pub, 64, h);
    for (int i=0;i<20;i++) addr[i]=h[12+i];
}
__device__ void derive_full(const u8 ent[ 16], char* mnem, u8 addr[ 20], u8 privk[ 32]) {
    char m[ 128];
    entropy_to_mnemonic(ent, m, 0);
    u8 seed[ 64];
    device_bip39_seed(m, seed);
    bip32_derive(privk, seed);
    derive_address(privk, addr);
    if (mnem) { int l=0; while (m[l]){ mnem[l]=m[l]; l++; } mnem[l]=0; }
}

// ==========================================
// Kernel：vec 诊断（逐层输出中间值）
// ==========================================
__global__ void vec_kernel(const u8* d_ent, u8* d_out, u32* d_done) {
    if (threadIdx.x!=0 || blockIdx.x!=0) return;
    u8 ent[ 16];
    for (int i=0;i<16;i++) ent[i]=d_ent[i];
    char m[ 128];
    entropy_to_mnemonic(ent, m, 0);
    int o=0;
    for (int i=0;i<16;i++) d_out[o++]=ent[i];
    u8 seed[ 64];
    device_bip39_seed(m, seed);
    for (int i=0;i<64;i++) d_out[o++]=seed[i];
    u8 k[ 32], c[ 32], out[ 64];
    hmac_sha512_gen((const u8*)"Bitcoin seed", 12, seed, 64, out);
    for (int i=0;i<32;i++){ k[i]=out[i]; c[i]=out[32+i]; }
    for (int i=0;i<32;i++) d_out[o++]=k[i];
    for (int i=0;i<32;i++) d_out[o++]=c[i];
    ckd_priv(k, c, 0x80000000u+44u, 1);
    for (int i=0;i<32;i++) d_out[o++]=k[i];
    for (int i=0;i<32;i++) d_out[o++]=c[i];
    ckd_priv(k, c, 0x80000000u+0u, 1);
    for (int i=0;i<32;i++) d_out[o++]=k[i];
    for (int i=0;i<32;i++) d_out[o++]=c[i];
    ckd_priv(k, c, 0x80000000u+0u, 1);
    for (int i=0;i<32;i++) d_out[o++]=k[i];
    for (int i=0;i<32;i++) d_out[o++]=c[i];
    ckd_priv(k, c, 0u, 0);
    for (int i=0;i<32;i++) d_out[o++]=k[i];
    ckd_priv(k, c, 0u, 0);
    for (int i=0;i<32;i++) d_out[o++]=k[i];
    u32 kf[ 8]; bytes32_to_fe(kf, k);
    Jacobian P; scalar_mult_base(P, kf);
    u32 x[ 8], y[ 8]; jac_to_affine(x, y, P);
    u8 xb[ 32], yb[ 32];
    fe_to_bytes32(xb, x); fe_to_bytes32(yb, y);
    for (int i=0;i<32;i++) d_out[o++]=xb[i];
    for (int i=0;i<32;i++) d_out[o++]=yb[i];
    u8 pub[ 64];
    for (int i=0;i<32;i++) pub[i]=xb[i];
    for (int i=0;i<32;i++) pub[32+i]=yb[i];
    u8 h[ 32];
    device_keccak256(pub, 64, h);
    for (int i=0;i<20;i++) d_out[o++]=h[12+i];
    int l=0; while (m[l]){ d_out[o++]=m[l]; l++; }
    d_out[o]=0;
    d_done[ 0]=1;
}

// ==========================================
// Kernel：selftest
// ==========================================
__global__ void selftest_kernel(u64* d_out, u32* d_done) {
    if (threadIdx.x!=0 || blockIdx.x!=0) return;
    fe a; for (int i=0;i<8;i++) a[i]=0xFFFFFFFFu;
    fe b; fe_set1(b);
    fe r; fe_add(r, a, b);
    u64 v0=0; for (int i=7;i>=0;i--) v0=(v0<<32)|r[i];
    d_out[ 0]=v0;
    fe m1; fe_set0(m1); m1[ 0]=123456789u;
    fe m2; fe_set0(m2); m2[ 0]=987654321u;
    fe_mul(r, m1, m2);
    u64 v1=0; for (int i=7;i>=0;i--) v1=(v1<<32)|r[i];
    d_out[ 1]=v1;
    fe two; fe_set0(two); two[ 0]=2u;
    Jacobian P2; scalar_mult_base(P2, two);
    u32 x[ 8], y[ 8]; jac_to_affine(x, y, P2);
    u64 v2x=0, v2y=0; for (int i=7;i>=0;i--){ v2x=(v2x<<32)|x[i]; v2y=(v2y<<32)|y[i]; }
    d_out[ 2]=v2x; d_out[ 3]=v2y;
    fe one; fe_set1(one);
    Jacobian P1; scalar_mult_base(P1, one);
    u32 x1[ 8], y1[ 8]; jac_to_affine(x1, y1, P1);
    u64 v3x=0, v3y=0; for (int i=7;i>=0;i--){ v3x=(v3x<<32)|x1[i]; v3y=(v3y<<32)|y1[i]; }
    d_out[ 4]=v3x; d_out[ 5]=v3y;
    u32 nm1[ 8]; fe_cpy(nm1, N_FE); nm1[ 0]-=1;
    u32 one32[ 8]; fe_set1(one32);
    u32 sr[ 8]; sc_add_mod_n(sr, nm1, one32);
    u64 v4=0; for (int i=7;i>=0;i--) v4=(v4<<32)|sr[i];
    d_out[ 6]=v4;
    u32 nm2[ 8]; fe_cpy(nm2, N_FE); nm2[ 0]-=2;
    u32 three[ 8]; fe_set0(three); three[ 0]=3;
    sc_add_mod_n(sr, nm2, three);
    u64 v5=0; for (int i=7;i>=0;i--) v5=(v5<<32)|sr[i];
    d_out[ 7]=v5;
    Jacobian P3a; jac_add_affine(P3a, P2, GX_FE, GY_FE);
    u32 x3[ 8], y3[ 8]; jac_to_affine(x3, y3, P3a);
    fe three3; fe_set0(three3); three3[ 0]=3;
    Jacobian P3b; scalar_mult_base(P3b, three3);
    u32 x3b[ 8], y3b[ 8]; jac_to_affine(x3b, y3b, P3b);
    u64 v6=0; for (int i=7;i>=0;i--) v6=(v6<<32)|x3[i];
    u64 v6b=0; for (int i=7;i>=0;i--) v6b=(v6b<<32)|x3b[i];
    d_out[ 8]=v6; d_out[ 9]=v6b;
    fe inv; fe_inv(inv, m1);
    fe_mul(r, m1, inv);
    u64 v7=0; for (int i=7;i>=0;i--) v7=(v7<<32)|r[i];
    d_out[ 10]=v7;
    d_done[ 0]=1;
}

// ==========================================
// Kernel：jac_double(G) 中间量诊断
// ==========================================
__global__ void jdbl_kernel(u32* d_out, u32* d_done) {
    if (threadIdx.x!=0 || blockIdx.x!=0) return;
    fe A, B, C, D, E, F, t, t2, F0, t0;
    fe_sqr(A, GX_FE);
    fe_sqr(B, GY_FE);
    fe_sqr(C, B);
    fe_add(t, GX_FE, B); fe_sqr(t, t);
    fe_sub(t, t, A); fe_sub(t, t, C);
    fe_add(D, t, t);
    fe_add(E, A, A); fe_add(E, E, A);
    fe_sqr(F, E);
    fe_cpy(F0, F);
    fe_add(t, D, D);
    fe_cpy(t0, t);
    fe_sub(t, F0, t0);
    fe_sub(t2, D, t);
    fe_mul(t2, t2, E);
    fe_add(F, C, C); fe_add(F, F, F); fe_add(F, F, F);
    fe_sub(t2, t2, F);
    fe_mul(F, GY_FE, GX_FE); fe_add(F, F, F);
    int o=0;
    for (int s=0;s<8;s++) d_out[o++]=A[s];
    for (int s=0;s<8;s++) d_out[o++]=B[s];
    for (int s=0;s<8;s++) d_out[o++]=C[s];
    for (int s=0;s<8;s++) d_out[o++]=D[s];
    for (int s=0;s<8;s++) d_out[o++]=E[s];
    for (int s=0;s<8;s++) d_out[o++]=F0[s];  // E^2
    for (int s=0;s<8;s++) d_out[o++]=t0[s];  // 2D
    for (int s=0;s<8;s++) d_out[o++]=t[s];   // X3
    for (int s=0;s<8;s++) d_out[o++]=t2[s];  // Y3
    for (int s=0;s<8;s++) d_out[o++]=F[s];   // Z3
    d_done[ 0]=1;
}

// ==========================================
// Kernel：最小化 scalar_mult_base(k0h) 诊断
// ==========================================

// ==========================================
// Kernel: keccak test
// ==========================================
__global__ void ktest_kernel(u8* d_out, u32* d_done) {
    if (threadIdx.x!=0 || blockIdx.x!=0) return;
    u8 h[ 32];
    device_keccak256((const u8*)"", 0, h);
    for (int i=0;i<32;i++) d_out[i]=h[i];
    device_keccak256((const u8*)"abc", 3, h);
    for (int i=0;i<32;i++) d_out[32+i]=h[i];
    const u8 pub[ 64] = {
        0x37,0xb0,0xbb,0x7a,0x82,0x88,0xd3,0x8e,0xd4,0x9a,0x52,0x4b,0x5d,0xc9,0x8c,0xff,
        0x3e,0xb5,0xca,0x82,0x4c,0x9f,0x9d,0xc0,0xdf,0xdb,0x3d,0x9c,0xd6,0x00,0xf2,0x99,
        0xa6,0x17,0x99,0x12,0xb7,0x45,0x1c,0x09,0x89,0x6c,0x40,0x98,0xec,0xa7,0xce,0x6b,
        0x2e,0x58,0x33,0x06,0x72,0x79,0x5e,0x84,0x7c,0x4d,0x6a,0xf4,0x4e,0x02,0x42,0x30 };
    device_keccak256(pub, 64, h);
    for (int i=0;i<32;i++) d_out[64+i]=h[i];
    u64 st[ 25] = {0};
    keccak_f1600(st);
    for (int i=0;i<8;i++) d_out[96+i]=(u8)((st[ 0]>>(8*i))&0xFF);
    d_done[ 0]=1;
}

__global__ void sm_kernel(u32* d_out, u32* d_done, int c) {
    if (threadIdx.x!=0 || blockIdx.x!=0) return;
    u32 kf[ 8] = {0,0,0,0,0,0,0,0};
    if (c==0) { // k0h
        const u8 kh[ 32] = { 0xe9,0xb9,0x1c,0x42,0x8e,0x67,0x9f,0x85,0x7f,0xbf,0xa0,0x20,0x34,0x40,0xea,0xea,
                             0xab,0xb0,0xca,0x46,0xd8,0x0e,0x70,0xb6,0xaa,0x62,0x50,0x69,0x6a,0xc0,0xdf,0xc7 };
        bytes32_to_fe(kf, kh);
    } else if (c==1) { kf[ 7]=0x80000000u; } // 2^255
    else if (c==2) { kf[ 7]=0xe9b91c42u; }  // top 32 bits of k0h
    else if (c==3) { kf[ 0]=0xe9u; }        // 0xe9
    else if (c==4) { kf[ 7]=0x00000080u; }  // 2^247
    else if (c==5) { kf[ 0]=0x0au; }        // 10G
    Jacobian P; scalar_mult_base(P, kf);
    if (c==1 || c==5) {
        for (int i=0;i<8;i++) d_out[i]=P.X[i];
        for (int i=0;i<8;i++) d_out[8+i]=P.Y[i];
        for (int i=0;i<8;i++) d_out[16+i]=P.Z[i];
        d_done[ 0]=1; return;
    }
    u32 x[ 8], y[ 8]; jac_to_affine(x, y, P);
    for (int i=0;i<8;i++) d_out[i]=x[i];
    for (int i=0;i<8;i++) d_out[8+i]=y[i];
    d_done[ 0]=1;
}

// ==========================================
// Kernel：ptest 点运算诊断（2G/3G/pubkey(k0h)）
// ==========================================
__global__ void ptest_kernel(u32* d_out, u32* d_done) {
    if (threadIdx.x!=0 || blockIdx.x!=0) return;
    int o=0;
    fe two; fe_set0(two); two[ 0]=2u;
    Jacobian P2; scalar_mult_base(P2, two);
    u32 x2[ 8], y2[ 8]; jac_to_affine(x2, y2, P2);
    for (int i=7;i>=0;i--) d_out[o++]=x2[i];
    for (int i=7;i>=0;i--) d_out[o++]=y2[i];
    fe three; fe_set0(three); three[ 0]=3u;
    Jacobian P3; scalar_mult_base(P3, three);
    u32 x3[ 8], y3[ 8]; jac_to_affine(x3, y3, P3);
    for (int i=7;i>=0;i--) d_out[o++]=x3[i];
    for (int i=7;i>=0;i--) d_out[o++]=y3[i];
    fe four; fe_set0(four); four[ 0]=4u;
    Jacobian P4; scalar_mult_base(P4, four);
    u32 x4[ 8], y4[ 8]; jac_to_affine(x4, y4, P4);
    for (int i=7;i>=0;i--) d_out[o++]=x4[i];
    for (int i=7;i>=0;i--) d_out[o++]=y4[i];
    fe five; fe_set0(five); five[ 0]=5u;
    Jacobian P5; scalar_mult_base(P5, five);
    u32 x5[ 8], y5[ 8]; jac_to_affine(x5, y5, P5);
    for (int i=7;i>=0;i--) d_out[o++]=x5[i];
    for (int i=7;i>=0;i--) d_out[o++]=y5[i];
    fe seven; fe_set0(seven); seven[ 0]=7u;
    Jacobian P7; scalar_mult_base(P7, seven);
    u32 x7[ 8], y7[ 8]; jac_to_affine(x7, y7, P7);
    for (int i=7;i>=0;i--) d_out[o++]=x7[i];
    for (int i=7;i>=0;i--) d_out[o++]=y7[i];
    fe eight; fe_set0(eight); eight[ 0]=8u;
    Jacobian P8; scalar_mult_base(P8, eight);
    u32 x8[ 8], y8[ 8]; jac_to_affine(x8, y8, P8);
    for (int i=7;i>=0;i--) d_out[o++]=x8[i];
    for (int i=7;i>=0;i--) d_out[o++]=y8[i];
    d_done[ 0]=1;
}

// ==========================================
// Kernel：sc_add_mod_n 诊断（IL + master_k）
// ==========================================
__global__ void scdiag_kernel(u32* d_out, u32* d_done) {
    if (threadIdx.x!=0 || blockIdx.x!=0) return;
    // IL (b50e42e12a00b9e0abc8d9a1ced0f570252afcf07ed746e16d9d3a12dcc7d883)
    const u8 ilb[ 32] = { 0xb5,0x0e,0x42,0xe1,0x2a,0x00,0xb9,0xe0,0xab,0xc8,0xd9,0xa1,0xce,0xd0,0xf5,0x70,
                          0x25,0x2a,0xfc,0xf0,0x7e,0xd7,0x46,0xe1,0x6d,0x9d,0x3a,0x12,0xdc,0xc7,0xd8,0x83 };
    // master_k (1837c1be8e2995ec11cda2b066151be2cfb48adf9e47b151d46adab3a21cdf67)
    const u8 kb[ 32] = { 0x18,0x37,0xc1,0xbe,0x8e,0x29,0x95,0xec,0x11,0xcd,0xa2,0xb0,0x66,0x15,0x1b,0xe2,
                         0xcf,0xb4,0x8a,0xdf,0x9e,0x47,0xb1,0x51,0xd4,0x6a,0xda,0xb3,0xa2,0x1c,0xdf,0x67 };
    u32 il[ 8], kf[ 8], r[ 8];
    bytes32_to_fe(il, ilb);
    bytes32_to_fe(kf, kb);
    int o=0;
    for (int i=0;i<8;i++) d_out[o++]=il[i];
    for (int i=0;i<8;i++) d_out[o++]=kf[i];
    u64 c=0; u32 t[ 9];
    for (int i=0;i<8;i++){ u64 s=(u64)il[i]+kf[i]+c; t[i]=(u32)s; c=s>>32; }
    t[ 8]=(u32)c;
    for (int i=0;i<9;i++) d_out[o++]=t[i];
    sc_add_mod_n(r, il, kf);
    for (int i=0;i<8;i++) d_out[o++]=r[i];
    // fe_ge check result
    d_out[o++]=fe_ge(t, N_FE);
    d_out[o++]=t[ 8];
    d_done[ 0]=1;
}

// ==========================================
// Kernel：字段测试
// ==========================================
__global__ void fieldtest_kernel(u32* d_out) {
    if (threadIdx.x!=0 || blockIdx.x!=0) return;
    int o=0;
    fe a; for (int i=0;i<8;i++) a[i]=0xFFFFFFFFu; a[ 0]=0xFFFFFC2Eu; a[ 1]=0xFFFFFFFEu;
    fe r;
    fe_mul(r, a, a);
    for (int i=0;i<8;i++) d_out[o++]=r[i];
    fe b; for (int i=0;i<8;i++) b[i]=0xFFFFFFFFu; b[ 0]=0xFFFFFC2Du; b[ 1]=0xFFFFFFFEu;
    fe_mul(r, b, a);
    for (int i=0;i<8;i++) d_out[o++]=r[i];
    fe c2; fe_set0(c2); c2[ 7]=0x80000000u;
    fe_mul(r, c2, c2);
    for (int i=0;i<8;i++) d_out[o++]=r[i];
    fe d2; for (int i=0;i<8;i++) d2[i]=0xAAAAAAAAu;
    fe_mul(r, d2, d2);
    for (int i=0;i<8;i++) d_out[o++]=r[i];
    fe e2; e2[ 0]=0x12345678u; e2[ 1]=0x9abcdef0u; e2[ 2]=0x11223344u; e2[ 3]=0x55667788u;
    e2[ 4]=0x99aabbccu; e2[ 5]=0xddeeff00u; e2[ 6]=0x10203040u; e2[ 7]=0x50607080u;
    fe_mul(r, e2, e2);
    for (int i=0;i<8;i++) d_out[o++]=r[i];
    fe f1; for (int i=0;i<8;i++) f1[i]=0xFFFFFFFFu;
    fe f2; fe_set0(f2); f2[ 0]=0x00000001u; f2[ 1]=0x00000001u;
    fe_add(r, f1, f2);
    for (int i=0;i<8;i++) d_out[o++]=r[i];
    fe g2; g2[ 0]=0x12345678u; g2[ 1]=0x9abcdef0u; g2[ 2]=0x11223344u; g2[ 3]=0x55667788u;
    g2[ 4]=0x99aabbccu; g2[ 5]=0xddeeff00u; g2[ 6]=0x10203040u; g2[ 7]=0x50607080u;
    fe_inv(r, g2);
    fe_mul(r, r, g2);
    for (int i=0;i<8;i++) d_out[o++]=r[i];
    u32 nm1[ 8]; fe_cpy(nm1, N_FE); nm1[ 0]-=1;
    u32 two[ 8]; fe_set0(two); two[ 0]=2u;
    u32 sr[ 8]; sc_add_mod_n(sr, nm1, two);
    for (int i=0;i<8;i++) d_out[o++]=sr[i];
}

// ==========================================
// Kernel：fieldtest 进度标记版（定位挂起用例）
// ==========================================
__global__ void ftprog_kernel(u32* d_out, u32* d_prog) {
    if (threadIdx.x!=0 || blockIdx.x!=0) return;
    int o=0;
    fe r;
    d_prog[ 0]=1;
    fe a; for (int i=0;i<8;i++) a[i]=0xFFFFFFFFu; a[ 0]=0xFFFFFC2Eu; a[ 1]=0xFFFFFFFEu;
    fe_mul(r, a, a);
    for (int i=0;i<8;i++) d_out[o++]=r[i];
    d_prog[ 0]=2;
    fe b; for (int i=0;i<8;i++) b[i]=0xFFFFFFFFu; b[ 0]=0xFFFFFC2Du; b[ 1]=0xFFFFFFFEu;
    fe_mul(r, b, a);
    for (int i=0;i<8;i++) d_out[o++]=r[i];
    d_prog[ 0]=3;
    fe c2; fe_set0(c2); c2[ 7]=0x80000000u;
    fe_mul(r, c2, c2);
    for (int i=0;i<8;i++) d_out[o++]=r[i];
    d_prog[ 0]=4;
    fe d2; for (int i=0;i<8;i++) d2[i]=0xAAAAAAAAu;
    fe_mul(r, d2, d2);
    for (int i=0;i<8;i++) d_out[o++]=r[i];
    d_prog[ 0]=5;
    fe e2; e2[ 0]=0x12345678u; e2[ 1]=0x9abcdef0u; e2[ 2]=0x11223344u; e2[ 3]=0x55667788u;
    e2[ 4]=0x99aabbccu; e2[ 5]=0xddeeff00u; e2[ 6]=0x10203040u; e2[ 7]=0x50607080u;
    fe_mul(r, e2, e2);
    for (int i=0;i<8;i++) d_out[o++]=r[i];
    d_prog[ 0]=6;
    fe f1; for (int i=0;i<8;i++) f1[i]=0xFFFFFFFFu;
    fe f2; fe_set0(f2); f2[ 0]=0x00000001u; f2[ 1]=0x00000001u;
    fe_add(r, f1, f2);
    for (int i=0;i<8;i++) d_out[o++]=r[i];
    d_prog[ 0]=7;
    fe g2; g2[ 0]=0x12345678u; g2[ 1]=0x9abcdef0u; g2[ 2]=0x11223344u; g2[ 3]=0x55667788u;
    g2[ 4]=0x99aabbccu; g2[ 5]=0xddeeff00u; g2[ 6]=0x10203040u; g2[ 7]=0x50607080u;
    fe_inv(r, g2);
    fe_mul(r, r, g2);
    for (int i=0;i<8;i++) d_out[o++]=r[i];
    d_prog[ 0]=8;
    u32 nm1[ 8]; fe_cpy(nm1, N_FE); nm1[ 0]-=1;
    u32 two[ 8]; fe_set0(two); two[ 0]=2u;
    u32 sr[ 8]; sc_add_mod_n(sr, nm1, two);
    for (int i=0;i<8;i++) d_out[o++]=sr[i];
    d_prog[ 0]=9;
}

// ==========================================
// Kernel：单用例 bisect（定位 GPU 挂起用例）
// ==========================================
__global__ void bisect_kernel(u32* d_out, int c) {
    if (threadIdx.x!=0 || blockIdx.x!=0) return;
    fe r;
    if (c==0) { fe a; for (int i=0;i<8;i++) a[i]=0xFFFFFFFFu; a[ 0]=0xFFFFFC2Eu; a[ 1]=0xFFFFFFFEu; fe_mul(r, a, a); }
    else if (c==1) { fe a; for (int i=0;i<8;i++) a[i]=0xFFFFFFFFu; a[ 0]=0xFFFFFC2Eu; a[ 1]=0xFFFFFFFEu;
                     fe b; for (int i=0;i<8;i++) b[i]=0xFFFFFFFFu; b[ 0]=0xFFFFFC2Du; b[ 1]=0xFFFFFFFEu; fe_mul(r, b, a); }
    else if (c==2) { fe c2; fe_set0(c2); c2[ 7]=0x80000000u; fe_mul(r, c2, c2); }
    else if (c==3) { fe d2; for (int i=0;i<8;i++) d2[i]=0xAAAAAAAAu; fe_mul(r, d2, d2); }
    else if (c==4) { fe e2; e2[ 0]=0x12345678u; e2[ 1]=0x9abcdef0u; e2[ 2]=0x11223344u; e2[ 3]=0x55667788u;
                     e2[ 4]=0x99aabbccu; e2[ 5]=0xddeeff00u; e2[ 6]=0x10203040u; e2[ 7]=0x50607080u; fe_mul(r, e2, e2); }
    else if (c==5) { fe f1; for (int i=0;i<8;i++) f1[i]=0xFFFFFFFFu;
                     fe f2; fe_set0(f2); f2[ 0]=0x00000001u; f2[ 1]=0x00000001u; fe_add(r, f1, f2); }
    else if (c==6) { fe g2; g2[ 0]=0x12345678u; g2[ 1]=0x9abcdef0u; g2[ 2]=0x11223344u; g2[ 3]=0x55667788u;
                     g2[ 4]=0x99aabbccu; g2[ 5]=0xddeeff00u; g2[ 6]=0x10203040u; g2[ 7]=0x50607080u;
                     fe_inv(r, g2); fe_mul(r, r, g2); }
    else if (c==7) { u32 nm1[ 8]; fe_cpy(nm1, N_FE); nm1[ 0]-=1;
           u32 two[ 8]; fe_set0(two); two[ 0]=2u;
           sc_add_mod_n(r, nm1, two); }
    else if (c==8) { // fe_add(D,D); D=cbc1950e... -> expect 97832a1c...
           u32 D[ 8] = { 0x69cfc671u, 0xd2076736u, 0xf147c112u, 0x6bcb0bbcu, 0xcb96483du, 0xd0271c6bu, 0x6fec4514u, 0xcbc1950eu };
           fe_add(r, D, D); }
    else if (c==9) { // fe_sub(F, T); F=E^2 mod p, T=2D mod p -> expect X3
           u32 F[ 8] = { 0x87054446u, 0x35e2d2b3u, 0xd92564edu, 0x8e25a078u, 0xb6d66bd0u, 0xc1dfbd14u, 0xfe816c05u, 0x14985620u };
           u32 T[ 8] = { 0xd39f90b3u, 0xa40ece6du, 0xe28f8225u, 0xd7961779u, 0x972c907au, 0xa04e38d7u, 0xdfd88a29u, 0x97832a1cu };
           fe_sub(r, F, T); }
    else { u32 nm1[ 8]; fe_cpy(nm1, N_FE); nm1[ 0]-=1;
           u32 two[ 8]; fe_set0(two); two[ 0]=2u;
           sc_add_mod_n(r, nm1, two); }
    for (int i=0;i<8;i++) d_out[i]=r[i];
}

// ==========================================
// Kernel：debug（(p-1)^2 中间量转储）
// ==========================================
__global__ void debug_kernel(u32* d_out) {
    if (threadIdx.x!=0 || blockIdx.x!=0) return;
    int o=0;
    fe a; for (int i=0;i<8;i++) a[i]=0xFFFFFFFFu; a[ 0]=0xFFFFFC2Eu; a[ 1]=0xFFFFFFFEu;
    u32 t[ 16];
    for (int i=0;i<16;i++) t[i]=0;
    for (int i=0;i<8;i++)
        for (int j=0;j<8;j++) {
            u64 p = (u64)a[i]*a[j];
            u64 s = (u64)t[i+j] + (u32)p;
            t[i+j] = (u32)s;
            u64 c = s >> 32;
            int k = i+j+1;
            while (c && k < 16) { u64 s2=(u64)t[k]+c; t[k]=(u32)s2; c=s2>>32; k++; }
            s = (u64)t[i+j+1] + (u32)(p>>32);
            t[i+j+1] = (u32)s;
            c = s >> 32;
            k = i+j+2;
            while (c && k < 16) { u64 s2=(u64)t[k]+c; t[k]=(u32)s2; c=s2>>32; k++; }
        }
    for (int i=0;i<16;i++) d_out[o++]=t[i];       // 0-15: 原始乘积
    u32 v[ 10];
    u64 c=0;
    for (int i=0;i<10;i++){
        u64 s = c + (i<8 ? (u64)t[i] : 0);
        if (i>=1 && (i-1)<8) s += (u64)t[ 8+(i-1)];
        if (i<8) s += (u64)t[ 8+i]*977u;
        v[i]=(u32)s; c=s>>32;
    }
    if (c){ u64 s=(u64)v[ 9]+c; v[ 9]=(u32)s; }
    for (int i=0;i<10;i++) d_out[o++]=v[i];       // 16-25: 初始折叠 v
    fe_fold_hi(v);
    for (int i=0;i<10;i++) d_out[o++]=v[i];       // 26-35: fe_fold_hi 后 v
    fe r; fe_mul(r, a, a);
    for (int i=0;i<8;i++) d_out[o++]=r[i];        // 36-43: fe_mul 结果
}

// ==========================================
// Kernel：固定熵测试（BIP39 标准向量）
// ==========================================
__global__ void test_kernel(const u8* d_ent, char* d_mnem, u8* d_addr, u8* d_priv, u32* d_done) {
    if (threadIdx.x!=0 || blockIdx.x!=0) return;
    u8 ent[ 16];
    for (int i=0;i<16;i++) ent[i]=d_ent[i];
    char mnem[ 128];
    u8 addr[ 20], privk[ 32];
    derive_full(ent, mnem, addr, privk);
    int l=0; while (mnem[l]){ d_mnem[l]=mnem[l]; l++; } d_mnem[l]=0;
    for (int i=0;i<20;i++) d_addr[i]=addr[i];
    for (int i=0;i<32;i++) d_priv[i]=privk[i];
    d_done[ 0]=1;
}

// ==========================================
// Kernel：vanity 搜索
// ==========================================


// ==========================================
// HD 快速模式：固定种子，变索引 m/44'/60'/0'/0/N 搜索
// setup: 熵->助记词->seed->派生到 m/44'/60'/0'/0 (k0n,c0n) + pubkey(k0n)
// search: N 变化 -> k_N = IL + k0n (mod n) -> pubkey -> keccak -> 前缀比对
// ==========================================
__global__ void hd_setup_kernel(u64 base_nonce, u32* d_kbase, u32* d_cbase, u32* d_pubx, u32* d_puby, char* d_mnem) {
    if (threadIdx.x!=0 || blockIdx.x!=0) return;
    u8 nb[ 8]; for (int i=0;i<8;i++) nb[i]=(u8)(base_nonce>>(8*i));
    u8 h[ 32]; sha256(nb, 8, h);
    u8 ent[ 16]; for (int i=0;i<16;i++) ent[i]=h[i];
    char m[ 128]; entropy_to_mnemonic(ent, m, 0);
    int l=0; while(m[l]){ d_mnem[l]=m[l]; l++; } d_mnem[l]=0;
    u8 seed[ 64]; device_bip39_seed(m, seed);
    // master
    u8 k[ 32], c[ 32], out[ 64];
    hmac_sha512_gen((const u8*)"Bitcoin seed", 12, seed, 64, out);
    for (int i=0;i<32;i++){ k[i]=out[i]; c[i]=out[32+i]; }
    // 44' 60' 0'
    ckd_priv(k, c, 0x80000000u+44u, 1);
    ckd_priv(k, c, 0x80000000u+0u, 1);
    ckd_priv(k, c, 0x80000000u+0u, 1);
    // 0 (non-hardened) -> k0n
    u8 k0n[ 32], c0n[ 32];
    for (int i=0;i<32;i++){ k0n[i]=k[i]; c0n[i]=c[i]; }
    ckd_priv(k0n, c0n, 0u, 0);
    // 先写 kbase/cbase，再算 pubkey（避免 comb 潜在污染）
    u32 kb[ 8], cb[ 8];
    bytes32_to_fe(kb, k0n); bytes32_to_fe(cb, c0n);
    for (int i=0;i<8;i++){ d_kbase[i]=kb[i]; d_cbase[i]=cb[i]; }
    // pubkey(k0n)
    u32 kf[ 8]; bytes32_to_fe(kf, k0n);
    Jacobian P; scalar_mult_base_comb(P, kf);
    u32 x[ 8], y[ 8]; jac_to_affine(x, y, P);
    for (int i=0;i<8;i++){ d_pubx[i]=x[i]; d_puby[i]=y[i]; }
}

__global__ __launch_bounds__(256, 2) void hd_vanity_kernel(const u8* d_prefix, int plen,
        const u32* d_kbase, const u32* d_cbase, const u32* d_pubx, const u32* d_puby,
        u64 start_nonce, int iters, char* d_mnem, u8* d_addr, u8* d_priv, u32* d_index, u32* d_found) {
    u64 tid = (u64)blockIdx.x*blockDim.x + threadIdx.x;
    for (int it=0; it<iters; it++) {
        if (*d_found) return;
        u64 n = start_nonce + tid + (u64)it*gridDim.x*blockDim.x;
        u32 N = (u32)(n & 0x7FFFFFFFu);
        // IL = HMAC-SHA512(c0n, 0x02/03||X || N)
        u32 cb[ 8]; for (int i=0;i<8;i++) cb[i]=d_cbase[i];
        u8 c8[ 32]; fe_to_bytes32(c8, cb);
        u8 data[ 37];
        data[ 0] = (d_puby[ 0]&1) ? 0x03 : 0x02;
        u8 xb[ 32]; fe_to_bytes32(xb, d_pubx);
        for (int i=0;i<32;i++) data[1+i]=xb[i];
        data[ 33]=(u8)(N>>24); data[ 34]=(u8)(N>>16); data[ 35]=(u8)(N>>8); data[ 36]=(u8)N;
        u8 out[ 64];
        hmac_sha512_gen(c8, 32, data, 37, out);
        u32 il[ 8]; bytes32_to_fe(il, out);
        u32 kf[ 8]; for (int i=0;i<8;i++) kf[i]=d_kbase[i];
        sc_add_mod_n(kf, il, kf);
        Jacobian P; scalar_mult_base_comb(P, kf);
        u32 x[ 8], y[ 8]; jac_to_affine(x, y, P);
        u8 pub[ 64];
        fe_to_bytes32(pub, x);
        fe_to_bytes32(pub+32, y);
        u8 hh[ 32];
        device_keccak256(pub, 64, hh);
        u8 addr[ 20]; for (int i=0;i<20;i++) addr[i]=hh[12+i];
        int ok=1;
        for (int i=0;i<plen;i++) {
            u8 nib = (i&1) ? (addr[i>>1]&0xF) : (addr[i>>1]>>4);
            if (nib != d_prefix[i]) { ok=0; break; }
        }
        if (ok) {
            u32 old = atomicCAS(d_found, 0, 1);
            if (old==0) {
                u8 privk[ 32]; fe_to_bytes32(privk, kf);
                for (int i=0;i<20;i++) d_addr[i]=addr[i];
                for (int i=0;i<32;i++) d_priv[i]=privk[i];
                d_index[ 0]=N;
            }
            return;
        }
    }
}

__global__ void hd_diag_kernel(u64 base_nonce, u8* d_out, u32* d_done) {
    if (threadIdx.x!=0 || blockIdx.x!=0) return;
    u8 nb[ 8]; for (int i=0;i<8;i++) nb[i]=(u8)(base_nonce>>(8*i));
    u8 h[ 32]; sha256(nb, 8, h);
    u8 ent[ 16]; for (int i=0;i<16;i++) ent[i]=h[i];
    char m[ 128]; entropy_to_mnemonic(ent, m, 0);
    for (int i=0;i<128;i++) d_out[i]=(u8)m[i]; // mnemonic bytes 0..127
    u8 seed[ 64]; device_bip39_seed(m, seed);
    for (int i=0;i<64;i++) d_out[128+i]=seed[i];
    u8 k[ 32], c[ 32], out[ 64];
    hmac_sha512_gen((const u8*)"Bitcoin seed", 12, seed, 64, out);
    for (int i=0;i<32;i++){ k[i]=out[i]; c[i]=out[32+i]; }
    ckd_priv(k, c, 0x80000000u+44u, 1);
    ckd_priv(k, c, 0x80000000u+0u, 1);
    ckd_priv(k, c, 0x80000000u+0u, 1);
    for (int i=0;i<32;i++) d_out[192+i]=k[i];  // k0h
    for (int i=0;i<32;i++) d_out[224+i]=c[i];  // c0h
    u8 k0n[ 32], c0n[ 32];
    for (int i=0;i<32;i++){ k0n[i]=k[i]; c0n[i]=c[i]; }
    ckd_priv(k0n, c0n, 0u, 0);
    for (int i=0;i<32;i++) d_out[256+i]=k0n[i]; // k0n
    for (int i=0;i<32;i++) d_out[288+i]=c0n[i]; // c0n
    u32 kf[ 8]; bytes32_to_fe(kf, k0n);
    Jacobian P; scalar_mult_base_comb(P, kf);
    u32 x[ 8], y[ 8]; jac_to_affine(x, y, P);
    u8 xb[ 32]; fe_to_bytes32(xb, x);
    for (int i=0;i<32;i++) d_out[320+i]=xb[i]; // pubx
    d_done[ 0]=1;
}

__global__ void hd_diag2_kernel(u64 base_nonce, u32 N, u8* d_out, u32* d_done) {
    if (threadIdx.x!=0 || blockIdx.x!=0) return;
    u8 nb[ 8]; for (int i=0;i<8;i++) nb[i]=(u8)(base_nonce>>(8*i));
    u8 h[ 32]; sha256(nb, 8, h);
    u8 ent[ 16]; for (int i=0;i<16;i++) ent[i]=h[i];
    char m[ 128]; entropy_to_mnemonic(ent, m, 0);
    for (int i=0;i<128;i++) d_out[i]=(u8)m[i];
    u8 seed[ 64]; device_bip39_seed(m, seed);
    u8 k[ 32], c[ 32], out[ 64];
    hmac_sha512_gen((const u8*)"Bitcoin seed", 12, seed, 64, out);
    for (int i=0;i<32;i++){ k[i]=out[i]; c[i]=out[32+i]; }
    ckd_priv(k, c, 0x80000000u+44u, 1);
    ckd_priv(k, c, 0x80000000u+0u, 1);
    ckd_priv(k, c, 0x80000000u+0u, 1);
    u8 k0n[ 32], c0n[ 32];
    for (int i=0;i<32;i++){ k0n[i]=k[i]; c0n[i]=c[i]; }
    ckd_priv(k0n, c0n, 0u, 0);
    // ===== 完全复用 hd_vanity_kernel 的 search 计算路径 (N=0) =====
    u32 kf0[ 8]; bytes32_to_fe(kf0, k0n);
    Jacobian P0; scalar_mult_base_comb(P0, kf0);
    u32 px[ 8], py[ 8]; jac_to_affine(px, py, P0);
    u32 cb[ 8]; bytes32_to_fe(cb, c0n);
    u8 c8[ 32]; fe_to_bytes32(c8, cb);
    u8 data[ 37];
    data[ 0] = (py[ 0]&1) ? 0x03 : 0x02;
    u8 xb[ 32]; fe_to_bytes32(xb, px);
    for (int i=0;i<32;i++) data[1+i]=xb[i];
    data[33]=(u8)(N>>24); data[34]=(u8)(N>>16); data[35]=(u8)(N>>8); data[36]=(u8)N;
    u8 o2[ 64];
    hmac_sha512_gen(c8, 32, data, 37, o2);
    u32 il[ 8]; bytes32_to_fe(il, o2);
    u32 kf[ 8]; for (int i=0;i<8;i++) kf[i]=kf0[i];
    sc_add_mod_n(kf, il, kf);
    u8 kchild[ 32]; fe_to_bytes32(kchild, kf);
    for (int i=0;i<32;i++) d_out[128+i]=kchild[i];   // child priv @ N=0
    Jacobian P; scalar_mult_base_comb(P, kf);
    u32 x[ 8], y[ 8]; jac_to_affine(x, y, P);
    u8 pub[ 64];
    fe_to_bytes32(pub, x);
    fe_to_bytes32(pub+32, y);
    u8 hh[ 32]; device_keccak256(pub, 64, hh);
    for (int i=0;i<20;i++) d_out[160+i]=hh[12+i];     // addr
    d_done[ 0]=1;
}
// ==========================================
// Kernel: 分阶段性能剖析 (stage: 0=mnemonic 1=+pbkdf2 2=+ckd 3=full)
// 每段结果都累加进 checksum 写入全局，防止 DCE
// ==========================================
__global__ void prof_kernel(u64 start_nonce, int iters, int stage, u64* d_out, u32* d_done) {
    u64 tid = (u64)blockIdx.x*blockDim.x + threadIdx.x;
    u64 acc = 0;
    for (int it=0; it<iters; it++) {
        u64 n = start_nonce + tid + (u64)it*gridDim.x*blockDim.x;
        u8 nb[ 8]; for (int i=0;i<8;i++) nb[i]=(u8)(n>>(8*i));
        u8 h[ 32]; sha256(nb, 8, h);
        u8 ent[ 16]; for (int i=0;i<16;i++) ent[i]=h[i];
        char m[ 128]; entropy_to_mnemonic(ent, m, 0);
        u64 acc0 = 0;
        for (int i=0;i<128;i++) acc0 = acc0*131 + (u8)m[i];
        if (stage>=1) {
            u8 seed[ 64]; device_bip39_seed(m, seed);
            u64 acc1 = acc0;
            for (int i=0;i<64;i++) acc1 = acc1*131 + seed[i];
            if (stage>=2) {
                u8 privk[ 32]; bip32_derive(privk, seed);
                u64 acc2 = acc1;
                for (int i=0;i<32;i++) acc2 = acc2*131 + privk[i];
                if (stage>=3) {
                    u8 addr[ 20]; derive_address(privk, addr);
                    for (int i=0;i<20;i++) acc2 = acc2*131 + addr[i];
                    acc += acc2;
                } else acc += acc2;
            } else acc += acc1;
        } else acc += acc0;
    }
    if (acc == 0xDEADBEEF) d_out[ tid % 1024 ] = acc;
    d_done[ 0]=1;
}

__device__ void ent_to_hd_base(const u8 ent[ 16], u32 kbase[ 8], u32 cbase[ 8],
                               u32 pubx[ 8], u32 puby[ 8], char* mnem_out);

// ==========================================
// BTC 地址原语：RIPEMD160 / Base58Check / bech32(bech32m) / 地址生成
// ==========================================
__device__ __forceinline__ u32 btc_rol32(u32 x, int n) { return (x << n) | (x >> (32 - n)); }
__device__ __forceinline__ u32 rp_f(int j, u32 x, u32 y, u32 z) {
    if (j < 16) return x ^ y ^ z;
    if (j < 32) return (x & y) | (~x & z);
    if (j < 48) return (x | ~y) ^ z;
    if (j < 64) return (x & z) | (y & ~z);
    return x ^ (y | ~z);
}
__device__ __forceinline__ u32 rp_f2(int j, u32 x, u32 y, u32 z) {
    if (j < 16) return x ^ (y | ~z);
    if (j < 32) return (x & z) | (y & ~z);
    if (j < 48) return (x | ~y) ^ z;
    if (j < 64) return (x & y) | (~x & z);
    return x ^ y ^ z;
}
__device__ __forceinline__ void ripemd160(const u8* msg, int len, u8 out[ 20]) {
    static const u32 rp_r[ 80] = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15, 7,4,13,1,10,6,15,3,12,0,9,5,2,14,11,8, 3,10,14,4,9,15,8,1,2,7,0,6,13,11,5,12, 1,9,11,10,0,8,12,4,13,3,7,15,14,5,6,2, 4,0,5,9,7,12,2,10,14,1,3,8,11,6,15,13};
    static const u32 rp_r2[ 80] = {5,14,7,0,9,2,11,4,13,6,15,8,1,10,3,12, 6,11,3,7,0,13,5,10,14,15,8,12,4,9,1,2, 15,5,1,3,7,14,6,9,11,8,12,2,10,0,4,13, 8,6,4,1,3,11,15,0,5,12,2,13,9,7,10,14, 12,15,10,4,1,5,8,7,6,2,13,14,0,3,9,11};
    static const u32 rp_s[ 80] = {11,14,15,12,5,8,7,9,11,13,14,15,6,7,9,8, 7,6,8,13,11,9,7,15,7,12,15,9,11,7,13,12, 11,13,6,7,14,9,13,15,14,8,13,6,5,12,7,5, 11,12,14,15,14,15,9,8,9,14,5,6,8,6,5,12, 9,15,5,11,6,8,13,12,5,12,13,14,11,8,5,6};
    static const u32 rp_s2[ 80] = {8,9,9,11,13,15,15,5,7,7,8,11,14,14,12,6, 9,13,15,7,12,8,9,11,7,7,12,7,6,15,13,11, 9,7,15,11,8,6,6,14,12,13,5,14,13,13,7,5, 15,5,8,11,14,14,6,14,6,9,12,9,12,5,15,8, 8,5,12,9,12,5,14,6,8,13,6,5,15,13,11,11};
    static const u32 rp_k[ 5] = {0x00000000, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e};
    static const u32 rp_k2[ 5] = {0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0x00000000};
    u8 blk[ 64];
    for (int i = 0; i < 64; i++) blk[i] = 0;
    for (int i = 0; i < len && i < 64; i++) blk[i] = msg[i];
    blk[len] = 0x80;
    u64 bits = (u64)len * 8;
    for (int i = 0; i < 8; i++) blk[56 + i] = (u8)((bits >> (8 * i)) & 0xFF);
    u32 M[ 16];
    for (int i = 0; i < 16; i++) { u32 v = 0; for (int j = 0; j < 4; j++) v |= ((u32)blk[i * 4 + j]) << (8 * j); M[i] = v; }
    u32 A = 0x67452301, B = 0xEFCDAB89, C = 0x98BADCFE, D = 0x10325476, E = 0xC3D2E1F0;
    u32 A2 = A, B2 = B, C2 = C, D2 = D, E2 = E;
    for (int j = 0; j < 80; j++) {
        u32 T = btc_rol32(A + rp_f(j, B, C, D) + M[rp_r[j]] + rp_k[j / 16], rp_s[j]) + E;
        A = E; E = D; D = btc_rol32(C, 10); C = B; B = T;
        u32 T2 = btc_rol32(A2 + rp_f2(j, B2, C2, D2) + M[rp_r2[j]] + rp_k2[j / 16], rp_s2[j]) + E2;
        A2 = E2; E2 = D2; D2 = btc_rol32(C2, 10); C2 = B2; B2 = T2;
    }
    u32 h0n = 0xEFCDAB89u + C + D2;
    u32 h1n = 0x98BADCFEu + D + E2;
    u32 h2n = 0x10325476u + E + A2;
    u32 h3n = 0xC3D2E1F0u + A + B2;
    u32 h4n = 0x67452301u + B + C2;
    u32 h[ 5] = {h0n, h1n, h2n, h3n, h4n};
    for (int i = 0; i < 20; i++) out[i] = (u8)((h[i / 4] >> (8 * (i % 4))) & 0xFF);
}
__device__ __forceinline__ void sha256d(const u8* msg, int len, u8 out[ 32]) {
    u8 h1[ 32]; sha256(msg, len, h1);
    sha256(h1, 32, out);
}
__device__ int base58check_encode(const u8* payload, int plen, char* out) {
    static const char* B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    u8 full[ 40];
    for (int i = 0; i < plen; i++) full[i] = payload[i];
    u8 chk[ 32]; sha256d(payload, plen, chk);
    for (int i = 0; i < 4; i++) full[plen + i] = chk[i];
    int n = plen + 4;
    int zeros = 0; while (zeros < n && full[zeros] == 0) zeros++;
    u8 buf[ 40]; for (int i = 0; i < n; i++) buf[i] = full[i];
    char b58[ 40]; int bl = 0;
    int start = 0;
    while (start < n) {
        int rem = 0;
        for (int i = start; i < n; i++) {
            int acc = rem * 256 + buf[i];
            buf[i] = (u8)(acc / 58);
            rem = acc % 58;
        }
        b58[bl++] = B58[rem];
        while (start < n && buf[start] == 0) start++;
    }
    int idx = 0;
    for (int i = 0; i < zeros; i++) out[idx++] = '1';
    for (int i = bl - 1; i >= 0; i--) out[idx++] = b58[i];
    return idx;
}
__device__ int bech32_encode(int witver, const u8* payload, int plen, char* out) {
    static const char* CH = "qpzry9x8gf2tvdw0s3jn54khce6mua7l";
    u8 conv[ 80]; int nc = 0;
    int acc = 0, bits = 0;
    for (int i = 0; i < plen; i++) {
        acc = (acc << 8) | payload[i]; bits += 8;
        while (bits >= 5) { bits -= 5; conv[nc++] = (u8)((acc >> bits) & 31); }
    }
    if (bits > 0) conv[nc++] = (u8)((acc << (5 - bits)) & 31);
    u8 d[ 90]; int m = 0; d[m++] = (u8)witver;
    for (int i = 0; i < nc; i++) d[m++] = conv[i];
    u32 v[ 100]; int nv = 0;
    v[nv++] = 'b' >> 5; v[nv++] = 'c' >> 5; v[nv++] = 0; v[nv++] = 'b' & 31; v[nv++] = 'c' & 31;
    for (int i = 0; i < m; i++) v[nv++] = d[i];
    u32 chk = 1;
    static const u32 gen[ 5] = {0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3};
    for (int i = 0; i < nv + 6; i++) {
        u32 x = (i < nv) ? v[i] : 0;
        u32 b = chk >> 25;
        chk = ((chk & 0x1ffffff) << 5) ^ x;
        for (int j = 0; j < 5; j++) chk ^= ((b >> j) & 1) ? gen[j] : 0;
    }
    u32 constv = (witver == 0) ? 1u : 0x2bc830a3u;
    chk ^= constv;
    out[0] = 'b'; out[1] = 'c'; out[2] = '1';
    int oi = 3;
    for (int i = 0; i < m; i++) out[oi++] = CH[d[i]];
    for (int i = 0; i < 6; i++) out[oi++] = CH[(chk >> (5 * (5 - i))) & 31];
    return oi;
}
// 双地址版：同一非压缩 pub(x||y) 算两个 P2PKH 地址（compressed / uncompressed 公钥）
__device__ int btc_p2pkh_addr(const u8 pub[ 64], int compressed, char* out) {
    u8 pk[ 65];
    if (compressed) {
        pk[ 0] = (pub[ 63] & 1) ? 0x03 : 0x02;
        for (int i=0;i<32;i++) pk[ 1 + i] = pub[i];
    } else {
        pk[ 0] = 0x04;
        for (int i=0;i<64;i++) pk[ 1 + i] = pub[i];
    }
    int pl = compressed ? 33 : 65;
    u8 h1[ 32]; sha256(pk, pl, h1);
    u8 h160[ 20]; ripemd160(h1, 32, h160);
    u8 pay[ 21]; pay[ 0] = 0x00; for (int i=0;i<20;i++) pay[ 1 + i] = h160[i];
    return base58check_encode(pay, 21, out);
}
// P2SH-P2WPKH（嵌套 SegWit）：compressed 公钥 -> redeemScript(0x00 0x14 hash160) -> scriptHash -> Base58(0x05)，3 开头 34 字符
__device__ int btc_p2sh_p2wpkh_addr(const u8 pub[ 64], char* out) {
    u8 comp[ 33];
    comp[ 0] = (pub[ 63] & 1) ? 0x03 : 0x02;
    for (int i=0;i<32;i++) comp[ 1 + i] = pub[i];
    u8 h1[ 32]; sha256(comp, 33, h1);
    u8 h160[ 20]; ripemd160(h1, 32, h160);
    u8 rs[ 22]; rs[ 0] = 0x00; rs[ 1] = 0x14;
    for (int i=0;i<20;i++) rs[ 2 + i] = h160[i];
    u8 h2[ 32]; sha256(rs, 22, h2);
    u8 sh[ 20]; ripemd160(h2, 32, sh);
    u8 pay[ 21]; pay[ 0] = 0x05; for (int i=0;i<20;i++) pay[ 1 + i] = sh[i];
    return base58check_encode(pay, 21, out);
}
// type: 0=P2PKH 1=P2SH 2=P2WPKH(bech32 v0) 3=P2TR(bech32m v1, x-only)
// pub = 64 字节 (x||y) 非压缩
__device__ int btc_address_from_pub(const u8 pub[ 64], int type, char* out) {
    u8 comp[ 33];
    comp[ 0] = (pub[ 63] & 1) ? 0x03 : 0x02;
    for (int i = 0; i < 32; i++) comp[ 1 + i] = pub[i];
    u8 h1[ 32]; sha256(comp, 33, h1);
    u8 h160[ 20]; ripemd160(h1, 32, h160);
    if (type == 0) { u8 pl[ 21]; pl[ 0] = 0x00; for (int i = 0; i < 20; i++) pl[ 1 + i] = h160[i]; return base58check_encode(pl, 21, out); }
    if (type == 1) { u8 pl[ 21]; pl[ 0] = 0x05; for (int i = 0; i < 20; i++) pl[ 1 + i] = h160[i]; return base58check_encode(pl, 21, out); }
    if (type == 2) { return bech32_encode(0, h160, 20, out); }
    return bech32_encode(1, pub, 32, out);
}
// 自检：固定熵(全 0) -> BTC m/44'/0'/0'/0/N (N=0,3) 各类型地址
__global__ void btc_test_kernel(u8* d_out, u32* d_done) {
    u8 nb[ 8]; for (int i = 0; i < 8; i++) nb[i] = 0;
    u8 h[ 32]; sha256(nb, 8, h);
    u8 ent[ 16]; for (int i = 0; i < 16; i++) ent[i] = h[i];
    u32 kbase[ 8], cbase[ 8], pubx[ 8], puby[ 8];
    char mnem[ 128];
    ent_to_hd_base(ent, kbase, cbase, pubx, puby, mnem);
    u8 c8[ 32]; fe_to_bytes32(c8, cbase);
    u8 xb0[ 32]; fe_to_bytes32(xb0, pubx);
    u32 NN[ 2] = {0, 3};
    for (int q = 0; q < 2; q++) {
        u32 N = NN[ q];
        u8 data[ 37];
        data[ 0] = (puby[ 0] & 1) ? 0x03 : 0x02;
        for (int i = 0; i < 32; i++) data[ 1 + i] = xb0[i];
        data[ 33] = (u8)(N >> 24); data[ 34] = (u8)(N >> 16); data[ 35] = (u8)(N >> 8); data[ 36] = (u8)N;
        u8 o2[ 64]; hmac_sha512_gen(c8, 32, data, 37, o2);
        u32 il[ 8]; bytes32_to_fe(il, o2);
        u32 kf[ 8]; for (int i = 0; i < 8; i++) kf[i] = kbase[i];
        sc_add_mod_n(kf, il, kf);
        u8 privk[ 32]; fe_to_bytes32(privk, kf);
        Jacobian P; scalar_mult_base_comb(P, kf);
        u32 x[ 8], y[ 8]; jac_to_affine(x, y, P);
        u8 pub[ 64]; fe_to_bytes32(pub, x); fe_to_bytes32(pub + 32, y);
        u8 comp[ 33]; comp[ 0] = (pub[ 63] & 1) ? 0x03 : 0x02;
        for (int i = 0; i < 32; i++) comp[ 1 + i] = pub[i];
        u8 h1[ 32]; sha256(comp, 33, h1);
        u8 h160[ 20]; ripemd160(h1, 32, h160);
        int o = q * 320;
        for (int i = 0; i < 32; i++) d_out[o + i] = privk[i];
        for (int i = 0; i < 33; i++) d_out[o + 32 + i] = comp[i];
        for (int i = 0; i < 20; i++) d_out[o + 65 + i] = h160[i];
        u8 pl[ 21]; pl[ 0] = 0x00; for (int i = 0; i < 20; i++) pl[ 1 + i] = h160[i];
        int l = base58check_encode(pl, 21, (char*)(d_out + o + 85));
        d_out[o + 85 + l] = 0;
        l = bech32_encode(0, h160, 20, (char*)(d_out + o + 149));
        d_out[o + 149 + l] = 0;
        l = bech32_encode(1, pub, 32, (char*)(d_out + o + 229));
        d_out[o + 229 + l] = 0;
    }
    for (int i = 0; i < 128; i++) d_out[640 + i] = (u8)mnem[i];
    d_done[ 0] = 1;
}

// 熵 -> 助记词 -> m/44'/60'/0'/0 基点（kbase/cbase/pubx/puby），供多索引派生复用
__device__ void ent_to_hd_base(const u8 ent[ 16], u32 kbase[ 8], u32 cbase[ 8],
                               u32 pubx[ 8], u32 puby[ 8], char* mnem_out) {
    char m[ 128];
    entropy_to_mnemonic(ent, m, 0);
    if (mnem_out) { int l=0; while (m[l]){ mnem_out[l]=m[l]; l++; } mnem_out[l]=0; }
    u8 seed[ 64];
    device_bip39_seed(m, seed);
    u8 k[ 32], c[ 32], out[ 64];
    hmac_sha512_gen((const u8*)"Bitcoin seed", 12, seed, 64, out);
    for (int i=0;i<32;i++){ k[i]=out[i]; c[i]=out[32+i]; }
    ckd_priv(k, c, 0x80000000u+44u, 1);
    ckd_priv(k, c, 0x80000000u+0u, 1);
    ckd_priv(k, c, 0x80000000u+0u, 1);
    u8 k0n[ 32], c0n[ 32];
    for (int i=0;i<32;i++){ k0n[i]=k[i]; c0n[i]=c[i]; }
    ckd_priv(k0n, c0n, 0u, 0);
    bytes32_to_fe(kbase, k0n);
    bytes32_to_fe(cbase, c0n);
    u32 kf[ 8]; bytes32_to_fe(kf, k0n);
    Jacobian P; scalar_mult_base_comb(P, kf);
    jac_to_affine(pubx, puby, P);
}

__global__ __launch_bounds__(256, 2) void vanity_kernel(const u8* d_prefix, int plen, u64 start_nonce, int iters, int nidx,
                              char* d_mnem, u8* d_addr, u8* d_priv, u32* d_index, u32* d_found) {
    u64 tid = (u64)blockIdx.x*blockDim.x + threadIdx.x;
    for (int it=0; it<iters; it++) {
        if (*d_found) return;
        u64 n = start_nonce + tid + (u64)it*gridDim.x*blockDim.x;
        u8 nb[ 8];
        for (int i=0;i<8;i++) nb[i]=(u8)(n>>(8*i));
        u8 h[ 32];
        sha256(nb, 8, h);
        u8 ent[ 16];
        for (int i=0;i<16;i++) ent[i]=h[i];
        u32 kbase[ 8], cbase[ 8], pubx[ 8], puby[ 8];
        char mnem[ 128];
        ent_to_hd_base(ent, kbase, cbase, pubx, puby, mnem);
        u8 c8[ 32]; fe_to_bytes32(c8, cbase);
        u8 xb0[ 32]; fe_to_bytes32(xb0, pubx);
        for (int idx=0; idx<nidx; idx++) {
            u32 N = (u32)idx;
            u8 data[ 37];
            data[ 0] = (puby[ 0]&1) ? 0x03 : 0x02;
            for (int i=0;i<32;i++) data[1+i]=xb0[i];
            data[ 33]=(u8)(N>>24); data[ 34]=(u8)(N>>16); data[ 35]=(u8)(N>>8); data[ 36]=(u8)N;
            u8 out[ 64];
            hmac_sha512_gen(c8, 32, data, 37, out);
            u32 il[ 8]; bytes32_to_fe(il, out);
            u32 kf[ 8]; for (int i=0;i<8;i++) kf[i]=kbase[i];
            sc_add_mod_n(kf, il, kf);
            Jacobian P; scalar_mult_base_comb(P, kf);
            u32 x[ 8], y[ 8]; jac_to_affine(x, y, P);
            u8 pub[ 64];
            fe_to_bytes32(pub, x);
            fe_to_bytes32(pub+32, y);
            u8 hh[ 32];
            device_keccak256(pub, 64, hh);
            u8 addr[ 20]; for (int i=0;i<20;i++) addr[i]=hh[12+i];
            int ok=1;
            for (int i=0;i<plen;i++) {
                u8 nib = (i&1) ? (addr[i>>1]&0xF) : (addr[i>>1]>>4);
                if (nib != d_prefix[i]) { ok=0; break; }
            }
            if (ok) {
                u32 old = atomicCAS(d_found, 0, 1);
                if (old==0) {
                    int l=0; while (mnem[l]){ d_mnem[l]=mnem[l]; l++; } d_mnem[l]=0;
                    u8 privk[ 32]; fe_to_bytes32(privk, kf);
                    for (int i=0;i<20;i++) d_addr[i]=addr[i];
                    for (int i=0;i<32;i++) d_priv[i]=privk[i];
                    d_index[ 0]=N;
                }
                return;
            }
        }
    }
}


// ==========================================
// 文件模式：一个固定种子，同时搜索多个前缀（HD m/44'/60'/0'/0/N）
// 每个前缀独立 found slot + 结果；全部找到则提前退出
// ==========================================
#define MAXP 256
__global__ __launch_bounds__(256, 2) void multi_hd_kernel(
        const u8* d_prefixes, const u8* d_plens, int nprefix,
        const u32* d_kbase, const u32* d_cbase, const u32* d_pubx, const u32* d_puby,
        u64 start_nonce, int iters, const char* d_mnem,
        u8* d_addrs, u8* d_privs, u32* d_idxs, u32* d_found, u32* d_nfound) {
    u64 tid = (u64)blockIdx.x*blockDim.x + threadIdx.x;
    for (int it=0; it<iters; it++) {
        if (*d_nfound >= (u32)nprefix) return;
        u64 n = start_nonce + tid + (u64)it*gridDim.x*blockDim.x;
        u32 N = (u32)(n & 0x7FFFFFFFu);
        // IL = HMAC-SHA512(c0n, 0x02/03||X || N)
        u32 cb[ 8]; for (int i=0;i<8;i++) cb[i]=d_cbase[i];
        u8 c8[ 32]; fe_to_bytes32(c8, cb);
        u8 data[ 37];
        data[ 0] = (d_puby[ 0]&1) ? 0x03 : 0x02;
        u8 xb[ 32]; fe_to_bytes32(xb, d_pubx);
        for (int i=0;i<32;i++) data[1+i]=xb[i];
        data[ 33]=(u8)(N>>24); data[ 34]=(u8)(N>>16); data[ 35]=(u8)(N>>8); data[ 36]=(u8)N;
        u8 out[ 64];
        hmac_sha512_gen(c8, 32, data, 37, out);
        u32 il[ 8]; bytes32_to_fe(il, out);
        u32 kf[ 8]; for (int i=0;i<8;i++) kf[i]=d_kbase[i];
        sc_add_mod_n(kf, il, kf);
        Jacobian P; scalar_mult_base_comb(P, kf);
        u32 x[ 8], y[ 8]; jac_to_affine(x, y, P);
        u8 pub[ 64];
        fe_to_bytes32(pub, x);
        fe_to_bytes32(pub+32, y);
        u8 hh[ 32];
        device_keccak256(pub, 64, hh);
        u8 addr[ 20]; for (int i=0;i<20;i++) addr[i]=hh[12+i];
        // 遍历所有未完成前缀
        for (int p=0; p<nprefix; p++) {
            if (d_found[p]) continue;
            int pl = d_plens[p];
            int ok=1;
            const u8* pfx = d_prefixes + p*40;
            for (int i=0;i<pl;i++) {
                u8 nib = (i&1) ? (addr[i>>1]&0xF) : (addr[i>>1]>>4);
                if (nib != pfx[i]) { ok=0; break; }
            }
            if (ok) {
                u32 old = atomicCAS(&d_found[p], 0, 1);
                if (old==0) {
                    u8 privk[ 32]; fe_to_bytes32(privk, kf);
                    for (int i=0;i<20;i++) d_addrs[p*20+i]=addr[i];
                    for (int i=0;i<32;i++) d_privs[p*32+i]=privk[i];
                    d_idxs[p]=N;
                    atomicAdd(d_nfound, 1);
                }
            }
        }
    }
}

// ==========================================
// 文件模式（vanity 语义）：随机助记词 + 多前缀并行 + 每助记词派生 nidx 个地址
// ==========================================
__global__ __launch_bounds__(256, 2) void multi_vanity_kernel(
        const u8* d_prefixes, const u8* d_plens, int nprefix, int nidx,
        u64 start_nonce, int iters,
        u8* d_mnems, u8* d_addrs, u8* d_privs, u32* d_idxs, u32* d_found, u32* d_nfound) {
    u64 tid = (u64)blockIdx.x*blockDim.x + threadIdx.x;
    for (int it=0; it<iters; it++) {
        if (*d_nfound >= (u32)nprefix) return;
        u64 n = start_nonce + tid + (u64)it*gridDim.x*blockDim.x;
        u8 nb[ 8];
        for (int i=0;i<8;i++) nb[i]=(u8)(n>>(8*i));
        u8 h[ 32];
        sha256(nb, 8, h);
        u8 ent[ 16];
        for (int i=0;i<16;i++) ent[i]=h[i];
        u32 kbase[ 8], cbase[ 8], pubx[ 8], puby[ 8];
        char mnem[ 128];
        ent_to_hd_base(ent, kbase, cbase, pubx, puby, mnem);
        u8 c8[ 32]; fe_to_bytes32(c8, cbase);
        u8 xb0[ 32]; fe_to_bytes32(xb0, pubx);
        for (int idx=0; idx<nidx; idx++) {
            u32 N = (u32)idx;
            u8 data[ 37];
            data[ 0] = (puby[ 0]&1) ? 0x03 : 0x02;
            for (int i=0;i<32;i++) data[1+i]=xb0[i];
            data[ 33]=(u8)(N>>24); data[ 34]=(u8)(N>>16); data[ 35]=(u8)(N>>8); data[ 36]=(u8)N;
            u8 out[ 64];
            hmac_sha512_gen(c8, 32, data, 37, out);
            u32 il[ 8]; bytes32_to_fe(il, out);
            u32 kf[ 8]; for (int i=0;i<8;i++) kf[i]=kbase[i];
            sc_add_mod_n(kf, il, kf);
            Jacobian P; scalar_mult_base_comb(P, kf);
            u32 x[ 8], y[ 8]; jac_to_affine(x, y, P);
            u8 pub[ 64];
            fe_to_bytes32(pub, x);
            fe_to_bytes32(pub+32, y);
            u8 hh[ 32];
            device_keccak256(pub, 64, hh);
            u8 addr[ 20]; for (int i=0;i<20;i++) addr[i]=hh[12+i];
            for (int p=0; p<nprefix; p++) {
                if (d_found[p]) continue;
                int pl = d_plens[p];
                int ok=1;
                const u8* pfx = d_prefixes + p*40;
                for (int i=0;i<pl;i++) {
                    u8 nib = (i&1) ? (addr[i>>1]&0xF) : (addr[i>>1]>>4);
                    if (nib != pfx[i]) { ok=0; break; }
                }
                if (ok) {
                    u32 old = atomicCAS(&d_found[p], 0, 1);
                    if (old==0) {
                        u8 privk[ 32]; fe_to_bytes32(privk, kf);
                        int l=0; while (mnem[l]){ d_mnems[p*128+l]=(u8)mnem[l]; l++; } d_mnems[p*128+l]=0;
                        for (int i=0;i<20;i++) d_addrs[p*20+i]=addr[i];
                        for (int i=0;i<32;i++) d_privs[p*32+i]=privk[i];
                        d_idxs[p]=N;
                        atomicAdd(d_nfound, 1);
                    }
                }
            }
        }
    }
}

#define PSTR 64
// 查表命中：返回匹配前缀索引，未命中返回 0xFFFFFFFF
__device__ u32 btc_tbl_hit(const u64* d_tbl_key, const u32* d_tbl_p, const u8* d_tbl_occ,
                           const u32* d_tbl_off, const u32* d_tbl_mask, const u32* d_tbl_cnt,
                           const u8* d_pfx, u64 uniq, const char* ast, int laddr, int nl_max) {
    u64 hv=0xcbf29ce484222325ull;
    for (int L=1; L<=nl_max; L++) {
        if (L > laddr) break;
        hv = (hv ^ (u8)ast[L-1]) * 0x100000001b3ull;
        int cnt = d_tbl_cnt[L-1];
        if (!cnt) continue;
        u32 mask = d_tbl_mask[L-1];
        u32 base = d_tbl_off[L-1];
        u32 hh2 = (u32)((hv * 0x9E3779B97F4A7C15ull) >> 32);
        int s = (int)(hh2 & mask);
        for (;;) {
            if (!d_tbl_occ[base+s]) break;
            if (d_tbl_key[base+s] == hv) {
                u32 p = d_tbl_p[base+s];
                int ok=1;
                for (int k=0;k<L;k++) if (d_pfx[(u64)p*PSTR+k]!=(u8)ast[k]) { ok=0; break; }
                if (ok) return p;
            }
            s = (s+1) & mask;
        }
    }
    return 0xFFFFFFFFu;
}
#define NLMAX 62
#define RESQ_CAP (1<<20)
#define RESQ_MASK (RESQ_CAP-1)
typedef struct { u32 p; u32 idx; u8 priv[32]; u8 wif[64]; u8 addr[PSTR]; u8 addr2[PSTR]; u8 addr3[PSTR]; } ResqEntry;
// 命中队列写入（三地址 + uncompressed WIF 固定写入）
__device__ void resq_write(u32 p, int idx, const u32 kf[ 8],
                           const char* ast_u, int lu, const char* ast_c, int lc,
                           const char* ast_w, int lw,
                           ResqEntry* d_resq, u32* d_resq_cnt, u32* d_nfound) {
    u8 privk[ 32]; fe_to_bytes32(privk, kf);
    u32 q = atomicAdd(d_resq_cnt, 1);
    ResqEntry* e = &d_resq[q & RESQ_MASK];
    e->p = p; e->idx = (u32)idx;
    for (int i=0;i<32;i++) e->priv[i]=privk[i];
    { u8 pl[ 33]; pl[0]=0x80; for (int i=0;i<32;i++) pl[1+i]=privk[i];
      int wl=base58check_encode(pl, 33, (char*)e->wif); e->wif[wl]=0; }
    for (int i=0;i<lc;i++) e->addr[i]=(u8)ast_c[i]; e->addr[lc]=0;
    for (int i=0;i<lu;i++) e->addr2[i]=(u8)ast_u[i]; e->addr2[lu]=0;
    for (int i=0;i<lw;i++) e->addr3[i]=(u8)ast_w[i]; e->addr3[lw]=0;
    atomicAdd(d_nfound, 1);
}
__global__ __launch_bounds__(256, 2) void multi_hash_kernel(
        const u64* d_tbl_key, const u32* d_tbl_p, const u8* d_tbl_occ,
        const u32* d_tbl_off, const u32* d_tbl_mask, const u32* d_tbl_cnt,
        const u8* d_pfx, u64 uniq,
        int nl_max, u64 start_nonce, int iters,
        u32* d_found, u32* d_nfound, ResqEntry* d_resq, u32* d_resq_cnt) {
    u64 tid = (u64)blockIdx.x*blockDim.x + threadIdx.x;
    // BitCrack 式顺序增量枚举：每线程一次标量乘得到起点，之后每次 P += G（单次点加）
    // 起点随机化：priv0 = sha256(start_nonce+tid) mod n，链内递增，覆盖空间均匀无重复
    u64 n = start_nonce + tid;
    u8 nb[ 8];
    for (int i=0;i<8;i++) nb[i]=(u8)(n>>(8*i));
    u8 h[ 32];
    sha256(nb, 8, h);
    u32 kf[ 8]; bytes32_to_fe(kf, h);
    {   // 保证 kf < n（sha256 输出 >= n 概率约 2^-127，仍需处理）
        int ge=1;
        for (int i=7;i>=0;i--) { if (kf[i] > N_FE[i]) { ge=1; break; } if (kf[i] < N_FE[i]) { ge=0; break; } }
        if (ge) { u64 borrow=0; for (int i=0;i<8;i++){ u64 sub=(u64)kf[i]-N_FE[i]-borrow; kf[i]=(u32)sub; borrow=(sub>>32)?1:0; } }
    }
    Jacobian P; scalar_mult_base_comb(P, kf);
    // 无限运行内核：不设"全部命中即退出"短路，每轮跑满 batch_iters，持续搜索重复命中
    for (int it=0; it<iters; it++) {
        u32 x[ 8], y[ 8]; jac_to_affine(x, y, P);
        u8 pub[ 64];
        fe_to_bytes32(pub, x);
        fe_to_bytes32(pub+32, y);
        char ast_u[ PSTR ]; int lu = btc_p2pkh_addr(pub, 0, ast_u); if (lu > PSTR) lu = PSTR;
        char ast_c[ PSTR ]; int lc = btc_p2pkh_addr(pub, 1, ast_c); if (lc > PSTR) lc = PSTR;
        char ast_w[ PSTR ]; int lw = btc_p2sh_p2wpkh_addr(pub, ast_w); if (lw > PSTR) lw = PSTR;
        // 三地址各自查表：uncomp(0) / comp(1) / p2sh_p2wpkh(2)
        u32 p1=0xFFFFFFFFu, p2=0xFFFFFFFFu, p3=0xFFFFFFFFu;
        p1 = btc_tbl_hit(d_tbl_key, d_tbl_p, d_tbl_occ, d_tbl_off, d_tbl_mask, d_tbl_cnt, d_pfx, uniq, ast_u, lu, nl_max);
        if (p1 != 0xFFFFFFFFu) { u32 old = atomicCAS(&d_found[p1], 0, 1); if (old==0) resq_write(p1, 0, kf, ast_u, lu, ast_c, lc, ast_w, lw, d_resq, d_resq_cnt, d_nfound); }
        p2 = btc_tbl_hit(d_tbl_key, d_tbl_p, d_tbl_occ, d_tbl_off, d_tbl_mask, d_tbl_cnt, d_pfx, uniq, ast_c, lc, nl_max);
        if (p2 != 0xFFFFFFFFu && p2 != p1) { u32 old = atomicCAS(&d_found[p2], 0, 1); if (old==0) resq_write(p2, 1, kf, ast_u, lu, ast_c, lc, ast_w, lw, d_resq, d_resq_cnt, d_nfound); }
        p3 = btc_tbl_hit(d_tbl_key, d_tbl_p, d_tbl_occ, d_tbl_off, d_tbl_mask, d_tbl_cnt, d_pfx, uniq, ast_w, lw, nl_max);
        if (p3 != 0xFFFFFFFFu && p3 != p1 && p3 != p2) { u32 old = atomicCAS(&d_found[p3], 0, 1); if (old==0) resq_write(p3, 2, kf, ast_u, lu, ast_c, lc, ast_w, lw, d_resq, d_resq_cnt, d_nfound); }
        // 增量枚举：P += G（affine 基点加），kf += 1 mod n
        jac_add_affine(P, P, GX_FE, GY_FE);
        u32 ONE[ 8]; fe_set1(ONE);
        sc_add_mod_n(kf, ONE, kf);
        if (fe_iszero(kf)) { Jacobian P2; scalar_mult_base_comb(P2, kf); P = P2; } // 理论不可达防御
    }
}

// ==========================================
// 主机辅助
// ==========================================
static void print_hex(const u8* p, int n) {
    for (int i=0;i<n;i++) printf("%02x", p[i]);
}

static int btc_nlmax(int addrtype) {
    return (addrtype==0||addrtype==1) ? 34 : (addrtype==2 ? 42 : 62);
}
static const char* btc_aname(int addrtype) {
    return (addrtype==0) ? "P2PKH(1)" : (addrtype==1) ? "P2SH(3)" : (addrtype==2) ? "P2WPKH(bc1q)" : "P2TR(bc1p)";
}
// pfx 行宽 PSTR, plen 每前缀长度; 统一搜索入口（file/vanity 共用）
static void run_dual_search(u8* pfx, u8* plen, u64 nprefix, int blocks) {
    // 命中即写文件：btc_hits.txt 追加模式，无缓冲每行立即落盘（Ctrl+C 强杀也不丢）
    FILE* hf = fopen("btc_hits.txt", "a");
    if (hf) setvbuf(hf, NULL, _IONBF, 0);
    if (nprefix==0) { fprintf(stderr,"no valid prefixes\n"); if (hf) fclose(hf); return; }
    int nl_max = 34;
    // 校验超长（调用方已处理则这里再兜底）
    u64 nskip=0;
    for (u64 p=0;p<nprefix;p++) if (plen[p] > nl_max) nskip++;
    if (nskip) printf("note: %llu prefix(es) longer than %d chars skipped\n", (unsigned long long)nskip, nl_max);
    printf("BTC triple-address vanity | P2PKH(1) comp+uncomp + P2SH-P2WPKH(3) | max prefix len %d | file prefixes %llu\n", nl_max, (unsigned long long)nprefix);
    int lcnt[ NLMAX+1 ];
    for (int i=0;i<=NLMAX;i++) lcnt[i]=0;
    for (u64 p=0;p<nprefix;p++) if (plen[p]<=nl_max) lcnt[plen[p]]++;
    printf("length dist: ");
    for (int L=1;L<=nl_max;L++) if (lcnt[L]) printf("%d-char:%d ", L, lcnt[L]);
    printf("\n");
    int hcap[ NLMAX ]; u32 off[ NLMAX ]; u32 mask[ NLMAX ];
    u64* hk[ NLMAX ]; u32* hp[ NLMAX ]; u8* hoc[ NLMAX ];
    u64 total_cap = 0;
    for (int L=1;L<=NLMAX;L++) {
        int cnt = (L<=nl_max) ? lcnt[L] : 0;
        u64 c2 = 8;
        while (c2 < (u64)cnt*2+1) c2 <<= 1;
        hcap[L-1]=(int)c2; off[L-1]=(u32)total_cap; mask[L-1]=(u32)(c2-1);
        hk[L-1]=(u64*)malloc((size_t)(c2*8));
        hp[L-1]=(u32*)malloc((size_t)(c2*4));
        hoc[L-1]=(u8*)malloc((size_t)c2);
        memset(hoc[L-1],0,(size_t)c2);
        total_cap += c2;
    }
    if (total_cap >= (1ull<<32)) { for (int L=1;L<=NLMAX;L++){free(hk[L-1]);free(hp[L-1]);free(hoc[L-1]);} fprintf(stderr,"hash table too large (>4G slots)\n"); return; }
    u64 uniq=0;
    for (u64 p=0;p<nprefix;p++) {
        int L=plen[p];
        if (L>nl_max) continue;
        u64 key=0xcbf29ce484222325ull;
        for (int i=0;i<L;i++) key = (key ^ pfx[p*PSTR+i]) * 0x100000001b3ull;
        u32 hh = (u32)((key * 0x9E3779B97F4A7C15ull) >> 32);
        int s = (int)(hh & mask[L-1]);
        u8* oc = hoc[L-1]; u64* kk = hk[L-1]; u32* pp = hp[L-1];
        for (;;) {
            if (!oc[s]) {
                oc[s]=1; kk[s]=key; pp[s]=(u32)uniq;
                if (uniq < p) { memmove(pfx+uniq*PSTR, pfx+p*PSTR, PSTR); plen[uniq]=plen[p]; }
                uniq++; break;
            }
            if (kk[s]==key) {
                u32 q = pp[s]; int same=1;
                for (int i=0;i<L;i++) if (pfx[(u64)q*PSTR+i]!=pfx[p*PSTR+i]) { same=0; break; }
                if (same) break;
            }
            s = (s+1) & mask[L-1];
        }
    }
    printf("unique prefixes after dedup: %llu\n", (unsigned long long)uniq);
    if (uniq >= (1ull<<31)) { for (int L=1;L<=NLMAX;L++){free(hk[L-1]);free(hp[L-1]);free(hoc[L-1]);} fprintf(stderr,"too many unique prefixes (>=2^31)\n"); return; }
    if (uniq==0) { for (int L=1;L<=NLMAX;L++){free(hk[L-1]);free(hp[L-1]);free(hoc[L-1]);} return; }
    u64* ck=(u64*)malloc((size_t)(total_cap*8));
    u32* cp=(u32*)malloc((size_t)(total_cap*4));
    u8* co=(u8*)malloc((size_t)total_cap);
    for (int L=1;L<=NLMAX;L++) {
        memcpy(ck+off[L-1], hk[L-1], hcap[L-1]*8);
        memcpy(cp+off[L-1], hp[L-1], hcap[L-1]*4);
        memcpy(co+off[L-1], hoc[L-1], hcap[L-1]);
        free(hk[L-1]); free(hp[L-1]); free(hoc[L-1]);
    }
    u64* d_tbl_key; u32* d_tbl_p; u8* d_tbl_occ;
    u32* d_tbl_off; u32* d_tbl_mask; u32* d_tbl_cnt;
    CUDA_CHECK(cudaMalloc(&d_tbl_key, (size_t)(total_cap*8)));
    CUDA_CHECK(cudaMalloc(&d_tbl_p, (size_t)(total_cap*4)));
    CUDA_CHECK(cudaMalloc(&d_tbl_occ, (size_t)total_cap));
    CUDA_CHECK(cudaMalloc(&d_tbl_off, NLMAX*4));
    CUDA_CHECK(cudaMalloc(&d_tbl_mask, NLMAX*4));
    CUDA_CHECK(cudaMalloc(&d_tbl_cnt, NLMAX*4));
    CUDA_CHECK(cudaMemcpy(d_tbl_key, ck, (size_t)(total_cap*8), cudaMemcpyHostToDevice));
    CUDA_CHECK(cudaMemcpy(d_tbl_p, cp, (size_t)(total_cap*4), cudaMemcpyHostToDevice));
    CUDA_CHECK(cudaMemcpy(d_tbl_occ, co, (size_t)total_cap, cudaMemcpyHostToDevice));
    u32 tcnt[ NLMAX ];
    for (int L=1;L<=NLMAX;L++) tcnt[L-1]=(u32)((L<=nl_max)?lcnt[L]:0);
    CUDA_CHECK(cudaMemcpy(d_tbl_off, off, NLMAX*4, cudaMemcpyHostToDevice));
    CUDA_CHECK(cudaMemcpy(d_tbl_mask, mask, NLMAX*4, cudaMemcpyHostToDevice));
    CUDA_CHECK(cudaMemcpy(d_tbl_cnt, tcnt, NLMAX*4, cudaMemcpyHostToDevice));
    u8* d_pfx;
    CUDA_CHECK(cudaMalloc(&d_pfx, (size_t)(uniq*PSTR)));
    CUDA_CHECK(cudaMemcpy(d_pfx, pfx, (size_t)(uniq*PSTR), cudaMemcpyHostToDevice));
    free(ck); free(cp); free(co);
    u32* d_found; u32* d_nfound;
    ResqEntry* d_resq; u32* d_resq_cnt;
    CUDA_CHECK(cudaMalloc(&d_found, (size_t)(uniq*4)));
    CUDA_CHECK(cudaMalloc(&d_nfound, 4));
    CUDA_CHECK(cudaMalloc(&d_resq, (size_t)(RESQ_CAP*sizeof(ResqEntry))));
    CUDA_CHECK(cudaMalloc(&d_resq_cnt, 4));
    CUDA_CHECK(cudaMemset(d_found, 0, (size_t)(uniq*4)));
    CUDA_CHECK(cudaMemset(d_nfound, 0, 4));
    CUDA_CHECK(cudaMemset(d_resq_cnt, 0, 4));
    // 每次启动使用高分辨率时钟纳秒数 + 进程内计数器混合，保证两次运行私钥序列不同
    static u64 run_seed = 0;
    u64 start = (u64)std::chrono::high_resolution_clock::now().time_since_epoch().count()
              ^ (++run_seed * 0x9E3779B97F4A7C15ull);
    int batch_iters=1; u64 total_mnem=0; double total_s=0;
    u64 qprev=0; u64 printed=0; u64 total_hits=0;
    cudaEvent_t t0,t1;
    CUDA_CHECK(cudaEventCreate(&t0)); CUDA_CHECK(cudaEventCreate(&t1));
    printf("searching random private keys -> P2PKH comp/uncomp + P2SH-P2WPKH, %d blocks x 256 threads... Ctrl+C to stop\n",
           blocks);
    // 无限运行：所有前缀命中后不退出；每轮重置去重表 -> 同一前缀可持续重复命中并持续记录，仅 Ctrl+C 停止
    while (1) {
        CUDA_CHECK(cudaMemset(d_found, 0, (size_t)(uniq*4)));
        CUDA_CHECK(cudaEventRecord(t0));
        multi_hash_kernel<<<blocks, 256>>>(d_tbl_key, d_tbl_p, d_tbl_occ,
                                           d_tbl_off, d_tbl_mask, d_tbl_cnt, d_pfx, uniq,
                                           nl_max, start, batch_iters,
                                           d_found, d_nfound, d_resq, d_resq_cnt);
        CUDA_CHECK(cudaGetLastError());
        CUDA_CHECK(cudaEventRecord(t1));
        CUDA_CHECK(cudaEventSynchronize(t1));
        float ms=0; CUDA_CHECK(cudaEventElapsedTime(&ms, t0, t1));
        total_mnem += (u64)batch_iters*blocks*256;
        total_s += ms/1000.0;
        if (ms > 1000.0f) { int nb=batch_iters/2; if (nb<1) nb=1; batch_iters=nb; }
        else if (ms < 200.0f) { int nb=batch_iters*3; if (nb<1) nb=1; if (nb>1000000) nb=1000000; batch_iters=nb; }
        u32 qcnt=0; CUDA_CHECK(cudaMemcpy(&qcnt, d_resq_cnt, 4, cudaMemcpyDeviceToHost));
        while (qprev < (u64)qcnt) {
            ResqEntry e;
            CUDA_CHECK(cudaMemcpy(&e, d_resq + (qprev & RESQ_MASK), sizeof(ResqEntry), cudaMemcpyDeviceToHost));
            qprev++;
            const char* tn = (e.idx==0)?"uncomp":((e.idx==1)?"comp":"p2sh_p2wpkh");
            const char* ha = (const char*)((e.idx==0)?e.addr2:((e.idx==1)?e.addr:e.addr3));
            printf("HIT(%s) [%4u] \"%s\" -> P2PKH/P2SH\n", tn, e.p, ha);
            printf("      Private Key (WIF): %s\n", e.wif);
            printf("      Address:           %s\n", e.addr2);
            printf("      Compressed Address:%s\n", e.addr);
            printf("      P2SH-P2WPKH:       %s\n", e.addr3);
            if (hf) {
                fprintf(hf, "HIT(%s) [%4u] \"%s\" -> P2PKH/P2SH\n", tn, e.p, ha);
                fprintf(hf, "      Private Key (WIF): %s\n", e.wif);
                fprintf(hf, "      Address:           %s\n", e.addr2);
                fprintf(hf, "      Compressed Address:%s\n", e.addr);
                fprintf(hf, "      P2SH-P2WPKH:       %s\n", e.addr3);
                fprintf(hf, "\n");
            }
            printed++; total_hits++;
        }
        double as = (double)total_mnem/total_s;
        printf("\r  [%7.1f s] %13.0f addr/s | hit %llu  (Ctrl+C stop)", total_s, as, (unsigned long long)total_hits);
        fflush(stdout);
        start += (u64)batch_iters*blocks*256;
    }
    printf("\n(stopped by Ctrl+C) ran %.1f s, total hits %llu\n", total_s, (unsigned long long)total_hits);
    CUDA_CHECK(cudaFree(d_tbl_key)); CUDA_CHECK(cudaFree(d_tbl_p)); CUDA_CHECK(cudaFree(d_tbl_occ));
    CUDA_CHECK(cudaFree(d_tbl_off)); CUDA_CHECK(cudaFree(d_tbl_mask)); CUDA_CHECK(cudaFree(d_tbl_cnt));
    CUDA_CHECK(cudaFree(d_found)); CUDA_CHECK(cudaFree(d_nfound));
    CUDA_CHECK(cudaFree(d_resq)); CUDA_CHECK(cudaFree(d_resq_cnt));
    CUDA_CHECK(cudaFree(d_pfx));
    CUDA_CHECK(cudaEventDestroy(t0)); CUDA_CHECK(cudaEventDestroy(t1));
    if (hf) fclose(hf);
}


int main(int argc, char** argv) {
    const char* mode = argc>1 ? argv[1] : "bench";
    printf("=== BTC Triple-Address Vanity Generator (P2PKH comp + uncomp + P2SH-P2WPKH + WIF) ===\n");

    // comb 固定基点预计算表（60 点）
    u32* d_comb;
    CUDA_CHECK(cudaMalloc(&d_comb, 60*16*4));
    precompute_comb_kernel<<<15, 4>>>(d_comb);
    CUDA_CHECK(cudaGetLastError());
    CUDA_CHECK(cudaMemcpyToSymbol(g_comb, &d_comb, sizeof(d_comb)));

    u8 prefix_nib[ 40];
    int plen=0;

    u8* d_prefix;
    char* d_mnem; u8* d_addr; u8* d_priv; u32* d_found; u32* d_index;
    CUDA_CHECK(cudaMalloc(&d_prefix, 40));
    CUDA_CHECK(cudaMalloc(&d_mnem, 128));
    CUDA_CHECK(cudaMalloc(&d_addr, 20));
    CUDA_CHECK(cudaMalloc(&d_priv, 32));
    CUDA_CHECK(cudaMalloc(&d_found, 4));
    CUDA_CHECK(cudaMalloc(&d_index, 4));
    if (plen) CUDA_CHECK(cudaMemcpy(d_prefix, prefix_nib, plen, cudaMemcpyHostToDevice));

    if (strcmp(mode,"selftest")==0) {
        u64* d_out; u32* d_done;
        CUDA_CHECK(cudaMalloc(&d_out, 11*8));
        CUDA_CHECK(cudaMalloc(&d_done, 4));
        CUDA_CHECK(cudaMemset(d_done, 0, 4));
        cudaStream_t sK, sP;
        CUDA_CHECK(cudaStreamCreate(&sK));
        CUDA_CHECK(cudaStreamCreate(&sP));
        selftest_kernel<<<1,1,0,sK>>>(d_out, d_done);
        for (int w=0;w<40;w++) {
            u32 p=0;
            cudaMemcpyAsync(&p, d_done, 4, cudaMemcpyDeviceToHost, sP);
            cudaStreamSynchronize(sP);
            if (p==1) break;
            std::this_thread::sleep_for(std::chrono::milliseconds(300));
        }
        u64 h_out[ 11];
        cudaMemcpyAsync(h_out, d_out, 11*8, cudaMemcpyDeviceToHost, sP);
        cudaStreamSynchronize(sP);
        printf("selftest:\n");
        printf("  (p-1)+1        = %016llx %016llx\n", (unsigned long long)(h_out[ 0]>>32), (unsigned long long)(h_out[ 0]&0xFFFFFFFFFFFFFFFFULL));
        printf("  123456789*987..= %016llx %016llx\n", (unsigned long long)(h_out[ 1]>>32), (unsigned long long)h_out[ 1]);
        printf("  2G x           = %016llx %016llx\n", (unsigned long long)(h_out[ 2]>>32), (unsigned long long)h_out[ 2]);
        printf("  2G y           = %016llx %016llx\n", (unsigned long long)(h_out[ 3]>>32), (unsigned long long)h_out[ 3]);
        printf("  1G x           = %016llx %016llx\n", (unsigned long long)(h_out[ 4]>>32), (unsigned long long)h_out[ 4]);
        printf("  1G y           = %016llx %016llx\n", (unsigned long long)(h_out[ 5]>>32), (unsigned long long)h_out[ 5]);
        printf("  (n-1)+1 mod n  = %016llx %016llx\n", (unsigned long long)(h_out[ 6]>>32), (unsigned long long)h_out[ 6]);
        printf("  (n-2)+3 mod n  = %016llx %016llx\n", (unsigned long long)(h_out[ 7]>>32), (unsigned long long)h_out[ 7]);
        printf("  2G+G x (jac)   = %016llx %016llx\n", (unsigned long long)(h_out[ 8]>>32), (unsigned long long)h_out[ 8]);
        printf("  3G x (scalar)  = %016llx %016llx\n", (unsigned long long)(h_out[ 9]>>32), (unsigned long long)h_out[ 9]);
        printf("  a*a^-1         = %016llx %016llx\n", (unsigned long long)(h_out[ 10]>>32), (unsigned long long)h_out[ 10]);
        CUDA_CHECK(cudaFree(d_out));
        CUDA_CHECK(cudaFree(d_done));
        cudaStreamDestroy(sK); cudaStreamDestroy(sP);
    }
    else if (strcmp(mode,"fieldtest")==0) {
        // ftprog 已验证模式：自定义流 + 异步轮询，不调用 cudaDeviceSynchronize
        u32* d_out; u32* d_prog;
        CUDA_CHECK(cudaMalloc(&d_out, 8*8*4));
        CUDA_CHECK(cudaMalloc(&d_prog, 4));
        CUDA_CHECK(cudaMemset(d_prog, 0, 4));
        cudaStream_t sK, sP;
        CUDA_CHECK(cudaStreamCreate(&sK));
        CUDA_CHECK(cudaStreamCreate(&sP));
        ftprog_kernel<<<1,1,0,sK>>>(d_out, d_prog);
        for (int t=0;t<30;t++) {
            u32 p=0;
            cudaMemcpyAsync(&p, d_prog, 4, cudaMemcpyDeviceToHost, sP);
            cudaStreamSynchronize(sP);
            printf("t=%d prog=%u\n", t, p);
            fflush(stdout);
            if (p>=9) break;
            std::this_thread::sleep_for(std::chrono::milliseconds(300));
        }
        u32 h_out[ 64];
        cudaError_t merr = cudaMemcpy(h_out, d_out, 8*8*4, cudaMemcpyDeviceToHost);
        printf("sync-copy err=%s\n", cudaGetErrorString(merr));
        const char* names[ 8] = {
            "(p-1)*(p-1)      ", "(p-2)*(p-1)      ", "2^255 * 2^255     ",
            "aaaa.. * aaaa..  ", "1234567890abcdef^2", "0xffff...+0x100000001",
            "inv(a)*a          ", "(n-1)+2 mod n     "
        };
        for (int t=0;t<8;t++) {
            printf("%s = ", names[t]);
            for (int i=7;i>=0;i--) printf("%08x", h_out[t*8+i]);
            printf("\n");
        }
        CUDA_CHECK(cudaFree(d_out));
        CUDA_CHECK(cudaFree(d_prog));
        cudaStreamDestroy(sK); cudaStreamDestroy(sP);
    }
    if (strcmp(mode,"ftprog")==0) {
        u32* d_out; u32* d_prog;
        CUDA_CHECK(cudaMalloc(&d_out, 8*8*4));
        CUDA_CHECK(cudaMalloc(&d_prog, 4));
        CUDA_CHECK(cudaMemset(d_prog, 0, 4));
        cudaStream_t sK, sP;
        CUDA_CHECK(cudaStreamCreate(&sK));
        CUDA_CHECK(cudaStreamCreate(&sP));
        ftprog_kernel<<<1,1,0,sK>>>(d_out, d_prog);
        for (int t=0;t<30;t++) {
            u32 p=0;
            cudaMemcpyAsync(&p, d_prog, 4, cudaMemcpyDeviceToHost, sP);
            cudaStreamSynchronize(sP);
            printf("t=%d prog=%u\n", t, p);
            fflush(stdout);
            if (p>=9) break;
            std::this_thread::sleep_for(std::chrono::milliseconds(300));
        }
        CUDA_CHECK(cudaFree(d_out));
        CUDA_CHECK(cudaFree(d_prog));
        cudaStreamDestroy(sK); cudaStreamDestroy(sP);
    }
    else if (strcmp(mode,"bisect")==0) {
        int c = (argc>2)?atoi(argv[ 2]):0;
        u32* d_out;
        CUDA_CHECK(cudaMalloc(&d_out, 8*4));
        bisect_kernel<<<1,1>>>(d_out, c);
        CUDA_CHECK(cudaGetLastError());
        u32 h_out[ 8];
        CUDA_CHECK(cudaMemcpy(h_out, d_out, 8*4, cudaMemcpyDeviceToHost));
        printf("case %d = ", c);
        for (int i=7;i>=0;i--) printf("%08x", h_out[i]);
        printf("\n");
        CUDA_CHECK(cudaFree(d_out));
    }
    else if (strcmp(mode,"debug")==0) {
        u32* d_out;
        CUDA_CHECK(cudaMalloc(&d_out, 44*4));
        debug_kernel<<<1,1>>>(d_out);
        CUDA_CHECK(cudaGetLastError());
        u32 h_out[ 44];
        CUDA_CHECK(cudaMemcpy(h_out, d_out, 44*4, cudaMemcpyDeviceToHost));
        printf("debug (p-1)^2 intermediates:\n");
        printf("  raw product t[0..15]:\n    ");
        for (int i=0;i<16;i++) printf("%08x ", h_out[i]);
        printf("\n  v after initial fold:\n    ");
        for (int i=0;i<10;i++) printf("%08x ", h_out[16+i]);
        printf("\n  v after fe_fold_hi:\n    ");
        for (int i=0;i<10;i++) printf("%08x ", h_out[26+i]);
        printf("\n  fe_mul r:\n    ");
        for (int i=0;i<8;i++) printf("%08x ", h_out[36+i]);
        printf("\n");
        CUDA_CHECK(cudaFree(d_out));
    }
    else if (strcmp(mode,"jdbl")==0) {
        u32* d_done; CUDA_CHECK(cudaMalloc(&d_done, 4));
        u32* d_out; CUDA_CHECK(cudaMalloc(&d_out, 256));
        CUDA_CHECK(cudaMemset(d_done, 0, 4));
        cudaStream_t sK, sP;
        CUDA_CHECK(cudaStreamCreate(&sK)); CUDA_CHECK(cudaStreamCreate(&sP));
        jdbl_kernel<<<1,1,0,sK>>>(d_out, d_done);
        for (int w=0;w<50;w++){ u32 p=0; cudaMemcpyAsync(&p,d_done,4,cudaMemcpyDeviceToHost,sP); cudaStreamSynchronize(sP); if(p==1)break; std::this_thread::sleep_for(std::chrono::milliseconds(300)); }
        u32 hb[ 64];
        cudaMemcpyAsync(hb, d_out, 256, cudaMemcpyDeviceToHost, sP);
        cudaStreamSynchronize(sP);
        const char* names[ 10] = { "A=X^2", "B=Y^2", "C=B^2", "D=2t", "E=3A", "F0=E^2", "t0=2D", "X3", "Y3", "Z3" };
        int o=0;
        for (int q=0;q<10;q++){ printf("%s: ",names[q]); for(int i=7;i>=0;i--) printf("%08x",hb[o++]); printf("\n"); }
        cudaStreamDestroy(sK); cudaStreamDestroy(sP);
        CUDA_CHECK(cudaFree(d_done)); CUDA_CHECK(cudaFree(d_out));
    }
    else if (strcmp(mode,"sm")==0) {
        u32* d_done; CUDA_CHECK(cudaMalloc(&d_done, 4));
        u32* d_out; CUDA_CHECK(cudaMalloc(&d_out, 128));
        cudaStream_t sK, sP;
        CUDA_CHECK(cudaStreamCreate(&sK)); CUDA_CHECK(cudaStreamCreate(&sP));
        for (int cc=0;cc<6;cc++) {
            CUDA_CHECK(cudaMemset(d_done, 0, 4));
            sm_kernel<<<1,1,0,sK>>>(d_out, d_done, cc);
            for (int w=0;w<50;w++){ u32 p=0; cudaMemcpyAsync(&p,d_done,4,cudaMemcpyDeviceToHost,sP); cudaStreamSynchronize(sP); if(p==1)break; std::this_thread::sleep_for(std::chrono::milliseconds(300)); }
            u32 hb[ 24];
            cudaMemcpyAsync(hb, d_out, 96, cudaMemcpyDeviceToHost, sP);
            cudaStreamSynchronize(sP);
            const char* nm[ 6] = { "k0h", "2^255", "k0h_top32", "0xe9", "2^247", "10G_jac" };
            if (cc==1 || cc==5) {
                printf("%s X: ", nm[cc]); for(int i=7;i>=0;i--) printf("%08x",hb[i]); printf("\n");
                printf("%s Y: ", nm[cc]); for(int i=15;i>=8;i--) printf("%08x",hb[i]); printf("\n");
                printf("%s Z: ", nm[cc]); for(int i=23;i>=16;i--) printf("%08x",hb[i]); printf("\n");
            } else {
                printf("%s x: ", nm[cc]); for(int i=7;i>=0;i--) printf("%08x",hb[i]); printf("\n");
                printf("%s y: ", nm[cc]); for(int i=15;i>=8;i--) printf("%08x",hb[i]); printf("\n");
            }
        }
        cudaStreamDestroy(sK); cudaStreamDestroy(sP);
        CUDA_CHECK(cudaFree(d_done)); CUDA_CHECK(cudaFree(d_out));
    }

    else if (strcmp(mode,"ktest")==0) {
        u32* d_done; CUDA_CHECK(cudaMalloc(&d_done, 4));
        u8* d_out; CUDA_CHECK(cudaMalloc(&d_out, 128));
        CUDA_CHECK(cudaMemset(d_done, 0, 4));
        cudaStream_t sK, sP;
        CUDA_CHECK(cudaStreamCreate(&sK)); CUDA_CHECK(cudaStreamCreate(&sP));
        ktest_kernel<<<1,1,0,sK>>>(d_out, d_done);
        for (int w=0;w<50;w++){ u32 p=0; cudaMemcpyAsync(&p,d_done,4,cudaMemcpyDeviceToHost,sP); cudaStreamSynchronize(sP); if(p==1)break; std::this_thread::sleep_for(std::chrono::milliseconds(300)); }
        u8 hb[ 96];
        cudaMemcpyAsync(hb, d_out, 96, cudaMemcpyDeviceToHost, sP);
        cudaStreamSynchronize(sP);
        printf("keccak(""):  "); for(int i=0;i<32;i++) printf("%02x",hb[i]); printf("\n");
        printf("keccak(abc): "); for(int i=0;i<32;i++) printf("%02x",hb[32+i]); printf("\n");
        printf("keccak(pub): "); for(int i=0;i<32;i++) printf("%02x",hb[64+i]); printf("\n");
        printf("f1600(0) st0: "); for(int i=0;i<8;i++) printf("%02x",hb[96+i]); printf("\n");
        cudaStreamDestroy(sK); cudaStreamDestroy(sP);
        CUDA_CHECK(cudaFree(d_done)); CUDA_CHECK(cudaFree(d_out));
    }
    else if (strcmp(mode,"ptest")==0) {
        u32* d_done; CUDA_CHECK(cudaMalloc(&d_done, 4));
        u32* d_out; CUDA_CHECK(cudaMalloc(&d_out, 256));
        CUDA_CHECK(cudaMemset(d_done, 0, 4));
        cudaStream_t sK, sP;
        CUDA_CHECK(cudaStreamCreate(&sK)); CUDA_CHECK(cudaStreamCreate(&sP));
        ptest_kernel<<<1,1,0,sK>>>(d_out, d_done);
        for (int w=0;w<50;w++){ u32 p=0; cudaMemcpyAsync(&p,d_done,4,cudaMemcpyDeviceToHost,sP); cudaStreamSynchronize(sP); if(p==1)break; std::this_thread::sleep_for(std::chrono::milliseconds(300)); }
        u32 hb[ 64];
        cudaMemcpyAsync(hb, d_out, 256, cudaMemcpyDeviceToHost, sP);
        cudaStreamSynchronize(sP);
        int o=0;
        printf("2G x: "); for(int i=0;i<8;i++) printf("%08x",hb[o++]); printf("\n");
        printf("2G y: "); for(int i=0;i<8;i++) printf("%08x",hb[o++]); printf("\n");
        printf("3G x: "); for(int i=0;i<8;i++) printf("%08x",hb[o++]); printf("\n");
        printf("3G y: "); for(int i=0;i<8;i++) printf("%08x",hb[o++]); printf("\n");
        printf("4G x: "); for(int i=0;i<8;i++) printf("%08x",hb[o++]); printf("\n");
        printf("4G y: "); for(int i=0;i<8;i++) printf("%08x",hb[o++]); printf("\n");
        printf("5G x: "); for(int i=0;i<8;i++) printf("%08x",hb[o++]); printf("\n");
        printf("5G y: "); for(int i=0;i<8;i++) printf("%08x",hb[o++]); printf("\n");
        printf("7G x: "); for(int i=0;i<8;i++) printf("%08x",hb[o++]); printf("\n");
        printf("7G y: "); for(int i=0;i<8;i++) printf("%08x",hb[o++]); printf("\n");
        printf("8G x: "); for(int i=0;i<8;i++) printf("%08x",hb[o++]); printf("\n");
        printf("8G y: "); for(int i=0;i<8;i++) printf("%08x",hb[o++]); printf("\n");
        cudaStreamDestroy(sK); cudaStreamDestroy(sP);
        CUDA_CHECK(cudaFree(d_done)); CUDA_CHECK(cudaFree(d_out));
    }
    else if (strcmp(mode,"scdiag")==0) {
        u32* d_done; CUDA_CHECK(cudaMalloc(&d_done, 4));
        u32* d_out; CUDA_CHECK(cudaMalloc(&d_out, 512));
        CUDA_CHECK(cudaMemset(d_done, 0, 4));
        cudaStream_t sK, sP;
        CUDA_CHECK(cudaStreamCreate(&sK)); CUDA_CHECK(cudaStreamCreate(&sP));
        scdiag_kernel<<<1,1,0,sK>>>(d_out, d_done);
        for (int w=0;w<50;w++){ u32 p=0; cudaMemcpyAsync(&p,d_done,4,cudaMemcpyDeviceToHost,sP); cudaStreamSynchronize(sP); if(p==1)break; std::this_thread::sleep_for(std::chrono::milliseconds(300)); }
        u32 hb[ 128];
        cudaMemcpyAsync(hb, d_out, 512, cudaMemcpyDeviceToHost, sP);
        cudaStreamSynchronize(sP);
        int o=0;
        printf("il:  "); for(int i=0;i<8;i++) printf("%08x",hb[o++]); printf("\n");
        printf("kf:  "); for(int i=0;i<8;i++) printf("%08x",hb[o++]); printf("\n");
        printf("t0-8:"); for(int i=0;i<9;i++) printf("%08x",hb[o++]); printf("\n");
        printf("r:   "); for(int i=0;i<8;i++) printf("%08x",hb[o++]); printf("\n");
        printf("fe_ge(t,N):%u  t8:%u\n", hb[o], hb[o+1]);
        cudaStreamDestroy(sK); cudaStreamDestroy(sP);
        CUDA_CHECK(cudaFree(d_done)); CUDA_CHECK(cudaFree(d_out));
    }
    else if (strcmp(mode,"vec")==0) {
        const char* ents[ 1] = { "00000000000000000000000000000000" };
        u32* d_done;
        CUDA_CHECK(cudaMalloc(&d_done, 4));
        u8* d_out;
        CUDA_CHECK(cudaMalloc(&d_out, 600));
        for (int t=0;t<1;t++) {
            u8 ent[ 16];
            for (int i=0;i<16;i++){ int a,b; char ch1=ents[t][2*i], ch2=ents[t][2*i+1];
                a=(ch1<='9')?ch1-'0':ch1-'a'+10; b=(ch2<='9')?ch2-'0':ch2-'a'+10; ent[i]=(u8)((a<<4)|b); }
            u8* d_ent;
            CUDA_CHECK(cudaMalloc(&d_ent, 16));
            CUDA_CHECK(cudaMemcpy(d_ent, ent, 16, cudaMemcpyHostToDevice));
            CUDA_CHECK(cudaMemset(d_done, 0, 4));
            cudaStream_t sK, sP;
            CUDA_CHECK(cudaStreamCreate(&sK));
            CUDA_CHECK(cudaStreamCreate(&sP));
            vec_kernel<<<1,1,0,sK>>>(d_ent, d_out, d_done);
            for (int w=0;w<50;w++) {
                u32 p=0;
                cudaMemcpyAsync(&p, d_done, 4, cudaMemcpyDeviceToHost, sP);
                cudaStreamSynchronize(sP);
                if (p==1) break;
                std::this_thread::sleep_for(std::chrono::milliseconds(300));
            }
            u8 hb[ 600];
            cudaMemcpyAsync(hb, d_out, 600, cudaMemcpyDeviceToHost, sP);
            cudaStreamSynchronize(sP);
            int o=0;
            printf("entropy: "); for(int i=0;i<16;i++) printf("%02x",hb[o++]); printf("\n");
            printf("seed:    "); for(int i=0;i<64;i++) printf("%02x",hb[o++]); printf("\n");
            printf("mK:      "); for(int i=0;i<32;i++) printf("%02x",hb[o++]); printf("\n");
            printf("mC:      "); for(int i=0;i<32;i++) printf("%02x",hb[o++]); printf("\n");
            printf("k44:     "); for(int i=0;i<32;i++) printf("%02x",hb[o++]); printf("\n");
            printf("c44:     "); for(int i=0;i<32;i++) printf("%02x",hb[o++]); printf("\n");
            printf("k60:     "); for(int i=0;i<32;i++) printf("%02x",hb[o++]); printf("\n");
            printf("c60:     "); for(int i=0;i<32;i++) printf("%02x",hb[o++]); printf("\n");
            printf("k0h:     "); for(int i=0;i<32;i++) printf("%02x",hb[o++]); printf("\n");
            printf("c0h:     "); for(int i=0;i<32;i++) printf("%02x",hb[o++]); printf("\n");
            printf("k0n:     "); for(int i=0;i<32;i++) printf("%02x",hb[o++]); printf("\n");
            printf("k0n2:    "); for(int i=0;i<32;i++) printf("%02x",hb[o++]); printf("\n");
            printf("pubX:    "); for(int i=0;i<32;i++) printf("%02x",hb[o++]); printf("\n");
            printf("pubY:    "); for(int i=0;i<32;i++) printf("%02x",hb[o++]); printf("\n");
            printf("addr:    "); for(int i=0;i<20;i++) printf("%02x",hb[o++]); printf("\n");
            printf("mnem:    %s\n", (char*)(hb+o));
            cudaStreamDestroy(sK); cudaStreamDestroy(sP);
            CUDA_CHECK(cudaFree(d_ent));
        }
        CUDA_CHECK(cudaFree(d_done));
        CUDA_CHECK(cudaFree(d_out));
    }
    else if (strcmp(mode,"test")==0) {
        const char* ents[ 3] = {
            "00000000000000000000000000000000",
            "7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f",
            "80808080808080808080808080808080"
        };
        u32* d_done;
        CUDA_CHECK(cudaMalloc(&d_done, 4));
        for (int t=0;t<3;t++) {
            u8 ent[ 16];
            for (int i=0;i<16;i++){ int a,b; char ch1=ents[t][2*i], ch2=ents[t][2*i+1];
                a=(ch1<='9')?ch1-'0':ch1-'a'+10; b=(ch2<='9')?ch2-'0':ch2-'a'+10; ent[i]=(u8)((a<<4)|b); }
            u8* d_ent;
            CUDA_CHECK(cudaMalloc(&d_ent, 16));
            CUDA_CHECK(cudaMemcpy(d_ent, ent, 16, cudaMemcpyHostToDevice));
            CUDA_CHECK(cudaMemset(d_done, 0, 4));
            cudaStream_t sK, sP;
            CUDA_CHECK(cudaStreamCreate(&sK));
            CUDA_CHECK(cudaStreamCreate(&sP));
            test_kernel<<<1,1,0,sK>>>(d_ent, d_mnem, d_addr, d_priv, d_done);
            for (int w=0;w<40;w++) {
                u32 p=0;
                cudaMemcpyAsync(&p, d_done, 4, cudaMemcpyDeviceToHost, sP);
                cudaStreamSynchronize(sP);
                if (p==1) break;
                std::this_thread::sleep_for(std::chrono::milliseconds(300));
            }
            char mnem[ 128]; u8 addr[ 20], privk[ 32];
            cudaMemcpyAsync(mnem, d_mnem, 128, cudaMemcpyDeviceToHost, sP);
            cudaMemcpyAsync(addr, d_addr, 20, cudaMemcpyDeviceToHost, sP);
            cudaMemcpyAsync(privk, d_priv, 32, cudaMemcpyDeviceToHost, sP);
            cudaStreamSynchronize(sP);
            printf("entropy %s:\n", ents[t]);
            printf("  mnemonic: %s\n", mnem);
            printf("  addr:     0x"); print_hex(addr,20); printf("\n");
            printf("  priv:     0x"); print_hex(privk,32); printf("\n");
            cudaStreamDestroy(sK); cudaStreamDestroy(sP);
            CUDA_CHECK(cudaFree(d_ent));
        }
        CUDA_CHECK(cudaFree(d_done));
    }

    else if (strcmp(mode,"prof")==0) {
        int stage = (argc>=3) ? atoi(argv[2]) : 3;
        int iters = (argc>=4) ? atoi(argv[3]) : 1;
        int blocks = (argc>=5) ? atoi(argv[4]) : 1024;
        u64* d_out; u32* d_done;
        CUDA_CHECK(cudaMalloc(&d_out, 1024*8));
        CUDA_CHECK(cudaMalloc(&d_done, 4));
        CUDA_CHECK(cudaMemset(d_done, 0, 4));
        cudaStream_t sK, sP;
        CUDA_CHECK(cudaStreamCreate(&sK)); CUDA_CHECK(cudaStreamCreate(&sP));
        cudaEvent_t t0,t1;
        CUDA_CHECK(cudaEventCreate(&t0)); CUDA_CHECK(cudaEventCreate(&t1));
        cudaEventRecord(t0);
        prof_kernel<<<blocks, 256, 0, sK>>>(0, iters, stage, d_out, d_done);
        CUDA_CHECK(cudaGetLastError());
        for (int w=0;w<100;w++){ u32 p=0; cudaMemcpyAsync(&p,d_done,4,cudaMemcpyDeviceToHost,sP); cudaStreamSynchronize(sP); if(p==1)break; std::this_thread::sleep_for(std::chrono::milliseconds(50)); }
        cudaEventRecord(t1, sK);
        cudaEventSynchronize(t1);
        float ms=0; cudaEventElapsedTime(&ms, t0, t1);
        u64 total=(u64)iters*blocks*256;
        printf("prof stage=%d: %llu attempts in %.2f s = %.1f addr/s\n", stage, (unsigned long long)total, ms/1000.0, total/(ms/1000.0));
        CUDA_CHECK(cudaFree(d_out)); CUDA_CHECK(cudaFree(d_done));
        cudaStreamDestroy(sK); cudaStreamDestroy(sP);
        cudaEventDestroy(t0); cudaEventDestroy(t1);
    }

    else if (strcmp(mode,"hd")==0 || strcmp(mode,"hddiag")==0 || strcmp(mode,"hddiag2")==0) {
        fprintf(stderr, "HD mode is not available in the BTC build (vanity/file modes only)\n");
        return 1;
    }
    else if (strcmp(mode,"btctest")==0) {
        u8* d_out; u32* d_done;
        CUDA_CHECK(cudaMalloc(&d_out, 768));
        CUDA_CHECK(cudaMalloc(&d_done, 4));
        CUDA_CHECK(cudaMemset(d_done, 0, 4));
        btc_test_kernel<<<1,1>>>(d_out, d_done);
        CUDA_CHECK(cudaGetLastError());
        u32 done=0; while (!done) { CUDA_CHECK(cudaMemcpy(&done, d_done, 4, cudaMemcpyDeviceToHost)); }
        u8 hb[ 768]; CUDA_CHECK(cudaMemcpy(hb, d_out, 768, cudaMemcpyDeviceToHost));
        for (int q=0;q<2;q++) {
            int o=q*320;
            printf("N=%d\n", q==0?0:3);
            printf("  priv:      "); print_hex(hb+o, 32); printf("\n");
            printf("  pub_comp:  "); print_hex(hb+o+32, 33); printf("\n");
            printf("  hash160:   "); print_hex(hb+o+65, 20); printf("\n");
            printf("  P2PKH:     %s\n", hb+o+85);
            printf("  P2WPKH:    %s\n", hb+o+149);
            printf("  P2TR:      %s\n", hb+o+229);
        }
        printf("  mnemonic:  %s\n", hb+640);
        CUDA_CHECK(cudaFree(d_out)); CUDA_CHECK(cudaFree(d_done));
    }

    else if (strcmp(mode,"file")==0) {
        if (argc<3) { fprintf(stderr,"usage: file <prefix_file> [blocks]\n"); return 1; }
        const char* fn = argv[2];
        int blocks = (argc>=4) ? atoi(argv[3]) : 1024;
        int nl_max = 34;
        FILE* fp = fopen(fn, "r");
        if (!fp) { fprintf(stderr,"cannot open %s\n", fn); return 1; }
        u64 cap = 1<<16, nprefix=0, nskip=0;
        u8* pfx = (u8*)malloc((size_t)(cap*PSTR));
        u8* plen = (u8*)malloc((size_t)cap);
        char line[ 1024 ];
        while (fgets(line, sizeof(line), fp)) {
            int a=0; while (line[a]==' '||line[a]=='\t'||line[a]=='\r'||line[a]=='\n') a++;
            int b=0; while (line[a+b]!='\0' && line[a+b]!='\n' && line[a+b]!='\r' && line[a+b]!='#' && line[a+b]!=' ' && line[a+b]!='\t') b++;
            if (b==0) continue;
            if (b > nl_max) { nskip++; continue; }
            const char* p = line + a;
            for (int i=0;i<b;i++) pfx[nprefix*PSTR+i]=(u8)p[i];
            plen[nprefix]=(u8)b;
            nprefix++;
            if (nprefix >= cap) { cap*=2; pfx=(u8*)realloc(pfx,cap*PSTR); plen=(u8*)realloc(plen,cap); }
        }
        fclose(fp);
        if (nprefix==0) { fprintf(stderr,"no valid prefixes in file\n"); return 1; }
        printf("file mode: read %llu string prefixes (skipped %llu with len>%d)\n", (unsigned long long)nprefix, (unsigned long long)nskip, nl_max);
        run_dual_search(pfx, plen, nprefix, blocks);
        free(pfx); free(plen);
    }
    else if (strcmp(mode,"vanity")==0) {
        if (argc<3) { fprintf(stderr,"usage: vanity <prefix> [blocks]\n"); return 1; }
        const char* p = argv[2];
        int blocks = (argc>=4) ? atoi(argv[3]) : 1024;
        int nl_max = 34;
        int len = (int)strlen(p);
        if (len==0) { fprintf(stderr,"bad prefix\n"); return 1; }
        if (len > nl_max) { fprintf(stderr,"prefix too long for P2PKH (max %d chars)\n", nl_max); return 1; }
        u8 pfx[ PSTR ]; u8 plen[ 1 ];
        for (int i=0;i<len;i++) pfx[i]=(u8)p[i];
        plen[0]=(u8)len;
        printf("vanity prefix: \"%s\" (%d chars), P2PKH comp/uncomp + P2SH-P2WPKH\n", p, len);
        run_dual_search(pfx, plen, 1, blocks);
    }
    else { // bench: BTC 地址生成吞吐（不查表）
        int iters = (argc>=3) ? atoi(argv[2]) : 5000;
        int blocks = (argc>=4) ? atoi(argv[3]) : 1024;
        u64* d_tbl_key; u32* d_tbl_p; u8* d_tbl_occ;
        u32* d_tbl_off; u32* d_tbl_mask; u32* d_tbl_cnt;
        CUDA_CHECK(cudaMalloc(&d_tbl_key, 8*8));
        CUDA_CHECK(cudaMalloc(&d_tbl_p, 8*4));
        CUDA_CHECK(cudaMalloc(&d_tbl_occ, 8));
        CUDA_CHECK(cudaMalloc(&d_tbl_off, NLMAX*4));
        CUDA_CHECK(cudaMalloc(&d_tbl_mask, NLMAX*4));
        CUDA_CHECK(cudaMalloc(&d_tbl_cnt, NLMAX*4));
        CUDA_CHECK(cudaMemset(d_tbl_occ, 0, 8));
        u8* d_pfx2; CUDA_CHECK(cudaMalloc(&d_pfx2, 1));
        u32* d_found2; u32* d_nfound; ResqEntry* d_resq; u32* d_resq_cnt;
        CUDA_CHECK(cudaMalloc(&d_found2, 4));
        CUDA_CHECK(cudaMalloc(&d_nfound, 4));
        CUDA_CHECK(cudaMalloc(&d_resq, (size_t)(RESQ_CAP*sizeof(ResqEntry))));
        CUDA_CHECK(cudaMalloc(&d_resq_cnt, 4));
        CUDA_CHECK(cudaMemset(d_found2, 0, 4)); CUDA_CHECK(cudaMemset(d_nfound, 0, 4)); CUDA_CHECK(cudaMemset(d_resq_cnt, 0, 4));
        cudaEvent_t t0,t1;
        CUDA_CHECK(cudaEventCreate(&t0)); CUDA_CHECK(cudaEventCreate(&t1));
        CUDA_CHECK(cudaEventRecord(t0));
        multi_hash_kernel<<<blocks, 256>>>(d_tbl_key, d_tbl_p, d_tbl_occ,
                                           d_tbl_off, d_tbl_mask, d_tbl_cnt, d_pfx2, 0,
                                           0, 0, iters,
                                           d_found2, d_nfound, d_resq, d_resq_cnt);
        CUDA_CHECK(cudaGetLastError());
        CUDA_CHECK(cudaEventRecord(t1));
        CUDA_CHECK(cudaEventSynchronize(t1));
        float ms=0; CUDA_CHECK(cudaEventElapsedTime(&ms, t0, t1));
        u64 total=(u64)iters*blocks*256;
        printf("bench BTC P2PKH triple(comp+uncomp+p2sh_p2wpkh): %llu addresses in %.2f s = %.1f addr/s\n",
               (unsigned long long)total, ms/1000.0, total/(ms/1000.0));
        CUDA_CHECK(cudaEventDestroy(t0)); CUDA_CHECK(cudaEventDestroy(t1));
        CUDA_CHECK(cudaFree(d_tbl_key)); CUDA_CHECK(cudaFree(d_tbl_p)); CUDA_CHECK(cudaFree(d_tbl_occ));
        CUDA_CHECK(cudaFree(d_tbl_off)); CUDA_CHECK(cudaFree(d_tbl_mask)); CUDA_CHECK(cudaFree(d_tbl_cnt));
        CUDA_CHECK(cudaFree(d_pfx2));
        CUDA_CHECK(cudaFree(d_found2)); CUDA_CHECK(cudaFree(d_nfound)); CUDA_CHECK(cudaFree(d_resq)); CUDA_CHECK(cudaFree(d_resq_cnt));
    }

    CUDA_CHECK(cudaFree(d_prefix)); CUDA_CHECK(cudaFree(d_mnem));
    CUDA_CHECK(cudaFree(d_addr)); CUDA_CHECK(cudaFree(d_priv)); CUDA_CHECK(cudaFree(d_found));
    CUDA_CHECK(cudaFree(d_index));
    return 0;
}
