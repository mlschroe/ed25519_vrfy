/*
 * Copyright (c) 2020, SUSE LLC.
 *
 * This program is licensed under the BSD license, read LICENSE.BSD
 * for further information
 */


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

/* 
 * simple, standalone, and not very fast ed25519 signature verification
 * no external libraries needed
 *
 * interface:
 *
 * unsigned char pub[32];	// ed25519 pubkey
 * unsigned char sig[64];	// signature to verify
 * unsigned char datahash[64];	// sha512 digest of sig[0..31] pub[0..31] data
 *
 * int result = ed25519_vrfy(pub, sig, datahash);	// success: 1, failure: 0
 *
 */

typedef uint32_t mp_t;
typedef uint64_t mp2_t;
#define MP_T_BYTES 4
#define MP_T_BITS (MP_T_BYTES * 8)

static inline void
mpzero(int len, mp_t *target)
{
  memset(target, 0, MP_T_BYTES * len);
}

static inline void
mpcpy(int len, mp_t *target, const mp_t *source)
{
  memcpy(target, source, len * MP_T_BYTES);
}

static inline int
mpisless(int len, const mp_t *a, const mp_t *b)
{
  int i;
  for (i = len - 1; i >= 0; i--)
    if (a[i] < b[i])
      return 1;
    else if (a[i] > b[i])
      return 0;
  return 0;
}

static inline int
mpisequal(int len, const mp_t *a, const mp_t *b)
{
  return memcmp(a, b, len * MP_T_BYTES) == 0;
}

static inline int
mpiszero(int len, const mp_t *a)
{
  int i;
  for (i = 0; i < len; i++)
    if (a[i])
      return 0;
  return 1;
}

/* subtract mod from target. target >= mod */
static inline void mpsubmod(int len, mp_t *target, const mp_t *mod)
{
  int i;
  mp2_t n;
  for (n = 0, i = 0; i < len; i++)
    {
      mp2_t n2 = (mp2_t)mod[i] + n;
      n = n2 > target[i] ? 1 : 0;
      target[i] -= (mp_t)n2;
    }
}

#define ED25519_LEN (32 / MP_T_BYTES)

#if MP_T_BYTES == 4
# define ED25519_CONST1(x) (mp_t)x
#elif MP_T_BYTES == 2
# define ED25519_CONST1(x) (mp_t)(x >> 0), (mp_t)(x >> 16)
#elif MP_T_BYTES == 1
# define ED25519_CONST1(x) (mp_t)(x >> 0), (mp_t)(x >> 8), (mp_t)(x >> 16), (mp_t)(x >> 24)
#endif

#define ED25519_CONST(a, b, c, d, e, f, g, h) { \
  ED25519_CONST1(h), ED25519_CONST1(g), ED25519_CONST1(f), ED25519_CONST1(e), \
  ED25519_CONST1(d), ED25519_CONST1(c), ED25519_CONST1(b), ED25519_CONST1(a) \
}

static const mp_t ed25519_q[] =		/* mod prime 2^255 - 19 */
  ED25519_CONST(0x7fffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffed);
static const mp_t ed25519_d[] = 	/* -(121665/121666) */
  ED25519_CONST(0x52036cee, 0x2b6ffe73, 0x8cc74079, 0x7779e898, 0x00700a4d, 0x4141d8ab, 0x75eb4dca, 0x135978a3);
static const mp_t ed25519_sqrtm1[] =	/* sqrt(-1) */
  ED25519_CONST(0x2b832480, 0x4fc1df0b, 0x2b4d0099, 0x3dfbd7a7, 0x2f431806, 0xad2fe478, 0xc4ee1b27, 0x4a0ea0b0);
static const mp_t ed25519_l[] = 	/* order of base point */
  ED25519_CONST(0x10000000, 0x00000000, 0x00000000, 0x00000000, 0x14def9de, 0xa2f79cd6, 0x5812631a, 0x5cf5d3ed);
static const mp_t ed25519_gx[] = 	/* base point */
  ED25519_CONST(0x216936d3, 0xcd6e53fe, 0xc0a4e231, 0xfdd6dc5c, 0x692cc760, 0x9525a7b2, 0xc9562d60, 0x8f25d51a);
static const mp_t ed25519_gy[] = 	/* base point */
  ED25519_CONST(0x66666666, 0x66666666, 0x66666666, 0x66666666, 0x66666666, 0x66666666, 0x66666666, 0x66666658);
static const mp_t ed25519_one[] = 	/* 1 */
  ED25519_CONST(0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000001);
static const mp_t ed25519_invl[] =	/* 2^512 / l - 15 * 2^256 */
  ED25519_CONST(0xffffffff, 0xffffffff, 0xffffffff, 0xffffffeb, 0x2106215d, 0x086329a7, 0xed9ce5a3, 0x0a2c131b);

static void
ed25519_add(mp_t *target, const mp_t *m1, const mp_t *m2)
{
  int i;
  mp2_t x = 0;
  for (i = 0; i < ED25519_LEN; i++)
    {
      x += (mp2_t)m1[i] + m2[i];
      target[i] = x;
      x >>= MP_T_BITS;
    }
  if (x || target[ED25519_LEN - 1] > ed25519_q[ED25519_LEN - 1] ||
      (target[ED25519_LEN - 1] == ed25519_q[ED25519_LEN - 1] && !mpisless(ED25519_LEN - 1, target, ed25519_q)))
    mpsubmod(ED25519_LEN, target, ed25519_q);
}

static void
ed25519_sub(mp_t *target, const mp_t *m1, const mp_t *m2)
{
  int i;
  mp2_t x = 0;
  for (i = 0; i < ED25519_LEN; i++)
    {
      x = (mp2_t)m1[i] - m2[i] - x;
      target[i] = x;
      x = x & ((mp2_t)1 << MP_T_BITS) ? 1 : 0;
    }
  if (x)
    {
      for (x = 0, i = 0; i < ED25519_LEN; i++)
	{
	  x += (mp2_t)target[i] + ed25519_q[i];
	  target[i] = x;
	  x >>= MP_T_BITS;
	}
    }
}

/* target = 512 bit input modulo ed25519_q */
static void
ed25519_reduce512(mp_t *target, const mp_t *a)
{
  int i;
  mp2_t x;

  for (x = 0, i = 0; i < ED25519_LEN; i++)
    {
      x += (mp2_t)a[i] + (mp2_t)a[i + ED25519_LEN] * 38;
      target[i] = x;
      x >>= MP_T_BITS;
    }
  x *= 38;
  if ((target[ED25519_LEN - 1] & (1 << (MP_T_BITS - 1))) != 0)
    {
      x += 19;
      target[ED25519_LEN - 1] -= 1 << (MP_T_BITS - 1);
    }
  for (i = 0; x && i < ED25519_LEN; i++)
    {
      x += (mp2_t)target[i];
      target[i] = x;
      x >>= MP_T_BITS;
    }
  if (target[ED25519_LEN - 1] > ed25519_q[ED25519_LEN - 1] ||
      (target[ED25519_LEN - 1] == ed25519_q[ED25519_LEN - 1] && !mpisless(ED25519_LEN - 1, target, ed25519_q)))
    mpsubmod(ED25519_LEN, target, ed25519_q);
}

static void
ed25519_mul(mp_t *target, const mp_t *m1, const mp_t *m2)
{
  mp_t tmp[ED25519_LEN * 2];
  int i, j;
  mp2_t x;

  mpzero(ED25519_LEN * 2, tmp);
  for (i = 0; i < ED25519_LEN; i++)
    {
      for (x = 0, j = 0; j < ED25519_LEN; j++)
	{
	  x += (mp2_t)tmp[i + j] + (mp2_t)m1[i] * m2[j];
	  tmp[i + j] = x;
	  x >>= MP_T_BITS;
	}
      tmp[i + j] = x;
    }
  ed25519_reduce512(target, tmp);
}

static inline void
ed25519_sqr(mp_t *target, const mp_t *m)
{
  ed25519_mul(target, m, m);
}

/* target = a ^ (2^252 - 4), a11 = a ^ 11 */
static void
ed25519_pow_252_4(mp_t *target, const mp_t *a, mp_t *a_11)
{
  static const int todo[16] = { 0, 5, 1, 10, 2, 20, 3, 10, 2, 50, 5, 100, 6, 50, 5, 2 };
  mp_t data[9][ED25519_LEN];
  int i, j;

  mpcpy(ED25519_LEN, target, a);
  ed25519_sqr(target, target);
  mpcpy(ED25519_LEN, a_11, target);
  ed25519_sqr(target, target);
  ed25519_sqr(target, target);
  ed25519_mul(data[0], target, a);		/* data[0] = 9 */
  ed25519_mul(a_11, data[0], a_11);		/* a_11 = 11 */
  ed25519_mul(target, a_11, a_11);		/* target = 22 */
  for (i = 0; i < 8; i++)
    {
      ed25519_mul(target, target, data[todo[i * 2]]);
      mpcpy(ED25519_LEN, data[i + 1], target);
      for (j = todo[i * 2 + 1]; j-- > 0;)
        ed25519_sqr(target, target);
    }
}

/* target = a ^ (2^252 - 3) */
static void
ed25519_pow_252_3(mp_t *target, const mp_t *a)
{
  mp_t t11[ED25519_LEN];
  ed25519_pow_252_4(target, a, t11);
  ed25519_mul(target, target, a);
}

/* target = a ^ -1 = a ^ (2^255 - 21) */
static void
ed25519_inv(mp_t *target, const mp_t *a)
{
  mp_t t[ED25519_LEN], t11[ED25519_LEN];
  ed25519_pow_252_4(t, a, t11);
  ed25519_sqr(t, t);
  ed25519_sqr(t, t);
  ed25519_sqr(t, t);		/* 2^255 - 32 */
  ed25519_mul(target, t, t11);
}

/* target = 512 bit input modulo ed25519_l */
/* algorithm: barrett reduction */
static void
ed25519_reduce512_l(mp_t *target, const mp_t *a)
{
  mp_t tmp[2 + ED25519_LEN + 1];
  mp2_t x;
  int i, j;
  mpzero(2 + ED25519_LEN + 1, tmp);
  for (i = 0; i < ED25519_LEN + 1; i++)
    {
      mp_t m = i == ED25519_LEN ? 15 : ed25519_invl[i];
      for (x = 0, j = -i; j < 2; j++)
        {
          x += (mp2_t)tmp[i + j] + (mp2_t)a[j + (ED25519_LEN * 2 - 2)] * m;
          tmp[i + j] = x;
          x >>= MP_T_BITS;
        }
      tmp[i + j] = x;
    }
  mpcpy(ED25519_LEN, target, a);
  for (i = 0; i < ED25519_LEN; i++)
    for (x = 0, j = 0; j < ED25519_LEN - i; j++)
      {
        mp2_t t = x + (mp2_t)tmp[i + 2] * ed25519_l[j];
        x = t > target[i + j] ? ((t - target[i + j] - 1) >> MP_T_BITS) + 1: 0;
        target[i + j] -= t;
      }
  while (target[ED25519_LEN - 1] > ed25519_l[ED25519_LEN - 1] ||
      (target[ED25519_LEN - 1] == ed25519_l[ED25519_LEN - 1] && !mpisless(ED25519_LEN - 1, target, ed25519_l)))
    mpsubmod(ED25519_LEN, target, ed25519_l);
}

/* recover x coordinate from y and sign */
static int
ed25519_recover_x(mp_t *x, const mp_t *y, int sign)
{
  mp_t num[ED25519_LEN], den[ED25519_LEN];
  mp_t tmp1[ED25519_LEN], tmp2[ED25519_LEN];

  if (!mpisless(ED25519_LEN, y, ed25519_q))
    return 0;
  /* calculate num=y^2-1 and den=dy^2+1 */
  ed25519_sqr(num, y);
  ed25519_mul(den, num, ed25519_d);
  ed25519_sub(num, num, ed25519_one);
  ed25519_add(den, den, ed25519_one);

  /* calculate x = num*den^3 * (num*den^7)^((q-5)/8) */
  ed25519_sqr(tmp1, den);		/* tmp1 = den^2 */
  ed25519_mul(tmp2, tmp1, den);		/* tmp2 = den^3 */
  ed25519_sqr(tmp1, tmp2);		/* tmp1 = den^6 */
  ed25519_mul(x, tmp1, den);		/* x = den^7 */
  ed25519_mul(tmp1, x, num);		/* tmp1 = num * den^7 */
  ed25519_pow_252_3(x, tmp1);		/* x = tmp1^((q-5)/8) */
  ed25519_mul(tmp1, x, tmp2);		/* tmp1 = x * den^3 */
  ed25519_mul(x, tmp1, num);		/* x = tmp1 * num */

  /* check if den*x^2 == num */
  ed25519_sqr(tmp2, x);
  ed25519_mul(tmp1, tmp2, den);
  if (!mpisequal(ED25519_LEN, tmp1, num))
    {
      ed25519_mul(x, x, ed25519_sqrtm1);	/* x = x * sqrt(-1) */
      ed25519_sqr(tmp2, x);
      ed25519_mul(tmp1, tmp2, den);
      if (!mpisequal(ED25519_LEN, tmp1, num))
	return 0;
    }
  if (mpiszero(ED25519_LEN, x))
    return 0;				/* (0,1) is bad */
  if ((x[0] & 1) != sign)
    ed25519_sub(x, ed25519_q, x);
  return 1;
}

/* see https://hyperelliptic.org/EFD/g1p/auto-twisted-projective.html */
/* M=7 add=6 */
static void
ed25519_ptdbl(mp_t *p_x, mp_t *p_y, mp_t *p_z)
{
  mp_t B[ED25519_LEN], C[ED25519_LEN], D[ED25519_LEN];
  mp_t F[ED25519_LEN], H[ED25519_LEN], J[ED25519_LEN];

  ed25519_add(C, p_x, p_y);
  ed25519_sqr(B, C);
  ed25519_sqr(C, p_x);
  ed25519_sqr(D, p_y);
  ed25519_sub(F, C, D);
  ed25519_sqr(H, p_z);
  ed25519_add(H, H, H);
  ed25519_add(J, F, H);
  ed25519_add(H, C, D);
  ed25519_mul(p_y, H, F);
  ed25519_mul(p_z, J, F);
  ed25519_sub(H, H, B);
  ed25519_mul(p_x, J, H);
}

/* M=12 add=7 */
static void
ed25519_ptadd(mp_t *p_x, mp_t *p_y, mp_t *p_z, const mp_t *q_x, const mp_t *q_y, const mp_t *q_z)
{
  mp_t A[ED25519_LEN], B[ED25519_LEN], C[ED25519_LEN];
  mp_t D[ED25519_LEN], E[ED25519_LEN], F[ED25519_LEN];
  mp_t G[ED25519_LEN], H[ED25519_LEN], J[ED25519_LEN];

  ed25519_mul(A, p_z, q_z);
  ed25519_sqr(B, A);
  ed25519_mul(C, p_x, q_x);
  ed25519_mul(D, p_y, q_y);
  ed25519_mul(F, ed25519_d, C);
  ed25519_mul(E, F, D);
  ed25519_sub(F, B, E);
  ed25519_add(G, B, E);
  ed25519_add(H, p_x, p_y);
  ed25519_add(J, q_x, q_y);
  ed25519_mul(p_x, H, J);
  ed25519_sub(p_x, p_x, C);
  ed25519_sub(p_x, p_x, D);
  ed25519_mul(H, p_x, F);
  ed25519_mul(p_x, H, A);
  ed25519_add(H, D, C);
  ed25519_mul(J, H, G);
  ed25519_mul(p_y, J, A);
  ed25519_mul(p_z, F, G);
}

static inline void
ed25519_ptcpy(mp_t *p_x, mp_t *p_y, mp_t *p_z, const mp_t *q_x, const mp_t *q_y, const mp_t *q_z)
{
  mpcpy(ED25519_LEN, p_x, q_x);
  mpcpy(ED25519_LEN, p_y, q_y);
  mpcpy(ED25519_LEN, p_z, q_z);
}

/* scalar multiplication and add: r = s1*p1 + s2*p2 */
/* needs about 13 + (256 - 32) / 2 = 125 point additions */
static int
ed25519_scmult2(mp_t *r_x, mp_t *r_y, const mp_t *s1, const mp_t *p1_x, const mp_t * p1_y, const mp_t *s2, const mp_t *p2_x, const mp_t * p2_y)
{
  mp_t p_x[ED25519_LEN], p_y[ED25519_LEN], p_z[ED25519_LEN];
  mp_t pi_z[ED25519_LEN];
  mp_t tabx[16][ED25519_LEN], taby[16][ED25519_LEN], tabz[16][ED25519_LEN];
  int i, x, dodouble = 0;

  mpzero(ED25519_LEN, p_x);
  mpzero(ED25519_LEN, p_y);
  mpzero(ED25519_LEN, p_z);
  p_y[0] = p_z[0] = 1;

  /* setup table: tab[i * 4 + j] = i * p1 + j * p2 */
  ed25519_ptcpy(tabx[0], taby[0], tabz[0], p_x, p_y, p_z);
  for (i = 4; i < 16; i += 4)
    ed25519_ptcpy(tabx[i], taby[i], tabz[i], p1_x, p1_y, ed25519_one);
  ed25519_ptdbl(tabx[8], taby[8], tabz[8]);
  ed25519_ptadd(tabx[12], taby[12], tabz[12], tabx[8], taby[8], tabz[8]);
  ed25519_ptcpy(tabx[1], taby[1], tabz[1], p2_x, p2_y, ed25519_one);
  for (i = 2; i < 16; i++)
    {
      if ((i & 3) == 0)
	continue;
      ed25519_ptcpy(tabx[i], taby[i], tabz[i], tabx[i - 1], taby[i - 1], tabz[i - 1]);
      ed25519_ptadd(tabx[i], taby[i], tabz[i], p2_x, p2_y, ed25519_one);
    }
  /* now do the scalar multiplication */
  for (i = 255; i >= 0; i--)
    {
      if (dodouble)
        ed25519_ptdbl(p_x, p_y, p_z);
      x  = s1[i / MP_T_BITS] & (1 << (i % MP_T_BITS)) ? 4 : 0;
      x |= s2[i / MP_T_BITS] & (1 << (i % MP_T_BITS)) ? 1 : 0;
      if (!x)
	continue;
      if (i > 0)
	{
	  i--;
	  if (dodouble)
	    ed25519_ptdbl(p_x, p_y, p_z);
	  x <<= 1;
	  x |= s1[i / MP_T_BITS] & (1 << (i % MP_T_BITS)) ? 4 : 0;
	  x |= s2[i / MP_T_BITS] & (1 << (i % MP_T_BITS)) ? 1 : 0;
	}
      ed25519_ptadd(p_x, p_y, p_z, tabx[x], taby[x], tabz[x]);
      dodouble = 1;
    }
  /* convert back to affine coordinates */
  ed25519_inv(pi_z, p_z);
  ed25519_mul(r_x, p_x, pi_z);
  ed25519_mul(r_y, p_y, pi_z);
  return mpiszero(ED25519_LEN, p_z) ? 0 : 1;
}

static void
ed25519_setfromle(int len, mp_t *out, const unsigned char *buf, int bufl, int highmask)
{
  int i;
  mpzero(len, out);
  for (i = 0; i < bufl - 1; i++)
    out[i / MP_T_BYTES] |= (mp_t)(buf[i]) << (8 * (i % MP_T_BYTES));
  out[i / MP_T_BYTES] |= (mp_t)(buf[i] & highmask) << (8 * (i % MP_T_BYTES));
}

int
ed25519_vrfy(const unsigned char *pub, const unsigned char *sig, const unsigned char *datahash)
{
  unsigned char rbuf[32];
  int i;
  mp_t pub_x[ED25519_LEN], pub_y[ED25519_LEN];
  mp_t h[ED25519_LEN], s[ED25519_LEN], h2[ED25519_LEN * 2];
  mp_t r_x[ED25519_LEN], r_y[ED25519_LEN];

  ed25519_setfromle(ED25519_LEN, s, sig + 32, 32, 0xff);
  if (!mpisless(ED25519_LEN, s, ed25519_l))
    return 0;		/* bad s */
  /* uncompress pubkey, we invert the sign to get -pub */
  ed25519_setfromle(ED25519_LEN, pub_y, pub, 32, 0x7f);
  if (!ed25519_recover_x(pub_x, pub_y, pub[31] & 0x80 ? 0 : 1))
    return 0;		/* bad pubkey */
  /* calculate h = H(sig[0..31]|pub|data) mod l */
  ed25519_setfromle(ED25519_LEN * 2, h2, datahash, 64, 0xff);
  ed25519_reduce512_l(h, h2);
  /* calculate r = s * G - h * pub */
  if (!ed25519_scmult2(r_x, r_y, s, ed25519_gx, ed25519_gy, h, pub_x, pub_y))
    return 0;
  /* compress r into rbuf and verify that it matches sig */
  for (i = 0; i < 32; i++)
    rbuf[i] = r_y[i / MP_T_BYTES] >> (8 * (i % MP_T_BYTES));
  if ((r_x[0] & 1) != 0)
    rbuf[31] |= 0x80;
  return memcmp(sig, rbuf, 32) == 0 ? 1 : 0;
}

