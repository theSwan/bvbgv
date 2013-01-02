#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>
#include <string.h>
#include <gmp.h>
#include "flint/fmpz_vec.h"
#include "flint/fmpz_poly.h"
#include "flint/fmpz_poly_mat.h"

typedef struct sk_node_t {
	fmpz_poly_mat_t sk;
	struct sk_node_t *next;
}sk_node_t;

typedef struct pk_node_t {
	fmpz_poly_mat_t a;
	fmpz_poly_mat_t b;
	struct pk_node_t *next;
}pk_node_t;

typedef struct param_node_t {
	fmpz_t q;
	long n;
	long bign;
	param_node_t *next;
}param_node_t;

const double pi = 3.1415926;
static long secparam, d;
/* denote d in fx */
static double dvn;
/* standard deviation of Guassian distribution*/
static fmpz_t bound;
static fmpz_poly_t fx;
/* for R = Z[x]/(x^d + 1); fx = x^d + 1 */
sk_node_t *skhead;
pk_node_t *pkhead;


void bgv_set_d(long td)
{
	d = td;
}

long bgv_get_d()
{
	return d;
}

void bgv_set_secparam(long sp)
{
	secparam = sp;
}

long bgv_get_secparam()
{
	return secparam;
}

void bgv_set_dvn(double tdvn)
{
	dvn = tdvn;
}

double bgv_get_dvn()
{
	return dvn;
}

void bgv_set_bound(int vb)
{
	fmpz_set_ui(bound, vb);
}

void bv_sym_vars_init()
{
	fmpz_init(bound);
	fmpz_init(t);
	fmpz_poly_init(fx);
}

void bv_sym_vars_clear()
{
	fmpz_clear(bound);
	fmpz_clear(t);
	fmpz_poly_clear(fx);
}

param_node_t *param_node_init(param_node_t *pnt)
{
	pnt = (param_node_t *)malloc(sizeof(param_node_t));
	pnt->next = NULL;
	pnt->n = pnt->bign = 0;
	fmpz_init(pnt->q);
	return pnt;
}

fmpz *samplez(fmpz *vec)
{
	long ele = bgv_get_d();
	if ( ele == 0 )
		return;
	double tdvn = bv_sym_get_dvn();
	long a = (long)ceil(-10*tdvn);
	long b = (long)floor(+10*tdvn);
	long x, i;
	double p;
	int len = sizeof(unsigned long int);
	mpz_t randseed;
	mpz_init(randseed);
	hcrypt_random(randseed, len);
	unsigned long int useed = mpz_get_ui(randseed);
	srand(useed);
	for( i = 0 ; i < ele ; i++) {
		do {
			x = rand()%(b - a) + a;
			p = exp(-pi*x / ( tdvn * tdvn));
		} while ( !( p > 0 && p <= 1) );

		vec[i] = x;
	}
	mpz_clear(randseed);
	return vec;
}

void guassian_poly(fmpz *c, fmpz_poly_t poly)
{
	fmpz *tmp = samplez(c);
	long k, ele = bgv_get_d();
	for( k = 0 ; k < ele ; k++ ) {
		fmpz_poly_set_coeff_si(poly, k, tmp[k]);
	}
}

void unif_poly(fmpz_poly_t poly, fmpz_t space)
{
	int i;
	int spacebit = fmpz_sizeinbase(space, 2);
	int len = sizeof(unsigned long int);
	fmpz_t randseed;
	fmpz_init(randseed);
	hcrypt_random(randseed, len);
	unsigned long int useed = fmpz_get_ui(randseed);
	mpz_t rndnum;
	fmpz_t rndfmpz;
	gmp_randstate_t gmpstate;

	mpz_init(rndnum);
	fmpz_init(rndfmpz);
	gmp_randinit_default(gmpstate);
	gmp_randseed_ui(gmpstate, useed);

	long ele = bgv_get_d();
	for( i = 0 ; i < ele ; i++ ) {
		mpz_urandomb(rndnum, gmpstate, spacebit);
		fmpz_set_mpz(rndfmpz, rndnum);
		fmpz_poly_set_coeff_fmpz(poly, i, rndfmpz);
	}
	fmpz_clear(randseed);
	fmpz_clear(rndfmpz);
	gmp_randclear(gmpstate);
	mpz_clear(rndnum);
}

void hcrypt_random(fmpz_t r, int len) {
	mpz_t tmp;
	FILE *fp;
	int flag = 0;
	mpz_init(tmp);
	fp = fopen("/dev/urandom", "rb");
	if (fp) {
		int bytecount, leftover;
		unsigned char *bytes;
		bytecount = (len + 7) / 8;
		leftover = len % 8;
		bytes = (unsigned char *) malloc(bytecount);

		if (fread(bytes, 1, bytecount, fp)) {
			if (leftover) {
				*bytes = *bytes % (1 << leftover);
			}
			mpz_import(tmp, bytecount, 1, 1, 0, 0, bytes);
			flag = 1;
		}
		fclose(fp);
		free(bytes);
	}
	if(!fp || !flag) {
		gmp_randstate_t gmpRandState;
		gmp_randinit_default(gmpRandState);
		gmp_randseed_ui(gmpRandState, (unsigned long)time(0)+(chrnd++));
		while( 1 ) {
			mpz_urandomb(tmp, gmpRandState, len);
			if( mpz_sizeinbase(tmp, 2) == len)
				break;
		}
		gmp_randclear(gmpRandState);
	}
	fmpz_set_mpz(r, tmp);
	mpz_clear(tmp);
}

param_node_t *e_setup(int miu, int lamda, int b, param_node_t *param)
{
	hcrypt_random(param->q, miu);
	fmpz_t tmp;
	fmpz_init(tmp);
	fmpz_fdiv_q(tmp, param->q, bound);
	long prod;
	prod = lamda * fmpz_flog_ui(tmp, 2);

	if(b == 0) {
		d = 1;
		param->n = prod;
	}  /* LWE */
	else {
		param->n = 1;
		d = prod;
	} /* RLWE */

	param->bign = ceil((2 * param->n + 1) * fmpz_flog_ui(param->q,2));
	return param;
}

sk_node_t *e_skeygen(param_node_t *param)
{
        sk_node_t *sknode;
        sknode = (sk_node_t *)malloc(sizeof(sk_node_t));
        fmpz_poly_mat_init(sknode->sk, 1 + param->n , 1);
        sknode->next = NULL;
        fmpz *coeffs = _fmpz_vec_init(d);
        fmpz_poly_t poly;
        fmpz_poly_init(poly);
        fmpz_poly_set_coeff_si(poly, 0, 1);
        fmpz_poly_set(fmpz_poly_mat_entry(sknode->sk, 0, 0), poly);
        long i;
        for( i = 1 ; i <= param->n ; i++ ) {
                guassian_poly(coeffs, fmpz_poly_mat_entry(sknode->sk, i, 0));
        }
        _fmpz_vec_clear(coeffs, d);
        fmpz_poly_clear(poly);
        return sknode;
}

fmpz_poly_mat_t e_pkeygen(param_node_t *param, sk_node_t *sknode)
{
        fmpz_poly_mat_t pk, ppk, ee, bb, ss, tmp, tmp1;
        fmpz_poly_mat_init(ppk, param->bign, param->n);
        fmpz_poly_mat_init(pk, param->bign, 1 + (param->n));
        fmpz_poly_mat_init(ee, param->bign, 1);
        fmpz_poly_mat_init(bb, param->bign, 1);
        fmpz_poly_mat_init(ss, param->n, 1);
        fmpz *coeffs = _fmpz_vec_init(d);

        long i, j;
        for( i = 0 ; i < param->n ; i++ ) {
                fmpz_poly_set(fmpz_poly_mat_entry(ss, i, 0), fmpz_poly_mat_entry(sknode->sk, i+1, 0 ));
        }
        for( i = 0 ; i < param->bign ; i++ ) {
                guassian_poly(coeffs, fmpz_poly_mat_entry(ee, i, 0));
        }
        for( i = 0 ; i < param->bign ; i++ ) {
                for( j = 0; j < param->n; j++ ){
                        unif_poly(fmpz_poly_mat_entry(ppk, i, j), param->q);
                }
        }
        fmpz_poly_mat_init(tmp, param->bign, 1);
        fmpz_poly_mat_init(tmp1, param->bign, 1);
        fmpz_poly_mat_mul(tmp, ppk, ss);
        fmpz_t c;
        fmpz_init_set_ui(c, 2);
        fmpz_poly_mat_scalar_mul_fmpz(tmp1, ee, c)
        fmpz_poly_mat_add(bb, tmp, tmp1);
        for( i = 0 ; i < param->bign ; i++ ) {
                fmpz_poly_set(fmpz_poly_mat_entry(pk, i, 0), fmpz_poly_mat_entry(bb, i, 0));
        }
        for( i = 0 ; i < param->bign ; i++ ) {
                for( j = 1; j <= param->n; j++ ){
                        fmpz_poly_neg(fmpz_poly_mat_entry(pk, i, j), fmpz_poly_mat_entry(ppk, i, j-1));
                }
        }
        for( i = 0 ; i < param->bign ; i++) {
                for( j = 0; j < param->n + 1 ; j++) {
                        fmpz_poly_rem_basecase(fmpz_poly_mat_entry(pk, i, j), fmpz_poly_mat_entry(pk, i, j), fx);
                        fmpz_poly_scalar_smod_fmpz(fmpz_poly_mat_entry(pk, i, j), fmpz_poly_mat_entry(pk, i, j), q);
                }
        }
        fmpz_clear(c);
        _fmpz_vec_clear(coeffs, d);
        fmpz_poly_mat_clear(tmp);
        fmpz_poly_mat_clear(tmp1);
        fmpz_poly_mat_clear(ee);
        fmpz_poly_mat_clear(ss);
        fmpz_poly_mat_clear(bb);
        fmpz_poly_mat_clear(ppk);
        return pk;
}

fmpz_poly_mat_t e_encrypt(param_node_t *param, fmpz_poly_mat_t pk, fmpz_poly_t ms)
{
        long i, j;
        fmpz_poly_mat_t mm, rr, ct, tmp, tmp1;
        fmpz_poly_mat_init(mm, 1 + param->n, 1);
        fmpz_poly_mat_init(rr, param->bign, 1);
        fmpz_poly_mat_init(ct, 1 + param->n, 1);
        fmpz_poly_mat_init(tmp, 1 + param->n, 1);
        fmpz_poly_mat_init(tmp1, 1 + (param->n), param->bign);
        for( i = 0 ; i < 1 + param->n ; i++ ) {
                for( j = 0; j < param->bign; j++ ){
                        fmpz_poly_set(fmpz_poly_mat_entry(tmp1, i, j), fmpz_poly_mat_entry(pk, j, i));
                }
        }
        fmpz_poly_mat_zero(mm);
        fmpz_poly_set(fmpz_poly_mat_entry(mm, 0, 0), ms);

        for( i = 0; i < param->bign; i++ ) {
                        unif_poly(fmpz_poly_mat_entry(rr, i, 0), t);
        }
        fmpz_poly_mat_mul(tmp, tmp1, rr);
        fmpz_poly_mat_add(ct, mm, ct);

        for( i = 0; i < param->n + 1 ; i++) {
                fmpz_poly_rem_basecase(fmpz_poly_mat_entry(ct, i, 0), fmpz_poly_mat_entry(ct, i, 0), fx);
                fmpz_poly_scalar_smod_fmpz(fmpz_poly_mat_entry(ct, i, 0), fmpz_poly_mat_entry(ct, i, 0), q);
        }

        fmpz_poly_mat_clear(tmp);
        fmpz_poly_mat_clear(tmp1);
        fmpz_poly_mat_clear(mm);
        fmpz_poly_mat_clear(rr);
        return ct;
}

fmpz_poly_t e_decrypt(param_node_t *param, fmpz_poly_mat_t sk, fmpz_poly_mat_t ct)
{
        fmpz_poly_t ms, tmp;
        fmpz_poly_init(ms);
        fmpz_poly_init(tmp);
        fmpz_poly_zero(ms);

        long i;
        for( i = 0 ; i < param->n + 1 ; i++) {
                fmpz_poly_mul(tmp, fmpz_poly_mat_entry(ct, i, 0), fmpz_poly_mat_entry(sk, i, 0));
                fmpz_poly_add(ms, ms, tmp);
        }
        fmpz_poly_rem_basecase(ms, ms, fx);
        fmpz_poly_scalar_smod_fmpz(ms, ms, q);
        fmpz_poly_scalar_smod_fmpz(ms, ms, t);

        fmpz_poly_clear(tmp);
        return ms;
}
fmpz_poly_mat_t bitdecomp(fmpz_poly_mat_t x, fmpz_t qq)
{

}




