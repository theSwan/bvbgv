#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>
#include <string.h>
#include <gmp.h>
#include "flint/fmpz_vec.h"
#include "flint/fmpz_poly.h"

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
static fmpz_t t, bound;
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

void bgv_set_t(int vt)
{
	fmpz_set_ui(t, vt);
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

void unif_poly(fmpz_poly_t poly)
{
	int i;
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
		mpz_urandomb(rndnum, gmpstate, qbit);
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
        fmpz_poly_mat_init(sknode->sk, 1, 1 + param->n);
        sknode->next = NULL;
        fmpz *coeffs = _fmpz_vec_init(d);
        fmpz_poly_t poly;
        fmpz_poly_init(poly);
        fmpz_poly_set_coeff_si(poly, 0, 1);
        fmpz_poly_set(fmpz_poly_mat_entry(sknode->sk, 0, 0), poly);
        long i;
        for( i = 0 ; i < param->n ; i++ ) {
                guassian_poly(coeffs, fmpz_poly_mat_entry(sknode->sk, 0, i));
        }
        return sknode;
}






