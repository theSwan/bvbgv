/*
  *implementation : Can Homomorphic Encryption be Practical?
  *author : Shiyin Wang
  */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>
#include <string.h>
#include <gmp.h>
#include "flint/fmpz_vec.h"
#include "flint/fmpz_poly.h"
#include "flint/fmpz.h"
#include "flint/fmpz_mat.h"

typedef struct hk_node_t{
	fmpz_poly_t a,b;
	struct hk_node_t *next;
} hk_node_t;

hk_node_t *head;
const double pi = 3.1415926;
static long n;
static double dvn; /* standard deviation of Guassian distribution*/
static fmpz_t q,t;
static fmpz_poly_t fx;
static fmpz *ctr;
static int qbit;
static int multimes;  /* mul times */
static long chrnd = 0;
void bv_swhe_set_multimes(int mt)
{
	multimes = mt;
}

int bv_swhe_get_multimes()
{
	return multimes;
}

void bv_swhe_set_t(int vt)
{
	fmpz_set_ui(t, vt);
}

void bv_swhe_set_lgq(int vq)
{
	qbit = vq;
	fmpz_t temp;
	fmpz_init(temp);
	fmpz_set_ui(temp, 1);
	fmpz_mul_2exp(q, temp, vq);
	fmpz_clear(temp);
}

void bv_swhe_vars_init()
{
	fmpz_init(q);
	fmpz_init(t);
	fmpz_poly_init(fx);
}

void bv_swhe_vars_clear()
{
	hk_node_t *r = head->next,*s = head;
	while ( r != NULL ) {
		free(s);
		s = r;
		r = s->next;
	}
	free(s);
	fmpz_clear(q);
	fmpz_clear(t);
	fmpz_poly_clear(fx);
	_fmpz_vec_clear(ctr, n);
}

void bv_swhe_set_n(long vn)
{
	n = vn;
	fmpz_poly_set_coeff_ui(fx, vn, 1);
	fmpz_poly_set_coeff_ui(fx, 0, 1);
	ctr = _fmpz_vec_init(vn);
}

long bv_swhe_get_n()
{
	return n;
}

void bv_swhe_set_dvn(double ndvn)
{
	dvn = ndvn;
}

double bv_swhe_get_dvn()
{
	return dvn;
}

void hcrypt_random(mpz_t r, int len) {
	FILE *fp;
	int flag = 0;
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
			mpz_import(r, bytecount, 1, 1, 0, 0, bytes);
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
			mpz_urandomb(r, gmpRandState, len);
			if( mpz_sizeinbase(r, 2) == len)
				break;
		}
		gmp_randclear(gmpRandState);
	}
}

fmpz *bv_swhe_samplez(fmpz *vec)
{
	long n = bv_swhe_get_n();
	if ( n == 0 )
		return;
	double tdvn = bv_swhe_get_dvn();
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
	for( i = 0 ; i < n ; i++) {
		do {
			x = rand()%(b - a) + a;
			p = exp(-pi*x / ( tdvn * tdvn));
		} while ( !( p > 0 && p <= 1) );

		vec[i] = x;
	}
	mpz_clear(randseed);
	return vec;
}

void bv_swhe_guassian_poly(fmpz *c, fmpz_poly_t poly)
{
	fmpz *tmp = bv_swhe_samplez(c);
	long k, n = bv_swhe_get_n();
	for( k = 0 ; k < n ; k++ ) {
		fmpz_poly_set_coeff_si(poly, k, tmp[k]);
	}
}

void bv_swhe_unif_poly(fmpz_poly_t poly)
{
	int i;
	int len = sizeof(unsigned long int);
	mpz_t randseed;
	mpz_init(randseed);
	hcrypt_random(randseed, len);
	unsigned long int useed = mpz_get_ui(randseed);
	mpz_t rndnum,rndbd;
	fmpz_t rndfmpz;
	gmp_randstate_t gmpstate;

	mpz_init(rndnum);
	mpz_init(rndbd);
	fmpz_get_mpz(rndbd, q);
	fmpz_init(rndfmpz);
	gmp_randinit_default(gmpstate);
	gmp_randseed_ui(gmpstate, useed);

	long n = bv_swhe_get_n();
	for( i = 0 ; i < n ; i++ ) {
		mpz_urandomm(rndnum, gmpstate, rndbd);
		fmpz_set_mpz(rndfmpz, rndnum);
		fmpz_poly_set_coeff_fmpz(poly, i, rndfmpz);
	}
	mpz_clear(randseed);
	fmpz_clear(rndfmpz);
	gmp_randclear(gmpstate);
	mpz_clear(rndnum);
	mpz_clear(rndbd);
}



void bv_swhe_keygen(fmpz_poly_t a0, fmpz_poly_t a1, fmpz_poly_t sk)
{
	long n = bv_swhe_get_n();

	bv_swhe_guassian_poly(ctr, sk);
	fmpz_poly_t e;
	fmpz_poly_init(e);
	bv_swhe_guassian_poly(ctr, e);

	int i, j;

	bv_swhe_unif_poly(a1);

	fmpz_poly_t tmp, tmp1, tmp2, sk2;
	fmpz_poly_init(tmp);
	fmpz_poly_init(tmp1);
	fmpz_poly_init(tmp2);
	fmpz_poly_init(sk2);
	fmpz_poly_mul(sk2, sk, sk);

	fmpz_poly_mul(tmp, a1, sk);
	fmpz_poly_scalar_mul_fmpz(tmp1, e, t);
	fmpz_poly_add(tmp2, tmp1, tmp);
	fmpz_poly_scalar_smod_fmpz(tmp2, tmp2, q);
	fmpz_poly_rem_basecase(tmp2, tmp2, fx);
	fmpz_poly_neg(a0, tmp2);

	hk_node_t *s, *r;
	fmpz_t ti;
	fmpz_init(ti);
	fmpz_set_ui(ti, 1);
	int len = ceil(log(fmpz_get_d(q)) / log(fmpz_get_d(t))) - 1;
	head = (hk_node_t *)malloc(sizeof(hk_node_t));
	head->next = NULL;
	r = head;
	for( i = 0 ; i <= len ; i++ ) {
		s = (hk_node_t *)malloc(sizeof(hk_node_t));
		fmpz_poly_init(s->a);
		bv_swhe_unif_poly(s->a);
		bv_swhe_guassian_poly(ctr, e);
		fmpz_poly_init(s->b);
		fmpz_poly_mul(tmp, s->a, sk);
		fmpz_poly_scalar_addmul_fmpz(tmp, e, t);
		fmpz_poly_neg(s->b, tmp);
		fmpz_poly_scalar_addmul_fmpz(s->b, sk2, ti);
		fmpz_poly_scalar_smod_fmpz(s->b, s->b, q);
		fmpz_poly_rem_basecase(s->b, s->b, fx);

		fmpz_mul(ti, ti, t);
		r->next = s;
		r = s;
	}

	r->next = NULL;

	fmpz_poly_clear(sk2);
	fmpz_poly_clear(e);
	fmpz_poly_clear(tmp);
	fmpz_poly_clear(tmp1);
	fmpz_poly_clear(tmp2);

}

void bv_swhe_encrypt(fmpz_poly_t m, fmpz_poly_t c0, fmpz_poly_t c1, fmpz_poly_t a0, fmpz_poly_t a1)
{
	fmpz_poly_t u, f, g, tmp, tmp1;
	long n = bv_swhe_get_n();
	fmpz_poly_init(u);
	fmpz_poly_init(f);
	fmpz_poly_init(g);
	bv_swhe_guassian_poly(ctr, u);
	bv_swhe_guassian_poly(ctr, f);
	bv_swhe_guassian_poly(ctr, g);

	fmpz_poly_init(tmp);
	fmpz_poly_init(tmp1);
	fmpz_poly_mul(tmp, a0, u);
	fmpz_poly_scalar_mul_fmpz(tmp1, g, t);
	fmpz_poly_add(tmp, tmp, tmp1);
	fmpz_poly_add(tmp, tmp, m);
	fmpz_poly_rem_basecase(tmp, tmp, fx);
	fmpz_poly_scalar_smod_fmpz(c0, tmp, q);

	fmpz_poly_mul(tmp, a1, u);
	fmpz_poly_scalar_mul_fmpz(tmp1, f, t);
	fmpz_poly_add(tmp, tmp, tmp1);
	fmpz_poly_rem_basecase(tmp, tmp, fx);
	fmpz_poly_scalar_smod_fmpz(c1, tmp, q);

	fmpz_poly_clear(u);
	fmpz_poly_clear(f);
	fmpz_poly_clear(g);
	fmpz_poly_clear(tmp);
	fmpz_poly_clear(tmp1);
}

void bv_swhe_decrypt(fmpz_poly_t m, fmpz_poly_t c0, fmpz_poly_t c1, fmpz_poly_t sk)
{
	fmpz_poly_t tmp;
	long n = bv_swhe_get_n();
	fmpz_poly_init(tmp);
	fmpz_poly_mul(tmp, c1, sk);
	fmpz_poly_scalar_smod_fmpz(tmp, tmp, q);
	fmpz_poly_rem_basecase(tmp, tmp, fx);
	fmpz_poly_add(tmp, tmp, c0);
	fmpz_poly_scalar_smod_fmpz(tmp, tmp, q);
	fmpz_poly_scalar_mod_fmpz(m, tmp, t);

	fmpz_poly_clear(tmp);
}

void bv_swhe_mul(fmpz_poly_t c10, fmpz_poly_t c11, fmpz_poly_t c20, fmpz_poly_t c21, fmpz_poly_t nc0, fmpz_poly_t nc1)
{
	long n = bv_swhe_get_n();
	unsigned long long lq = fmpz_get_d(q), lt = fmpz_get_d(t);
	fmpz_poly_t tmp0, tmp1, tmp2, tmp;
	fmpz_poly_init(tmp0);
	fmpz_poly_mul(tmp0, c10, c20);
	fmpz_poly_rem_basecase(tmp0, tmp0, fx);
	fmpz_poly_init(tmp1);
	fmpz_poly_init(tmp);
	fmpz_poly_mul(tmp, c10, c21);
	fmpz_poly_mul(tmp1, c20, c11);
	fmpz_poly_add(tmp1, tmp1, tmp);
	fmpz_poly_rem_basecase(tmp1, tmp1, fx);
	fmpz_poly_init(tmp2);
	fmpz_poly_mul(tmp2, c11, c21);
	fmpz_poly_rem_basecase(tmp2, tmp2, fx);
	fmpz_poly_scalar_smod_fmpz(tmp0, tmp0, q);
	fmpz_poly_scalar_smod_fmpz(tmp1, tmp1, q);
	fmpz_poly_scalar_mod_fmpz(tmp2, tmp2, q);

	long len = fmpz_clog(q, t);
	long i, j;
	fmpz_t hold;
	fmpz_init(hold);
	fmpz_mat_t bits;
	fmpz_mat_init(bits, fmpz_poly_length(tmp2), len);
	fmpz_mat_zero(bits);
	for ( i = 0 ; i < fmpz_poly_length(tmp2) ; ++i ) {
		fmpz_poly_get_coeff_fmpz(hold, tmp2, i);
		j = 0;
		while ( !fmpz_is_zero(hold) ) {
			fmpz_mod(fmpz_mat_entry(bits, i, j), hold, t);
			fmpz_tdiv_q(hold, hold, t);
			j++;
		}
	}
	fmpz_poly_t xtmp,multmp;
	fmpz_poly_init(xtmp);
	fmpz_poly_init(multmp);
	hk_node_t *r;
	r = head->next;
	for( i = 0 ; i < len ; i++ ) {
		for( j = 0; j < fmpz_poly_length(tmp2) ; ++j ) {
			fmpz_poly_set_coeff_fmpz(xtmp, j, fmpz_mat_entry(bits, j, i));
		}
		fmpz_poly_mul(multmp, xtmp, r->a);
		fmpz_poly_add(tmp1, tmp1, multmp);
		fmpz_poly_mul(multmp, xtmp, r->b);
		fmpz_poly_add(tmp0, tmp0, multmp);
		r = r->next;
	}

	fmpz_poly_rem_basecase(nc0, tmp0, fx);
	fmpz_poly_rem_basecase(nc1, tmp1, fx);
	fmpz_poly_scalar_smod_fmpz(nc0, nc0, q);
	fmpz_poly_scalar_smod_fmpz(nc1, nc1, q);

	fmpz_poly_clear(tmp);
	fmpz_poly_clear(tmp1);
	fmpz_poly_clear(tmp0);
	fmpz_poly_clear(tmp2);
	fmpz_poly_clear(multmp);
	fmpz_poly_clear(xtmp);
	fmpz_clear(hold);
	fmpz_mat_clear(bits);
}

void bv_swhe_add(fmpz_poly_t c10, fmpz_poly_t c11, fmpz_poly_t c20, fmpz_poly_t c21, fmpz_poly_t nc0, fmpz_poly_t nc1)
{
	fmpz_poly_add(nc0, c10, c20);
	fmpz_poly_add(nc1, c11, c21);
}

/* function for test */
void test_mul(fmpz_poly_t test0,fmpz_poly_t test1,fmpz_poly_t nc0,fmpz_poly_t nc1)
{
	fmpz_poly_t tmp1,tmp2;
	fmpz_poly_init(tmp1);
	fmpz_poly_init(tmp2);
	fmpz_poly_set(tmp1,test0);
	fmpz_poly_set(tmp2,test1);

	int i;
	for(i=2;i<=bv_swhe_get_multimes();i++) {
		bv_swhe_mul(test0,test1,tmp1,tmp2,nc0,nc1);
		fmpz_poly_set(tmp1,nc0);
		fmpz_poly_set(tmp2,nc1);
	}
}

/* test */

int main()
{
	fmpz_poly_t a0,a1,sk,c10,c11,m1,nc0,nc1,m;

	bv_swhe_vars_init();
	bv_swhe_set_n(16);
	bv_swhe_set_dvn(8.0);
	bv_swhe_set_multimes(2);
	bv_swhe_set_t(2);
	bv_swhe_set_lgq(23);

	fmpz_poly_init(a0);
	fmpz_poly_init(a1);
	fmpz_poly_init(sk);
	fmpz_poly_init(m1);
	fmpz_poly_init(c10);
	fmpz_poly_init(c11);

	fmpz_poly_init(m);
	fmpz_poly_init(nc0);
	fmpz_poly_init(nc1);
	fmpz_poly_set_coeff_si(m1,2,1);
	fmpz_poly_set_coeff_si(m1,0,1);


	clock_t start1, finish1, start2, finish2, start3, finish3, start4, finish4, start5, finish5;
	double  dur1,dur2,dur3,dur4,dur5;
	start1=clock();
	bv_swhe_keygen(a0,a1,sk);
	finish1=clock();
	dur1 = (double)(finish1 - start1) / CLOCKS_PER_SEC;
	printf( "keygen: %f seconds\n", dur1);

	start2=clock();
	bv_swhe_encrypt(m1,c10,c11,a0,a1);
	finish2=clock();
	dur2 = (double)(finish2 - start2) / CLOCKS_PER_SEC;
	printf( "encrypt: %f seconds\n", dur2);

	start3=clock();
	bv_swhe_add(c10,c11,c10,c11,nc0,nc1);
	finish3=clock();
	dur3 = (double)(finish3 - start3) / CLOCKS_PER_SEC;
	printf( "add: %f seconds\n", dur3);

	start4=clock();
	bv_swhe_mul(c10,c11,c10,c11,nc0,nc1);
	finish4=clock();
	dur4 = (double)(finish4 - start4) / CLOCKS_PER_SEC;
	printf( "mul: %f seconds\n", dur4);

	start5=clock();
	bv_swhe_decrypt(m,nc0,nc1,sk);
	finish5=clock();
	dur5 = (double)(finish5 - start5) / CLOCKS_PER_SEC;
	printf( "decrypt: %f seconds\n", dur5);
	fmpz_poly_print(m);
	printf("\n");
	fmpz_poly_clear(a0);
	fmpz_poly_clear(a1);
	fmpz_poly_clear(sk);
	fmpz_poly_clear(c10);
	fmpz_poly_clear(c11);
	fmpz_poly_clear(m1);
	fmpz_poly_clear(nc0);
	fmpz_poly_clear(nc1);
	fmpz_poly_clear(m);
	bv_swhe_vars_clear();
	return 0;
}
