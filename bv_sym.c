#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>
#include <string.h>
#include <gmp.h>
#include "flint/fmpz_vec.h"
#include "flint/fmpz_poly.h"

typedef struct sk_node_t{
	fmpz_poly_t sknode;
	struct sk_node_t *next;
} sk_node_t;

typedef struct bv_sym_ct{
	sk_node_t *front, *rear;
	int len;
} bv_sym_ct;

sk_node_t *sk_head;
const double pi = 3.1415926;
static long secparam, n;
static double dvn; /* standard deviation of Guassian distribution*/
static fmpz_t q,t;
static fmpz_poly_t fx;
static fmpz *ctr;
static int qbit;
static int d;   /* denote D*/
static long chrnd = 0;
void bv_sym_set_d(int vd)
{
	d = vd;
}

int bv_sym_get_d()
{
	return d;
}

void bv_sym_set_n(long vn)
{
	n = vn;
	fmpz_poly_set_coeff_ui(fx, vn, 1);
	fmpz_poly_set_coeff_ui(fx, 0, 1);
	ctr = _fmpz_vec_init(vn);
}

long bv_sym_get_n()
{
	return n;
}

bv_sym_ct *bv_sym_ctinit(bv_sym_ct *ct)
{
	ct = (bv_sym_ct *)malloc(sizeof(bv_sym_ct));
	ct->len = 0;
	ct->front = ct->rear = NULL;
	return ct;
}

bv_sym_ct *bv_sym_ctsetlen(bv_sym_ct *ct, int nlen)
{
	ct->len = nlen;
	return ct;
}

int bv_sym_ctgetlen(bv_sym_ct *ct)
{
	return ct->len;
}

bv_sym_ct *bv_sym_ctadd(bv_sym_ct *ct, fmpz_poly_t fp)
{
	sk_node_t *tmp;
	tmp = (sk_node_t *)malloc(sizeof(sk_node_t));
	fmpz_poly_init(tmp->sknode);
	fmpz_poly_set(tmp->sknode, fp);
	tmp->next = NULL;
	if ( ct->rear == NULL) {
		ct->front = ct->rear = tmp;
	}
	else {
		ct->rear->next = tmp;
		ct->rear = tmp;
	}
	ct->len = ct->len + 1;
	return ct;
}

void bv_sym_set_secparam(int vsp)
{
	secparam = vsp;
	double lgs;
	lgs = log((double)vsp)/log(2.0);
	int nlgs;
	nlgs = ((lgs - floor(lgs))>0.5?ceil(lgs):floor(lgs));
	long nn = pow(2, nlgs-1);
	bv_sym_set_n(nn);
}

int bv_sym_get_secparam()
{
	return secparam;
}

void bv_sym_set_t(int vt)
{
	fmpz_set_ui(t, vt);
}

void bv_sym_set_lgq(int vq)
{
	qbit = vq;
	fmpz_t temp;
	fmpz_init(temp);
	fmpz_set_ui(temp, 1);
	fmpz_mul_2exp(q, temp, vq);
	fmpz_clear(temp);
}

void bv_sym_vars_init()
{
	fmpz_init(q);
	fmpz_init(t);
	fmpz_poly_init(fx);
}

void bv_sym_vars_clear()
{
	sk_node_t *r = sk_head->next,*s = sk_head;
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

void bv_sym_set_dvn(double ndvn)
{
	dvn = ndvn;
}

double bv_sym_get_dvn()
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

fmpz *bv_sym_samplez(fmpz *vec)
{
	long n = bv_sym_get_n();
	if ( n == 0 )
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

void bv_sym_guassian_poly(fmpz *c, fmpz_poly_t poly)
{
	fmpz *tmp = bv_sym_samplez(c);
	long k, n = bv_sym_get_n();
	for( k = 0 ; k < n ; k++ ) {
		fmpz_poly_set_coeff_si(poly, k, tmp[k]);
	}
}

void bv_sym_unif_poly(fmpz_poly_t poly)
{
	int i;
	int len = sizeof(unsigned long int);
	mpz_t randseed;
	mpz_init(randseed);
	hcrypt_random(randseed, len);
	unsigned long int useed = mpz_get_ui(randseed);
	mpz_t rndnum;
	fmpz_t rndfmpz;
	gmp_randstate_t gmpstate;

	mpz_init(rndnum);
	fmpz_init(rndfmpz);
	gmp_randinit_default(gmpstate);
	gmp_randseed_ui(gmpstate, useed);

	long n = bv_sym_get_n();
	for( i = 0 ; i < n ; i++ ) {
		mpz_urandomb(rndnum, gmpstate, qbit);
		fmpz_set_mpz(rndfmpz, rndnum);
		fmpz_poly_set_coeff_fmpz(poly, i, rndfmpz);
	}
	mpz_clear(randseed);
	fmpz_clear(rndfmpz);
	gmp_randclear(gmpstate);
	mpz_clear(rndnum);
}

void bv_sym_keygen(fmpz_poly_t sk)
{
	long n = bv_sym_get_n();
	bv_sym_guassian_poly(ctr, sk);

	sk_node_t *s, *r;
	sk_head = (sk_node_t *)malloc(sizeof(sk_node_t));
	sk_head->next = NULL;
	s = sk_head;
	fmpz_poly_init(s->sknode);
	fmpz_poly_set_coeff_si(s->sknode, 0, 1);
	int dn = bv_sym_get_d();
	int i;
	for( i = 1 ; i <= dn ; i++ ) {
		r = (sk_node_t *)malloc(sizeof(sk_node_t));
		fmpz_poly_init(r->sknode);
		fmpz_poly_mul( r->sknode, sk, s->sknode);
		fmpz_poly_rem_basecase(r->sknode, r->sknode, fx);
		s->next = r;
		s = r;
	}
	s->next = NULL;
}

bv_sym_ct *bv_sym_encrypt(fmpz_poly_t sk, fmpz_poly_t m, bv_sym_ct *ct)
{
	long n = bv_sym_get_n();
	fmpz_poly_t e, a, b;
	fmpz_poly_init(e);
	fmpz_poly_init(a);
	fmpz_poly_init(b);
	bv_sym_guassian_poly(ctr, e);
	bv_sym_unif_poly(a);
	fmpz_poly_mul(b, a, sk);
	fmpz_poly_scalar_addmul_fmpz(b, e, t);
	fmpz_poly_t sk1, sk2;
	fmpz_poly_init(sk1);
	fmpz_poly_init(sk2);

	fmpz_poly_add(sk1, b, m);
	fmpz_poly_neg(sk2, a);
	ct = bv_sym_ctadd(ct, sk1);
	ct = bv_sym_ctadd(ct, sk2);

	fmpz_poly_clear(e);
	fmpz_poly_clear(a);
	fmpz_poly_clear(b);
	return ct;
}

bv_sym_ct *bv_sym_add(bv_sym_ct *ct, bv_sym_ct *ct1, bv_sym_ct *ct2)
{
	int len1 = ct1->len, len2 = ct2->len;
	fmpz_poly_t tmp;
	fmpz_poly_init(tmp);
	sk_node_t *list1, *list2;
	list1 = ct1->front;
	list2 = ct2->front;
	if ( len1 < len2 ) {
		while ( list1 != NULL ) {
			fmpz_poly_add(tmp, list1->sknode, list2->sknode);
			fmpz_poly_rem_basecase(tmp, tmp, fx);
			fmpz_poly_scalar_smod_fmpz(tmp, tmp, q);
			ct = bv_sym_ctadd(ct, tmp);
			list1 = list1->next;
			list2 = list2->next;
		}
		while(list2 != NULL) {
			fmpz_poly_set(tmp, list2->sknode);
			ct = bv_sym_ctadd(ct, tmp);
			list2 = list2->next;
		}
	}
	else {
		while ( list2 != NULL ) {
			fmpz_poly_add(tmp, list1->sknode, list2->sknode);
			fmpz_poly_rem_basecase(tmp, tmp, fx);
			fmpz_poly_scalar_smod_fmpz(tmp, tmp, q);
			ct = bv_sym_ctadd(ct, tmp);
			list1 = list1->next;
			list2 = list2->next;
		}
		while(list1 != NULL) {
			fmpz_poly_set(tmp, list1->sknode);
			ct = bv_sym_ctadd(ct, tmp);
			list1 = list1->next;
		}
	}
	fmpz_poly_clear(tmp);
	return ct;
}

bv_sym_ct *bv_sym_mul(bv_sym_ct *ct, bv_sym_ct *ct1, bv_sym_ct *ct2)
{
	int len1 = ct1->len, len2 = ct2->len, len;
	fmpz_poly_t tmp, tmp1;
	fmpz_poly_init(tmp);
	fmpz_poly_init(tmp1);
	sk_node_t *list1, *list2;
	len = len1 + len2 - 1;
	int i, j, k;
	for(k = 0 ; k < len ; k++) {
		fmpz_poly_zero(tmp);
		list1 = ct1->front;

		for(i=0 ; i<len1 ; i++) {
			list2 = ct2->front;
			for(j=0 ; j<len2 ; j++) {
				if ( i + j == k ) {
					fmpz_poly_mul(tmp1, list1->sknode, list2->sknode);
					fmpz_poly_add(tmp, tmp, tmp1);
				}
				list2 = list2->next;
			}
		list1 = list1->next;
		}
		fmpz_poly_rem_basecase(tmp, tmp, fx);
		fmpz_poly_scalar_smod_fmpz(tmp, tmp, q);
		ct = bv_sym_ctadd(ct, tmp);

	}
	fmpz_poly_clear(tmp);
	fmpz_poly_clear(tmp1);
	return ct;
}

void bv_sym_decrypt(fmpz_poly_t m, bv_sym_ct *ct)
{
	sk_node_t *list = ct->front, *r;
	r=sk_head;
	fmpz_poly_t tmp;
	fmpz_poly_init(tmp);
	fmpz_poly_zero(m);
	int i;
	for( i = 0 ; i < ct->len ; i++) {
		fmpz_poly_mul(tmp, list->sknode,  r->sknode);
		fmpz_poly_add(m, m, tmp);
		list = list->next;
		r = r->next;
	}
	fmpz_poly_rem_basecase(m, m, fx);
	fmpz_poly_scalar_smod_fmpz(m, m, q);
	fmpz_poly_scalar_mod_fmpz(m, m, t);
}

int main()
{
	fmpz_poly_t ms, sk, m1;
	bv_sym_ct *ct, *ct1;
	ct = bv_sym_ctinit(ct);
	ct1 = bv_sym_ctinit(ct1);
	fmpz_poly_init(ms);
	fmpz_poly_init(sk);
	fmpz_poly_init(m1);
	fmpz_poly_set_coeff_si(ms, 3, 1);
	fmpz_poly_set_coeff_si(ms, 1, 1);
	bv_sym_vars_init();
	bv_sym_set_secparam(32768);
	bv_sym_set_dvn(8.0);
	bv_sym_set_d(15);
	bv_sym_set_t(3);
	bv_sym_set_lgq(423);

	clock_t start1, finish1, start2, finish2, start3, finish3, start4, finish4, start5, finish5;
	double  dur1,dur2,dur3,dur4,dur5;
	start1=clock();
	bv_sym_keygen(sk);
	finish1=clock();
	dur1 = (double)(finish1 - start1) / CLOCKS_PER_SEC;
	printf( "keygen: %f seconds\n", dur1);

	start2=clock();
	ct = bv_sym_encrypt(sk, ms, ct);
	finish2=clock();
	dur2 = (double)(finish2 - start2) / CLOCKS_PER_SEC;
	printf( "encrypt: %f seconds\n", dur2);

	start3=clock();
	ct1 = bv_sym_add(ct1, ct, ct);
	finish3=clock();
	dur3 = (double)(finish3 - start3) / CLOCKS_PER_SEC;
	printf( "add: %f seconds\n", dur3);

	start4=clock();
	ct1 = bv_sym_mul(ct1, ct, ct);
	finish4=clock();
	dur4 = (double)(finish4 - start4) / CLOCKS_PER_SEC;
	printf( "mul: %f seconds\n", dur4);

	start5=clock();
	bv_sym_decrypt(m1, ct1);
	finish5=clock();
	dur5 = (double)(finish5 - start5) / CLOCKS_PER_SEC;
	printf( "decrypt: %f seconds\n", dur5);
	//fmpz_poly_print(m1);
	//printf("\n");
	return 0;
}
