#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>
#include <string.h>
#include <gmp.h>
#include "flint/fmpz_vec.h"
#include "flint/fmpz_poly.h"
#include "flint/fmpz_poly_mat.h"
#include "flint/fmpz.h"
#include "flint/fmpz_mat.h"

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
	struct param_node_t *next;
}param_node_t;

const double pi = 3.1415926;
static long secparam, d;
/* denote d in fx */
static double dvn;
/* standard deviation of Guassian distribution*/
static fmpz_t bound, t;
static fmpz_poly_t fx;
/* for R = Z[x]/(x^d + 1); fx = x^d + 1 */
sk_node_t *skhead;
pk_node_t *pkhead;
static long chrnd = 0;

void set_mspace(long vt);
long get_mspace();
void bgv_set_d(long td);
long bgv_get_d();
void bgv_set_secparam(long sp);
long bgv_get_secparam();
void bgv_set_dvn(double tdvn);
double bgv_get_dvn();
void bgv_set_bound(int vb);
void bv_sym_vars_init();
void bv_sym_vars_clear();
void hcrypt_random(fmpz_t r, int len);
fmpz *samplez(fmpz *vec);
void guassian_poly(fmpz *c, fmpz_poly_t poly);
void unif_poly(fmpz_poly_t poly, fmpz_t space);
param_node_t *e_setup(int miu, int lamda, int b, param_node_t *param);
sk_node_t *e_skeygen(param_node_t *param);
void e_pkeygen(fmpz_poly_mat_t pk, param_node_t *param, fmpz_poly_mat_t sk);
void e_encrypt(fmpz_poly_mat_t ct, param_node_t *param, fmpz_poly_mat_t pk, fmpz_poly_t ms);
void e_decrypt(fmpz_poly_t ms, param_node_t *param, fmpz_poly_mat_t sk, fmpz_poly_mat_t ct);
void bitdecomp(fmpz_poly_mat_t dc, fmpz_poly_mat_t x, fmpz_t qq);
void powers(fmpz_poly_mat_t po, fmpz_poly_mat_t x, fmpz_t qq);
void switchkeygen(fmpz_poly_mat_t mapb, fmpz_poly_mat_t s1, fmpz_poly_mat_t s2, fmpz_t qq);
void switchkey(fmpz_poly_mat_t c2, fmpz_poly_mat_t mapb, fmpz_poly_mat_t c1, fmpz_t qq);

void switchkey(fmpz_poly_mat_t c2, fmpz_poly_mat_t mapb, fmpz_poly_mat_t c1, fmpz_t qq)
{
	fmpz_poly_mat_t bd, bdt;
	bitdecomp(bd, c1, qq);
	long bdtrow, bdtcol, i, j, bcol;
	bdtrow = fmpz_poly_mat_ncols(bd);
	bdtcol = fmpz_poly_mat_nrows(bd);
	bcol = fmpz_poly_mat_ncols(mapb);
	fmpz_poly_mat_init(c2, bdtrow, bcol);
	fmpz_poly_mat_init(bdt, bdtrow, bdtcol);
	for( i = 0 ; i < bdtrow ; i++ ) {
		for( j = 0 ; j < bdtcol ; j++ ) {
			fmpz_poly_set(fmpz_poly_mat_entry(bdt, i, j), fmpz_poly_mat_entry(bd, j, i));
		}
	}
	fmpz_poly_mat_mul(c2, bdt, mapb);
}

void switchkeygen(fmpz_poly_mat_t mapb, fmpz_poly_mat_t s1, fmpz_poly_mat_t s2, fmpz_t qq)
{
	fmpz_poly_mat_t sp1;
	param_node_t *param;
	param = (param_node_t *)malloc(sizeof(param_node_t));
	long n1, n2, i;
	n1 = fmpz_poly_mat_nrows(s1);
	n2 = fmpz_poly_mat_nrows(s2)
	param->n = n2 - 1;
	param->bign = n1 * fmpz_clog(qq, t);
	fmpz_init_set(param->q, qq);
	param->next = NULL;
	e_pkeygen(mapb, param, s2);
	powers(sp1, s1, qq);
	for( i = 0 ; i < param->bign ; i++) {
		fmpz_poly_add(fmpz_poly_mat_entry(mapb, i, 0), fmpz_poly_mat_entry(mapb, i, 0), fmpz_poly_mat_entry(sp1, i, 0));
	}	
	fmpz_poly_mat_clear(sp1);
	free(param);
}

void set_mspace(long vt)
{
	fmpz_set_ui(t, vt);
}

long get_mspace()
{
	return fmpz_get_ui(t);
}

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

void hcrypt_random(fmpz_t r, int len)
{
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

fmpz *samplez(fmpz *vec)
{
	long ele = bgv_get_d();
	if ( ele == 0 )
		return;
	double tdvn = bgv_get_dvn();
	long a = (long)ceil(-10*tdvn);
	long b = (long)floor(+10*tdvn);
	long x, i;
	double p;
	int len = sizeof(unsigned long int);
	fmpz_t randseed;
	fmpz_init(randseed);
	hcrypt_random(randseed, len);
	unsigned long int useed = fmpz_get_ui(randseed);
	srand(useed);
	for( i = 0 ; i < ele ; i++) {
		do {
			x = rand()%(b - a) + a;
			p = exp(-pi*x / ( tdvn * tdvn));
		} while ( !( p > 0 && p <= 1) );

		vec[i] = x;
	}
	fmpz_clear(randseed);
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
	int len = sizeof(unsigned long int);
	fmpz_t randseed;
	fmpz_init(randseed);
	hcrypt_random(randseed, len);
	unsigned long int useed = fmpz_get_ui(randseed);
	mpz_t rndnum, rndbd;
	fmpz_t rndfmpz;
	gmp_randstate_t gmpstate;

	mpz_init(rndnum);
	mpz_init(rndbd);
	fmpz_get_mpz(rndbd, space);
	fmpz_init(rndfmpz);
	gmp_randinit_default(gmpstate);
	gmp_randseed_ui(gmpstate, useed);

	long ele = bgv_get_d();
	for( i = 0 ; i < ele ; i++ ) {
		mpz_urandomm(rndnum, gmpstate, rndbd);
		fmpz_set_mpz(rndfmpz, rndnum);
		fmpz_poly_set_coeff_fmpz(poly, i, rndfmpz);
	}
	fmpz_clear(randseed);
	fmpz_clear(rndfmpz);
	gmp_randclear(gmpstate);
	mpz_clear(rndnum);
	mpz_clear(rndbd);
}

param_node_t *e_setup(int miu, int lamda, int b, param_node_t *param)
{
	hcrypt_random(param->q, miu);
	fmpz_t tmp;
	fmpz_init(tmp);
	fmpz_fdiv_q(tmp, param->q, bound);
	long prod;
	prod = lamda * fmpz_flog(tmp, t);

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

void e_pkeygen(fmpz_poly_mat_t pk, param_node_t *param, fmpz_poly_mat_t sk)
{
        fmpz_poly_mat_t ppk, ee, bb, ss, tmp, tmp1;
        fmpz_poly_mat_init(ppk, param->bign, param->n);
        fmpz_poly_mat_init(pk, param->bign, 1 + (param->n));
        fmpz_poly_mat_init(ee, param->bign, 1);
        fmpz_poly_mat_init(bb, param->bign, 1);
        fmpz_poly_mat_init(ss, param->n, 1);
        fmpz *coeffs = _fmpz_vec_init(d);

        long i, j;
        for( i = 0 ; i < param->n ; i++ ) {
                fmpz_poly_set(fmpz_poly_mat_entry(ss, i, 0), fmpz_poly_mat_entry(sk, i+1, 0 ));
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
        fmpz_poly_mat_scalar_mul_fmpz(tmp1, ee, t);
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
                        fmpz_poly_scalar_smod_fmpz(fmpz_poly_mat_entry(pk, i, j), fmpz_poly_mat_entry(pk, i, j), param->q);
                }
        }

        _fmpz_vec_clear(coeffs, d);
        fmpz_poly_mat_clear(tmp);
        fmpz_poly_mat_clear(tmp1);
        fmpz_poly_mat_clear(ee);
        fmpz_poly_mat_clear(ss);
        fmpz_poly_mat_clear(bb);
        fmpz_poly_mat_clear(ppk);
}

void e_encrypt(fmpz_poly_mat_t ct, param_node_t *param, fmpz_poly_mat_t pk, fmpz_poly_t ms)
{
        long i, j;
        fmpz_poly_mat_t mm, rr, tmp, tmp1;
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
                fmpz_poly_scalar_smod_fmpz(fmpz_poly_mat_entry(ct, i, 0), fmpz_poly_mat_entry(ct, i, 0), param->q);
        }

        fmpz_poly_mat_clear(tmp);
        fmpz_poly_mat_clear(tmp1);
        fmpz_poly_mat_clear(mm);
        fmpz_poly_mat_clear(rr);
}

void e_decrypt(fmpz_poly_t ms, param_node_t *param, fmpz_poly_mat_t sk, fmpz_poly_mat_t ct)
{
        fmpz_poly_t tmp;
        fmpz_poly_init(ms);
        fmpz_poly_init(tmp);
        fmpz_poly_zero(ms);

        long i;
        for( i = 0 ; i < param->n + 1 ; i++) {
                fmpz_poly_mul(tmp, fmpz_poly_mat_entry(ct, i, 0), fmpz_poly_mat_entry(sk, i, 0));
                fmpz_poly_add(ms, ms, tmp);
        }
        fmpz_poly_rem_basecase(ms, ms, fx);
        fmpz_poly_scalar_smod_fmpz(ms, ms, param->q);
        fmpz_poly_scalar_smod_fmpz(ms, ms, t);

        fmpz_poly_clear(tmp);
}

void bitdecomp(fmpz_poly_mat_t dc, fmpz_poly_mat_t x, fmpz_t qq)
{
	long xrow = fmpz_poly_mat_nrows(x);
	long len = fmpz_clog(qq, t);
	long qrow = xrow * len;
	long i, j, k;
	fmpz_poly_mat_init(dc, qrow, 1);
	fmpz_mat_t bits;
	fmpz_mat_init(bits, d, len);
	fmpz_t hold;
	fmpz_init(hold);
	fmpz_poly_t xtmp;
	fmpz_poly_init(xtmp);
	for( i = 0 ; i < xrow ; i++ ) {
		fmpz_mat_zero(bits);
		for( j = 0 ; j < d ; j++) {
			fmpz_poly_get_coeff_fmpz(hold, fmpz_poly_mat_entry(x, i, 0), j);
			k = 0;
			while ( !fmpz_is_zero(hold) ) {
				fmpz_mod(fmpz_mat_entry(bits, j, k), hold, t);
				fmpz_tdiv_q(hold, hold, t);
				k++;
			}
		}

		for( j = 0 ; j < len ; j++ ) {
			fmpz_poly_zero(xtmp);
			for( k = 0; k < d ; k++ ) {
				fmpz_poly_set_coeff_fmpz(xtmp, k, fmpz_mat_entry(bits, k, j));
			}
			fmpz_poly_set(fmpz_poly_mat_entry(dc, i + j * xrow, 0), xtmp);
		}
	}
	
	fmpz_clear(hold);
	fmpz_poly_clear(xtmp);
	fmpz_mat_clear(bits);
}

void powers(fmpz_poly_mat_t po, fmpz_poly_mat_t x, fmpz_t qq)
{
	long xrow = fmpz_poly_mat_nrows(x);
	long len = fmpz_clog(qq, t);
	long qrow = xrow * len;
	long i, j;
	fmpz_poly_mat_init(po, qrow, 1);

	for( i = 0 ; i < xrow ; i++) {
		fmpz_poly_set(fmpz_poly_mat_entry(po, i, 0), fmpz_poly_mat_entry(x, i, 0));
	}
	for( i = 1 ; i < len ; i++) {
		for( j = 0 ; j < xrow ; j++) {
			fmpz_poly_scalar_mul_fmpz(fmpz_poly_mat_entry(po, j + i * xrow, 0), fmpz_poly_mat_entry(po, j + (i-1)*xrow, 0), t);
		}
	}
}



int main()
{
	fmpz_poly_mat_t x,dc;
	fmpz_t qq;
	fmpz_init(qq);
	fmpz_set_ui(qq, 8);
	set_mspace(2);
	bgv_set_d(4);
	fmpz_poly_mat_init(x, 2, 1);
	fmpz_poly_set_str(fmpz_poly_mat_entry(x,0,0),"4  0 1 2 7");
	fmpz_poly_set_str(fmpz_poly_mat_entry(x,1,0),"4  1 3 0 5");
	bitdecomp(dc,x,qq);
	
	fmpz_poly_mat_print(dc, "x");
	printf("\n");
	
	fmpz_clear(qq);
	fmpz_poly_mat_clear(x);
	fmpz_poly_mat_clear(dc);
	return 0;
}



