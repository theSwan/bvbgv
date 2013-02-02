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

typedef struct pk_node_t {
	fmpz_poly_mat_t pka;
	fmpz_poly_mat_t pkb;
	struct pk_node_t *next;
}pk_node_t ;

typedef struct sk_node_t {
	fmpz_poly_mat_t sk;
	struct sk_node_t *next;
}sk_node_t;

typedef struct key_node_t {
	pk_node_t *pubkey;
	sk_node_t *prvkey;
}key_node_t;

typedef struct param_node_t {
	fmpz_t q;
	long n;
	long bign;
	struct param_node_t *next;
}param_node_t;

typedef struct ciphertext_t {
        fmpz_poly_mat_t text;
        int lv;
}ciphertext_t;
const double pi = 3.1415926;
static long secparam, d;
/* denote d in fx */
static double dvn;
/* standard deviation of Guassian distribution*/
static fmpz_t bound, t;
static fmpz_poly_t fx;
static int bgv_level;
/* for R = Z[x]/(x^d + 1); fx = x^d + 1 */
key_node_t *keylist;
param_node_t *param;
static long chrnd = 0;

void set_mspace(long vt);//
long get_mspace();//
void bgv_set_d(long td);//
long bgv_get_d();//
void bgv_set_secparam(long sp);//
long bgv_get_secparam();//
void bgv_set_dvn(double tdvn);//
double bgv_get_dvn();//
void bgv_set_bound(int vb);//
void bgv_vars_init();//
void bgv_vars_clear();//
void bgv_set_level(int l);//
int bgv_get_level();//
void hcrypt_random(fmpz_t r, int len);//
fmpz *samplez(fmpz *vec);//
void guassian_poly(fmpz *c, fmpz_poly_t poly);//
void unif_poly(fmpz_poly_t poly, fmpz_t space);//
param_node_t *param_node_init(param_node_t *pnt);//
param_node_t *e_setup(int miu, int lamda, int b, param_node_t *param);//
void e_skeygen(fmpz_poly_mat_t sk, param_node_t *param);//
void e_pkeygen(fmpz_poly_mat_t pk, param_node_t *param, fmpz_poly_mat_t sk);//
void e_encrypt(fmpz_poly_mat_t ct, param_node_t *param, fmpz_poly_mat_t pk, fmpz_poly_t ms);//
void e_decrypt(fmpz_poly_t ms, param_node_t *param, fmpz_poly_mat_t sk, fmpz_poly_mat_t ct);//
void bitdecomp(fmpz_poly_mat_t dc, fmpz_poly_mat_t x, fmpz_t qq);//
void powers(fmpz_poly_mat_t po, fmpz_poly_mat_t x, fmpz_t qq);//
void switchkeygen(fmpz_poly_mat_t mapb, fmpz_poly_mat_t s1, fmpz_poly_mat_t s2, fmpz_t qq);//
void switchkey(fmpz_poly_mat_t c2, fmpz_poly_mat_t mapb, fmpz_poly_mat_t c1, fmpz_t qq);
void scale(fmpz_poly_mat_t c2, fmpz_poly_mat_t c1, fmpz_t qq, fmpz_t pp, fmpz_t r);
void hcrypt_bgv_refresh(fmpz_poly_mat_t c3, fmpz_poly_mat_t c, fmpz_poly_mat_t map, fmpz_t qq, fmpz_t pp, fmpz_t r);//
param_node_t *hcrypt_bgv_setup(int lamda, int level, int b, param_node_t *param);//
void vec_tensor(fmpz_poly_mat_t tensor, fmpz_poly_mat_t x, fmpz_t qq);//
key_node_t *hcrypt_bgv_keygen(key_node_t *kn, param_node_t *param);//
ciphertext_t *hcrypt_bgv_encrypt(ciphertext_t *ct, param_node_t *param, fmpz_poly_mat_t pk, fmpz_poly_t ms);
void hcrypt_bgv_decrypt(fmpz_poly_t ms, param_node_t *param, fmpz_poly_mat_t sk, ciphertext_t *ct);
ciphertext_t *hcrypt_bgv_add(ciphertext_t *c, pk_node_t *pbk, ciphertext_t *c1, ciphertext_t *c2);
ciphertext_t *hcrypt_bgv_mul(ciphertext_t *c, pk_node_t *pbk, ciphertext_t *c1, ciphertext_t *c2);

ciphertext_t *hcrypt_bgv_mul(ciphertext_t *c, pk_node_t *pbk, ciphertext_t *c1, ciphertext_t *c2)
{
	c = (ciphertext_t *)malloc(sizeof(ciphertext_t));
	pk_node_t *pktmp;
	pktmp = keylist->pubkey;

	int l1 = c1->lv, l2 = c2->lv, l;
	if (l1 == l2) {
                l = bgv_get_level();
		c->lv = l1 - 1;
		while( l > l1 ) {
			pktmp = pktmp->next;
			param = param->next;
			l--;
		}
		pktmp = pktmp->next;
		fmpz_poly_mat_t c3;
		long row = fmpz_poly_mat_nrows(c1->text)*fmpz_poly_mat_nrows(c2->text);
		fmpz_poly_mat_init(c3, row, 1);
		fmpz_poly_mat_mul(c3, c1->text, c2->text);
		fmpz_poly_mat_init(c->text, row, 1);
		hcrypt_bgv_refresh(c->text, c3, pktmp->pkb, param->q, param->next->q, t);
	}
	else if ( l1 > l2 ) {
		fmpz_poly_mat_t holdc1;
		fmpz_poly_mat_init_set(holdc1, c1->text);
		l = bgv_get_level();
		while ( l > l1 ) { 
			pktmp = pktmp->next; 
			param = param->next;
			l--;
		}
		pktmp = pktmp->next;
		l--;
		while( l >= l2 ) {
			fmpz_poly_mat_t ctmp;			
			hcrypt_bgv_refresh(ctmp, holdc1, pktmp->pkb, param->q, param->next->q, t);
			fmpz_poly_mat_swap(ctmp, holdc1);
			fmpz_poly_mat_clear(ctmp);
			pktmp = pktmp->next;
			param = param->next;
			l--;
		}	
		c->lv = l;
		fmpz_poly_mat_t c3;
		long row = fmpz_poly_mat_nrows(holdc1)*fmpz_poly_mat_nrows(c2->text);
		fmpz_poly_mat_init(c3, row, 1);
		fmpz_poly_mat_mul(c3, holdc1, c2->text);
		fmpz_poly_mat_init(c->text, row, 1);
		hcrypt_bgv_refresh(c->text, c3, pktmp->pkb, param->q, param->next->q, t); 
	}
	else {
		fmpz_poly_mat_t holdc2;
		fmpz_poly_mat_init_set(holdc2, c2->text);
		l = bgv_get_level();
		while ( l > l2 ) { 
			pktmp = pktmp->next; 
			param = param->next;
			l--;
		}
		pktmp = pktmp->next;
		l--;
		while( l >= l1 ) {
			fmpz_poly_mat_t ctmp;			
			hcrypt_bgv_refresh(ctmp, holdc2, pktmp->pkb, param->q, param->next->q, t);
			fmpz_poly_mat_swap(ctmp, holdc2);
			fmpz_poly_mat_clear(ctmp);
			pktmp = pktmp->next;
			param = param->next;
			l--;
		}	
		c->lv = l;
		fmpz_poly_mat_t c3;
		long row = fmpz_poly_mat_nrows(c1->text)*fmpz_poly_mat_nrows(holdc2);
		fmpz_poly_mat_init(c3, row, 1);
		fmpz_poly_mat_mul(c3, c1->text, holdc2);
		fmpz_poly_mat_init(c->text, row, 1);
		hcrypt_bgv_refresh(c->text, c3, pktmp->pkb, param->q, param->next->q, t);
	}
	return c;
}

ciphertext_t *hcrypt_bgv_add(ciphertext_t *c, pk_node_t *pbk, ciphertext_t *c1, ciphertext_t *c2)
{
	c = (ciphertext_t *)malloc(sizeof(ciphertext_t));
	pk_node_t *pktmp;
	pktmp = keylist->pubkey;

	int l1 = c1->lv, l2 = c2->lv, l;
	if (l1 == l2) {
                printf("equal\n");
		c->lv = l1 - 1;
                l = bgv_get_level();
		while( l > l1 ) {
			pktmp = pktmp->next;
			param = param->next;
			l--;
		}
		pktmp = pktmp->next;
		fmpz_poly_mat_t c3;
		long row = fmpz_poly_mat_nrows(c1->text);
		fmpz_poly_mat_init(c3, row, 1);
		fmpz_poly_mat_add(c3, c1->text, c2->text);
		fmpz_poly_mat_init(c->text, row, 1);
                printf("add end\n");
		hcrypt_bgv_refresh(c->text, c3, pktmp->pkb, param->q, param->next->q, t);
	}
	else if ( l1 > l2 ) {
		fmpz_poly_mat_t holdc1;
		fmpz_poly_mat_init_set(holdc1, c1->text);
		l = bgv_get_level();
		while ( l > l1 ) { 
			pktmp = pktmp->next; 
			param = param->next;
			l--;
		}
		pktmp = pktmp->next;
		l--;
		while( l >= l2 ) {
			fmpz_poly_mat_t ctmp;			
			hcrypt_bgv_refresh(ctmp, holdc1, pktmp->pkb, param->q, param->next->q, t);
			fmpz_poly_mat_swap(ctmp, holdc1);
			fmpz_poly_mat_clear(ctmp);
			pktmp = pktmp->next;
			param = param->next;
			l--;
		}	
		c->lv = l;
		fmpz_poly_mat_t c3;
		long row = fmpz_poly_mat_nrows(holdc1);
		fmpz_poly_mat_init(c3, row, 1);
		fmpz_poly_mat_add(c3, holdc1, c2->text);
		fmpz_poly_mat_init(c->text, row, 1);
		hcrypt_bgv_refresh(c->text, c3, pktmp->pkb, param->q, param->next->q, t); 
	}
	else {
		fmpz_poly_mat_t holdc2;
		fmpz_poly_mat_init_set(holdc2, c2->text);
		l = bgv_get_level();
		while ( l > l2 ) { 
			pktmp = pktmp->next; 
			param = param->next;
			l--;
		}
		pktmp = pktmp->next;
		l--;
		while( l >= l1 ) {
			fmpz_poly_mat_t ctmp;			
			hcrypt_bgv_refresh(ctmp, holdc2, pktmp->pkb, param->q, param->next->q, t);
			fmpz_poly_mat_swap(ctmp, holdc2);
			fmpz_poly_mat_clear(ctmp);
			pktmp = pktmp->next;
			param = param->next;
			l--;
		}	
		c->lv = l;
		fmpz_poly_mat_t c3;
		long row = fmpz_poly_mat_nrows(holdc2);
		fmpz_poly_mat_init(c3, row, 1);
		fmpz_poly_mat_add(c3, holdc2, c1->text);
		fmpz_poly_mat_init(c->text, row, 1);
		hcrypt_bgv_refresh(c->text, c3, pktmp->pkb, param->q, param->next->q, t);
	}
	return c;
}


void hcrypt_bgv_refresh(fmpz_poly_mat_t c3, fmpz_poly_mat_t c, fmpz_poly_mat_t map, fmpz_t qq, fmpz_t pp, fmpz_t r)
{
        fmpz_poly_mat_t c1;
        powers(c1, c, qq);
        fmpz_poly_mat_t c2;
	long row, col, len;
	row = fmpz_poly_mat_nrows(c1);
        col = fmpz_poly_mat_ncols(c1);
        fmpz_poly_mat_init(c2, row, col);
        printf("scale start\n");
        scale(c2, c1, qq, pp, r);
        printf("switch start\n");
        switchkey(c3, map, c2, pp);
        printf("switch end\n");
        
	fmpz_poly_mat_clear(c1);
	fmpz_poly_mat_clear(c2);
}

void switchkey(fmpz_poly_mat_t c3, fmpz_poly_mat_t mapb, fmpz_poly_mat_t c1, fmpz_t qq)
{
	fmpz_poly_mat_t bd, bdt;
	long c1row = fmpz_poly_mat_nrows(c1);
	long len = fmpz_clog(qq, t);
	long qrow = c1row * len;
	fmpz_poly_mat_init(bd, qrow, 1);
	bitdecomp(bd, c1, qq);
        printf("decomp end\n");
	long bdtrow, bdtcol, i, j;
	bdtrow = fmpz_poly_mat_ncols(bd);
        printf("dd\n");
	bdtcol = fmpz_poly_mat_nrows(bd);
        printf("dd\n");
        fmpz_poly_mat_print(mapb,"x");
        printf("before init\n");
	fmpz_poly_mat_init(bdt, bdtrow, bdtcol);
        printf(" trans start\n");
        for( i = 0 ; i < bdtrow ; i++ ) {
		for( j = 0 ; j < bdtcol ; j++ ) {
			fmpz_poly_set(fmpz_poly_mat_entry(bdt, i, j), fmpz_poly_mat_entry(bd, j, i));
		}
	}
        printf(" trans ends\n");
	long col = fmpz_poly_mat_ncols(mapb);
	//fmpz_poly_mat_init(c3, bdtrow, col);
        printf("ty\n");
	fmpz_poly_mat_mul(c3, bdt, mapb);
        fmpz_poly_mat_print(c3, "t");
	for( i = 0 ; i < bdtrow ; i++ ) {
		for( j = 0 ; j < col ; j++ ) {
			fmpz_poly_rem_basecase(fmpz_poly_mat_entry(c3, i, j), fmpz_poly_mat_entry(c3, i, j), fx);
                	fmpz_poly_scalar_smod_fmpz(fmpz_poly_mat_entry(c3, i, j), fmpz_poly_mat_entry(c3, i, j), qq);
		}
	}
	fmpz_poly_mat_clear(bd);
	fmpz_poly_mat_clear(bdt);
}

void hcrypt_bgv_decrypt(fmpz_poly_t ms, param_node_t *param, fmpz_poly_mat_t sk, ciphertext_t *ct)
{
	int i = bgv_get_level();;
	sk_node_t *tmp;
	tmp = keylist->prvkey;
	while(i > ct->lv) {
		tmp = tmp->next;
		i--;
	}
        fmpz_poly_init(ms);
        printf("before decode\n");
        //fmpz_poly_mat_print(tmp->sk,"x");
        e_decrypt(ms, param, tmp->sk, ct->text);
        printf("decode end\n");
}

ciphertext_t *hcrypt_bgv_encrypt(ciphertext_t *ct, param_node_t *param, fmpz_poly_mat_t pk, fmpz_poly_t ms)
{
        ct = (ciphertext_t *)malloc(sizeof(ciphertext_t));
        ct->lv = bgv_get_level();
        fmpz_poly_mat_init(ct->text, 1 + param->n, 1);
        e_encrypt(ct->text, param, keylist->pubkey->pka, ms);
        return ct;
}


int main()
{
        bgv_vars_init();
        bgv_set_bound(1);
        bgv_set_dvn(8.0);
        set_mspace(2);
	fmpz_poly_t ms,mr;
	fmpz_poly_init(ms);
	fmpz_poly_init(mr);
	fmpz_poly_set_coeff_si(ms, 0, 1);
	//fmpz_poly_set_coeff_si(ms, 1, 1);
	/*fmpz_poly_mat_t a,b;
	fmpz_poly_mat_init(a,2,1);
	fmpz_poly_mat_init(b,2,1);
	fmpz_poly_set_str(fmpz_poly_mat_entry(a,0,0),"2  2 1");
	fmpz_poly_set_str(fmpz_poly_mat_entry(a,1,0),"2  2 1");
	fmpz_t qq,pp;
	fmpz_set_si(qq,3);
	fmpz_set_si(pp,2);
	powers(b,a,qq);
	fmpz_poly_mat_print(b, "x");*/
	param_node_t *r;
	param = param_node_init(param);
	r = param_node_init(r);
        param->n = 10;
        param->bign = 105;
        fmpz_set_si(param->q, 29);
        param->next = r;
        r->n = 8;
        r->bign = 51;
        fmpz_set_si(r->q, 6);
        param_node_t *s;
        s = param_node_init(s);
        s->n = 4;
        s->bign = 18;
        fmpz_set_si(s->q, 4);
        r->next = s;
        s->next = NULL;
	// param = hcrypt_bgv_setup(4, 2, 0, param);
        bgv_set_level(2);
	
        fmpz_poly_set_coeff_ui(fx, 1, 1);
	fmpz_poly_set_coeff_ui(fx, 0, 1);
	keylist = (key_node_t *)malloc(sizeof(key_node_t)); 
	keylist =  hcrypt_bgv_keygen(keylist, param);
	printf("ok\n");
	ciphertext_t *ct, *nct;
	ct = hcrypt_bgv_encrypt(ct, param, keylist->pubkey->pka, ms);
	//fmpz_poly_mat_print(keylist->pubkey->pka,"x");
	nct = hcrypt_bgv_add(nct, keylist->pubkey, ct, ct);
	hcrypt_bgv_decrypt(mr, param->next, keylist->prvkey->sk, nct);
	fmpz_poly_print(mr);
	printf("\n");
	bgv_vars_clear();
	return 0;
}

key_node_t *hcrypt_bgv_keygen(key_node_t *kn, param_node_t *param)
{
        printf("ok\n");
	sk_node_t *sh;
	pk_node_t *ph;
	sh = (sk_node_t *)malloc(sizeof(sk_node_t));
	fmpz_poly_mat_init(sh->sk, 1 + param->n , 1);

        e_skeygen(sh->sk, param);
	fmpz_poly_mat_print(sh->sk,"x");
	sh->next = NULL;
	ph = (pk_node_t *)malloc(sizeof(pk_node_t));
	fmpz_poly_mat_init(ph->pkb, 1, 1);
        fmpz_poly_mat_zero(ph->pkb);
	fmpz_poly_mat_init(ph->pka, param->bign, 1 + (param->n));
        e_pkeygen(ph->pka, param, sh->sk);
	//fmpz_poly_mat_print(ph->pka,"x");
	fmpz_poly_mat_t tensor;
	long row1 = fmpz_poly_mat_nrows(sh->sk), row2, len;
        row2 = row1 * row1;
        fmpz_poly_mat_init(tensor, row2, 1);
        vec_tensor(tensor, sh->sk, param->q);
	//fmpz_poly_mat_print(tensor,"x");
	fmpz_poly_mat_t s1;
	len = fmpz_clog(param->q, t);
	row2 = len * row2;
	fmpz_poly_mat_init(s1, row2, 1);
        bitdecomp(s1, tensor, param->q);
	
	fmpz_poly_mat_clear(tensor);
	ph->next = NULL;
        param_node_t *pam, *pamm;
	sk_node_t *ss, *sr;
	pk_node_t *ps, *pr;
        ss = sh;
	ps = ph;
        int l = bgv_get_level() - 1;
        int i;
        pamm = param;
        pam = param->next;
	fmpz_poly_mat_t s2;
        for(i = l ; i >= 0 ; i-- ){
                printf("ok\n");
                sr = (sk_node_t *)malloc(sizeof(sk_node_t));
		fmpz_poly_mat_init(sr->sk, 1 + pam->n , 1);		
		e_skeygen(sr->sk, pam);
		ss->next = sr;
                ss = sr;

		pr = (pk_node_t *)malloc(sizeof(pk_node_t));
		fmpz_poly_mat_init(pr->pka, pam->bign, 1 + (pam->n));
                e_pkeygen(pr->pka, pam, sr->sk);
		fmpz_poly_mat_print(pr->pka, "x");

		row1 = fmpz_poly_mat_nrows(sr->sk);
        	row2 = row1 * row1;
        	fmpz_poly_mat_init(tensor, row2, 1);
                vec_tensor(tensor, sr->sk, pam->q);
            
		len = fmpz_clog(pam->q, t);
		row2 = row2 * len;
		fmpz_poly_mat_init(s2, row2, 1);
                bitdecomp(s2, tensor, pam->q);
		row1 = fmpz_poly_mat_nrows(s1) * len;
		row2 = fmpz_poly_mat_nrows(sr->sk);
		fmpz_poly_mat_init(pr->pkb, row1, row2);
               
                switchkeygen(pr->pkb, s1, sr->sk, pam->q);
        
		fmpz_poly_mat_clear(s1);
		fmpz_poly_mat_init_set(s1, s2);
                fmpz_poly_mat_clear(s2);
                fmpz_poly_mat_clear(tensor);
                pam = pam->next;
                pamm = pamm->next;
		ps->next = pr;
		ps = pr;
        }
        ss->next = NULL;
	ps->next = NULL;
	kn->prvkey = sh;
	kn->pubkey = ph;
        fmpz_poly_mat_clear(s1);
        return kn;
}

param_node_t *hcrypt_bgv_setup(int lamda, int level, int b, param_node_t *param)
{
        bgv_set_level(level);
        fmpz_t mult;
	fmpz_set_ui(mult, lamda*level);
	int miu;
        miu = (int)fmpz_flog(mult, t);

        int high;
        high = (level + 1) * miu;
        hcrypt_random(param->q, high);
	fmpz_t tmp;
	fmpz_init(tmp);
	fmpz_fdiv_q(tmp, param->q, bound);
	long prod;
	prod = lamda * fmpz_flog(tmp, t);

	if(b == 0) {
		param->n = prod;
		d = 1;
	}
	else {
		param->n = 1;
		d = prod;
	}
        param->bign = ceil((2 * param->n + 1) * fmpz_flog(param->q,t));
        fmpz_poly_set_coeff_ui(fx, d, 1);
	fmpz_poly_set_coeff_ui(fx, 0, 1);
	param_node_t *r, *pn;

        r = param;
        int j;
        for(j = level - 1 ; j >= 0 ; j--) {
                pn = e_setup((j+1)*miu, lamda, b, pn);
                r->next = pn;
                r = pn;
        }
        r->next = NULL;

        fmpz_clear(tmp);
        return param;
}


void scale(fmpz_poly_mat_t c2, fmpz_poly_mat_t c1, fmpz_t qq, fmpz_t pp, fmpz_t r)
{
        long row, col, i, j, len, k;
        row = fmpz_poly_mat_nrows(c1);
        col = fmpz_poly_mat_ncols(c1);
        fmpz_poly_t poly;
        fmpz_poly_init(poly);
        fmpz_t coeff, tmp, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6;
        fmpz_init(coeff);
        fmpz_init(tmp);
        fmpz_init(tmp1);
        fmpz_init(tmp2);
        fmpz_init(tmp3);
        fmpz_init(tmp4);
        fmpz_init(tmp5);
        fmpz_init(tmp6);
        
        for( i = 0 ; i < row ; i++ ) {
                for( j = 0 ; j < col ; j++ ) {
                        fmpz_poly_set(poly, fmpz_poly_mat_entry(c1, i, j));
                        len = fmpz_poly_length(poly);
                        for( k = 0 ; k < len ; k++ ) {
                                fmpz_poly_get_coeff_fmpz(tmp, poly, k);
                                fmpz_mod(tmp1, tmp, r);   /* tmp1 = base */
                                fmpz_mul(coeff, tmp, pp);  /* tmp2 = bound */
				fmpz_cdiv_q(tmp2, coeff, qq);
				if(fmpz_cmp(tmp2, pp) > 0)
				fmpz_set(tmp2, pp);
                                fmpz_sub(tmp3, tmp2, tmp1);
                                fmpz_fdiv_q(tmp4, tmp3, r);   /* tmp4 = ( bound - base ) / r = h */
                                fmpz_mul(tmp5, tmp4, r);
                                fmpz_add(tmp6, tmp5, tmp1);                           
				fmpz_mod(tmp6, tmp6, pp);
                                fmpz_poly_set_coeff_fmpz(poly, k, tmp6);
                        }
                        fmpz_poly_set(fmpz_poly_mat_entry(c2, i, j), poly);
                }
        }
        fmpz_poly_clear(poly);
        fmpz_clear(coeff);
        fmpz_clear(tmp);
        fmpz_clear(tmp1);
        fmpz_clear(tmp2);
        fmpz_clear(tmp3);
        fmpz_clear(tmp4);
        fmpz_clear(tmp5);
        fmpz_clear(tmp6);
}


void switchkeygen(fmpz_poly_mat_t mapb, fmpz_poly_mat_t s1, fmpz_poly_mat_t s2, fmpz_t qq)
{
	fmpz_poly_mat_t sp1;
	param_node_t *param;
	param = (param_node_t *)malloc(sizeof(param_node_t));
	long n1, n2, i;
	n1 = fmpz_poly_mat_nrows(s1);
	n2 = fmpz_poly_mat_nrows(s2);
	param->n = n2 - 1;
	param->bign = n1 * fmpz_clog(qq, t);
	fmpz_init_set(param->q, qq);
	param->next = NULL;
        //printf("pkeygen\n");
	e_pkeygen(mapb, param, s2);
        //printf("pkeygen\n");
	long s1row = fmpz_poly_mat_nrows(s1);
	long len = fmpz_clog(qq, t);
	long qrow = s1row * len;
	//fmpz_poly_mat_init(sp1, qrow, 1);
        //printf("powers start\n");
	powers(sp1, s1, qq);
        //printf("end\n");
	for( i = 0 ; i < param->bign ; i++) {
		fmpz_poly_add(fmpz_poly_mat_entry(mapb, i, 0), fmpz_poly_mat_entry(mapb, i, 0), fmpz_poly_mat_entry(sp1, i, 0));
		fmpz_poly_rem_basecase(fmpz_poly_mat_entry(mapb, i, 0), fmpz_poly_mat_entry(mapb, i, 0), fx);
                fmpz_poly_scalar_smod_fmpz(fmpz_poly_mat_entry(mapb, i, 0), fmpz_poly_mat_entry(mapb, i, 0), qq);
               // printf("ert");
        }
	fmpz_poly_mat_clear(sp1);
	free(param);
}


void vec_tensor(fmpz_poly_mat_t tensor, fmpz_poly_mat_t x, fmpz_t qq)
{
        long row1 = fmpz_poly_mat_nrows(x);

        long i, j;
        for( i = 0 ; i < row1 ; i++ ) {
                for( j = 0 ; j < row1 ; j++ ){
                        fmpz_poly_mul(fmpz_poly_mat_entry(tensor,j+i*row1,0),fmpz_poly_mat_entry(x,i,0),fmpz_poly_mat_entry(x,j,0));
			fmpz_poly_rem_basecase(fmpz_poly_mat_entry(tensor,j+i*row1,0), fmpz_poly_mat_entry(tensor,j+i*row1,0), fx);
        		fmpz_poly_scalar_smod_fmpz(fmpz_poly_mat_entry(tensor,j+i*row1,0), fmpz_poly_mat_entry(tensor,j+i*row1,0), qq);
                }
        }
}

param_node_t *e_setup(int miu, int lamda, int b, param_node_t *param)
{
        param = param_node_init(param);
	hcrypt_random(param->q, miu);
	fmpz_t tmp;
	fmpz_init(tmp);
	fmpz_fdiv_q(tmp, param->q, bound);
	long prod;
	prod = lamda * fmpz_flog(tmp, t);

	if(b == 0) {
		param->n = prod;
	}  /* LWE */
	else {
		param->n = 1;
	} /* RLWE */

	param->bign = ceil((2 * param->n + 1) * fmpz_flog(param->q,t));

	fmpz_clear(tmp);
	return param;
}

void e_skeygen(fmpz_poly_mat_t sk, param_node_t *param)
{
        fmpz *coeffs = _fmpz_vec_init(d);
        fmpz_poly_t poly;
        fmpz_poly_init(poly);
        fmpz_poly_set_coeff_si(poly, 0, 1);
        fmpz_poly_set(fmpz_poly_mat_entry(sk, 0, 0), poly);
        long i;
        for( i = 1 ; i <= param->n ; i++ ) {
                guassian_poly(coeffs, fmpz_poly_mat_entry(sk, i, 0));
        }

        _fmpz_vec_clear(coeffs, d);
        fmpz_poly_clear(poly);
}

void e_pkeygen(fmpz_poly_mat_t pk, param_node_t *param, fmpz_poly_mat_t sk)
{
       // printf("pk1\n");
        fmpz_poly_mat_t ppk, ee, bb, ss, tmp, tmp1;
        fmpz_poly_mat_init(ppk, param->bign, param->n);
        fmpz_poly_mat_init(ee, param->bign, 1);
        fmpz_poly_mat_init(bb, param->bign, 1);
        fmpz_poly_mat_init(ss, param->n, 1);
        fmpz *coeffs = _fmpz_vec_init(d);

        long i, j;
       // printf("pk11\n");
        for( i = 0 ; i < param->n ; i++ ) {
                fmpz_poly_set(fmpz_poly_mat_entry(ss, i, 0), fmpz_poly_mat_entry(sk, i+1, 0 ));
               // printf("%ld\n",i);
        }
        for( i = 0 ; i < param->bign ; i++ ) {
                guassian_poly(coeffs, fmpz_poly_mat_entry(ee, i, 0));
                //printf("%ld\n",i);
        }
        for( i = 0 ; i < param->bign ; i++ ) {
                for( j = 0; j < param->n; j++ ){
                        unif_poly(fmpz_poly_mat_entry(ppk, i, j), param->q);
                }
                //printf("%ld\n",i);
        }
        fmpz_poly_mat_init(tmp, param->bign, 1);
        fmpz_poly_mat_init(tmp1, param->bign, 1);
       // printf("pk12\n");
        fmpz_poly_mat_mul(tmp, ppk, ss);
       // printf("pk13\n");
        fmpz_poly_mat_scalar_mul_fmpz(tmp1, ee, t);
        fmpz_poly_mat_add(bb, tmp, tmp1);
       // printf("pk2\n");
        for( i = 0 ; i < param->bign ; i++ ) {
                fmpz_poly_set(fmpz_poly_mat_entry(pk, i, 0), fmpz_poly_mat_entry(bb, i, 0));
        }
        for( i = 0 ; i < param->bign ; i++ ) {
                for( j = 1; j <= param->n; j++ ){
                        fmpz_poly_neg(fmpz_poly_mat_entry(pk, i, j), fmpz_poly_mat_entry(ppk, i, j-1));
                }
        }
       // printf("pk3\n");
        for( i = 0 ; i < param->bign ; i++) {
                for( j = 0; j < param->n + 1 ; j++) {
                        fmpz_poly_rem_basecase(fmpz_poly_mat_entry(pk, i, j), fmpz_poly_mat_entry(pk, i, j), fx);
                        fmpz_poly_scalar_smod_fmpz(fmpz_poly_mat_entry(pk, i, j), fmpz_poly_mat_entry(pk, i, j), param->q);
                }
        }
        // printf("pk4\n");
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
        fmpz_poly_mat_add(ct, mm, tmp);

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
        fmpz_poly_init(tmp);
        fmpz_poly_zero(ms);

        long i;
        
        fmpz_poly_mat_print(ct, "x");
        fmpz_poly_mat_print(sk, "x");
        for( i = 0 ; i < param->n + 1 ; i++) {
                fmpz_poly_mul(tmp, fmpz_poly_mat_entry(ct, 0, i), fmpz_poly_mat_entry(sk, i, 0));
                fmpz_poly_add(ms, ms, tmp);
                fmpz_poly_print(ms);
                printf("\n");
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
	//long qrow = xrow * len;
	long i, j, k;
	fmpz_mat_t bits;
	fmpz_mat_init(bits, d, len);
	fmpz_t hold;
	fmpz_init(hold);
	fmpz_poly_t xtmp;
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
			fmpz_poly_init(xtmp);
			for( k = 0; k < d ; k++ ) {
				fmpz_poly_set_coeff_fmpz(xtmp, k, fmpz_mat_entry(bits, k, j));
			}

			fmpz_poly_set(fmpz_poly_mat_entry(dc, i + j * xrow, 0), xtmp);
			fmpz_poly_clear(xtmp);
		}
	}
	fmpz_clear(hold);
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
			fmpz_poly_scalar_smod_fmpz(fmpz_poly_mat_entry(po, j + i * xrow, 0), fmpz_poly_mat_entry(po , j + i * xrow, 0), qq);
		}
	}
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

void bgv_set_level(int l)
{
        bgv_level = l;
}

int bgv_get_level()
{
        return bgv_level;
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

void bgv_vars_init()
{
	fmpz_init(bound);
	fmpz_init(t);
	fmpz_poly_init(fx);
}

void bgv_vars_clear()
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
		bytes = (unsigned char *) malloc (bytecount);
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
	hcrypt_random(randseed, 3/*len*/);
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
