#pragma once
#define __mm256 float*

/*@
predicate zeroed(float* A, integer b, integer e) = \forall integer i; b <= i < e ==> A[i] == 0;

inductive zeroed_ind(float* a, integer b, integer e){
case zeroed_empty:
    \forall float* a, integer b, e; b >= e ==> zeroed_ind(a, b, e);
case zeroed_range:
    \forall float* a, integer b, e; b < e ==>
    zeroed_ind(a, b, e-1) && a[e-1] == 0 ==> zeroed_ind(a,b,e);
}


*/

/*
lemma zeroed_lin_to_ind:
    \forall float *a, integer b, integer e; zeroed(a, b, e) ==> zeroed_ind(a, b, e);

lemma zeroed_ind_to_lin:
    \forall float *a, integer b, integer e; zeroed_ind(a, b, e) ==> zeroed(a, b, e);
*/

__mm256 REG1; // __mm256_setzero_ps
__mm256 REG2; // __mm256_set1_ps
__mm256 REG3; // __mm256_loadu_ps
__mm256 REG4; // __mm256_fmadd_ps

int COUNTER1 = 0; // __mm256_setzero_ps
int COUNTER2 = 0; // __mm256_set1_ps
int COUNTER3 = 0; // __mm256_loadu_ps
int COUNTER4 = 0; // __mm256_fmadd_ps

/*@
requires \valid(REG1 + (COUNTER1 * 8 .. COUNTER1 * 8 + 7));
requires COUNTER1 >= 0;
assigns REG1[COUNTER1 * 8 .. COUNTER1 * 8 + 7], COUNTER1;
ensures \forall integer i; 0 <= i <= 7 ==> \result[i] == 0.0;
ensures \result == REG1 + COUNTER1 * 8;
ensures COUNTER1 == 1 + \old(COUNTER1);
ensures \valid(\result + (0 .. 7));

assigns \result \from \nothing;
*/
__mm256 _mm256_setzero_ps();

/*@
requires \valid(REG2 + (COUNTER2 * 8 .. COUNTER2 * 8 + 7));
requires COUNTER2 >= 0;
assigns REG2[COUNTER2 * 8 .. COUNTER2 * 8 + 7];
ensures \forall integer i; 0 <= i <= 7 ==> \result[i] == v;
ensures \result == REG2 + COUNTER2 * 8;
ensures COUNTER2 == 1 + \old(COUNTER2);
ensures \valid(\result + (0 .. 7));
*/
__mm256 _mm256_set1_ps(float v);

/*@
requires \valid(REG3 + (COUNTER3 * 8 .. COUNTER3 * 8 + 7));
requires \valid_read(a + (0 .. 7));
requires COUNTER3 >= 0;
requires \separated(a + (0 .. 7), REG3 + (COUNTER3 * 8 .. COUNTER3 * 8 + 7));
assigns REG3[COUNTER3 * 8 .. COUNTER3 * 8 + 7];
ensures \forall integer i; 0 <= i <= 7 ==> \result[i] == a[i];
ensures \result == REG3 + COUNTER3 * 8;
ensures COUNTER3 == 1 + \old(COUNTER3);
ensures \valid(\result + (0 .. 7));
*/
__mm256 _mm256_loadu_ps(float* a);

/*@
requires \valid(mem_addr + (0 .. 7));

ensures zeroed(mem_addr, 0, 8);
ensures \valid(mem_addr + (0 .. 7));

assigns mem_addr[0 .. 7];
*/
void setZero(float *mem_addr);


/*@
requires \valid(mem_addr + (0 .. 7));
requires \valid_read(a + (0 .. 7));
assigns mem_addr[0 .. 7];
ensures \forall integer i; 0 <= i <= 7 ==> mem_addr[i] == a[i];
ensures \valid(mem_addr + (0 .. 7));
ensures mem_addr == \old(mem_addr);
*/
void _mm256_storeu_ps(float * mem_addr, __mm256 a);


/*@
requires \valid_read(a + (0 .. 7));
requires \valid_read(b + (0 .. 7));
requires \valid_read(c + (0 .. 7));
requires \valid(REG4 + (COUNTER4 * 8 .. COUNTER4 * 8 + 7));
requires \separated(a + (0 .. 7), REG4 + (COUNTER4 * 8 .. COUNTER4 * 8 + 7));
requires \separated(b + (0 .. 7), REG4 + (COUNTER4 * 8 .. COUNTER4 * 8 + 7));
requires \separated(c + (0 .. 7), REG4 + (COUNTER4 * 8 .. COUNTER4 * 8 + 7));
requires COUNTER4 >= 0;
assigns REG4[COUNTER4 * 8 .. COUNTER4 * 8 + 7];
ensures \forall integer i; 0 <= i < 8 ==> \result[i] == a[i] * b[i] + c[i];
ensures \result == REG4 + COUNTER4 * 8;
ensures COUNTER4 == 1 + \old(COUNTER4);
ensures \valid(\result + (0 .. 7));
*/
__mm256 _mm256_fmadd_ps(__mm256 a, __mm256 b, __mm256 c);
