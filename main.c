#include "immintrin.h"

/*@
  axiomatic MatrixMult
  {
    inductive DotProduction(float* A, float* B, integer to, 
                                   integer i, integer K, integer j, integer N, real res)
	{
    case dotproduction_empty_range:
      \forall float* A, float* B, integer to, integer i, integer K, integer j, integer N;
      0 >= to ==> DotProduction(A, B, to, i, K, j, N, 0.0);

    case dotproduction_positive_range:
      \forall float* A, float* B, integer to, integer i, integer K, integer j, integer N, real res;
      (0 < to) &&
      DotProduction(A, B, to-1, i, K, j, N, res) ==> 
      DotProduction(A, B, to, i, K, j, N, res + A[i*K + (to-1)] * B[(to-1)*N + j]);
      
	}      
    inductive RowResult{L2}(float* A, float* B, float* C, integer to, 
                                integer i, integer K, integer N) 
    {
      case rowresult_empty{L2}:
        \forall float* A, float* B, float* C, integer to, integer i, integer K, integer N; 
        0 >= to ==> RowResult{L2}(A, B, C, to, i, K, N);

      case rowresult_step{L2}:
        \forall float* A, float* B, float* C, integer to, integer i, integer K, integer N; 
        0 < to &&
        RowResult{L2}(A, B, C, to-1, i, K, N) && 
        DotProduction(A, B, K, i, K, (to-1), N, \at(C[i*N + (to-1)], L2))
        ==> RowResult{L2}(A, B, C, to, i, K, N);
    }
       
    inductive MatrixResult{L2}(float* A, float* B, float* C, integer to, 
                                   integer K, integer N, integer M) 
    {
      case matrixresult_empty{L2}:
        \forall float* A, float* B, float* C, integer to, integer K, integer N, integer M; 
        0 >= to ==> MatrixResult{L2}(A, B, C, to, K, N, M);

      case matrixresult_step{L2}:
        \forall float* A, float* B, float* C, integer to, integer K, integer N, integer M;
        0 < to &&
        MatrixResult{L2}(A, B, C, to-1, K, N, M) && 
        RowResult{L2}(A, B, C, N, to-1, K, N)
        ==> MatrixResult{L2}(A, B, C, to, K, N, M);
    }
  }
*/

/*@
lemma zeroed_contat:
  \forall float *A, integer b, integer c, integer d; b < c < d && zeroed(A, b, c) && zeroed(A, c, d) ==> zeroed(A, b, d);

lemma zeroed_succ:
  \forall float *A, integer b, integer e; b < e && zeroed(A, b, e) && A[e] == 0 ==> zeroed(A, b, e+1);

lemma zeroed_last:
  \forall float *A, integer b, integer e; b < e+1 && zeroed(A, b, e+1) ==> A[e] == 0;

lemma zeroed_first:
  \forall float *A, integer b, integer e; b < e && zeroed(A, b, e) ==> A[b] == 0;

lemma eq_index:
  \forall float *A, integer j, integer k; A + k + j == A + j + k;

lemma eq_cells:
  \forall float *A, integer shift, integer b; (A + shift)[b] == A[shift + b];

lemma zeroed_shift_0:
  \forall float *A, integer b, integer e, integer shift; shift == 0 && zeroed(A+shift, b, e) 
    ==> zeroed(A, b+shift, e+shift);

lemma eq_cells_all:
  \forall float *A, integer b, integer e, integer i; b <= i < e ==> (A + b)[i] == A[b + i];

lemma shiftAAAAAA: 
  \forall float *A, integer b, integer e, integer shift, integer i; b <= i < e && (A + shift)[i] == 0 
    ==> A[i + shift] == 0;

lemma zeroed_shift_comm:
  \forall float *A, integer shift, integer b, integer e; shift >= 0 && 0 <= b < e && zeroed(A+shift, b, e) 
  ==> zeroed(A, b+shift, e+shift);

lemma zeroed_shift:
  \forall float *A, integer shift, integer b, integer e; shift >= 0 && 0 <= b < e && zeroed(A+shift, b, e) 
  ==> zeroed(A, shift+b, shift+e);

lemma zeroed_shift_comm_inv:
  \forall float *A, integer shift, integer b, integer e; shift >= 0 && 0 <= b < e && zeroed(A, b+shift, e+shift) 
  ==> zeroed(A+shift, b, e);

lemma zeroed_shift_inv:
  \forall float *A, integer shift, integer b, integer e; shift >= 0 && 0 <= b < e && zeroed(A, shift+b, shift+e)
  ==> zeroed(A+shift, b, e);

lemma zeroed_0_8:
  \forall float *c, integer j; j >= 0 && zeroed(c+j, 0, 8)
  ==> zeroed(c, j+0, j+8);
*/

/*@
  lemma math_bounds:
    \forall integer i, M, N;
    0 <= i < M && 0 < N ==> 0 <= i*N && i*N + N <= M*N;

  lemma div8:
    \forall integer m; m % 16 == 0 ==> m % 8 == 0;

*/

/*@
  requires COUNTER1 == 0;
  requires COUNTER2 == 0;
  requires COUNTER3 == 0;
  requires COUNTER4 == 0;
  requires \valid_read(A + (0 .. M*K-1));
  requires \valid_read(B + (0 .. K*N-1));
  requires \valid(C + (0 .. M*N-1));
  requires \forall integer i; \valid(REG1 + (i * 8 .. i * 8 + 7));
  requires \forall integer i; \valid(REG2 + (i * 8 .. i * 8 + 7));
  requires \forall integer i; \valid(REG3 + (i * 8 .. i * 8 + 7));
  requires \forall integer i; \valid(REG4 + (i * 8 .. i * 8 + 7));
  requires \forall integer i, j, k, l; \separated(REG1 + (i * 8 .. i * 8 + 7), REG2 + (j * 8 .. j * 8 + 7), REG3 + (k * 8 .. k * 8 + 7), REG4 + (l * 8 .. l * 8 + 7), A + (0 .. M*K-1), C + (0 .. M*N-1));
  requires \forall integer i, j, k, l; \separated(REG1 + (i * 8 .. i * 8 + 7), REG2 + (j * 8 .. j * 8 + 7), REG3 + (k * 8 .. k * 8 + 7), REG4 + (l * 8 .. l * 8 + 7), B + (0 .. K*N-1), C + (0 .. M*N-1));
  requires M > 0 && N > 0 && K > 0;
  requires N % 16 == 0;

  ensures MatrixResult{Post}(A, B, C, M, K, N, M);
*/
void gemm_v2(int M, int N, int K, const float * A, const float * B, float * C)
{
    /*@
      loop invariant \at(N, Pre) == N;
      loop invariant \at(M, Pre) == M;
      loop invariant \at(K, Pre) == K;
      loop invariant 0 <= i <= M;
      loop invariant N % 16 == 0;
      loop invariant MatrixResult{Here}(A, B, C, i, K, N, M);
      loop invariant COUNTER1 >= 0;
      loop invariant COUNTER2 >= 0;
      loop invariant \valid(C + (0 .. M*N-1));
      
      loop variant M-i;
    */
    for (int i = 0; i < M; ++i)
    {
        float * c = C + i * N;
        /*@
          loop invariant \at(N, Pre) == N;
          loop invariant \at(M, Pre) == M;
          loop invariant \at(K, Pre) == K;
          loop invariant N % 16 == 0;
          loop invariant 0 <= j <= N;
          loop invariant j % 8 == 0;
          loop invariant 0 <= i < M;
          loop invariant zeroed(C, i*N, i*N + j);
          loop invariant COUNTER1 >= 0;
          loop invariant \valid(C + (0 .. M*N-1));
          loop invariant c == C + i*N;

          loop variant N-j;
        */
        for (int j = 0; j < N; j += 8)
        {
          /*@ assert \valid(c + j + 0 + (0 .. 7)); */
          /*@ assert zeroed(C, i*N, i*N + j); */
          /*@ assert C[i*N] == 0; */

          // __mm256 tmp = _mm256_setzero_ps();
          /* assert C[i*N] == 0; */
          /* assert zeroed(C, i*N, i*N + j); */
          // _mm256_storeu_ps(c + j + 0, tmp);

          setZero(c + j);
          /*@ assert zeroed(c+j, 0, 8); */
          int q = 7;
          /*@ assert zeroed(c, j+0, j+8); */
          /*@ assert *(c + j) == 0; */
          /*@ assert c == C + i*N; */
          /*@ assert zeroed(C, i*N + j, i*N + j + 8); */

          /*@ assert zeroed(C, i*N, i*N + j+1); */
          /*@ assert zeroed(C + i*N, 0, j+1); */

          /*@ assert C[i*N + j + 0] == 0; */
          /*@ assert zeroed(C, i*N, i*N + j + 1); */

          /*@ assert C[i*N + j + 1] == 0; */
          /*@ assert i*N < i*N+j+1 && zeroed(C, i*N, i*N + j + 1) && C[i*N+j+1] == 0; */
          /*@ assert zeroed(C, i*N, i*N + j + 2); */

          /*@ assert C[i*N + j + 2] == 0; */
          /*@ assert i*N < i*N+j+2 && zeroed(C, i*N, i*N + j + 2) && C[i*N+j+2] == 0; */
          /*@ assert zeroed(C, i*N, i*N + j + 3); */

          /*@ assert C[i*N + j + 3] == 0; */
          /*@ assert i*N < i*N+j+2 && zeroed(C, i*N, i*N + j + 2) && C[i*N+j+2] == 0; */
          /*@ assert zeroed(C, i*N, i*N + j + 3); */

          /*@ assert C[i*N + j + 3] == 0; */
          /*@ assert i*N < i*N+j+3 && zeroed(C, i*N, i*N + j + 3) && C[i*N+j+3] == 0; */
          /*@ assert zeroed(C, i*N, i*N + j + 4); */

          /*@ assert C[i*N + j + 4] == 0; */
          /*@ assert i*N < i*N+j+4 && zeroed(C, i*N, i*N + j + 4) && C[i*N+j+4] == 0; */
          /*@ assert zeroed(C, i*N, i*N + j + 5); */

          /*@ assert C[i*N + j + 5] == 0; */
          /*@ assert i*N < i*N+j+5 && zeroed(C, i*N, i*N + j + 5) && C[i*N+j+5] == 0; */
          /*@ assert zeroed(C, i*N, i*N + j + 6); */

          /*@ assert C[i*N + j + 6] == 0; */
          /*@ assert i*N < i*N+j+6 && zeroed(C, i*N, i*N + j + 6) && C[i*N+j+6] == 0; */
          /*@ assert zeroed(C, i*N, i*N + j + 7); */

          /*@ assert C[i*N + j + 7] == 0; */
          /*@ assert i*N < i*N+j+7 && zeroed(C, i*N, i*N + j + 7) && C[i*N+j+7] == 0; */
          /* assert zeroed(C, i*N, i*N + j + 8); */
        }
        /*@ assert zeroed(C, i*N, i*N + N);*/ 


        /*@
            loop invariant \at(N, Pre) == N;
            loop invariant \at(M, Pre) == M;
            loop invariant \at(K, Pre) == K;
            loop invariant 0 <= k <= K;
            loop invariant 0 <= i < M;
			      loop invariant \forall integer l; 0<=l<N ==> DotProduction(A, B, k, i, K, l, N, c[l]);
            loop invariant COUNTER2 >= 0;
            loop invariant \valid(C + (0 .. M*N-1));

            loop variant K-k;
        */
        for (int k = 0; k < K; ++k)
        {
            const float * b = B + k * N;
            __mm256 a = _mm256_set1_ps(A[i*K + k]);
            /*@
                loop invariant \at(N, Pre) == N;
                loop invariant \at(M, Pre) == M;
                loop invariant \at(K, Pre) == K;
                loop invariant 0 <= j <= N;
                loop invariant 0 <= k < K;
                loop invariant 0 <= i < M;
                loop invariant j % 16 == 0;
                loop invariant \forall integer q; 0 <= q < j ==> DotProduction(A, B, k+1, i, K, q, N, c[q]);
                loop invariant \forall integer q; j <= q < N ==> DotProduction(A, B, k, i, K, q, N, c[q]);
                loop invariant \valid(C + (0 .. M*N-1));

                loop variant N-j;
            */
            for (int j = 0; j < N; j += 16)
            {
               /*@ assert step0: DotProduction(A, B, k+1, i, K, j, N, c[j]+a[0]*b[j]); */
               /*@ assert step1: DotProduction(A, B, k+1, i, K, j+1, N, c[j+1]+a[1]*b[j+1]); */
               /*@ assert step2: DotProduction(A, B, k+1, i, K, j+2, N, c[j+2]+a[2]*b[j+2]); */
               /*@ assert step3: DotProduction(A, B, k+1, i, K, j+3, N, c[j+3]+a[3]*b[j+3]); */
               /*@ assert step4: DotProduction(A, B, k+1, i, K, j+4, N, c[j+4]+a[4]*b[j+4]); */
               /*@ assert step5: DotProduction(A, B, k+1, i, K, j+5, N, c[j+5]+a[5]*b[j+5]); */
               /*@ assert step6: DotProduction(A, B, k+1, i, K, j+6, N, c[j+6]+a[6]*b[j+6]); */
               /*@ assert step7: DotProduction(A, B, k+1, i, K, j+7, N, c[j+7]+a[7]*b[j+7]); */
                _mm256_storeu_ps(c + j + 0, _mm256_fmadd_ps(a, 
                    _mm256_loadu_ps(b + j + 0), _mm256_loadu_ps(c + j + 0)));
               /*@ assert step8: DotProduction(A, B, k+1, i, K, j+8, N, c[j+8]+a[0]*b[j+8]); */
               /*@ assert step9: DotProduction(A, B, k+1, i, K, j+9, N, c[j+9]+a[1]*b[j+9]); */
               /*@ assert step10: DotProduction(A, B, k+1, i, K, j+10, N, c[j+10]+a[2]*b[j+10]); */
               /*@ assert step11: DotProduction(A, B, k+1, i, K, j+11, N, c[j+11]+a[3]*b[j+11]); */
               /*@ assert step12: DotProduction(A, B, k+1, i, K, j+12, N, c[j+12]+a[4]*b[j+12]); */
               /*@ assert step13: DotProduction(A, B, k+1, i, K, j+13, N, c[j+13]+a[5]*b[j+13]); */
               /*@ assert step14: DotProduction(A, B, k+1, i, K, j+14, N, c[j+14]+a[6]*b[j+14]); */
               /*@ assert step15: DotProduction(A, B, k+1, i, K, j+15, N, c[j+15]+a[7]*b[j+15]); */
                _mm256_storeu_ps(c + j + 8, _mm256_fmadd_ps(a, 
                    _mm256_loadu_ps(b + j + 8), _mm256_loadu_ps(c + j + 8)));
            }
            /*@ assert dot_done:  \forall integer l; 0<=l<N ==> DotProduction(A, B, k+1, i, K, l, N, c[l]);*/
        }
        /*@ assert row_done: RowResult{Here}(A, B, C, N, i, K, N); */
        /*@ assert mat_step: MatrixResult{Here}(A, B, C, i+1, K, N, M); */
        /*@ assert \at(M, Pre) == M; */
        /*@ assert \at(K, Pre) == K; */
    }
}