/*@
axiomatic MatrixMult {

  predicate zeroed(float* a, integer b, integer e) = \forall integer k; b <= k < e ==> a[k] == 0.0;

  inductive DotProduction(float* A, float* B, integer to,
                          integer i, integer K, integer j, integer N, real res) {
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
                          integer i, integer K, integer N) {
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
                             integer K, integer N, integer M) {
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
