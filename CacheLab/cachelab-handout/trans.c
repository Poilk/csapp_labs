/* 
 * trans.c - Matrix transpose B = A^T
 *
 * Each transpose function must have a prototype of the form:
 * void trans(int M, int N, int A[N][M], int B[M][N]);
 *
 * A transpose function is evaluated by counting the number of misses
 * on a 1KB direct mapped cache with a block size of 32 bytes.
 */
#include <stdio.h>
#include "cachelab.h"

int is_transpose(int M, int N, int A[N][M], int B[M][N]);

/* 
 * transpose_submit - This is the solution transpose function that you
 *     will be graded on for Part B of the assignment. Do not change
 *     the description string "Transpose submission", as the driver
 *     searches for that string to identify the transpose function to
 *     be graded. 
 */
char transpose_submit_desc[] = "Transpose submission";
void transpose_submit(int M, int N, int A[N][M], int B[M][N]) {
  int v0, v1, v2, v3, v4, v5, v6, v7;

  if (M == 32 && N == 32) {
    for (int i8 = 0; i8 < N; i8 += 8) {
      for (int j8 = 0; j8 < M; j8 += 8) {
        if (i8 != j8) {
          for (int i = 0; i < 8; i++) {
            for (int j = 0; j < 8; j++) {
              B[j8 + j][i8 + i] = A[i8 + i][j8 + j];
            }
          }
        } else {
          for (int i = 0; i < 8; i++) {
            v0 = A[i8 + i][j8 + 0];
            v1 = A[i8 + i][j8 + 1];
            v2 = A[i8 + i][j8 + 2];
            v3 = A[i8 + i][j8 + 3];
            v4 = A[i8 + i][j8 + 4];
            v5 = A[i8 + i][j8 + 5];
            v6 = A[i8 + i][j8 + 6];
            v7 = A[i8 + i][j8 + 7];
            B[i8 + i][j8 + 0] = v0;
            B[i8 + i][j8 + 1] = v1;
            B[i8 + i][j8 + 2] = v2;
            B[i8 + i][j8 + 3] = v3;
            B[i8 + i][j8 + 4] = v4;
            B[i8 + i][j8 + 5] = v5;
            B[i8 + i][j8 + 6] = v6;
            B[i8 + i][j8 + 7] = v7;
          }
          for (int i = 0; i < 8; i++) {
            for (int j = i + 1; j < 8; j++) {
              v0 = B[i8 + i][j8 + j];
              B[i8 + i][j8 + j] = B[j8 + j][i8 + i];
              B[j8 + j][i8 + i] = v0;
            }
          }
        }
      }
    }
  } else if (M == 64 && N == 64) {
    for (int j8 = 0; j8 < N; j8 += 8) {
      //diagonal
      {
        int j_shift = j8 == 0 ? 8 : 0;
        for (int i = 0; i < 4; i++) {
          for (int j = 0; j < 8; j++) {
            B[j8 + i][j_shift + j] = A[j8 + 4 + i][j8 + j];
          }
        }
        for (int i = 0; i < 4; i++) {
          v0 = A[j8 + i][j8 + 0];
          v1 = A[j8 + i][j8 + 1];
          v2 = A[j8 + i][j8 + 2];
          v3 = A[j8 + i][j8 + 3];
          v4 = A[j8 + i][j8 + 4];
          v5 = A[j8 + i][j8 + 5];
          v6 = A[j8 + i][j8 + 6];
          v7 = A[j8 + i][j8 + 7];
          B[j8 + i][j8 + 0] = v0;
          B[j8 + i][j8 + 1] = v1;
          B[j8 + i][j8 + 2] = v2;
          B[j8 + i][j8 + 3] = v3;
          v0 = B[j8 + 0][j_shift + i];
          v1 = B[j8 + 1][j_shift + i];
          v2 = B[j8 + 2][j_shift + i];
          v3 = B[j8 + 3][j_shift + i];
          B[j8 + i][j8 + 4] = v0;
          B[j8 + i][j8 + 5] = v1;
          B[j8 + i][j8 + 6] = v2;
          B[j8 + i][j8 + 7] = v3;
          B[j8 + 0][j_shift + i] = v4;
          B[j8 + 1][j_shift + i] = v5;
          B[j8 + 2][j_shift + i] = v6;
          B[j8 + 3][j_shift + i] = v7;
        }
        for (int i = 0; i < 4; i++) {
          for (int j = i + 1; j < 4; j++) {
            v0 = B[j8 + i][j8 + j];
            B[j8 + i][j8 + j] = B[j8 + j][j8 + i];
            B[j8 + j][j8 + i] = v0;
          }
        }
        for (int i = 0; i < 4; i++) {
          for (int j = 0; j < 8; j++) {
            B[j8 + 4 + i][j8 + j] = B[j8 + i][j_shift + j];
          }
        }
        for (int i = 0; i < 4; i++) {
          for (int j = i + 1; j < 4; j++) {
            v0 = B[j8 + 4 + i][j8 + 4 + j];
            B[j8 + 4 + i][j8 + 4 + j] = B[j8 + 4 + j][j8 + 4 + i];
            B[j8 + 4 + j][j8 + 4 + i] = v0;
          }
        }
      }
      //not diagonal
      for (int i8 = 0; i8 < M; i8 += 8) {
        if (i8 == j8)continue;
        for (int i = 0; i < 4; i++) {
          for (int j = 0; j < 4; j++) {
            B[j8 + j][i8 + i] = A[i8 + i][j8 + j];
          }
        }
        for (int i = 0; i < 4; i++) {
          for (int j = 0; j < 4; j++) {
            B[j8 + j][i8 + 4 + i] = A[i8 + i][j8 + 4 + j];
          }
        }
        for (int i = 0; i < 4; i++) {
          v0 = B[j8 + i][i8 + 4 + 0];
          v1 = B[j8 + i][i8 + 4 + 1];
          v2 = B[j8 + i][i8 + 4 + 2];
          v3 = B[j8 + i][i8 + 4 + 3];
          B[j8 + i][i8 + 4 + 0] = A[i8 + 4 + 0][j8 + i];
          B[j8 + i][i8 + 4 + 1] = A[i8 + 4 + 1][j8 + i];
          B[j8 + i][i8 + 4 + 2] = A[i8 + 4 + 2][j8 + i];
          B[j8 + i][i8 + 4 + 3] = A[i8 + 4 + 3][j8 + i];
          B[j8 + 4 + i][i8 + 0] = v0;
          B[j8 + 4 + i][i8 + 1] = v1;
          B[j8 + 4 + i][i8 + 2] = v2;
          B[j8 + 4 + i][i8 + 3] = v3;
          B[j8 + 4 + i][i8 + 4] = A[i8 + 4 + 0][j8 + 4 + i];
          B[j8 + 4 + i][i8 + 5] = A[i8 + 4 + 1][j8 + 4 + i];
          B[j8 + 4 + i][i8 + 6] = A[i8 + 4 + 2][j8 + 4 + i];
          B[j8 + 4 + i][i8 + 7] = A[i8 + 4 + 3][j8 + 4 + i];
        }
      }
    }
  } else if( M == 61 && N == 67){
#define block_size 8
    for (int i8 = 0; i8 < N; i8 += block_size) {
      for (int j8 = 0; j8 < M; j8 += block_size) {
        for (int i = 0; i < block_size && i8 + i < N; i++) {
          if ( j8 + block_size >= M){
            //for (int j = 0; j < block_size && j8 + j < M; j++) {
            //  B[j8 + j][i8 + i] = A[i8 + i][j8 + j];
            //}
            v0 = A[i8 + i][j8 + 0];
            v1 = A[i8 + i][j8 + 1];
            v2 = A[i8 + i][j8 + 2];
            v3 = A[i8 + i][j8 + 3];
            v4 = A[i8 + i][j8 + 4];
            //v5 = A[i8 + i][j8 + 5];
            //v6 = A[i8 + i][j8 + 6];
            //v7 = A[i8 + i][j8 + 7];
            B[j8 + 0][i8 + i] = v0;
            B[j8 + 1][i8 + i] = v1;
            B[j8 + 2][i8 + i] = v2;
            B[j8 + 3][i8 + i] = v3;
            B[j8 + 4][i8 + i] = v4;
            //B[j8 + 5][i8 + i] = v5;
            //B[j8 + 6][i8 + i] = v6;
            //B[j8 + 7][i8 + i] = v7;
          } else{
            v0 = A[i8 + i][j8 + 0];
            v1 = A[i8 + i][j8 + 1];
            v2 = A[i8 + i][j8 + 2];
            v3 = A[i8 + i][j8 + 3];
            v4 = A[i8 + i][j8 + 4];
            v5 = A[i8 + i][j8 + 5];
            v6 = A[i8 + i][j8 + 6];
            v7 = A[i8 + i][j8 + 7];
            B[j8 + 0][i8 + i] = v0;
            B[j8 + 1][i8 + i] = v1;
            B[j8 + 2][i8 + i] = v2;
            B[j8 + 3][i8 + i] = v3;
            B[j8 + 4][i8 + i] = v4;
            B[j8 + 5][i8 + i] = v5;
            B[j8 + 6][i8 + i] = v6;
            B[j8 + 7][i8 + i] = v7;
          }
        }
      }
    }
  }
}

/* 
 * You can define additional transpose functions below. We've defined
 * a simple one below to help you get started. 
 */ 

/* 
 * trans - A simple baseline transpose function, not optimized for the cache.
 */
char trans_desc[] = "Simple row-wise scan transpose";
void trans(int M, int N, int A[N][M], int B[M][N]) {
  int i, j, tmp;

  for (i = 0; i < N; i++) {
    for (j = 0; j < M; j++) {
      tmp = A[i][j];
      B[j][i] = tmp;
    }
  }

}

/*
 * registerFunctions - This function registers your transpose
 *     functions with the driver.  At runtime, the driver will
 *     evaluate each of the registered functions and summarize their
 *     performance. This is a handy way to experiment with different
 *     transpose strategies.
 */
void registerFunctions() {
  /* Register your solution function */
  registerTransFunction(transpose_submit, transpose_submit_desc);

  /* Register any additional transpose functions */
  registerTransFunction(trans, trans_desc);
}

/* 
 * is_transpose - This helper function checks if B is the transpose of
 *     A. You can check the correctness of your transpose by calling
 *     it before returning from the transpose function.
 */
int is_transpose(int M, int N, int A[N][M], int B[M][N]) {
  int i, j;

  for (i = 0; i < N; i++) {
    for (j = 0; j < M; ++j) {
      if (A[i][j] != B[j][i]) {
        return 0;
      }
    }
  }
  return 1;
}

