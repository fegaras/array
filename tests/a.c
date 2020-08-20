#include <stdlib.h>
#include <stdio.h>
#include <time.h>

int main ( int argc, char* argv[] ) {
  int n = atol(argv[1]);
  int* A = (int*)malloc(n*sizeof(int));
  float v = 0;

  printf("n = %d\n",n);

  clock_t t = clock();

  for ( int k = 0; k < 10; k++ )
    for ( long i = 0; i < n; i++ )
      v = 0.3*A[i]+1.2;

  printf("for: %f   %f\n",v,(double)(clock()-t)/CLOCKS_PER_SEC/10.0);

  t = clock();

  for ( int k = 0; k < 10; k++ ) {
     long i = 0;
     while (i < n) {
        v = 0.3*A[i]+1.2;
        i++;
     }
  }

  printf("while: %f   %f\n",v,(double)(clock()-t)/CLOCKS_PER_SEC/10.0);

  return 0;
}
