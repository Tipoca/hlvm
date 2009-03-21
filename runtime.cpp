#include <cstdio>
#include <cstdlib>
#include <sys/time.h>

extern "C" {

double hlvm_time() {
  struct timeval t;
  gettimeofday(&t, NULL);
  return (double)t.tv_sec + 1e-6 * (double)t.tv_usec;
}

void *hlvm_alloc(int n, int m) {
  if (n*m == 0) return 0;
  void *data = calloc(n, m);
  if (data == 0) {
    printf("Out of memory\n");
    exit(1);
  }
  return data;
}

void hlvm_free(void *n) {
  if (n != 0) free(n);
}

}
