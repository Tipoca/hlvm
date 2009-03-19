#include <stdio.h>
#include <stdlib.h>

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
