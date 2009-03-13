#include "llvm-c/Core.h"
#include "caml/alloc.h"
#include "caml/custom.h"
#include "caml/memory.h"
#include "caml/fail.h"
#include "caml/callback.h"
#include "llvm/Config/config.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#define Builder_val(v)  (*(LLVMBuilderRef *)(Data_custom_val(v)))

CAMLprim LLVMValueRef llvm_build_extractvalue(LLVMValueRef Agg,
                                              value Idx,
                                              value Name, value B) {
  return LLVMBuildExtractValue(Builder_val(B),
			       Agg, Int_val(Idx),
			       String_val(Name));
}

CAMLprim LLVMValueRef llvm_build_insertvalue(LLVMValueRef Agg,
                                             LLVMValueRef Elt,
                                             value Idx,
                                             value Name, value B) {
  return LLVMBuildInsertValue(Builder_val(B),
			      Agg, Elt, Int_val(Idx),
                              String_val(Name));
}

extern void enable_tail_call_opt();

CAMLprim void llvm_enable_tail_call_opt() {
  enable_tail_call_opt();
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
