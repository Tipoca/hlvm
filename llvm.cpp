#include "llvm/Target/TargetOptions.h"

extern "C" {

  void enable_tail_call_opt() {
    llvm::PerformTailCallOpt = true;
  }
  
}
