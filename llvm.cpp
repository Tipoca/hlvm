#include "llvm/Target/TargetOptions.h"

extern "C" {

  void enable_tail_call_opt() {
    llvm::PerformTailCallOpt = true;
    // This has been renamed for LLVM 2.7 onwards:
    //llvm::GuaranteedTailCallOpt = true;
  }

}
