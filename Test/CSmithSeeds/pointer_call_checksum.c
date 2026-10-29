/* Fixed-signature checksum fixture exercising pointer arguments to functions. */
#include "csmith_checksum_runtime.h"

unsigned int target = 0x1A2AU;

static unsigned int bump(unsigned int *pointer) {
  *pointer = *pointer + 1U;
  return *pointer;
}

int main(void) {
  csmith_checksum_print(bump(&target));
  return 0;
}
