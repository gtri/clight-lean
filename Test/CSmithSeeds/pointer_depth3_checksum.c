/* Fixed-signature checksum fixture exercising three levels of indirection. */
#include "csmith_checksum_runtime.h"

unsigned int target = 0x1A2AU;
unsigned int *level1 = &target;
unsigned int **level2 = &level1;
unsigned int ***level3 = &level2;

int main(void) {
  ***level3 = ***level3 + 1U;
  csmith_checksum_print(***level3);
  return 0;
}
