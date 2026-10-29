/* Fixed-signature checksum fixture exercising global pointer initialization. */
#include "csmith_checksum_runtime.h"

unsigned int target = 0x1A2AU;
unsigned int *alias = &target;

int main(void) {
  *alias = *alias + 1U;
  csmith_checksum_print(*alias);
  return 0;
}
