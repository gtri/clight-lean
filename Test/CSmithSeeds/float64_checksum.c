/* Fixed-signature checksum fixture exercising double arithmetic and narrowing. */
#include "csmith_checksum_runtime.h"

double value = 1.5;

int main(void) {
  value = (value + 2.25) * 4.0 / 1.5;
  csmith_checksum_print((unsigned int)value);
  return 0;
}
