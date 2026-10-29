/* Fixed-signature checksum fixture exercising signed 64-bit division/casts. */
#include "csmith_checksum_runtime.h"

long long value = -0x123456789LL;

int main(void) {
  value = (value * 6LL) / 3LL;
  csmith_checksum_print((unsigned int)value);
  return 0;
}
