/* Fixed-signature checksum fixture exercising uint64_t-style arithmetic. */
#include "csmith_checksum_runtime.h"

unsigned long long value = 0x123456789ABCDEF0ULL;

int main(void) {
  value = (value * 3ULL) / 3ULL;
  value = value + 0x10ULL;
  csmith_checksum_print((unsigned int)value);
  return 0;
}
