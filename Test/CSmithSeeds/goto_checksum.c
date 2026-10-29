/* Fixed-signature checksum fixture exercising a forward goto and label. */
#include "csmith_checksum_runtime.h"

unsigned int value = 0U;

int main(void) {
  goto checksum_value;
  value = 99U;

checksum_value:
  value = value + 0x1A2BU;
  csmith_checksum_print(value);
  return 0;
}
