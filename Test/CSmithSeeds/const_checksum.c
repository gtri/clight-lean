/* Fixed-signature checksum fixture exercising const-qualified scalar loads. */
#include "csmith_checksum_runtime.h"

const unsigned int value = 0x1A2BU;

int main(void) {
  csmith_checksum_print(value);
  return 0;
}
