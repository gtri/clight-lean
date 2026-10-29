/* Fixed-signature checksum fixture exercising initialized global storage. */
#include "csmith_checksum_runtime.h"

unsigned int crc = 0x1A2B;

int main(void) {
  crc = crc + 1U;
  csmith_checksum_print(crc);
  return 0;
}
