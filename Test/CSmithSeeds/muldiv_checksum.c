/* Fixed-signature checksum fixture exercising defined unsigned div/mul. */
#include "csmith_checksum_runtime.h"

unsigned int value = 84U;

int main(void) {
  value = (value / 7U) * 3U;
  csmith_checksum_print(value);
  return 0;
}
