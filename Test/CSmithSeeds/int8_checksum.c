/* Fixed-signature checksum fixture exercising int8_t sign extension. */
#include "csmith.h"
#include "csmith_checksum_runtime.h"

int8_t value = -2;

int main(void) {
  value = (int8_t)(value - 3);
  csmith_checksum_print((uint32_t)(int32_t)value);
  return 0;
}
