/* Fixed-signature checksum fixture exercising uint8_t storage and narrowing. */
#include "csmith.h"
#include "csmith_checksum_runtime.h"

uint8_t value = 0xFEU;

int main(void) {
  value = (uint8_t)(value + 3U);
  csmith_checksum_print((uint32_t)value);
  return 0;
}
