/* Fixed-signature checksum fixture exercising initialized global array access. */
#include "csmith_checksum_runtime.h"

unsigned int values[3] = { 1U, 2U, 0x1A2BU };

int main(void) {
  values[1] = values[1] + values[0];
  csmith_checksum_print(values[2] + values[1]);
  return 0;
}
