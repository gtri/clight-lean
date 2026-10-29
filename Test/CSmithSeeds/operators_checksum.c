/* Fixed-signature checksum fixture for frontend-normalized operators. */
#include "csmith_checksum_runtime.h"

unsigned int value = 0U;
unsigned int aux = 0U;

int main(void) {
  value += 2U;
  aux = value++;
  aux = ++value;
  (aux = value + 1U, value = value + 2U);
  aux = (value--, value);
  aux = --value;
  value = +value;
  csmith_checksum_print(value);
  return 0;
}
