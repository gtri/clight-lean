/* Fixed-signature checksum fixture exercising ordered float comparison. */
#include "csmith_checksum_runtime.h"

float left = 1.5f;
float right = 2.25f;

int main(void) {
  unsigned int result = 0U;
  if (left < right) {
    result = 7U;
  }
  csmith_checksum_print(result);
  return 0;
}
