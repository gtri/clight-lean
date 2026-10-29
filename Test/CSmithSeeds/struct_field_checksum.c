/* Fixed-signature checksum fixture exercising initialized struct field access. */
#include "csmith_checksum_runtime.h"

struct pair {
  unsigned int left;
  unsigned int right;
};

struct pair value = { 0x1A2AU, 0U };

int main(void) {
  value.right = value.left + 1U;
  csmith_checksum_print(value.right);
  return 0;
}
