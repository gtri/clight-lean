/* Fixed-signature checksum fixture exercising whole-struct assignment. */
#include "csmith_checksum_runtime.h"

struct pair {
  unsigned int left;
  unsigned int right;
};

struct pair source = { 0x1A2AU, 1U };
struct pair destination;

int main(void) {
  destination = source;
  csmith_checksum_print(destination.left + destination.right);
  return 0;
}
