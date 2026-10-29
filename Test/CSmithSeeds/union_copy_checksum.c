/* Fixed-signature checksum fixture exercising whole-union assignment. */
#include "csmith_checksum_runtime.h"

union cell {
  unsigned int word;
  unsigned short half;
};

union cell source = { 0x1A2AU };
union cell destination = { 0U };

int main(void) {
  destination = source;
  csmith_checksum_print(destination.word);
  return 0;
}
