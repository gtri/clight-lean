/* Fixed-signature checksum fixture exercising an active union member update. */
#include "csmith_checksum_runtime.h"

union cell {
  unsigned int word;
  unsigned short half;
};

union cell value = { 0x1A2AU };

int main(void) {
  value.word = value.word + 1U;
  csmith_checksum_print(value.word);
  return 0;
}
