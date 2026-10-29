/* Fixed-signature checksum fixture exercising defined pointer comparisons. */
#include "csmith_checksum_runtime.h"

unsigned int values[3] = { 0U, 0U, 0U };
unsigned int *first = &values[0];
unsigned int *second = &values[1];

int main(void) {
  unsigned int result = 0U;
  unsigned int *null_pointer = 0;

  if (first < second) result += 1U;
  if (first != second) result += 2U;
  if (first != 0) result += 4U;
  if (null_pointer == 0) result += 8U;
  csmith_checksum_print(result);
  return 0;
}
