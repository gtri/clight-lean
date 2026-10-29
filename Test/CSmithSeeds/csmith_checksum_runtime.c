#include "csmith_checksum_runtime.h"

/*
 * Native-only companion for the Phase 0 fixed-signature bootstrap profile.
 *
 * ABI/output contract: csmith_checksum_print accepts exactly one unsigned int,
 * writes its value as `checksum = %X\n` (uppercase hexadecimal) to stdout, and
 * returns printf's byte-count result.  This file is linked into the native test
 * executable but is deliberately not exported to Lean, so its printf varargs
 * call is outside the generated program's source surface.
 */
extern int printf(const char *format, ...);

int csmith_checksum_print(unsigned int checksum) {
  return printf("checksum = %X\n", checksum);
}
