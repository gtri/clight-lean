/* Hardware oracle for Test/Exec/FloatApiTest.lean.
 * Prints bit patterns (and, for float->int, whether the value is in range)
 * for boundary inputs. Expected values in the Lean test come from running
 * this on x86-64 with gcc, not from the Lean implementation. */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

static uint64_t b64(double d) { uint64_t u; memcpy(&u, &d, 8); return u; }
static uint32_t b32(float f) { uint32_t u; memcpy(&u, &f, 4); return u; }
static double d64(uint64_t u) { double d; memcpy(&d, &u, 8); return d; }

/* C leaves out-of-range float->int undefined; CompCert models it as None.
 * Report the truncated value only when it is representable. */
static void to_int(const char *name, double x) {
  double t = trunc(x);
  if (isnan(x) || t < -2147483648.0 || t > 2147483647.0) printf("%s none\n", name);
  else printf("%s some %d\n", name, (int32_t)x);
}
static void to_intu(const char *name, double x) {
  double t = trunc(x);
  if (isnan(x) || t < 0.0 || t > 4294967295.0) printf("%s none\n", name);
  else printf("%s some %u\n", name, (uint32_t)x);
}
static void to_long(const char *name, double x) {
  double t = trunc(x);
  if (isnan(x) || t < -9223372036854775808.0 || t >= 9223372036854775808.0) printf("%s none\n", name);
  else printf("%s some %lld\n", name, (long long)(int64_t)x);
}
static void to_longu(const char *name, double x) {
  double t = trunc(x);
  if (isnan(x) || t < 0.0 || t >= 18446744073709551616.0) printf("%s none\n", name);
  else printf("%s some %llu\n", name, (unsigned long long)(uint64_t)x);
}

int main(void) {
  volatile double pz = 0.0, nz = -0.0, one = 1.0, two = 2.0;
  volatile double nan = NAN, inf = INFINITY;
  volatile double x;

  /* arithmetic (nearest-even) */
  printf("add_1_2 0x%016llx\n", (unsigned long long)b64(one + two));
  printf("sub_1_2 0x%016llx\n", (unsigned long long)b64(one - two));
  x = 3.0;
  printf("mul_3_3 0x%016llx\n", (unsigned long long)b64(x * x));
  printf("div_1_3 0x%016llx\n", (unsigned long long)b64(one / 3.0));
  printf("add_eps 0x%016llx\n", (unsigned long long)b64(one + d64(0x3CA0000000000000ULL)));

  /* sign ops */
  printf("neg_pz 0x%016llx\n", (unsigned long long)b64(-pz));
  printf("abs_nz 0x%016llx\n", (unsigned long long)b64(fabs(nz)));
  printf("abs_m3 0x%016llx\n", (unsigned long long)b64(fabs(-3.0)));

  /* comparisons */
  printf("eq_pz_nz %d\n", pz == nz);
  printf("ne_nan_nan %d\n", nan != nan);
  printf("eq_nan_nan %d\n", nan == nan);
  printf("le_nan_1 %d\n", nan <= one);
  printf("ge_nan_1 %d\n", nan >= one);
  printf("lt_1_2 %d\n", one < two);
  printf("gt_1_2 %d\n", one > two);
  printf("le_pz_nz %d\n", pz <= nz);

  /* int -> float */
  volatile int32_t im1 = -1; volatile uint32_t um1 = 0xFFFFFFFFu;
  printf("of_int_m1 0x%016llx\n", (unsigned long long)b64((double)im1));
  printf("of_intu_ffffffff 0x%016llx\n", (unsigned long long)b64((double)um1));
  volatile int64_t big = (1LL << 53) + 1;
  printf("of_long_2p53p1 0x%016llx\n", (unsigned long long)b64((double)big));
  volatile uint64_t ubig = 0xFFFFFFFFFFFFFFFFULL;
  printf("of_longu_max 0x%016llx\n", (unsigned long long)b64((double)ubig));
  volatile int32_t i16777217 = 16777217;
  printf("of_int_f32_16777217 0x%08x\n", b32((float)i16777217));

  /* float32 <-> float64 */
  volatile double d1e40 = 1e40, dthird = 1.0 / 3.0;
  printf("to_single_1e40 0x%08x\n", b32((float)d1e40));
  printf("to_single_third 0x%08x\n", b32((float)dthird));
  volatile float fthird = 1.0f / 3.0f;
  printf("of_single_third 0x%016llx\n", (unsigned long long)b64((double)fthird));

  /* float -> int (truncation, None out of range / NaN / Inf) */
  to_int("to_int_m2p5", -2.5);
  to_int("to_int_max_frac", 2147483647.9);
  to_int("to_int_2p31", 2147483648.0);
  to_int("to_int_min_frac", -2147483648.9);
  to_int("to_int_min_m1", -2147483649.0);
  to_int("to_int_nan", nan);
  to_int("to_int_inf", inf);
  to_intu("to_intu_m0p9", -0.9);
  to_intu("to_intu_m1", -1.0);
  to_intu("to_intu_max_frac", 4294967295.9);
  to_intu("to_intu_2p32", 4294967296.0);
  to_long("to_long_m2p5", -2.5);
  to_long("to_long_2p63", 9223372036854775808.0);
  to_long("to_long_m2p63", -9223372036854775808.0);
  to_longu("to_longu_2p64", 18446744073709551616.0);
  to_longu("to_longu_2p63", 9223372036854775808.0);
  to_longu("to_longu_m0p5", -0.5);

  /* constants and words */
  printf("zero 0x%016llx\n", (unsigned long long)b64(0.0));
  printf("one 0x%016llx\n", (unsigned long long)b64(1.0));
  return 0;
}
