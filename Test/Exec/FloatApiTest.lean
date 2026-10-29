import CLightLean.Lib.Floats

/-!
Hardware-oracle tests for the FloatLib-backed `CompCert.Float64/32` API.

Every expected value is copied from `Test/FloatOracle/float_oracle.expected`, the
output of `Test/FloatOracle/float_oracle.c` compiled with gcc on x86-64. Inputs
are given as exact IEEE bit patterns; the C program uses the same doubles.
Regenerate with `gcc -O0 -std=c11 float_oracle.c -lm && ./a.out`.
-/

open FloatLib.Floats

example : ExecFloat.Binary.toBits64 ((CompCert.Float64.add (ExecFloat.Binary.ofBits64 0x3FF0000000000000 : CompCert.Float64) (ExecFloat.Binary.ofBits64 0x4000000000000000 : CompCert.Float64)).value) = 0x4008000000000000 := by decide  -- add_1_2
example : ExecFloat.Binary.toBits64 ((CompCert.Float64.sub (ExecFloat.Binary.ofBits64 0x3FF0000000000000 : CompCert.Float64) (ExecFloat.Binary.ofBits64 0x4000000000000000 : CompCert.Float64)).value) = 0xbff0000000000000 := by decide  -- sub_1_2
example : ExecFloat.Binary.toBits64 ((CompCert.Float64.mul (ExecFloat.Binary.ofBits64 0x4008000000000000 : CompCert.Float64) (ExecFloat.Binary.ofBits64 0x4008000000000000 : CompCert.Float64)).value) = 0x4022000000000000 := by decide  -- mul_3_3
set_option maxRecDepth 100000 in
example : ExecFloat.Binary.toBits64 ((CompCert.Float64.div (ExecFloat.Binary.ofBits64 0x3FF0000000000000 : CompCert.Float64) (ExecFloat.Binary.ofBits64 0x4008000000000000 : CompCert.Float64)).value) = 0x3fd5555555555555 := by decide  -- div_1_3
-- tie rounds to even
example : ExecFloat.Binary.toBits64 ((CompCert.Float64.add (ExecFloat.Binary.ofBits64 0x3FF0000000000000 : CompCert.Float64) (ExecFloat.Binary.ofBits64 0x3CA0000000000000 : CompCert.Float64)).value) = 0x3ff0000000000000 := by decide  -- add_eps
example : ExecFloat.Binary.toBits64 (CompCert.Float64.neg (ExecFloat.Binary.ofBits64 0x0000000000000000 : CompCert.Float64)) = 0x8000000000000000 := by decide  -- neg_pz
example : ExecFloat.Binary.toBits64 (CompCert.Float64.abs (ExecFloat.Binary.ofBits64 0x8000000000000000 : CompCert.Float64)) = 0x0000000000000000 := by decide  -- abs_nz
example : ExecFloat.Binary.toBits64 (CompCert.Float64.abs (ExecFloat.Binary.ofBits64 0xC008000000000000 : CompCert.Float64)) = 0x4008000000000000 := by decide  -- abs_m3
example : CompCert.Float64.cmp .Ceq (ExecFloat.Binary.ofBits64 0x0000000000000000 : CompCert.Float64) (ExecFloat.Binary.ofBits64 0x8000000000000000 : CompCert.Float64) = true := by decide  -- eq_pz_nz
example : CompCert.Float64.cmp .Cne (ExecFloat.Binary.ofBits64 0x7FF8000000000000 : CompCert.Float64) (ExecFloat.Binary.ofBits64 0x7FF8000000000000 : CompCert.Float64) = true := by decide  -- ne_nan_nan
example : CompCert.Float64.cmp .Ceq (ExecFloat.Binary.ofBits64 0x7FF8000000000000 : CompCert.Float64) (ExecFloat.Binary.ofBits64 0x7FF8000000000000 : CompCert.Float64) = false := by decide  -- eq_nan_nan
example : CompCert.Float64.cmp .Cle (ExecFloat.Binary.ofBits64 0x7FF8000000000000 : CompCert.Float64) (ExecFloat.Binary.ofBits64 0x3FF0000000000000 : CompCert.Float64) = false := by decide  -- le_nan_1
example : CompCert.Float64.cmp .Cge (ExecFloat.Binary.ofBits64 0x7FF8000000000000 : CompCert.Float64) (ExecFloat.Binary.ofBits64 0x3FF0000000000000 : CompCert.Float64) = false := by decide  -- ge_nan_1
example : CompCert.Float64.cmp .Clt (ExecFloat.Binary.ofBits64 0x3FF0000000000000 : CompCert.Float64) (ExecFloat.Binary.ofBits64 0x4000000000000000 : CompCert.Float64) = true := by decide  -- lt_1_2
example : CompCert.Float64.cmp .Cgt (ExecFloat.Binary.ofBits64 0x3FF0000000000000 : CompCert.Float64) (ExecFloat.Binary.ofBits64 0x4000000000000000 : CompCert.Float64) = false := by decide  -- gt_1_2
example : CompCert.Float64.cmp .Cle (ExecFloat.Binary.ofBits64 0x0000000000000000 : CompCert.Float64) (ExecFloat.Binary.ofBits64 0x8000000000000000 : CompCert.Float64) = true := by decide  -- le_pz_nz
example : ExecFloat.Binary.toBits64 (CompCert.Float64.of_int (CompCert.Int.repr (-1))) = 0xbff0000000000000 := by decide  -- of_int_m1
example : ExecFloat.Binary.toBits64 (CompCert.Float64.of_intu (CompCert.Int.repr 0xFFFFFFFF)) = 0x41efffffffe00000 := by decide  -- of_intu_ffffffff
-- tie rounds to even
example : ExecFloat.Binary.toBits64 (CompCert.Float64.of_long (CompCert.Int64.repr (2^53 + 1))) = 0x4340000000000000 := by decide  -- of_long_2p53p1
example : ExecFloat.Binary.toBits64 (CompCert.Float64.of_longu (CompCert.Int64.repr 0xFFFFFFFFFFFFFFFF)) = 0x43f0000000000000 := by decide  -- of_longu_max
example : ExecFloat.Binary.toBits32 (CompCert.Float32.of_int (CompCert.Int.repr 16777217)) = 0x4b800000 := by decide  -- of_int_f32_16777217
-- overflow gives +inf
example : ExecFloat.Binary.toBits32 (CompCert.Float64.to_single (ExecFloat.Binary.ofBits64 0x483D6329F1C35CA5 : CompCert.Float64)) = 0x7f800000 := by decide  -- to_single_1e40
example : ExecFloat.Binary.toBits32 (CompCert.Float64.to_single (ExecFloat.Binary.ofBits64 0x3FD5555555555555 : CompCert.Float64)) = 0x3eaaaaab := by decide  -- to_single_third
example : ExecFloat.Binary.toBits64 (CompCert.Float64.of_single (ExecFloat.Binary.ofBits32 0x3EAAAAAB : CompCert.Float32)) = 0x3fd5555560000000 := by decide  -- of_single_third
example : CompCert.Float64.to_int (ExecFloat.Binary.ofBits64 0xC004000000000000 : CompCert.Float64) = some (CompCert.Int.repr (-2)) := by decide  -- to_int_m2p5
example : CompCert.Float64.to_int (ExecFloat.Binary.ofBits64 0x41DFFFFFFFF9999A : CompCert.Float64) = some (CompCert.Int.repr (2147483647)) := by decide  -- to_int_max_frac
example : CompCert.Float64.to_int (ExecFloat.Binary.ofBits64 0x41E0000000000000 : CompCert.Float64) = none := by decide  -- to_int_2p31
example : CompCert.Float64.to_int (ExecFloat.Binary.ofBits64 0xC1E00000001CCCCD : CompCert.Float64) = some (CompCert.Int.repr (-2147483648)) := by decide  -- to_int_min_frac
example : CompCert.Float64.to_int (ExecFloat.Binary.ofBits64 0xC1E0000000200000 : CompCert.Float64) = none := by decide  -- to_int_min_m1
example : CompCert.Float64.to_int (ExecFloat.Binary.ofBits64 0x7FF8000000000000 : CompCert.Float64) = none := by decide  -- to_int_nan
example : CompCert.Float64.to_int (ExecFloat.Binary.ofBits64 0x7FF0000000000000 : CompCert.Float64) = none := by decide  -- to_int_inf
example : CompCert.Float64.to_intu (ExecFloat.Binary.ofBits64 0xBFECCCCCCCCCCCCD : CompCert.Float64) = some (CompCert.Int.repr (0)) := by decide  -- to_intu_m0p9
example : CompCert.Float64.to_intu (ExecFloat.Binary.ofBits64 0xBFF0000000000000 : CompCert.Float64) = none := by decide  -- to_intu_m1
example : CompCert.Float64.to_intu (ExecFloat.Binary.ofBits64 0x41EFFFFFFFFCCCCD : CompCert.Float64) = some (CompCert.Int.repr (4294967295)) := by decide  -- to_intu_max_frac
example : CompCert.Float64.to_intu (ExecFloat.Binary.ofBits64 0x41F0000000000000 : CompCert.Float64) = none := by decide  -- to_intu_2p32
example : CompCert.Float64.to_long (ExecFloat.Binary.ofBits64 0xC004000000000000 : CompCert.Float64) = some (CompCert.Int64.repr (-2)) := by decide  -- to_long_m2p5
example : CompCert.Float64.to_long (ExecFloat.Binary.ofBits64 0x43E0000000000000 : CompCert.Float64) = none := by decide  -- to_long_2p63
example : CompCert.Float64.to_long (ExecFloat.Binary.ofBits64 0xC3E0000000000000 : CompCert.Float64) = some (CompCert.Int64.repr (-9223372036854775808)) := by decide  -- to_long_m2p63
example : CompCert.Float64.to_longu (ExecFloat.Binary.ofBits64 0x43F0000000000000 : CompCert.Float64) = none := by decide  -- to_longu_2p64
example : CompCert.Float64.to_longu (ExecFloat.Binary.ofBits64 0x43E0000000000000 : CompCert.Float64) = some (CompCert.Int64.repr (9223372036854775808)) := by decide  -- to_longu_2p63
example : CompCert.Float64.to_longu (ExecFloat.Binary.ofBits64 0xBFE0000000000000 : CompCert.Float64) = some (CompCert.Int64.repr (0)) := by decide  -- to_longu_m0p5
example : ExecFloat.Binary.toBits64 (CompCert.Float64.zero) = 0x0000000000000000 := by decide  -- zero
example : ExecFloat.Binary.toBits64 (CompCert.Float64.one) = 0x3ff0000000000000 := by decide  -- one
