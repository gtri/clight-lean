/-
  The CompCert verified compiler
  Original Rocq/Coq implementation: Xavier Leroy, INRIA Paris-Rocquencourt
  Lean 4 translation: Georgia Tech Research Institute

  Copyright (c) 2005-2024 Institut National de Recherche en Informatique et en Automatique (INRIA)
  Copyright (c) 2026 Georgia Tech Research Institute

  Derivative work: Lean 4 translation and adaptation of CompCert's cfrontend semantics.

  This file is distributed under the terms of the GNU Lesser General Public License
  as published by the Free Software Foundation, either version 2.1 of the License,
  or (at your option) any later version.

  SPDX-License-Identifier: LGPL-2.1-or-later
-/

import CLightLean.Builtins0

/-!
# Platform-specific built-in functions

Port of `x86/Builtins1.v` — but architecture-selection itself is ported
differently from CompCert.

CompCert selects the target architecture's `Builtins1.v` at *build time*:
each architecture directory (`x86/`, `arm/`, `aarch64/`, `powerpc/`,
`riscV/`) provides its own file defining `platform_builtin` and friends,
and the build system picks exactly one to compile against. There is no
single Coq type doing double duty for every architecture.

We instead expose a `PlatformBuiltins` typeclass: `platform_builtin` becomes
an *associated type* of the class (`PBuiltin`) rather than a fixed name
resolved by which file got compiled. Each architecture provides an
`instance` (only `x86PlatformBuiltins` for now, matching the platform this
project currently targets); downstream code that needs "the" platform
builtins just requires `[PlatformBuiltins]` in scope, exactly the way it
already requires `[Archi]`. This is the same style of deviation as
`Archi.lean` itself (see the warning there): a typeclass stands in for
what CompCert resolves via file selection.
-/

namespace Builtins1

variable [Archi]

/-- Architecture-specific built-in functions, as an associated-type
    typeclass (see the module docstring for why this replaces CompCert's
    per-architecture `Builtins1.v` file selection). -/
class PlatformBuiltins where
  /-- The type of platform-specific builtins for this architecture. -/
  PBuiltin : Type
  [instDecEq : DecidableEq PBuiltin]
  /-- Maps builtin names (as they appear in source, e.g. `__builtin_fmin`)
      to the platform builtin(s) they can resolve to. -/
  table : List (String × PBuiltin)
  sig : PBuiltin → signature
  sem : (b : PBuiltin) → Builtins0.builtin_sem (sig b).sig_res

-- Re-exposed as an ordinary (reducible) instance so that
-- `DecidableEq PlatformBuiltins.PBuiltin` is found automatically by
-- typeclass search wherever `[PlatformBuiltins]` is in scope, without
-- every consumer needing its own `haveI`.
attribute [instance, reducible] PlatformBuiltins.instDecEq

/-! ## x86 platform builtins -/

inductive X86PlatformBuiltin : Type where
  | BI_fmin
  | BI_fmax
  deriving DecidableEq

def x86_platform_builtin_table : List (String × X86PlatformBuiltin) :=
  [ ("__builtin_fmin", .BI_fmin)
  , ("__builtin_fmax", .BI_fmax)
  ]

def x86_platform_builtin_sig (_b : X86PlatformBuiltin) : signature :=
  { sig_args := [.Xfloat, .Xfloat], sig_res := .Xfloat, sig_cc := cc_default }

/-- `fmin f1 f2` picks `f1` exactly when `f1 < f2`, matching CompCert's
    `match Float.compare f1 f2 with Some Lt => f1 | Some Eq | Some Gt | None => f2 end`
    (in every other case — equal, greater, or unordered/NaN — it picks
    `f2`). -/
def x86_fmin (f1 f2 : CompCert.Float64) : CompCert.Float64 := if f1 < f2 then f1 else f2

/-- `fmax f1 f2` picks `f1` exactly when `f1 > f2` (i.e. `f2 < f1`),
    matching CompCert's
    `match Float.compare f1 f2 with Some Gt => f1 | Some Eq | Some Lt | None => f2 end`. -/
def x86_fmax (f1 f2 : CompCert.Float64) : CompCert.Float64 := if f2 < f1 then f1 else f2

def x86_platform_builtin_sem (b : X86PlatformBuiltin) :
    Builtins0.builtin_sem (x86_platform_builtin_sig b).sig_res :=
  match b with
  | .BI_fmin =>
      Builtins0.mkbuiltin_v2t .Xfloat
        (fun v1 v2 => match v1, v2 with
          | .Vfloat f1, .Vfloat f2 => .Vfloat (x86_fmin f1 f2)
          | _, _ => .Vundef)
        (by intro v1 v2; cases v1 <;> cases v2 <;> trivial)
        (by
          intro j v1 v1' v2 v2' H1 H2
          cases H1 with
          | inject_float f1 =>
              cases H2 with
              | inject_float f2 => exact .inject_float _
              | _ => exact .val_inject_undef _
          | _ => exact .val_inject_undef _)
  | .BI_fmax =>
      Builtins0.mkbuiltin_v2t .Xfloat
        (fun v1 v2 => match v1, v2 with
          | .Vfloat f1, .Vfloat f2 => .Vfloat (x86_fmax f1 f2)
          | _, _ => .Vundef)
        (by intro v1 v2; cases v1 <;> cases v2 <;> trivial)
        (by
          intro j v1 v1' v2 v2' H1 H2
          cases H1 with
          | inject_float f1 =>
              cases H2 with
              | inject_float f2 => exact .inject_float _
              | _ => exact .val_inject_undef _
          | _ => exact .val_inject_undef _)

instance x86PlatformBuiltins : PlatformBuiltins where
  PBuiltin := X86PlatformBuiltin
  instDecEq := inferInstance
  table := x86_platform_builtin_table
  sig := x86_platform_builtin_sig
  sem := x86_platform_builtin_sem

end Builtins1
