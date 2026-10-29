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

import CLightLean.Exec.Types

/-!
Pure resumption of a returned value through a call continuation for the
additive executor.

This is only the computational content of the authoritative
`step_returnstate` rule.  It does not handle returns from a function body,
`Sskip`, freeing local blocks, or general statement stepping.
-/

namespace CLightLean.Exec

variable [Archi]

/-- Resume a caller after its callee has returned `v`, preserving the caller's
function, environment, continuation, and memory while updating its optional
result temporary exactly through `set_opttemp`. -/
def resumeReturn (v : val) (optid : Option ident) (f : function) (e : env)
    (le : temp_env) (k : cont) (m : Memory.mem) : state :=
  .State f .Sskip k e (set_opttemp optid v le) m

end CLightLean.Exec
