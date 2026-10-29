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

import CLightLean.Exec.Return

/-!
Direct soundness for resuming a `Returnstate` through a call continuation.

The relational `step2` semantics remains authoritative; this theorem exposes
only its existing `step_returnstate` constructor through the pure helper.
-/

namespace CLightLean.Exec

variable [Archi]

/-- Resuming a returned value through a call continuation is exactly the
authoritative `step2` `step_returnstate` transition. -/
theorem resumeReturn_sound
    (ge : genv) (v : val) (optid : Option ident) (f : function) (e : env)
    (le : temp_env) (k : cont) (m : Memory.mem) :
    step2 ge (.Returnstate v (.Kcall optid f e le k) m) Events.E0
      (resumeReturn v optid f e le k m) := by
  exact .step_returnstate v optid f e le k m

end CLightLean.Exec
