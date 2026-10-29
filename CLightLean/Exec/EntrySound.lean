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

import CLightLean.Exec.Entry

/-!
Compositional soundness for the pure internal-function entry helper.

The theorem intentionally assumes the authoritative `function_entry2` premise;
full correspondence of the executable setup function is outside this module.
-/

namespace CLightLean.Exec

variable [Archi]

/-- A successful internal-entry helper result, together with the corresponding
authoritative `function_entry2` premise, yields exactly the `step2` internal
function transition. -/
theorem enterInternalFunction_sound
    (ge : genv) (f : function) (args : List val) (k : cont) (m : Memory.mem)
    (entry : FunctionEntryState)
    (_h : enterInternalFunction ge f args k m =
      .ok (.State f f.fn_body k entry.env entry.temps entry.memory))
    (hentry : function_entry2 ge f args m entry.env entry.temps entry.memory) :
    step2 ge (.Callstate (.Internal f) args k m) Events.E0
      (.State f f.fn_body k entry.env entry.temps entry.memory) := by
  exact .step_internal_function f args k m entry.env entry.temps entry.memory hentry

end CLightLean.Exec
