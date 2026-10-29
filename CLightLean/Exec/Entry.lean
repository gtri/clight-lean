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

import CLightLean.Exec.State

/-!
Pure entry of an internal `Callstate` for the additive executor.

This module covers only the parameter-as-temporaries function-entry setup used
by `step2`.  It deliberately does not dispatch arbitrary call states, evaluate
statements, or model external calls.  The relational semantics in `CLight.lean`
remains authoritative.
-/

namespace CLightLean.Exec

variable [Archi]

/-- Enter an internal function using the executor's `functionEntry2` setup.
On success, retain the supplied continuation and enter exactly at the function
body with the allocated local environment, bound temporaries, and resulting
memory.  Any setup failure is propagated unchanged. -/
def enterInternalFunction (ge : genv) (f : function) (args : List val) (k : cont)
    (m : Memory.mem) : Except ExecError state :=
  match functionEntry2 ge f args m with
  | .ok entry => .ok (.State f f.fn_body k entry.env entry.temps entry.memory)
  | .error err => .error err

end CLightLean.Exec
