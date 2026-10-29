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
Pure deterministic continuation-control transitions for the additive CLight
executor.

This module deliberately covers only `step2` rules whose successor is selected
without evaluating an expression, changing memory, entering a function, or
calling an external function.  States outside that narrow control subset return
`ExecError.stuck`; this helper never invents a successor for them.
-/

namespace CLightLean.Exec

variable [Archi]

/-- Execute the deterministic control-only subset of one CLight transition.

The supported cases mirror `step_seq`, the `Kseq` propagation rules,
`step_label`, `step_goto`, the `Kswitch` propagation rules, `step_loop`, and
the syntactically determined `Kloop1`/`Kloop2` continuation rules.  A failed
label lookup and every unsupported state/control combination are reported as
`stuck`; no relational witness is searched for. -/
def stepControl : state → Except ExecError state
  | .State f (.Ssequence s1 s2) k e le m =>
      .ok (.State f s1 (.Kseq s2 k) e le m)
  | .State f .Sskip (.Kseq s k) e le m =>
      .ok (.State f s k e le m)
  | .State f .Scontinue (.Kseq _s k) e le m =>
      .ok (.State f .Scontinue k e le m)
  | .State f .Sbreak (.Kseq _s k) e le m =>
      .ok (.State f .Sbreak k e le m)
  | .State f (.Slabel _lbl s) k e le m =>
      .ok (.State f s k e le m)
  | .State f (.Sgoto lbl) k e le m =>
      match find_label lbl f.fn_body (call_cont k) with
      | some (s', k') => .ok (.State f s' k' e le m)
      | none => .error .stuck
  | .State f .Sskip (.Kswitch k) e le m =>
      .ok (.State f .Sskip k e le m)
  | .State f .Sbreak (.Kswitch k) e le m =>
      .ok (.State f .Sskip k e le m)
  | .State f .Scontinue (.Kswitch k) e le m =>
      .ok (.State f .Scontinue k e le m)
  | .State f (.Sloop s1 s2) k e le m =>
      .ok (.State f s1 (.Kloop1 s1 s2 k) e le m)
  | .State f .Sskip (.Kloop1 s1 s2 k) e le m =>
      .ok (.State f s2 (.Kloop2 s1 s2 k) e le m)
  | .State f .Scontinue (.Kloop1 s1 s2 k) e le m =>
      .ok (.State f s2 (.Kloop2 s1 s2 k) e le m)
  | .State f .Sbreak (.Kloop1 _s1 _s2 k) e le m =>
      .ok (.State f .Sskip k e le m)
  | .State f .Sskip (.Kloop2 s1 s2 k) e le m =>
      .ok (.State f (.Sloop s1 s2) k e le m)
  | .State f .Sbreak (.Kloop2 _s1 _s2 k) e le m =>
      .ok (.State f .Sskip k e le m)
  | _ => .error .stuck

end CLightLean.Exec
