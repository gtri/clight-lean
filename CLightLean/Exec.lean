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

import CLightLean.Exec.Core
import CLightLean.Exec.Types
import CLightLean.Exec.Expr
import CLightLean.Exec.State
import CLightLean.Exec.Basic
import CLightLean.Exec.BasicSound
import CLightLean.Exec.Call
import CLightLean.Exec.CallSound
import CLightLean.Exec.Entry
import CLightLean.Exec.EntrySound
import CLightLean.Exec.Return
import CLightLean.Exec.ReturnSound
import CLightLean.Exec.FunctionReturn
import CLightLean.Exec.FunctionReturnSound
import CLightLean.Exec.Control
import CLightLean.Exec.ControlSound
import CLightLean.Exec.Step
import CLightLean.Exec.StepSound
import CLightLean.Exec.Run
import CLightLean.Exec.RunSound
import CLightLean.Exec.Program
import CLightLean.Exec.ProgramSound
import CLightLean.Exec.CSmithRuntime

/-!
Public facade for the additive functional CLight executor.

The concrete CSmith memory adapter, fixed-signature external step/run/IO path,
and the CSmith relational specialization are intentionally not imported here:
they pull the full memory/relational closure into the otherwise lightweight
executor facade. External integration and proof code must import
`CLightLean.Exec.CSmithRuntimeMemory`, `CLightLean.Exec.CSmithStep`,
`CLightLean.Exec.CSmithRun`, `CLightLean.Exec.CSmithIO`,
`CLightLean.Exec.CSmithRelation`, or
`CLightLean.Exec.CSmithRelationSound` explicitly.
-/
