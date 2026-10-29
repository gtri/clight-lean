import CLightLean.Exec.Types

namespace Test.Exec

open CLightLean.Exec

attribute [local instance] x86_64

def bytes (values : List UInt8) : ByteArray :=
  values.foldl ByteArray.push ByteArray.empty

theorem runtime_empty_stdout : Runtime.empty.stdout = ByteArray.empty := by
  rfl

theorem runtime_append_preserves_bytes :
    (Runtime.appendStdout
      (Runtime.appendStdout Runtime.empty (bytes [0x00, 0xff, 0xfe]))
      (bytes [0x41, 0x0a])).stdout
      = bytes [0x00, 0xff, 0xfe, 0x41, 0x0a] := by
  rfl

theorem exec_error_codes_and_details_are_discriminating :
    (ExecError.unsupportedExternal "printf").isUnsupported = true ∧
    (ExecError.unsupportedExternal "printf").code = "unsupported_external" ∧
    (ExecError.unsupportedExternal "printf").detail = some "printf" ∧
    ExecError.memoryFailure.isUnsupported = false ∧
    ExecError.memoryFailure.code = "memory_failure" ∧
    ExecError.memoryFailure.detail = none := by
  decide

theorem exec_error_serialization_is_stable :
    ExecError.invalidExpression.code = "invalid_expression" ∧
    ExecError.invalidExpression.detail = none ∧
    ExecError.invalidAssignment.code = "invalid_assignment" ∧
    ExecError.invalidAssignment.detail = none ∧
    (ExecError.unsupportedPrintfFormat "%d").code = "unsupported_printf_format" ∧
    (ExecError.unsupportedPrintfFormat "%d").detail = some "%d" := by
  decide

theorem exec_error_codes_cover_all_variants :
    ExecError.invalidExpression.code = "invalid_expression" ∧
    ExecError.invalidLvalue.code = "invalid_lvalue" ∧
    ExecError.invalidAssignment.code = "invalid_assignment" ∧
    ExecError.memoryFailure.code = "memory_failure" ∧
    ExecError.malformedCall.code = "malformed_call" ∧
    (ExecError.unsupportedExternal "puts").code = "unsupported_external" ∧
    (ExecError.unsupportedPrintfFormat "%s").code = "unsupported_printf_format" ∧
    ExecError.invalidCString.code = "invalid_cstring" ∧
    ExecError.stuck.code = "stuck" ∧
    ExecError.invalidExpression.isUnsupported = false ∧
    ExecError.invalidLvalue.isUnsupported = false ∧
    ExecError.invalidAssignment.isUnsupported = false ∧
    ExecError.memoryFailure.isUnsupported = false ∧
    ExecError.malformedCall.isUnsupported = false ∧
    (ExecError.unsupportedExternal "puts").isUnsupported = true ∧
    (ExecError.unsupportedPrintfFormat "%s").isUnsupported = true ∧
    ExecError.invalidCString.isUnsupported = false ∧
    ExecError.stuck.isUnsupported = false ∧
    ExecError.invalidExpression.detail = none ∧
    ExecError.invalidLvalue.detail = none ∧
    ExecError.invalidAssignment.detail = none ∧
    ExecError.memoryFailure.detail = none ∧
    ExecError.malformedCall.detail = none ∧
    (ExecError.unsupportedExternal "puts").detail = some "puts" ∧
    (ExecError.unsupportedPrintfFormat "%s").detail = some "%s" ∧
    ExecError.invalidCString.detail = none ∧
    ExecError.stuck.detail = none := by
  decide

theorem completed_result_exposes_exit :
    let result := RunResult.completed Runtime.empty [] (CompCert.Int.repr 7) 4
    result.statusCode = "completed" ∧
    result.exit? = some (CompCert.Int.repr 7) ∧
    result.error? = none ∧
    result.steps = 4 := by
  simp [RunResult.statusCode, RunResult.status, OutcomeStatus.code,
    RunResult.exit?, RunResult.error?, RunResult.steps]

theorem run_result_statuses_are_discriminating (state : state) :
    let runtime := Runtime.appendStdout Runtime.empty (bytes [0xff])
    let exhausted := RunResult.fuelExhausted runtime [] state 3
    let unsupported := RunResult.unsupported runtime [] (.unsupportedExternal "puts") 3
    let stuck := RunResult.stuck runtime [] .memoryFailure 3
    exhausted.statusCode = "fuel_exhausted" ∧
    unsupported.statusCode = "unsupported" ∧
    stuck.statusCode = "stuck" ∧
    exhausted.runtime.stdout = bytes [0xff] ∧
    unsupported.error? = some (.unsupportedExternal "puts") ∧
    stuck.error? = some .memoryFailure ∧
    exhausted.exit? = none := by
  simp [bytes, Runtime.empty, Runtime.appendStdout, RunResult.statusCode, RunResult.status,
    OutcomeStatus.code, RunResult.runtime, RunResult.error?, RunResult.exit?]

theorem run_result_projections_cover_each_constructor (state : state) :
    let completedRuntime := Runtime.appendStdout Runtime.empty (bytes [0x01])
    let exhaustedRuntime := Runtime.appendStdout Runtime.empty (bytes [0x02])
    let unsupportedRuntime := Runtime.appendStdout Runtime.empty (bytes [0x03])
    let stuckRuntime := Runtime.appendStdout Runtime.empty (bytes [0x04])
    let completed := RunResult.completed completedRuntime [] (CompCert.Int.repr 7) 1
    let exhausted := RunResult.fuelExhausted exhaustedRuntime [] state 2
    let unsupported := RunResult.unsupported unsupportedRuntime [] (.unsupportedExternal "puts") 3
    let stuck := RunResult.stuck stuckRuntime [] .memoryFailure 4
    completed.runtime.stdout = bytes [0x01] ∧
    exhausted.runtime.stdout = bytes [0x02] ∧
    unsupported.runtime.stdout = bytes [0x03] ∧
    stuck.runtime.stdout = bytes [0x04] ∧
    completed.steps = 1 ∧
    exhausted.steps = 2 ∧
    unsupported.steps = 3 ∧
    stuck.steps = 4 ∧
    completed.exit? = some (CompCert.Int.repr 7) ∧
    exhausted.exit? = none ∧
    unsupported.exit? = none ∧
    stuck.exit? = none ∧
    completed.error? = none ∧
    exhausted.error? = none ∧
    unsupported.error? = some (.unsupportedExternal "puts") ∧
    stuck.error? = some .memoryFailure := by
  simp [bytes, Runtime.empty, Runtime.appendStdout, RunResult.runtime, RunResult.steps,
    RunResult.exit?, RunResult.error?]

theorem step_result_construction (state : state) :
    match StepResult.advanced Runtime.empty [] state with
    | .advanced runtime trace state' => runtime = Runtime.empty ∧ trace = [] ∧ state' = state
    | _ => False := by
  simp

theorem step_result_terminal_construction :
    (match StepResult.completed Runtime.empty (CompCert.Int.repr 0) with
    | .completed runtime exit => runtime = Runtime.empty ∧ exit = CompCert.Int.repr 0
    | _ => False) ∧
    (match StepResult.error Runtime.empty .memoryFailure with
    | .error runtime error => runtime = Runtime.empty ∧ error = .memoryFailure
    | _ => False) := by
  simp

end Test.Exec
