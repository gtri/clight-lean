import CLightLean.Exec.CSmithRuntime

namespace Test.Exec

open CLightLean.Exec

def csmithTestBytes (values : List UInt8) : ByteArray :=
  values.foldl ByteArray.push ByteArray.empty

/-- Small list-backed byte source for lightweight runtime-unit tests. -/
def csmithTestLookup (contents : List UInt8) : CByteLookup :=
  fun block offset =>
    if block = 1 ∧ 0 ≤ offset then contents[offset.toNat]? else none

def csmithTestPointer : CPointer := { block := 1, offset := 0 }
def csmithInvalidPointer : CPointer := { block := 0, offset := 0 }

def canonicalFormatWithNul : List UInt8 :=
  [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d,
    0x20, 0x3d, 0x20, 0x25, 0x58, 0x0a, 0x00]

theorem bounded_cstring_reader_reads_initialized_raw_bytes :
    readCStringBoundedWith (csmithTestLookup canonicalFormatWithNul) csmithTestPointer 15 =
      .ok csmithChecksumFormat := by
  rfl

theorem bounded_cstring_reader_stops_at_nul :
    readCStringBoundedWith (csmithTestLookup [0x41, 0x00, 0xff]) csmithTestPointer 3 =
      .ok (csmithTestBytes [0x41]) := by
  rfl

theorem bounded_cstring_reader_rejects_missing_nul_at_bound :
    readCStringBoundedWith (csmithTestLookup [0x41, 0x42, 0x43]) csmithTestPointer 3 =
      .error .invalidCString := by
  rfl

theorem bounded_cstring_reader_rejects_zero_scan_bound :
    readCStringBoundedWith (csmithTestLookup canonicalFormatWithNul) csmithTestPointer 0 =
      .error .invalidCString := by
  rfl

theorem bounded_cstring_reader_rejects_missing_cell :
    readCStringBoundedWith (csmithTestLookup [0x41]) csmithTestPointer 2 =
      .error .invalidCString := by
  rfl

theorem bounded_cstring_reader_rejects_invalid_pointer :
    readCStringBoundedWith (csmithTestLookup canonicalFormatWithNul) csmithInvalidPointer 1 =
      .error .invalidCString := by
  rfl

theorem uppercase_uint32_hex_formatting_is_exact :
    formatUInt32HexUpper 0 = csmithTestBytes [0x30] ∧
    formatUInt32HexUpper 0x1A2B = csmithTestBytes [0x31, 0x41, 0x32, 0x42] ∧
    formatUInt32HexUpper 0xffffffff =
      csmithTestBytes [0x46, 0x46, 0x46, 0x46, 0x46, 0x46, 0x46, 0x46] := by
  constructor
  · rfl
  constructor <;> rfl

def canonicalChecksumPrintSucceeds : Bool :=
  let runtime := Runtime.appendStdout Runtime.empty (csmithTestBytes [0xff])
  match checksumPrintfWith (csmithTestLookup canonicalFormatWithNul)
      csmithChecksumFormatMaxScan runtime csmithTestPointer 0x1A2B with
  | .ok outcome =>
      outcome.runtime.stdout ==
          csmithTestBytes [0xff, 0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75,
            0x6d, 0x20, 0x3d, 0x20, 0x31, 0x41, 0x32, 0x42, 0x0a] &&
        outcome.resultByteCount == 16
  | .error _ => false

theorem canonical_checksum_print_emits_exact_bytes_and_count :
    canonicalChecksumPrintSucceeds = true := by
  rfl

def noncanonicalFormatIsRejected : Bool :=
  match checksumPrintfWith (csmithTestLookup [0x25, 0x64, 0x00])
      csmithChecksumFormatMaxScan Runtime.empty csmithTestPointer 7 with
  | .error (.unsupportedPrintfFormat diagnostic) =>
      diagnostic == csmithUnsupportedFormatDiagnostic
  | _ => false

theorem readable_noncanonical_format_is_rejected_safely :
    noncanonicalFormatIsRejected = true := by
  rfl

def invalidCStringChecksumFormatIsRejected : Bool :=
  match checksumPrintfWith (csmithTestLookup [0x25]) 1 Runtime.empty csmithTestPointer 0 with
  | .error .invalidCString => true
  | _ => false

theorem checksum_print_propagates_invalid_cstring_format_failure :
    invalidCStringChecksumFormatIsRejected = true := by
  rfl

theorem checksum_print_rejects_invalid_pointer :
    checksumPrintfWith (csmithTestLookup canonicalFormatWithNul)
        csmithChecksumFormatMaxScan Runtime.empty csmithInvalidPointer 0 =
      .error .invalidCString := by
  rfl

theorem checksum_runtime_errors_have_stable_classifications :
    ExecError.invalidCString.code = "invalid_cstring" ∧
    (ExecError.unsupportedPrintfFormat csmithUnsupportedFormatDiagnostic).code =
      "unsupported_printf_format" := by
  constructor <;> rfl

end Test.Exec
