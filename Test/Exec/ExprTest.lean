import CLightLean.Exec.Expr

namespace Test.Exec

open CLightLean.Exec

attribute [local instance] x86_64

def testGenv : genv :=
  { genv_genv := Genv.empty_genv []
    genv_cenv := empty_composite_env }

def id17 : ident := (17 : Nat)
def id21 : ident := (21 : Nat)
def id99 : ident := (99 : Nat)
def id31 : ident := (31 : Nat)
def id32 : ident := (32 : Nat)
def id41 : ident := (41 : Nat)

def localEnv : env := empty_env.insert id17 (3, type_int32s)

def emptyTemps : temp_env := ∅

def intTy : type := type_int32s
def longTy : type := .Tlong .Signed noattr
def floatTy : type := .Tfloat .F64 noattr
def singleTy : type := .Tfloat .F32 noattr
def intPtrTy : type := .Tpointer intTy noattr

def bitfieldTy : type := .Tint .I32 .Signed noattr
def bitfieldStructTy : type := .Tstruct id41 noattr

def bitfieldComposite : composite :=
  { co_su := .Struct
    co_members := [.Member_bitfield id32 .I32 .Signed noattr 1 false]
    co_attr := noattr
    co_sizeof := 4
    co_alignof := 4
    co_rank := 0
    co_sizeof_pos := by omega
    co_alignof_two_p := ⟨2, by norm_num⟩
    co_sizeof_alignof := by norm_num }

def bitfieldGenv : genv :=
  { genv_genv := Genv.empty_genv []
    genv_cenv := empty_composite_env.insert id41 bitfieldComposite }

def mismatchLocalGenv : genv :=
  { genv_genv := Genv.add_global (Genv.empty_genv [])
      (id17, .Gvar { gvar_info := longTy,
                      gvar_init := [],
                      gvar_readonly := false,
                      gvar_volatile := false })
    genv_cenv := empty_composite_env }

theorem eval_expr_all_literal_families :
    evalExpr testGenv empty_env emptyTemps Memory.empty
        (.Econst_int (CompCert.Int.repr 7) intTy)
      = .ok (.Vint (CompCert.Int.repr 7)) ∧
    evalExpr testGenv empty_env emptyTemps Memory.empty
        (.Econst_float CompCert.Float64.zero floatTy)
      = .ok (.Vfloat CompCert.Float64.zero) ∧
    evalExpr testGenv empty_env emptyTemps Memory.empty
        (.Econst_single CompCert.Float32.zero singleTy)
      = .ok (.Vsingle CompCert.Float32.zero) ∧
    evalExpr testGenv empty_env emptyTemps Memory.empty
        (.Econst_long (CompCert.Int64.repr 9) longTy)
      = .ok (.Vlong (CompCert.Int64.repr 9)) := by
  exact ⟨rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩

theorem eval_expr_temp_lookup_success :
    evalExpr testGenv empty_env
        (emptyTemps.insert id21 (.Vint (CompCert.Int.repr 11))) Memory.empty
        (.Etempvar id21 intTy)
      = .ok (.Vint (CompCert.Int.repr 11)) := by
  simp [evalExpr, emptyTemps]

theorem eval_expr_temp_lookup_failure :
    evalExpr testGenv empty_env emptyTemps Memory.empty (.Etempvar id21 intTy)
      = .error .invalidExpression := by
  have hlookup : emptyTemps.get? id21 = none := by
    simp only [emptyTemps, Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.getElem?_empty
  unfold evalExpr
  rw [hlookup]

theorem eval_expr_integer_unary_operation :
    evalExpr testGenv empty_env emptyTemps Memory.empty
        (.Eunop .Oneg (.Econst_int (CompCert.Int.repr 7) intTy) intTy)
      = .ok (.Vint (CompCert.Int.repr (-7))) := by
  rfl

theorem eval_expr_integer_binary_operation :
    evalExpr testGenv empty_env emptyTemps Memory.empty
        (.Ebinop .Oadd (.Econst_int (CompCert.Int.repr 2) intTy)
          (.Econst_int (CompCert.Int.repr 3) intTy) intTy)
      = .ok (.Vint (CompCert.Int.repr 5)) := by
  rfl

theorem eval_expr_cast_success :
    evalExpr testGenv empty_env emptyTemps Memory.empty
        (.Ecast (.Econst_int (CompCert.Int.repr 7) intTy) (.Tint .I8 .Unsigned noattr))
      = .ok (.Vint (CompCert.Int.repr 7)) := by
  rfl

theorem eval_expr_cast_failure :
    evalExpr testGenv empty_env emptyTemps Memory.empty
        (.Ecast (.Econst_float CompCert.Float64.zero floatTy) intPtrTy)
      = .error .invalidExpression := by
  rfl

theorem eval_lvalue_local_type_mismatch_rejected :
    evalLvalue mismatchLocalGenv localEnv emptyTemps Memory.empty (.Evar id17 longTy)
      = .error .invalidLvalue := by
  simp [evalLvalue, evalVarLvalue, localEnv, empty_env, longTy, type_int32s]

theorem eval_lvalue_missing_variable_fails :
    evalLvalue testGenv empty_env emptyTemps Memory.empty (.Evar id99 intTy)
      = .error .invalidLvalue := by
  have hlocal : empty_env.get? id99 = none := by
    simp only [empty_env, Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.getElem?_empty
  have hglobal : Genv.find_symbol testGenv.genv_genv id99 = none := by
    simp [testGenv, Genv.find_symbol, Genv.empty_genv]
  unfold evalLvalue evalVarLvalue
  rw [hlocal, hglobal]

theorem eval_expr_addrof_local_lvalue :
    evalExpr testGenv localEnv emptyTemps Memory.empty
        (.Eaddrof (.Evar id17 intTy) intPtrTy)
      = .ok (.Vptr 3 Ptrofs.zero) := by
  simp [evalExpr, evalLvalue, evalVarLvalue, localEnv, empty_env, intTy]

theorem eval_expr_addrof_bitfield_lvalue_rejected :
    evalExpr bitfieldGenv empty_env
        (emptyTemps.insert id31 (.Vptr 7 Ptrofs.zero)) Memory.empty
        (.Eaddrof (.Efield (.Etempvar id31 bitfieldStructTy) id32 bitfieldTy) intPtrTy)
      = .error .invalidExpression := by
  have htemp : (emptyTemps.insert id31 (.Vptr 7 Ptrofs.zero)).get? id31 =
      some (.Vptr 7 Ptrofs.zero) := by
    simp [emptyTemps]
  have hcenv : (empty_composite_env.insert id41 bitfieldComposite).get? id41 =
      some bitfieldComposite := by
    rfl
  simp only [evalExpr, evalLvalue]
  rw [htemp]
  simp only [evalFieldLvalue]
  change (match (match (empty_composite_env.insert id41 bitfieldComposite).get? id41 with
    | none => Except.error ExecError.invalidLvalue
    | some co =>
        match field_offset (empty_composite_env.insert id41 bitfieldComposite) id32 co.co_members with
        | Except.ok (delta, bf) =>
            Except.ok ({ block := 7, offset := Ptrofs.add Ptrofs.zero (Ptrofs.repr delta), bitfield := bf } : Lvalue)
        | Except.error _ => Except.error ExecError.invalidLvalue) with
    | Except.error err => Except.error err
    | Except.ok { bitfield := .Full, block, offset } => Except.ok (val.Vptr block offset)
    | Except.ok _ => Except.error ExecError.invalidExpression) = Except.error ExecError.invalidExpression
  rw [hcenv]
  rfl

theorem deref_bitfield_carrier_size_mismatch_rejected :
    derefBitfield (.Tint .I16 .Signed noattr) .I32 .Signed 0 1
        Memory.empty (.Vptr 1 Ptrofs.zero)
      = .error .invalidExpression := by
  rfl

theorem eval_lvalue_rejects_non_lvalue :
    evalLvalue testGenv empty_env emptyTemps Memory.empty
        (.Econst_int CompCert.Int.zero intTy)
      = .error .invalidLvalue := by
  rfl

theorem eval_expr_sizeof_and_alignof :
    evalExpr testGenv empty_env emptyTemps Memory.empty (.Esizeof intTy intTy)
      = .ok (Vptrofs (Ptrofs.repr 4)) ∧
    evalExpr testGenv empty_env emptyTemps Memory.empty (.Ealignof intTy intTy)
      = .ok (Vptrofs (Ptrofs.repr 4)) := by
  exact ⟨rfl, rfl⟩

theorem deref_loc_array_reference_returns_pointer_without_memory_access :
    derefLoc (.Tarray intTy 4 noattr) Memory.empty 1 Ptrofs.zero .Full
      = .ok (.Vptr 1 Ptrofs.zero) := by
  rfl

end Test.Exec
