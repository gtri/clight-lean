import CLightLean.Exec.Expr

namespace Test.Exec

open CLightLean.Exec

attribute [local instance] x86_64

def exprListTestGenv : genv :=
  { genv_genv := Genv.empty_genv []
    genv_cenv := empty_composite_env }

def exprListEmptyTemps : temp_env := ∅

def exprListIntTy : type := type_int32s
def exprListByteTy : type := .Tint .I8 .Unsigned noattr
def exprListIntPtrTy : type := .Tpointer exprListIntTy noattr
def exprListFloatTy : type := .Tfloat .F64 noattr

theorem eval_exprlist_empty_success :
    evalExprList exprListTestGenv empty_env exprListEmptyTemps Memory.empty [] [] = .ok [] := by
  rfl

theorem eval_exprlist_single_integer_cast_success :
    evalExprList exprListTestGenv empty_env exprListEmptyTemps Memory.empty
        [.Econst_int (CompCert.Int.repr 7) exprListIntTy] [exprListByteTy]
      = .ok [.Vint (CompCert.Int.repr 7)] := by
  rfl

theorem eval_exprlist_multiple_integer_casts_success :
    evalExprList exprListTestGenv empty_env exprListEmptyTemps Memory.empty
        [.Econst_int (CompCert.Int.repr 7) exprListIntTy,
          .Econst_int (CompCert.Int.repr 300) exprListIntTy]
        [exprListByteTy, exprListByteTy]
      = .ok [.Vint (CompCert.Int.repr 7), .Vint (CompCert.Int.repr 44)] := by
  rfl

theorem eval_exprlist_expression_type_length_mismatches_fail :
    evalExprList exprListTestGenv empty_env exprListEmptyTemps Memory.empty
        [] [exprListIntTy]
      = .error .malformedCall ∧
    evalExprList exprListTestGenv empty_env exprListEmptyTemps Memory.empty
        [.Econst_int (CompCert.Int.repr 1) exprListIntTy] []
      = .error .malformedCall := by
  exact ⟨rfl, rfl⟩

theorem eval_exprlist_expression_failure_propagates :
    evalExprList exprListTestGenv empty_env exprListEmptyTemps Memory.empty
        [.Etempvar (88 : Nat) exprListIntTy] [exprListIntTy]
      = .error .invalidExpression := by
  have hlookup : exprListEmptyTemps.get? (88 : Nat) = none := by
    simp only [exprListEmptyTemps, Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.getElem?_empty
  unfold evalExprList evalExpr
  rw [hlookup]

theorem eval_exprlist_cast_failure_is_invalid_expression :
    evalExprList exprListTestGenv empty_env exprListEmptyTemps Memory.empty
        [.Econst_float CompCert.Float64.zero exprListFloatTy] [exprListIntPtrTy]
      = .error .invalidExpression := by
  rfl

end Test.Exec
