import CLightLean.CLight

attribute [instance] x86_64

def _csmith_checksum_print : ident := (124101875217104144492282944803087935244 : Nat)
def _main : ident := (22880918 : Nat)
def _value : ident := (1316573855 : Nat)

def v_value : globvar type := {
  gvar_info := (type.Tfloat floatsize.F64 noattr),
  gvar_init := [(init_data.Init_float64
    (CompCert.Float64.of_bits (CompCert.Int64.repr 4609434218613702656)))],
  gvar_readonly := false,
  gvar_volatile := false
}

def f_main : function := {
  fn_return := type_int32s,
  fn_callconv := cc_default,
  fn_params := [],
  fn_vars := [],
  fn_temps := [],
  fn_body :=
    (statement.Ssequence
      (statement.Sassign
        (expr.Evar _value (type.Tfloat floatsize.F64 noattr))
        (expr.Ebinop binary_operation.Odiv
          (expr.Ebinop binary_operation.Omul
            (expr.Ebinop binary_operation.Oadd
              (expr.Evar _value (type.Tfloat floatsize.F64 noattr))
              (expr.Econst_float
                (CompCert.Float64.of_bits (CompCert.Int64.repr 4612248968380809216))
                (type.Tfloat floatsize.F64 noattr))
              (type.Tfloat floatsize.F64 noattr))
            (expr.Econst_float
              (CompCert.Float64.of_bits (CompCert.Int64.repr 4616189618054758400))
              (type.Tfloat floatsize.F64 noattr))
            (type.Tfloat floatsize.F64 noattr))
          (expr.Econst_float
            (CompCert.Float64.of_bits (CompCert.Int64.repr 4609434218613702656))
            (type.Tfloat floatsize.F64 noattr))
          (type.Tfloat floatsize.F64 noattr)))
      (statement.Ssequence
        (statement.Scall none
          (expr.Evar _csmith_checksum_print (type.Tfunction
            [(type.Tint intsize.I32 signedness.Unsigned noattr)]
            type_int32s cc_default))
          [(expr.Ecast (expr.Evar _value (type.Tfloat floatsize.F64 noattr))
            (type.Tint intsize.I32 signedness.Unsigned noattr))])
        (statement.Sreturn (some (expr.Econst_int (CompCert.Int.repr 0) type_int32s)))))
}

def composites : List composite_definition := []

def global_definitions : List (ident × globdef (fundef_type function) type) :=
  [(_csmith_checksum_print,
    globdef.Gfun (fundef_type.External (external_function.EF_external "csmith_checksum_print"
      { sig_args := [xtype.Xint], sig_res := xtype.Xint, sig_cc := cc_default })
      [(type.Tint intsize.I32 signedness.Unsigned noattr)] type_int32s cc_default)),
   (_value, globdef.Gvar v_value),
   (_main, globdef.Gfun (fundef_type.Internal f_main))]

def public_idents : List ident := [_main, _value, _csmith_checksum_print]

def prog : program_type function :=
  make_program! function composites global_definitions public_idents _main
