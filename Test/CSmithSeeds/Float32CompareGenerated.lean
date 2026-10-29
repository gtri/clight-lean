import CLightLean.CLight

attribute [instance] x86_64

def _csmith_checksum_print : ident := (124101875217104144492282944803087935244 : Nat)
def _left : ident := (24441749 : Nat)
def _main : ident := (22880918 : Nat)
def _result : ident := (100218291099 : Nat)
def _right : ident := (1564804251 : Nat)

def v_left : globvar type := {
  gvar_info := (type.Tfloat floatsize.F32 noattr),
  gvar_init := [(init_data.Init_float32
    (CompCert.Float32.of_bits (CompCert.Int.repr 1069547520)))],
  gvar_readonly := false,
  gvar_volatile := false
}

def v_right : globvar type := {
  gvar_info := (type.Tfloat floatsize.F32 noattr),
  gvar_init := [(init_data.Init_float32
    (CompCert.Float32.of_bits (CompCert.Int.repr 1074790400)))],
  gvar_readonly := false,
  gvar_volatile := false
}

def f_main : function := {
  fn_return := type_int32s,
  fn_callconv := cc_default,
  fn_params := [],
  fn_vars := [],
  fn_temps := [(_result, (type.Tint intsize.I32 signedness.Unsigned noattr))],
  fn_body :=
    (statement.Ssequence
      (statement.Sset _result (expr.Econst_int (CompCert.Int.repr 0)
        (type.Tint intsize.I32 signedness.Unsigned noattr)))
      (statement.Ssequence
        (statement.Sifthenelse (expr.Ebinop binary_operation.Olt
          (expr.Evar _left (type.Tfloat floatsize.F32 noattr))
          (expr.Evar _right (type.Tfloat floatsize.F32 noattr)) type_int32s)
          (statement.Sset _result (expr.Econst_int (CompCert.Int.repr 7)
            (type.Tint intsize.I32 signedness.Unsigned noattr)))
          statement.Sskip)
        (statement.Ssequence
          (statement.Scall none
            (expr.Evar _csmith_checksum_print (type.Tfunction
              [(type.Tint intsize.I32 signedness.Unsigned noattr)]
              type_int32s cc_default))
            [(expr.Etempvar _result (type.Tint intsize.I32 signedness.Unsigned noattr))])
          (statement.Sreturn (some (expr.Econst_int (CompCert.Int.repr 0) type_int32s))))))
}

def composites : List composite_definition := []

def global_definitions : List (ident × globdef (fundef_type function) type) :=
  [(_csmith_checksum_print,
    globdef.Gfun (fundef_type.External (external_function.EF_external "csmith_checksum_print"
      { sig_args := [xtype.Xint], sig_res := xtype.Xint, sig_cc := cc_default })
      [(type.Tint intsize.I32 signedness.Unsigned noattr)] type_int32s cc_default)),
   (_left, globdef.Gvar v_left),
   (_right, globdef.Gvar v_right),
   (_main, globdef.Gfun (fundef_type.Internal f_main))]

def public_idents : List ident := [_main, _left, _right, _csmith_checksum_print]

def prog : program_type function :=
  make_program! function composites global_definitions public_idents _main
