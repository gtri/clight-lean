import CLightLean.CLight

attribute [instance] x86_64
-- Neither `x86_64` nor `x86_32` (CLightLean/Archi.lean) is a global
-- `instance` -- both are plain `def`s, by design, since `Archi` has no
-- parameters to disambiguate on and two competing global instances would
-- be structurally ambiguous. This line opts this whole file in to `x86_64`
-- explicitly, matching what clightgen's own generated header already does.

-- clightgen (Lean backend) run information:
--   version: 3.17
--   build:    (, )
--   arch:    x86 (64, standard)
--   bitsize: 64
--   endian:  little
--   source:  /mnt/new_storage/projects/verus/CLight-Lean/Test/array_sum_equiv.c
--   normalized: false
--   Archi instance: x86_64

def ___builtin_ais_annot : ident := (30303770880514375679012103607861182 : Nat)
def ___builtin_annot : ident := (1806245498686479628810895294 : Nat)
def ___builtin_annot_intval : ident := (7244945951003588654475720662375441416126 : Nat)
def ___builtin_bswap : ident := (1724685877248640965123030974 : Nat)
def ___builtin_bswap16 : ident := (5547696061875752272513199554494 : Nat)
def ___builtin_bswap32 : ident := (5233259291897265682688822001598 : Nat)
def ___builtin_bswap64 : ident := (5395429437043650498700607274942 : Nat)
def ___builtin_clz : ident := (469078766812154373390270 : Nat)
def ___builtin_clzl : ident := (25856520978719367042219966 : Nat)
def ___builtin_clzll : ident := (1650652822540780977847320510 : Nat)
def ___builtin_ctz : ident := (469669062622513079041982 : Nat)
def ___builtin_ctzl : ident := (25857111274529725747871678 : Nat)
def ___builtin_ctzll : ident := (1650653412836591336552972222 : Nat)
def ___builtin_debug : ident := (1556544987914242128768188350 : Nat)
def ___builtin_expect : ident := (115364889162671663917173358526 : Nat)
def ___builtin_fabs : ident := (27857996169481367213096894 : Nat)
def ___builtin_fabsf : ident := (1536597419048538577246404542 : Nat)
def ___builtin_fmadd : ident := (1493374484074548252663922622 : Nat)
def ___builtin_fmax : ident := (29365316521232322094743486 : Nat)
def ___builtin_fmin : ident := (26380780904058706319687614 : Nat)
def ___builtin_fmsub : ident := (1459911795176933946679672766 : Nat)
def ___builtin_fnmadd : ident := (95575967517583508903697104830 : Nat)
def ___builtin_fnmsub : ident := (93434355428136193320705114046 : Nat)
def ___builtin_fsqrt : ident := (1807166734850128206852833214 : Nat)
def ___builtin_membar : ident := (112849401203679898087896694718 : Nat)
def ___builtin_memcpy_aligned : ident := (26908785589146098326477794481020231027834814 : Nat)
def ___builtin_read16_reversed : ident := (1722190430963115689536940915573820800533839806 : Nat)
def ___builtin_read32_reversed : ident := (1722190430963115684623866384659967834527940542 : Nat)
def ___builtin_sel : ident := (402467573961989182504894 : Nat)
def ___builtin_sqrt : ident := (28236981067711216130506686 : Nat)
def ___builtin_unreachable : ident := (104119558379386447252596066449494687678 : Nat)
def ___builtin_va_arg : ident := (99560774972908693690150076350 : Nat)
def ___builtin_va_copy : ident := (7795776575233686167852206833598 : Nat)
def ___builtin_va_end : ident := (95770792528416831227446214590 : Nat)
def ___builtin_va_start : ident := (473718132770801822480211367215038 : Nat)
def ___builtin_write16_reversed : ident := (110220187581639404130389322663063742220938559422 : Nat)
def ___builtin_write32_reversed : ident := (110220187581639403815952552684577152396561006526 : Nat)
def ___compcert_i64_dtos : ident := (29979716304623666515338210580680638 : Nat)
def ___compcert_i64_dtou : ident := (30628753411940519968904522621833150 : Nat)
def ___compcert_i64_sar : ident := (462252962922391389178819298512830 : Nat)
def ___compcert_i64_sdiv : ident := (30921599269693830241354384549138366 : Nat)
def ___compcert_i64_shl : ident := (432383945654513733906053229236158 : Nat)
def ___compcert_i64_shr : ident := (462807560059991239541974106165182 : Nat)
def ___compcert_i64_smod : ident := (25111401971710255043931838951247806 : Nat)
def ___compcert_i64_smulh : ident := (1689272968746527987493591833343217598 : Nat)
def ___compcert_i64_stod : ident := (25111956568847854894294993758900158 : Nat)
def ___compcert_i64_stof : ident := (25760993676164708347861305800052670 : Nat)
def ___compcert_i64_udiv : ident := (30921601745573908812114934347386814 : Nat)
def ___compcert_i64_umod : ident := (25111404447590333614692388749496254 : Nat)
def ___compcert_i64_umulh : ident := (1689272971222408066064352383141466046 : Nat)
def ___compcert_i64_utod : ident := (25111959044727933465055543557148606 : Nat)
def ___compcert_i64_utof : ident := (25760996152044786918621855598301118 : Nat)
def ___compcert_va_composite : ident := (427163956635663619511819329762952789151678 : Nat)
def ___compcert_va_float64 : ident := (90521582509840790022117316103474565054 : Nat)
def ___compcert_va_int32 : ident := (21435762804951289275389675485319102 : Nat)
def ___compcert_va_int64 : ident := (22100011719470881481773947964936126 : Nat)
def _a : ident := (74 : Nat)
def _acc : ident := (312074 : Nat)
def _b : ident := (75 : Nat)
def _i : ident := (82 : Nat)
def _main : ident := (22880918 : Nat)
def _n : ident := (87 : Nat)
def _sum_inplace : ident := (90146958993193002908 : Nat)
def _sum_separate : ident := (5789006664154415196060 : Nat)

def f_sum_inplace : function := {
  fn_return := (type.Tint intsize.I32 signedness.Signed noattr),
  fn_callconv := cc_default,
  fn_params := [(_a,
                 (type.Tpointer
                   (type.Tint intsize.I32 signedness.Signed noattr) noattr)),
                (_b,
                 (type.Tpointer
                   (type.Tint intsize.I32 signedness.Signed noattr) noattr)),
                (_n, (type.Tint intsize.I32 signedness.Signed noattr))],
  fn_vars := [],
  fn_temps := [(_i, (type.Tint intsize.I32 signedness.Signed noattr)),
               (_acc, (type.Tint intsize.I32 signedness.Signed noattr))],
  fn_body :=
(statement.Ssequence
  (statement.Ssequence
    (statement.Ssequence
      statement.Sskip
      (statement.Sset _i
        (expr.Econst_int (CompCert.Int.repr 0) (type.Tint intsize.I32
                                                 signedness.Signed noattr))))
    (statement.Sloop
      (statement.Ssequence
        (statement.Ssequence
          statement.Sskip
          (statement.Sifthenelse (expr.Ebinop binary_operation.Olt
                                   (expr.Etempvar _i (type.Tint intsize.I32
                                                       signedness.Signed
                                                       noattr))
                                   (expr.Etempvar _n (type.Tint intsize.I32
                                                       signedness.Signed
                                                       noattr))
                                   (type.Tint intsize.I32 signedness.Signed
                                     noattr))
            statement.Sskip
            statement.Sbreak))
        (statement.Ssequence
          statement.Sskip
          (statement.Sassign
            (expr.Ederef
              (expr.Ebinop binary_operation.Oadd
                (expr.Etempvar _a (type.Tpointer
                                    (type.Tint intsize.I32 signedness.Signed
                                      noattr) noattr))
                (expr.Etempvar _i (type.Tint intsize.I32 signedness.Signed
                                    noattr))
                (type.Tpointer
                  (type.Tint intsize.I32 signedness.Signed noattr) noattr))
              (type.Tint intsize.I32 signedness.Signed noattr))
            (expr.Ebinop binary_operation.Oadd
              (expr.Ederef
                (expr.Ebinop binary_operation.Oadd
                  (expr.Etempvar _a (type.Tpointer
                                      (type.Tint intsize.I32
                                        signedness.Signed noattr) noattr))
                  (expr.Etempvar _i (type.Tint intsize.I32 signedness.Signed
                                      noattr))
                  (type.Tpointer
                    (type.Tint intsize.I32 signedness.Signed noattr) noattr))
                (type.Tint intsize.I32 signedness.Signed noattr))
              (expr.Ederef
                (expr.Ebinop binary_operation.Oadd
                  (expr.Etempvar _b (type.Tpointer
                                      (type.Tint intsize.I32
                                        signedness.Signed noattr) noattr))
                  (expr.Etempvar _i (type.Tint intsize.I32 signedness.Signed
                                      noattr))
                  (type.Tpointer
                    (type.Tint intsize.I32 signedness.Signed noattr) noattr))
                (type.Tint intsize.I32 signedness.Signed noattr))
              (type.Tint intsize.I32 signedness.Signed noattr)))))
      (statement.Ssequence
        statement.Sskip
        (statement.Sset _i
          (expr.Ebinop binary_operation.Oadd
            (expr.Etempvar _i (type.Tint intsize.I32 signedness.Signed
                                noattr))
            (expr.Econst_int (CompCert.Int.repr 1) (type.Tint intsize.I32
                                                     signedness.Signed
                                                     noattr))
            (type.Tint intsize.I32 signedness.Signed noattr))))))
  (statement.Ssequence
    (statement.Ssequence
      statement.Sskip
      (statement.Sset _acc
        (expr.Econst_int (CompCert.Int.repr 0) (type.Tint intsize.I32
                                                 signedness.Signed noattr))))
    (statement.Ssequence
      (statement.Ssequence
        (statement.Ssequence
          statement.Sskip
          (statement.Sset _i
            (expr.Econst_int (CompCert.Int.repr 0) (type.Tint intsize.I32
                                                     signedness.Signed
                                                     noattr))))
        (statement.Sloop
          (statement.Ssequence
            (statement.Ssequence
              statement.Sskip
              (statement.Sifthenelse (expr.Ebinop binary_operation.Olt
                                       (expr.Etempvar _i (type.Tint
                                                           intsize.I32
                                                           signedness.Signed
                                                           noattr))
                                       (expr.Etempvar _n (type.Tint
                                                           intsize.I32
                                                           signedness.Signed
                                                           noattr))
                                       (type.Tint intsize.I32
                                         signedness.Signed noattr))
                statement.Sskip
                statement.Sbreak))
            (statement.Ssequence
              statement.Sskip
              (statement.Sset _acc
                (expr.Ebinop binary_operation.Oadd
                  (expr.Etempvar _acc (type.Tint intsize.I32
                                        signedness.Signed noattr))
                  (expr.Ederef
                    (expr.Ebinop binary_operation.Oadd
                      (expr.Etempvar _a (type.Tpointer
                                          (type.Tint intsize.I32
                                            signedness.Signed noattr) noattr))
                      (expr.Etempvar _i (type.Tint intsize.I32
                                          signedness.Signed noattr))
                      (type.Tpointer
                        (type.Tint intsize.I32 signedness.Signed noattr)
                        noattr))
                    (type.Tint intsize.I32 signedness.Signed noattr))
                  (type.Tint intsize.I32 signedness.Signed noattr)))))
          (statement.Ssequence
            statement.Sskip
            (statement.Sset _i
              (expr.Ebinop binary_operation.Oadd
                (expr.Etempvar _i (type.Tint intsize.I32 signedness.Signed
                                    noattr))
                (expr.Econst_int (CompCert.Int.repr 1) (type.Tint intsize.I32
                                                         signedness.Signed
                                                         noattr))
                (type.Tint intsize.I32 signedness.Signed noattr))))))
      (statement.Ssequence
        statement.Sskip
        (statement.Sreturn (some (expr.Etempvar _acc (type.Tint intsize.I32
                                                       signedness.Signed
                                                       noattr))))))))
}

def f_sum_separate : function := {
  fn_return := (type.Tint intsize.I32 signedness.Signed noattr),
  fn_callconv := cc_default,
  fn_params := [(_a,
                 (type.Tpointer
                   (type.Tint intsize.I32 signedness.Signed noattr) noattr)),
                (_b,
                 (type.Tpointer
                   (type.Tint intsize.I32 signedness.Signed noattr) noattr)),
                (_n, (type.Tint intsize.I32 signedness.Signed noattr))],
  fn_vars := [],
  fn_temps := [(_acc, (type.Tint intsize.I32 signedness.Signed noattr)),
               (_i, (type.Tint intsize.I32 signedness.Signed noattr))],
  fn_body :=
(statement.Ssequence
  (statement.Ssequence
    statement.Sskip
    (statement.Sset _acc
      (expr.Econst_int (CompCert.Int.repr 0) (type.Tint intsize.I32
                                               signedness.Signed noattr))))
  (statement.Ssequence
    (statement.Ssequence
      (statement.Ssequence
        statement.Sskip
        (statement.Sset _i
          (expr.Econst_int (CompCert.Int.repr 0) (type.Tint intsize.I32
                                                   signedness.Signed noattr))))
      (statement.Sloop
        (statement.Ssequence
          (statement.Ssequence
            statement.Sskip
            (statement.Sifthenelse (expr.Ebinop binary_operation.Olt
                                     (expr.Etempvar _i (type.Tint intsize.I32
                                                         signedness.Signed
                                                         noattr))
                                     (expr.Etempvar _n (type.Tint intsize.I32
                                                         signedness.Signed
                                                         noattr))
                                     (type.Tint intsize.I32 signedness.Signed
                                       noattr))
              statement.Sskip
              statement.Sbreak))
          (statement.Ssequence
            statement.Sskip
            (statement.Sset _acc
              (expr.Ebinop binary_operation.Oadd
                (expr.Etempvar _acc (type.Tint intsize.I32 signedness.Signed
                                      noattr))
                (expr.Ederef
                  (expr.Ebinop binary_operation.Oadd
                    (expr.Etempvar _a (type.Tpointer
                                        (type.Tint intsize.I32
                                          signedness.Signed noattr) noattr))
                    (expr.Etempvar _i (type.Tint intsize.I32
                                        signedness.Signed noattr))
                    (type.Tpointer
                      (type.Tint intsize.I32 signedness.Signed noattr)
                      noattr))
                  (type.Tint intsize.I32 signedness.Signed noattr))
                (type.Tint intsize.I32 signedness.Signed noattr)))))
        (statement.Ssequence
          statement.Sskip
          (statement.Sset _i
            (expr.Ebinop binary_operation.Oadd
              (expr.Etempvar _i (type.Tint intsize.I32 signedness.Signed
                                  noattr))
              (expr.Econst_int (CompCert.Int.repr 1) (type.Tint intsize.I32
                                                       signedness.Signed
                                                       noattr))
              (type.Tint intsize.I32 signedness.Signed noattr))))))
    (statement.Ssequence
      (statement.Ssequence
        (statement.Ssequence
          statement.Sskip
          (statement.Sset _i
            (expr.Econst_int (CompCert.Int.repr 0) (type.Tint intsize.I32
                                                     signedness.Signed
                                                     noattr))))
        (statement.Sloop
          (statement.Ssequence
            (statement.Ssequence
              statement.Sskip
              (statement.Sifthenelse (expr.Ebinop binary_operation.Olt
                                       (expr.Etempvar _i (type.Tint
                                                           intsize.I32
                                                           signedness.Signed
                                                           noattr))
                                       (expr.Etempvar _n (type.Tint
                                                           intsize.I32
                                                           signedness.Signed
                                                           noattr))
                                       (type.Tint intsize.I32
                                         signedness.Signed noattr))
                statement.Sskip
                statement.Sbreak))
            (statement.Ssequence
              statement.Sskip
              (statement.Sset _acc
                (expr.Ebinop binary_operation.Oadd
                  (expr.Etempvar _acc (type.Tint intsize.I32
                                        signedness.Signed noattr))
                  (expr.Ederef
                    (expr.Ebinop binary_operation.Oadd
                      (expr.Etempvar _b (type.Tpointer
                                          (type.Tint intsize.I32
                                            signedness.Signed noattr) noattr))
                      (expr.Etempvar _i (type.Tint intsize.I32
                                          signedness.Signed noattr))
                      (type.Tpointer
                        (type.Tint intsize.I32 signedness.Signed noattr)
                        noattr))
                    (type.Tint intsize.I32 signedness.Signed noattr))
                  (type.Tint intsize.I32 signedness.Signed noattr)))))
          (statement.Ssequence
            statement.Sskip
            (statement.Sset _i
              (expr.Ebinop binary_operation.Oadd
                (expr.Etempvar _i (type.Tint intsize.I32 signedness.Signed
                                    noattr))
                (expr.Econst_int (CompCert.Int.repr 1) (type.Tint intsize.I32
                                                         signedness.Signed
                                                         noattr))
                (type.Tint intsize.I32 signedness.Signed noattr))))))
      (statement.Ssequence
        statement.Sskip
        (statement.Sreturn (some (expr.Etempvar _acc (type.Tint intsize.I32
                                                       signedness.Signed
                                                       noattr))))))))
}

def composites : List composite_definition :=
[]

def global_definitions : List (ident × globdef (fundef_type function) type) :=
[(___compcert_va_int32,
   globdef.Gfun (fundef_type.External (external_function.EF_runtime "__compcert_va_int32"
                                        { sig_args := [xtype.Xptr],
                                          sig_res := xtype.Xint,
                                          sig_cc := cc_default })
     [(type.Tpointer type.Tvoid noattr)]
     (type.Tint intsize.I32 signedness.Unsigned noattr) cc_default)),
 (___compcert_va_int64,
   globdef.Gfun (fundef_type.External (external_function.EF_runtime "__compcert_va_int64"
                                        { sig_args := [xtype.Xptr],
                                          sig_res := xtype.Xlong,
                                          sig_cc := cc_default })
     [(type.Tpointer type.Tvoid noattr)]
     (type.Tlong signedness.Unsigned noattr) cc_default)),
 (___compcert_va_float64,
   globdef.Gfun (fundef_type.External (external_function.EF_runtime "__compcert_va_float64"
                                        { sig_args := [xtype.Xptr],
                                          sig_res := xtype.Xfloat,
                                          sig_cc := cc_default })
     [(type.Tpointer type.Tvoid noattr)] (type.Tfloat floatsize.F64 noattr)
     cc_default)),
 (___compcert_va_composite,
   globdef.Gfun (fundef_type.External (external_function.EF_runtime "__compcert_va_composite"
                                        { sig_args := [xtype.Xptr,
                                                       xtype.Xlong],
                                          sig_res := xtype.Xptr,
                                          sig_cc := cc_default })
     [(type.Tpointer type.Tvoid noattr),
      (type.Tlong signedness.Unsigned noattr)]
     (type.Tpointer type.Tvoid noattr) cc_default)),
 (___compcert_i64_dtos,
   globdef.Gfun (fundef_type.External (external_function.EF_runtime "__compcert_i64_dtos"
                                        { sig_args := [xtype.Xfloat],
                                          sig_res := xtype.Xlong,
                                          sig_cc := cc_default })
     [(type.Tfloat floatsize.F64 noattr)]
     (type.Tlong signedness.Signed noattr) cc_default)),
 (___compcert_i64_dtou,
   globdef.Gfun (fundef_type.External (external_function.EF_runtime "__compcert_i64_dtou"
                                        { sig_args := [xtype.Xfloat],
                                          sig_res := xtype.Xlong,
                                          sig_cc := cc_default })
     [(type.Tfloat floatsize.F64 noattr)]
     (type.Tlong signedness.Unsigned noattr) cc_default)),
 (___compcert_i64_stod,
   globdef.Gfun (fundef_type.External (external_function.EF_runtime "__compcert_i64_stod"
                                        { sig_args := [xtype.Xlong],
                                          sig_res := xtype.Xfloat,
                                          sig_cc := cc_default })
     [(type.Tlong signedness.Signed noattr)]
     (type.Tfloat floatsize.F64 noattr) cc_default)),
 (___compcert_i64_utod,
   globdef.Gfun (fundef_type.External (external_function.EF_runtime "__compcert_i64_utod"
                                        { sig_args := [xtype.Xlong],
                                          sig_res := xtype.Xfloat,
                                          sig_cc := cc_default })
     [(type.Tlong signedness.Unsigned noattr)]
     (type.Tfloat floatsize.F64 noattr) cc_default)),
 (___compcert_i64_stof,
   globdef.Gfun (fundef_type.External (external_function.EF_runtime "__compcert_i64_stof"
                                        { sig_args := [xtype.Xlong],
                                          sig_res := xtype.Xsingle,
                                          sig_cc := cc_default })
     [(type.Tlong signedness.Signed noattr)]
     (type.Tfloat floatsize.F32 noattr) cc_default)),
 (___compcert_i64_utof,
   globdef.Gfun (fundef_type.External (external_function.EF_runtime "__compcert_i64_utof"
                                        { sig_args := [xtype.Xlong],
                                          sig_res := xtype.Xsingle,
                                          sig_cc := cc_default })
     [(type.Tlong signedness.Unsigned noattr)]
     (type.Tfloat floatsize.F32 noattr) cc_default)),
 (___compcert_i64_sdiv,
   globdef.Gfun (fundef_type.External (external_function.EF_runtime "__compcert_i64_sdiv"
                                        { sig_args := [xtype.Xlong,
                                                       xtype.Xlong],
                                          sig_res := xtype.Xlong,
                                          sig_cc := cc_default })
     [(type.Tlong signedness.Signed noattr),
      (type.Tlong signedness.Signed noattr)]
     (type.Tlong signedness.Signed noattr) cc_default)),
 (___compcert_i64_udiv,
   globdef.Gfun (fundef_type.External (external_function.EF_runtime "__compcert_i64_udiv"
                                        { sig_args := [xtype.Xlong,
                                                       xtype.Xlong],
                                          sig_res := xtype.Xlong,
                                          sig_cc := cc_default })
     [(type.Tlong signedness.Unsigned noattr),
      (type.Tlong signedness.Unsigned noattr)]
     (type.Tlong signedness.Unsigned noattr) cc_default)),
 (___compcert_i64_smod,
   globdef.Gfun (fundef_type.External (external_function.EF_runtime "__compcert_i64_smod"
                                        { sig_args := [xtype.Xlong,
                                                       xtype.Xlong],
                                          sig_res := xtype.Xlong,
                                          sig_cc := cc_default })
     [(type.Tlong signedness.Signed noattr),
      (type.Tlong signedness.Signed noattr)]
     (type.Tlong signedness.Signed noattr) cc_default)),
 (___compcert_i64_umod,
   globdef.Gfun (fundef_type.External (external_function.EF_runtime "__compcert_i64_umod"
                                        { sig_args := [xtype.Xlong,
                                                       xtype.Xlong],
                                          sig_res := xtype.Xlong,
                                          sig_cc := cc_default })
     [(type.Tlong signedness.Unsigned noattr),
      (type.Tlong signedness.Unsigned noattr)]
     (type.Tlong signedness.Unsigned noattr) cc_default)),
 (___compcert_i64_shl,
   globdef.Gfun (fundef_type.External (external_function.EF_runtime "__compcert_i64_shl"
                                        { sig_args := [xtype.Xlong,
                                                       xtype.Xint],
                                          sig_res := xtype.Xlong,
                                          sig_cc := cc_default })
     [(type.Tlong signedness.Signed noattr),
      (type.Tint intsize.I32 signedness.Signed noattr)]
     (type.Tlong signedness.Signed noattr) cc_default)),
 (___compcert_i64_shr,
   globdef.Gfun (fundef_type.External (external_function.EF_runtime "__compcert_i64_shr"
                                        { sig_args := [xtype.Xlong,
                                                       xtype.Xint],
                                          sig_res := xtype.Xlong,
                                          sig_cc := cc_default })
     [(type.Tlong signedness.Unsigned noattr),
      (type.Tint intsize.I32 signedness.Signed noattr)]
     (type.Tlong signedness.Unsigned noattr) cc_default)),
 (___compcert_i64_sar,
   globdef.Gfun (fundef_type.External (external_function.EF_runtime "__compcert_i64_sar"
                                        { sig_args := [xtype.Xlong,
                                                       xtype.Xint],
                                          sig_res := xtype.Xlong,
                                          sig_cc := cc_default })
     [(type.Tlong signedness.Signed noattr),
      (type.Tint intsize.I32 signedness.Signed noattr)]
     (type.Tlong signedness.Signed noattr) cc_default)),
 (___compcert_i64_smulh,
   globdef.Gfun (fundef_type.External (external_function.EF_runtime "__compcert_i64_smulh"
                                        { sig_args := [xtype.Xlong,
                                                       xtype.Xlong],
                                          sig_res := xtype.Xlong,
                                          sig_cc := cc_default })
     [(type.Tlong signedness.Signed noattr),
      (type.Tlong signedness.Signed noattr)]
     (type.Tlong signedness.Signed noattr) cc_default)),
 (___compcert_i64_umulh,
   globdef.Gfun (fundef_type.External (external_function.EF_runtime "__compcert_i64_umulh"
                                        { sig_args := [xtype.Xlong,
                                                       xtype.Xlong],
                                          sig_res := xtype.Xlong,
                                          sig_cc := cc_default })
     [(type.Tlong signedness.Unsigned noattr),
      (type.Tlong signedness.Unsigned noattr)]
     (type.Tlong signedness.Unsigned noattr) cc_default)),
 (___builtin_ais_annot,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_ais_annot"
                                        { sig_args := [xtype.Xptr],
                                          sig_res := xtype.Xvoid,
                                          sig_cc := { cc_vararg := (some 1), cc_unproto := false, cc_structret := false } })
     [(type.Tpointer (type.Tint intsize.I8 signedness.Signed noattr) noattr)]
     type.Tvoid
     { cc_vararg := (some 1), cc_unproto := false, cc_structret := false })),
 (___builtin_bswap64,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_bswap64"
                                        { sig_args := [xtype.Xlong],
                                          sig_res := xtype.Xlong,
                                          sig_cc := cc_default })
     [(type.Tlong signedness.Unsigned noattr)]
     (type.Tlong signedness.Unsigned noattr) cc_default)),
 (___builtin_bswap,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_bswap"
                                        { sig_args := [xtype.Xint],
                                          sig_res := xtype.Xint,
                                          sig_cc := cc_default })
     [(type.Tint intsize.I32 signedness.Unsigned noattr)]
     (type.Tint intsize.I32 signedness.Unsigned noattr) cc_default)),
 (___builtin_bswap32,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_bswap32"
                                        { sig_args := [xtype.Xint],
                                          sig_res := xtype.Xint,
                                          sig_cc := cc_default })
     [(type.Tint intsize.I32 signedness.Unsigned noattr)]
     (type.Tint intsize.I32 signedness.Unsigned noattr) cc_default)),
 (___builtin_bswap16,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_bswap16"
                                        { sig_args := [xtype.Xint16unsigned],
                                          sig_res := xtype.Xint16unsigned,
                                          sig_cc := cc_default })
     [(type.Tint intsize.I16 signedness.Unsigned noattr)]
     (type.Tint intsize.I16 signedness.Unsigned noattr) cc_default)),
 (___builtin_clz,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_clz"
                                        { sig_args := [xtype.Xint],
                                          sig_res := xtype.Xint,
                                          sig_cc := cc_default })
     [(type.Tint intsize.I32 signedness.Unsigned noattr)]
     (type.Tint intsize.I32 signedness.Signed noattr) cc_default)),
 (___builtin_clzl,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_clzl"
                                        { sig_args := [xtype.Xlong],
                                          sig_res := xtype.Xint,
                                          sig_cc := cc_default })
     [(type.Tlong signedness.Unsigned noattr)]
     (type.Tint intsize.I32 signedness.Signed noattr) cc_default)),
 (___builtin_clzll,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_clzll"
                                        { sig_args := [xtype.Xlong],
                                          sig_res := xtype.Xint,
                                          sig_cc := cc_default })
     [(type.Tlong signedness.Unsigned noattr)]
     (type.Tint intsize.I32 signedness.Signed noattr) cc_default)),
 (___builtin_ctz,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_ctz"
                                        { sig_args := [xtype.Xint],
                                          sig_res := xtype.Xint,
                                          sig_cc := cc_default })
     [(type.Tint intsize.I32 signedness.Unsigned noattr)]
     (type.Tint intsize.I32 signedness.Signed noattr) cc_default)),
 (___builtin_ctzl,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_ctzl"
                                        { sig_args := [xtype.Xlong],
                                          sig_res := xtype.Xint,
                                          sig_cc := cc_default })
     [(type.Tlong signedness.Unsigned noattr)]
     (type.Tint intsize.I32 signedness.Signed noattr) cc_default)),
 (___builtin_ctzll,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_ctzll"
                                        { sig_args := [xtype.Xlong],
                                          sig_res := xtype.Xint,
                                          sig_cc := cc_default })
     [(type.Tlong signedness.Unsigned noattr)]
     (type.Tint intsize.I32 signedness.Signed noattr) cc_default)),
 (___builtin_fabs,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_fabs"
                                        { sig_args := [xtype.Xfloat],
                                          sig_res := xtype.Xfloat,
                                          sig_cc := cc_default })
     [(type.Tfloat floatsize.F64 noattr)] (type.Tfloat floatsize.F64 noattr)
     cc_default)),
 (___builtin_fabsf,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_fabsf"
                                        { sig_args := [xtype.Xsingle],
                                          sig_res := xtype.Xsingle,
                                          sig_cc := cc_default })
     [(type.Tfloat floatsize.F32 noattr)] (type.Tfloat floatsize.F32 noattr)
     cc_default)),
 (___builtin_fsqrt,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_fsqrt"
                                        { sig_args := [xtype.Xfloat],
                                          sig_res := xtype.Xfloat,
                                          sig_cc := cc_default })
     [(type.Tfloat floatsize.F64 noattr)] (type.Tfloat floatsize.F64 noattr)
     cc_default)),
 (___builtin_sqrt,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_sqrt"
                                        { sig_args := [xtype.Xfloat],
                                          sig_res := xtype.Xfloat,
                                          sig_cc := cc_default })
     [(type.Tfloat floatsize.F64 noattr)] (type.Tfloat floatsize.F64 noattr)
     cc_default)),
 (___builtin_memcpy_aligned,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_memcpy_aligned"
                                        { sig_args := [xtype.Xptr,
                                                       xtype.Xptr,
                                                       xtype.Xlong,
                                                       xtype.Xlong],
                                          sig_res := xtype.Xvoid,
                                          sig_cc := cc_default })
     [(type.Tpointer type.Tvoid noattr), (type.Tpointer type.Tvoid noattr),
      (type.Tlong signedness.Unsigned noattr),
      (type.Tlong signedness.Unsigned noattr)] type.Tvoid cc_default)),
 (___builtin_sel,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_sel"
                                        { sig_args := [xtype.Xbool],
                                          sig_res := xtype.Xvoid,
                                          sig_cc := { cc_vararg := (some 1), cc_unproto := false, cc_structret := false } })
     [(type.Tint intsize.IBool signedness.Unsigned noattr)] type.Tvoid
     { cc_vararg := (some 1), cc_unproto := false, cc_structret := false })),
 (___builtin_annot,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_annot"
                                        { sig_args := [xtype.Xptr],
                                          sig_res := xtype.Xvoid,
                                          sig_cc := { cc_vararg := (some 1), cc_unproto := false, cc_structret := false } })
     [(type.Tpointer (type.Tint intsize.I8 signedness.Signed noattr) noattr)]
     type.Tvoid
     { cc_vararg := (some 1), cc_unproto := false, cc_structret := false })),
 (___builtin_annot_intval,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_annot_intval"
                                        { sig_args := [xtype.Xptr,
                                                       xtype.Xint],
                                          sig_res := xtype.Xint,
                                          sig_cc := cc_default })
     [(type.Tpointer (type.Tint intsize.I8 signedness.Signed noattr) noattr),
      (type.Tint intsize.I32 signedness.Signed noattr)]
     (type.Tint intsize.I32 signedness.Signed noattr) cc_default)),
 (___builtin_membar,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_membar"
                                        { sig_args := [],
                                          sig_res := xtype.Xvoid,
                                          sig_cc := cc_default }) []
     type.Tvoid cc_default)),
 (___builtin_va_start,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_va_start"
                                        { sig_args := [xtype.Xptr],
                                          sig_res := xtype.Xvoid,
                                          sig_cc := cc_default })
     [(type.Tpointer type.Tvoid noattr)] type.Tvoid cc_default)),
 (___builtin_va_arg,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_va_arg"
                                        { sig_args := [xtype.Xptr,
                                                       xtype.Xint],
                                          sig_res := xtype.Xvoid,
                                          sig_cc := cc_default })
     [(type.Tpointer type.Tvoid noattr),
      (type.Tint intsize.I32 signedness.Unsigned noattr)] type.Tvoid
     cc_default)),
 (___builtin_va_copy,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_va_copy"
                                        { sig_args := [xtype.Xptr,
                                                       xtype.Xptr],
                                          sig_res := xtype.Xvoid,
                                          sig_cc := cc_default })
     [(type.Tpointer type.Tvoid noattr), (type.Tpointer type.Tvoid noattr)]
     type.Tvoid cc_default)),
 (___builtin_va_end,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_va_end"
                                        { sig_args := [xtype.Xptr],
                                          sig_res := xtype.Xvoid,
                                          sig_cc := cc_default })
     [(type.Tpointer type.Tvoid noattr)] type.Tvoid cc_default)),
 (___builtin_unreachable,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_unreachable"
                                        { sig_args := [],
                                          sig_res := xtype.Xvoid,
                                          sig_cc := cc_default }) []
     type.Tvoid cc_default)),
 (___builtin_expect,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_expect"
                                        { sig_args := [xtype.Xlong,
                                                       xtype.Xlong],
                                          sig_res := xtype.Xlong,
                                          sig_cc := cc_default })
     [(type.Tlong signedness.Signed noattr),
      (type.Tlong signedness.Signed noattr)]
     (type.Tlong signedness.Signed noattr) cc_default)),
 (___builtin_fmax,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_fmax"
                                        { sig_args := [xtype.Xfloat,
                                                       xtype.Xfloat],
                                          sig_res := xtype.Xfloat,
                                          sig_cc := cc_default })
     [(type.Tfloat floatsize.F64 noattr), (type.Tfloat floatsize.F64 noattr)]
     (type.Tfloat floatsize.F64 noattr) cc_default)),
 (___builtin_fmin,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_fmin"
                                        { sig_args := [xtype.Xfloat,
                                                       xtype.Xfloat],
                                          sig_res := xtype.Xfloat,
                                          sig_cc := cc_default })
     [(type.Tfloat floatsize.F64 noattr), (type.Tfloat floatsize.F64 noattr)]
     (type.Tfloat floatsize.F64 noattr) cc_default)),
 (___builtin_fmadd,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_fmadd"
                                        { sig_args := [xtype.Xfloat,
                                                       xtype.Xfloat,
                                                       xtype.Xfloat],
                                          sig_res := xtype.Xfloat,
                                          sig_cc := cc_default })
     [(type.Tfloat floatsize.F64 noattr), (type.Tfloat floatsize.F64 noattr),
      (type.Tfloat floatsize.F64 noattr)] (type.Tfloat floatsize.F64 noattr)
     cc_default)),
 (___builtin_fmsub,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_fmsub"
                                        { sig_args := [xtype.Xfloat,
                                                       xtype.Xfloat,
                                                       xtype.Xfloat],
                                          sig_res := xtype.Xfloat,
                                          sig_cc := cc_default })
     [(type.Tfloat floatsize.F64 noattr), (type.Tfloat floatsize.F64 noattr),
      (type.Tfloat floatsize.F64 noattr)] (type.Tfloat floatsize.F64 noattr)
     cc_default)),
 (___builtin_fnmadd,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_fnmadd"
                                        { sig_args := [xtype.Xfloat,
                                                       xtype.Xfloat,
                                                       xtype.Xfloat],
                                          sig_res := xtype.Xfloat,
                                          sig_cc := cc_default })
     [(type.Tfloat floatsize.F64 noattr), (type.Tfloat floatsize.F64 noattr),
      (type.Tfloat floatsize.F64 noattr)] (type.Tfloat floatsize.F64 noattr)
     cc_default)),
 (___builtin_fnmsub,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_fnmsub"
                                        { sig_args := [xtype.Xfloat,
                                                       xtype.Xfloat,
                                                       xtype.Xfloat],
                                          sig_res := xtype.Xfloat,
                                          sig_cc := cc_default })
     [(type.Tfloat floatsize.F64 noattr), (type.Tfloat floatsize.F64 noattr),
      (type.Tfloat floatsize.F64 noattr)] (type.Tfloat floatsize.F64 noattr)
     cc_default)),
 (___builtin_read16_reversed,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_read16_reversed"
                                        { sig_args := [xtype.Xptr],
                                          sig_res := xtype.Xint16unsigned,
                                          sig_cc := cc_default })
     [(type.Tpointer (type.Tint intsize.I16 signedness.Unsigned noattr)
        noattr)] (type.Tint intsize.I16 signedness.Unsigned noattr)
     cc_default)),
 (___builtin_read32_reversed,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_read32_reversed"
                                        { sig_args := [xtype.Xptr],
                                          sig_res := xtype.Xint,
                                          sig_cc := cc_default })
     [(type.Tpointer (type.Tint intsize.I32 signedness.Unsigned noattr)
        noattr)] (type.Tint intsize.I32 signedness.Unsigned noattr)
     cc_default)),
 (___builtin_write16_reversed,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_write16_reversed"
                                        { sig_args := [xtype.Xptr,
                                                       xtype.Xint16unsigned],
                                          sig_res := xtype.Xvoid,
                                          sig_cc := cc_default })
     [(type.Tpointer (type.Tint intsize.I16 signedness.Unsigned noattr)
        noattr), (type.Tint intsize.I16 signedness.Unsigned noattr)]
     type.Tvoid cc_default)),
 (___builtin_write32_reversed,
   globdef.Gfun (fundef_type.External (external_function.EF_builtin "__builtin_write32_reversed"
                                        { sig_args := [xtype.Xptr,
                                                       xtype.Xint],
                                          sig_res := xtype.Xvoid,
                                          sig_cc := cc_default })
     [(type.Tpointer (type.Tint intsize.I32 signedness.Unsigned noattr)
        noattr), (type.Tint intsize.I32 signedness.Unsigned noattr)]
     type.Tvoid cc_default)),
 (___builtin_debug,
   globdef.Gfun (fundef_type.External (external_function.EF_external "__builtin_debug"
                                        { sig_args := [xtype.Xint],
                                          sig_res := xtype.Xvoid,
                                          sig_cc := { cc_vararg := (some 1), cc_unproto := false, cc_structret := false } })
     [(type.Tint intsize.I32 signedness.Signed noattr)] type.Tvoid
     { cc_vararg := (some 1), cc_unproto := false, cc_structret := false })),
 (_sum_inplace, globdef.Gfun (fundef_type.Internal f_sum_inplace)),
 (_sum_separate, globdef.Gfun (fundef_type.Internal f_sum_separate))]

def public_idents : List ident :=
[_sum_separate, _sum_inplace, ___builtin_debug, ___builtin_write32_reversed,
 ___builtin_write16_reversed, ___builtin_read32_reversed,
 ___builtin_read16_reversed, ___builtin_fnmsub, ___builtin_fnmadd,
 ___builtin_fmsub, ___builtin_fmadd, ___builtin_fmin, ___builtin_fmax,
 ___builtin_expect, ___builtin_unreachable, ___builtin_va_end,
 ___builtin_va_copy, ___builtin_va_arg, ___builtin_va_start,
 ___builtin_membar, ___builtin_annot_intval, ___builtin_annot,
 ___builtin_sel, ___builtin_memcpy_aligned, ___builtin_sqrt,
 ___builtin_fsqrt, ___builtin_fabsf, ___builtin_fabs, ___builtin_ctzll,
 ___builtin_ctzl, ___builtin_ctz, ___builtin_clzll, ___builtin_clzl,
 ___builtin_clz, ___builtin_bswap16, ___builtin_bswap32, ___builtin_bswap,
 ___builtin_bswap64, ___builtin_ais_annot, ___compcert_i64_umulh,
 ___compcert_i64_smulh, ___compcert_i64_sar, ___compcert_i64_shr,
 ___compcert_i64_shl, ___compcert_i64_umod, ___compcert_i64_smod,
 ___compcert_i64_udiv, ___compcert_i64_sdiv, ___compcert_i64_utof,
 ___compcert_i64_stof, ___compcert_i64_utod, ___compcert_i64_stod,
 ___compcert_i64_dtou, ___compcert_i64_dtos, ___compcert_va_composite,
 ___compcert_va_float64, ___compcert_va_int64, ___compcert_va_int32]

def prog : program_type function :=
  make_program! function composites global_definitions public_idents _main

-- ============================================================================
-- Hand-written equivalence proof (below this point: not clightgen output).
--
-- Goal: sum_inplace and sum_separate return the same int for all inputs
-- where `a` and `b` denote disjoint, fully-readable length-`n` int arrays.
-- ============================================================================

set_option linter.style.nameCheck false
set_option autoImplicit false

open Smallstep (star star_one star_trans)

/-- Some genv for `prog`; our functions never touch globals, call other
    functions, or use `sizeof`/`alignof`, so its exact contents never matter
    beyond well-typedness. -/
def ge : genv := globalenv prog

abbrev tint : type := type.Tint intsize.I32 signedness.Signed noattr
abbrev tintptr : type := type.Tpointer tint noattr

/-- `int_array_at m b n vs` : block `b`, at byte offset 0, holds `n`
    consecutive readable `int`s whose values are `vs 0, vs 1, ..., vs (n-1)`.
    This is how "the length of both arrays is `n`" gets stated: `vs` is a
    total function `Nat → CompCert.Int`, but only indices `< n` are
    constrained to correspond to real, successfully-loadable memory. -/
def int_array_at (m : Memory.mem) (b : block) (n : Nat) (vs : Nat → CompCert.Int) : Prop :=
  ∀ i : Nat, i < n → Memory.load .Mint32 m b (4 * (i : Int)) = some (.Vint (vs i))

/-- Left-to-right running sum of `vs 0, ..., vs (n-1)`, matching the exact
    accumulation order of the C loops (`acc = 0; for i in 0..n: acc += vs i`). -/
def isum (n : Nat) (vs : Nat → CompCert.Int) : CompCert.Int :=
  match n with
  | 0 => CompCert.Int.zero
  | n + 1 => CompCert.Int.add (isum n vs) (vs n)

theorem int_repr_signed_of_range (i : Nat) (h : i ≤ 2147483647) :
    (CompCert.Int.repr (i : Int)).signed = (i : Int) := by
  unfold CompCert.Int.repr CompCert.Int.signed UInt32.ofInt
  have hb : (UInt32.ofNat ((i:Int) % 2^32).toNat).toBitVec
      = BitVec.ofNat 32 ((i:Int) % 2^32).toNat := rfl
  rw [hb, BitVec.toInt_ofNat']
  have h1 : ((i:Int) % 2^32).toNat = i := by omega
  rw [h1]
  unfold Int.bmod
  norm_num
  omega

theorem ptr_index_offset (i : Nat) (h : i < 2^30) :
    Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_int (CompCert.Int.repr (i:Int)))
    = Ptrofs.repr (4 * (i:Int)) := by
  have hsig : (CompCert.Int.repr (i:Int)).signed = (i:Int) :=
    int_repr_signed_of_range i (by omega)
  have h1 : Ptrofs.of_int (CompCert.Int.repr (i:Int)) = Ptrofs.repr (i:Int) := by
    simp only [Ptrofs.of_int, hsig]
  rw [h1, Ptrofs.eq_iff_unsigned]
  simp only [Ptrofs.mul, Ptrofs.unsigned_repr_eq, Ptrofs.modulus, Ptrofs.wordsize,
    Archi.ptr64]
  norm_num
  omega

theorem ptrofs_repr_signed_of_range (z : Int) (h0 : 0 ≤ z) (h1 : z < 2^62) :
    (Ptrofs.repr z).signed = z := by
  have hm : Ptrofs.modulus = 2^64 := by
    unfold Ptrofs.modulus Ptrofs.wordsize
    simp [Archi.ptr64]
  unfold Ptrofs.repr Ptrofs.signed
  simp only [hm]
  dsimp only [Int.bmod]
  omega

/-- Reading `*(aptr + aidx)` for a pointer-to-`aidx`-th-int array element. -/
theorem eval_read_array (ge : genv) (e : env) (le : temp_env) (m : Memory.mem)
    (aptr aidx : expr) (b : block) (i n : Nat) (vs : Nat → CompCert.Int)
    (haptr : eval_expr ge e le m aptr (.Vptr b Ptrofs.zero))
    (haidx : eval_expr ge e le m aidx (.Vint (CompCert.Int.repr (i:Int))))
    (htaptr : typeof aptr = tintptr) (htaidx : typeof aidx = tint)
    (harr : int_array_at m b n vs) (hi : i < n) (hn : n < 2^30) :
    eval_expr ge e le m (.Ederef (.Ebinop .Oadd aptr aidx tintptr) tint) (.Vint (vs i)) := by
  have hoff : Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_int (CompCert.Int.repr (i:Int)))
      = Ptrofs.repr (4 * (i:Int)) := ptr_index_offset i (by omega)
  have hbin : sem_binary_operation ge.genv_cenv .Oadd (.Vptr b Ptrofs.zero) tintptr
      (.Vint (CompCert.Int.repr (i:Int))) tint m = some (.Vptr b (Ptrofs.repr (4 * (i:Int)))) := by
    show sem_binary_operation ge.genv_cenv .Oadd (.Vptr b Ptrofs.zero) tintptr
      (.Vint (CompCert.Int.repr (i:Int))) tint m = _
    unfold tintptr tint
    simp only [sem_binary_operation, sem_add, classify_add, typeconv, remove_attributes,
      change_attributes, sem_add_ptr_int, ptrofs_of_int]
    norm_num [sizeof]
    exact hoff
  have heb : eval_expr ge e le m (.Ebinop .Oadd aptr aidx tintptr)
      (.Vptr b (Ptrofs.repr (4 * (i:Int)))) :=
    eval_expr.eval_Ebinop .Oadd aptr aidx tintptr (.Vptr b Ptrofs.zero) (.Vint (CompCert.Int.repr (i:Int)))
      (.Vptr b (Ptrofs.repr (4 * (i:Int)))) haptr haidx (by rw [htaptr, htaidx]; exact hbin)
  have hlv : eval_lvalue ge e le m (.Ederef (.Ebinop .Oadd aptr aidx tintptr) tint)
      b (Ptrofs.repr (4 * (i:Int))) .Full :=
    eval_lvalue.eval_Ederef (.Ebinop .Oadd aptr aidx tintptr) tint b (Ptrofs.repr (4 * (i:Int))) heb
  have hload : Memory.loadv .Mint32 m (.Vptr b (Ptrofs.repr (4 * (i:Int)))) = some (.Vint (vs i)) := by
    show Memory.load .Mint32 m b (Ptrofs.repr (4 * (i:Int))).signed = some (.Vint (vs i))
    have hsig : (Ptrofs.repr (4 * (i:Int))).signed = 4 * (i:Int) :=
      ptrofs_repr_signed_of_range (4 * (i:Int)) (by omega) (by omega)
    rw [hsig]
    exact harr i hi
  have hderef : deref_loc tint m b (Ptrofs.repr (4 * (i:Int))) .Full (.Vint (vs i)) :=
    deref_loc.deref_loc_value .Mint32 (.Vint (vs i)) (by unfold tint; rfl) hload
  exact eval_expr.eval_Elvalue (.Ederef (.Ebinop .Oadd aptr aidx tintptr) tint) b
    (Ptrofs.repr (4 * (i:Int))) .Full (.Vint (vs i)) hlv hderef

theorem sem_cast_tint_tint (v : CompCert.Int) (m : Memory.mem) :
    sem_cast (.Vint v) tint tint m = some (.Vint v) := by
  unfold sem_cast tint classify_cast
  simp only [Archi.ptr64]
  norm_num [cast_int_int]

theorem store_ok_of_load_ok (m : Memory.mem) (b : block) (ofs : Int) (v : CompCert.Int) (v0 : val)
    (hload : Memory.load .Mint32 m b ofs = some v0) :
    ∃ m', Memory.store .Mint32 m b ofs (.Vint v) = some m' := by
  have ha : Memory.is_aligned ofs .Mint32 = true := by
    unfold Memory.load at hload
    dsimp only at hload
    by_contra hcon
    rw [if_pos hcon] at hload
    cases hload
  have hb : ((List.range (Memory.size_chunk .Mint32)).map (fun (i : Nat) => (b, ofs + (i:Int)))).all
      (fun p => Memory.valid_pointer m p.1 p.2) = true := by
    unfold Memory.load at hload
    dsimp only at hload
    rw [if_neg (by simp [ha])] at hload
    by_contra hcon
    rw [if_neg hcon] at hload
    cases hload
  unfold Memory.store
  dsimp only
  rw [if_neg (by simp [ha])]
  have hlen : (Memory.encode_val .Mint32 (.Vint v)).length = Memory.size_chunk .Mint32 := by
    unfold Memory.encode_val Memory.size_chunk
    rfl
  rw [if_neg (by simp [hlen])]
  rw [if_pos hb]
  generalize hpairs : (List.zip _ (Memory.encode_val memory_chunk.Mint32 (val.Vint v))) = pairs
  clear hpairs hload ha hb hlen
  induction pairs generalizing m with
  | nil => exact ⟨m, rfl⟩
  | cons hd tl ih =>
      obtain ⟨⟨b', ofs'⟩, byte⟩ := hd
      exact ih { contents := m.contents.insert (b', ofs') byte, blocks := m.blocks, nextblock := m.nextblock }


/-- Writing `*(aptr + aidx) = aval` for a pointer-to-`aidx`-th-int array element.
    Store success is derived from `harr`/`hn`/`hlt` (the location was already
    known-readable), not assumed. -/
theorem step_write_array (ge : genv) (f : function) (e : env) (le : temp_env) (m : Memory.mem)
    (aptr aidx aval : expr) (k : cont) (b : block) (i n : Nat) (v : CompCert.Int)
    (vs : Nat → CompCert.Int)
    (haptr : eval_expr ge e le m aptr (.Vptr b Ptrofs.zero))
    (haidx : eval_expr ge e le m aidx (.Vint (CompCert.Int.repr (i:Int))))
    (haval : eval_expr ge e le m aval (.Vint v))
    (htaptr : typeof aptr = tintptr) (htaidx : typeof aidx = tint) (htaval : typeof aval = tint)
    (harr : int_array_at m b n vs) (hlt : i < n) (hn : n < 2^30) :
    ∃ m', Memory.store .Mint32 m b (4 * (i:Int)) (.Vint v) = some m' ∧
      step2 ge (.State f (.Sassign (.Ederef (.Ebinop .Oadd aptr aidx tintptr) tint) aval) k e le m)
        Events.E0 (.State f .Sskip k e le m') := by
  have hi : i < 2^30 := by omega
  have hoff : Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_int (CompCert.Int.repr (i:Int)))
      = Ptrofs.repr (4 * (i:Int)) := ptr_index_offset i hi
  have hbin : sem_binary_operation ge.genv_cenv .Oadd (.Vptr b Ptrofs.zero) tintptr
      (.Vint (CompCert.Int.repr (i:Int))) tint m = some (.Vptr b (Ptrofs.repr (4 * (i:Int)))) := by
    show sem_binary_operation ge.genv_cenv .Oadd (.Vptr b Ptrofs.zero) tintptr
      (.Vint (CompCert.Int.repr (i:Int))) tint m = _
    unfold tintptr tint
    simp only [sem_binary_operation, sem_add, classify_add, typeconv, remove_attributes,
      change_attributes, sem_add_ptr_int, ptrofs_of_int]
    norm_num [sizeof]
    exact hoff
  have heb : eval_expr ge e le m (.Ebinop .Oadd aptr aidx tintptr)
      (.Vptr b (Ptrofs.repr (4 * (i:Int)))) :=
    eval_expr.eval_Ebinop .Oadd aptr aidx tintptr (.Vptr b Ptrofs.zero) (.Vint (CompCert.Int.repr (i:Int)))
      (.Vptr b (Ptrofs.repr (4 * (i:Int)))) haptr haidx (by rw [htaptr, htaidx]; exact hbin)
  have hlv : eval_lvalue ge e le m (.Ederef (.Ebinop .Oadd aptr aidx tintptr) tint)
      b (Ptrofs.repr (4 * (i:Int))) .Full :=
    eval_lvalue.eval_Ederef (.Ebinop .Oadd aptr aidx tintptr) tint b (Ptrofs.repr (4 * (i:Int))) heb
  have hcast : sem_cast (.Vint v) (typeof aval) tint m = some (.Vint v) := by
    rw [htaval]; exact sem_cast_tint_tint v m
  have hsig : (Ptrofs.repr (4 * (i:Int))).signed = 4 * (i:Int) :=
    ptrofs_repr_signed_of_range (4 * (i:Int)) (by omega) (by omega)
  obtain ⟨m', hstore⟩ := store_ok_of_load_ok m b (4 * (i:Int)) v _ (harr i hlt)
  refine ⟨m', hstore, ?_⟩
  have hassign : assign_loc ge.genv_cenv tint m b (Ptrofs.repr (4 * (i:Int))) .Full (.Vint v) m' :=
    assign_loc.assign_loc_value (.Vint v) .Mint32 m' (by unfold tint; rfl) (by
      show Memory.storev .Mint32 m (.Vptr b (Ptrofs.repr (4 * (i:Int)))) (.Vint v) = some m'
      show Memory.store .Mint32 m b (Ptrofs.repr (4 * (i:Int))).signed (.Vint v) = some m'
      rw [hsig]; exact hstore)
  exact step.step_assign f (.Ederef (.Ebinop .Oadd aptr aidx tintptr) tint) aval k e le m
      b (Ptrofs.repr (4 * (i:Int))) .Full (.Vint v) (.Vint v) m' hlv haval hcast hassign
abbrev acc_body (aptr : expr) : statement :=
  .Ssequence
    (.Ssequence .Sskip
      (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak))
    (.Ssequence .Sskip
      (.Sset _acc (.Ebinop .Oadd (.Etempvar _acc tint)
        (.Ederef (.Ebinop .Oadd aptr (.Etempvar _i tint) tintptr) tint) tint)))

/-- The `i++` statement. -/
abbrev acc_incr : statement :=
  .Ssequence .Sskip
    (.Sset _i (.Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (CompCert.Int.repr 1) tint) tint))
theorem step_then (ge : genv) (s1 s2 s3 : state) (t2 : Events.trace)
    (h1 : step2 ge s1 Events.E0 s2) (h2 : star step2 ge s2 t2 s3) :
    star step2 ge s1 t2 s3 :=
   .star_step s1 Events.E0 s2 t2 s3 t2 h1 h2 (by simp)

theorem sem_add_tint_tint (ge : genv) (n1 n2 : CompCert.Int) (m : Memory.mem) :
    sem_binary_operation ge.genv_cenv .Oadd (.Vint n1) tint (.Vint n2) tint m
      = some (.Vint (CompCert.Int.add n1 n2)) := by
  simp only [sem_binary_operation, sem_add, classify_add, typeconv, remove_attributes,
    change_attributes]
  unfold sem_binarith classify_binarith binarith_type
  simp only []
  rw [sem_cast_tint_tint n1 m, sem_cast_tint_tint n2 m]


theorem temp_env_get_insert_self (le : temp_env) (id : ident) (v : val) :
    (le.insert id v).get? id = some v := by
  show (Std.HashMap.insert le id v).get? id = some v
  rw [Std.HashMap.get?_insert]
  simp

theorem temp_env_get_insert_ne (le : temp_env) (id id' : ident) (v : val) (h : id' ≠ id) :
    (le.insert id v).get? id' = le.get? id' := by
  show (Std.HashMap.insert le id v).get? id' = le.get? id'
  rw [Std.HashMap.get?_insert]
  simp [h.symm]


theorem int_repr_succ (i : Nat) (h : i < 2^30) :
    CompCert.Int.add (CompCert.Int.repr (i:Int)) (CompCert.Int.repr 1) = CompCert.Int.repr ((i+1:Nat):Int) := by
  show CompCert.Int.repr (i:Int) + CompCert.Int.repr 1 = CompCert.Int.repr ((i+1:Nat):Int)
  have h1 : (CompCert.Int.repr (1:Int)).signed = (1:Int) := int_repr_signed_of_range 1 (by omega)
  have h2 := CompCert.Int.repr_add_signed (i:Int) (CompCert.Int.repr (1:Int))
  rw [h1] at h2
  rw [← h2]
  push_cast
  ring_nf

/-- One iteration of the accumulate loop: from the loop-entry state at index
    `i < n`, run exactly one pass of the body (guard true, `acc += arr[i]`,
    `i++`) and land back at the loop-entry state, at index `i+1`. -/
theorem sem_cmp_lt_tint (ge : genv) (n1 n2 : CompCert.Int) (m : Memory.mem) :
    sem_binary_operation ge.genv_cenv .Olt (.Vint n1) tint (.Vint n2) tint m
      = some (Val.of_bool (CompCert.Int.cmp .Clt n1 n2)) := by
  have hty : classify_cmp tint tint = classify_cmp_cases.cmp_default := by
    unfold classify_cmp
    rfl
  unfold sem_binary_operation sem_cmp
  rw [hty]
  unfold sem_binarith classify_binarith binarith_type
  simp only []
  rw [sem_cast_tint_tint n1 m, sem_cast_tint_tint n2 m]

theorem bool_val_of_bool (b : Bool) (m : Memory.mem) :
    bool_val (Val.of_bool b) tint m = some b := by
  unfold bool_val classify_bool Val.of_bool typeconv remove_attributes change_attributes
  cases b <;> simp [Vtrue, Vfalse, CompCert.Int.eq]; decide

theorem int_cmp_lt_repr (i n : Nat) (hi : i < 2^30) (hn : n < 2^30) :
    CompCert.Int.cmp .Clt (CompCert.Int.repr (i:Int)) (CompCert.Int.repr (n:Int)) = decide (i < n) := by
  unfold CompCert.Int.cmp
  rw [int_repr_signed_of_range i (by omega), int_repr_signed_of_range n (by omega)]
  simp only [decide_eq_decide]
  omega

theorem accumulate_loop_iter (ge : genv) (f : function) (k : cont) (e : env) (le : temp_env)
    (m : Memory.mem) (b : block) (arr_id : ident) (i n : Nat) (vs : Nat → CompCert.Int)
    (c0 : CompCert.Int)
    (hi_get : le.get? _i = some (.Vint (CompCert.Int.repr (i:Int))))
    (hn_get : le.get? _n = some (.Vint (CompCert.Int.repr (n:Int))))
    (hacc_get : le.get? _acc = some (.Vint (CompCert.Int.add c0 (isum i vs))))
    (haptr_get : le.get? arr_id = some (.Vptr b Ptrofs.zero))
    (harr_ne_i : arr_id ≠ _i) (harr_ne_acc : arr_id ≠ _acc)
    (harr : int_array_at m b n vs) (hlt : i < n) (hn30 : n < 2^30) :
    ∃ le' : temp_env,
      le'.get? _i = some (.Vint (CompCert.Int.repr ((i+1 : Nat):Int))) ∧
      le'.get? _acc = some (.Vint (CompCert.Int.add c0 (isum (i+1) vs))) ∧
      (∀ x, x ≠ _i → x ≠ _acc → le'.get? x = le.get? x) ∧
      star step2 ge (.State f (.Sloop (acc_body (.Etempvar arr_id tintptr)) acc_incr) k e le m) Events.E0
        (.State f (.Sloop (acc_body (.Etempvar arr_id tintptr)) acc_incr) k e le' m) := by
  have hne : _i ≠ _acc := by decide
  -- eval the guard: i < n is true
  have heval_i : eval_expr ge e le m (.Etempvar _i tint) (.Vint (CompCert.Int.repr (i:Int))) :=
    eval_expr.eval_Etempvar _i tint _ hi_get
  have heval_n : eval_expr ge e le m (.Etempvar _n tint) (.Vint (CompCert.Int.repr (n:Int))) :=
    eval_expr.eval_Etempvar _n tint _ hn_get
  have hcond : eval_expr ge e le m
      (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) (Val.of_bool true) := by
    have hcmp : CompCert.Int.cmp .Clt (CompCert.Int.repr (i:Int)) (CompCert.Int.repr (n:Int)) = true := by
      rw [int_cmp_lt_repr i n (by omega) (by omega)]; simp [hlt]
    have := eval_expr.eval_Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint
      (.Vint (CompCert.Int.repr (i:Int))) (.Vint (CompCert.Int.repr (n:Int)))
      (Val.of_bool (CompCert.Int.cmp .Clt (CompCert.Int.repr (i:Int)) (CompCert.Int.repr (n:Int))))
      heval_i heval_n (sem_cmp_lt_tint ge _ _ m)
    rwa [hcmp] at this
  have hbool : bool_val (Val.of_bool true) tint m = some true := bool_val_of_bool true m
  -- one pass through the array-read + add for the accumulator
  have heval_acc : eval_expr ge e le m (.Etempvar _acc tint) (.Vint (CompCert.Int.add c0 (isum i vs))) :=
    eval_expr.eval_Etempvar _acc tint _ hacc_get
  have heval_arr : eval_expr ge e le m
      (.Ederef (.Ebinop .Oadd (.Etempvar arr_id tintptr) (.Etempvar _i tint) tintptr) tint) (.Vint (vs i)) :=
    eval_read_array ge e le m (.Etempvar arr_id tintptr) (.Etempvar _i tint) b i n vs
      (eval_expr.eval_Etempvar arr_id tintptr _ haptr_get) heval_i rfl rfl harr hlt hn30
  have hnewacc : eval_expr ge e le m
      (.Ebinop .Oadd (.Etempvar _acc tint)
        (.Ederef (.Ebinop .Oadd (.Etempvar arr_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)
      (.Vint (CompCert.Int.add c0 (isum (i+1) vs))) := by
    have := eval_expr.eval_Ebinop .Oadd (.Etempvar _acc tint)
      (.Ederef (.Ebinop .Oadd (.Etempvar arr_id tintptr) (.Etempvar _i tint) tintptr) tint) tint
      (.Vint (CompCert.Int.add c0 (isum i vs))) (.Vint (vs i))
      (.Vint (CompCert.Int.add (CompCert.Int.add c0 (isum i vs)) (vs i)))
      heval_acc heval_arr (sem_add_tint_tint ge _ _ m)
    have heq : CompCert.Int.add (CompCert.Int.add c0 (isum i vs)) (vs i)
        = CompCert.Int.add c0 (isum (i+1) vs) := by
      show c0 + isum i vs + vs i = c0 + isum (i+1) vs
      rw [CompCert.Int.add_assoc]; rfl
    rwa [heq] at this
  set le1 : temp_env := le.insert _acc (.Vint (CompCert.Int.add c0 (isum (i+1) vs))) with hle1_def
  -- one pass through the increment
  have hle1_i : le1.get? _i = some (.Vint (CompCert.Int.repr (i:Int))) := by
    rw [hle1_def, temp_env_get_insert_ne _ _ _ _ hne]; exact hi_get
  have heval_i1 : eval_expr ge e le1 m (.Etempvar _i tint) (.Vint (CompCert.Int.repr (i:Int))) :=
    eval_expr.eval_Etempvar _i tint _ hle1_i
  have heval_one : eval_expr ge e le1 m (.Econst_int (CompCert.Int.repr 1) tint) (.Vint (CompCert.Int.repr 1)) :=
    eval_expr.eval_Econst_int (CompCert.Int.repr 1) tint
  have hnewi : eval_expr ge e le1 m
      (.Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (CompCert.Int.repr 1) tint) tint)
      (.Vint (CompCert.Int.repr ((i+1:Nat):Int))) := by
    have := eval_expr.eval_Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (CompCert.Int.repr 1) tint) tint
      (.Vint (CompCert.Int.repr (i:Int))) (.Vint (CompCert.Int.repr 1))
      (.Vint (CompCert.Int.add (CompCert.Int.repr (i:Int)) (CompCert.Int.repr 1)))
      heval_i1 heval_one (sem_add_tint_tint ge _ _ m)
    rwa [int_repr_succ i (by omega)] at this
  set le2 : temp_env := le1.insert _i (.Vint (CompCert.Int.repr ((i+1:Nat):Int))) with hle2_def
  refine ⟨le2, ?_, ?_, ?_, ?_⟩
  · rw [hle2_def]; exact temp_env_get_insert_self _ _ _
  · rw [hle2_def, temp_env_get_insert_ne _ _ _ _ hne.symm, hle1_def]
    exact temp_env_get_insert_self _ _ _
  · intro x hxi hxacc
    rw [hle2_def, temp_env_get_insert_ne _ _ _ _ hxi]
    rw [hle1_def, temp_env_get_insert_ne _ _ _ _ hxacc]
  · -- the 14-step chain
    have S1 : step2 ge (.State f (.Sloop (acc_body (.Etempvar arr_id tintptr)) acc_incr) k e le m) Events.E0
        (.State f (acc_body (.Etempvar arr_id tintptr)) (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k) e le m) :=
      step.step_loop f (acc_body (.Etempvar arr_id tintptr)) acc_incr k e le m
    have S2 : step2 ge (.State f (acc_body (.Etempvar arr_id tintptr)) (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k) e le m) Events.E0
        (.State f (.Ssequence .Sskip (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak))
          (.Kseq (.Ssequence .Sskip (.Sset _acc (.Ebinop .Oadd (.Etempvar _acc tint)
            (.Ederef (.Ebinop .Oadd (.Etempvar arr_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
            (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k)) e le m) :=
      step.step_seq f _ _ (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k) e le m
    have S3 : step2 ge (.State f (.Ssequence .Sskip (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak))
          (.Kseq (.Ssequence .Sskip (.Sset _acc (.Ebinop .Oadd (.Etempvar _acc tint)
            (.Ederef (.Ebinop .Oadd (.Etempvar arr_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
            (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k)) e le m) Events.E0
        (.State f .Sskip
          (.Kseq (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)
            (.Kseq (.Ssequence .Sskip (.Sset _acc (.Ebinop .Oadd (.Etempvar _acc tint)
              (.Ederef (.Ebinop .Oadd (.Etempvar arr_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
              (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k))) e le m) :=
      step.step_seq f _ _ _ e le m
    have S4 : step2 ge (.State f .Sskip
          (.Kseq (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)
            (.Kseq (.Ssequence .Sskip (.Sset _acc (.Ebinop .Oadd (.Etempvar _acc tint)
              (.Ederef (.Ebinop .Oadd (.Etempvar arr_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
              (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k))) e le m) Events.E0
        (.State f (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)
          (.Kseq (.Ssequence .Sskip (.Sset _acc (.Ebinop .Oadd (.Etempvar _acc tint)
            (.Ederef (.Ebinop .Oadd (.Etempvar arr_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
            (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k)) e le m) :=
      step.step_skip_seq f _ _ e le m
    have S5 : step2 ge (.State f (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)
          (.Kseq (.Ssequence .Sskip (.Sset _acc (.Ebinop .Oadd (.Etempvar _acc tint)
            (.Ederef (.Ebinop .Oadd (.Etempvar arr_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
            (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k)) e le m) Events.E0
        (.State f .Sskip
          (.Kseq (.Ssequence .Sskip (.Sset _acc (.Ebinop .Oadd (.Etempvar _acc tint)
            (.Ederef (.Ebinop .Oadd (.Etempvar arr_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
            (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k)) e le m) :=
      step.step_ifthenelse f (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint)
        .Sskip .Sbreak (.Kseq (.Ssequence .Sskip (.Sset _acc (.Ebinop .Oadd (.Etempvar _acc tint)
          (.Ederef (.Ebinop .Oadd (.Etempvar arr_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
          (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k)) e le m (Val.of_bool true) true hcond hbool
    have S6 : step2 ge (.State f .Sskip
          (.Kseq (.Ssequence .Sskip (.Sset _acc (.Ebinop .Oadd (.Etempvar _acc tint)
            (.Ederef (.Ebinop .Oadd (.Etempvar arr_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
            (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k)) e le m) Events.E0
        (.State f (.Ssequence .Sskip (.Sset _acc (.Ebinop .Oadd (.Etempvar _acc tint)
            (.Ederef (.Ebinop .Oadd (.Etempvar arr_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
          (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k) e le m) :=
      step.step_skip_seq f _ _ e le m
    have S7 : step2 ge (.State f (.Ssequence .Sskip (.Sset _acc (.Ebinop .Oadd (.Etempvar _acc tint)
            (.Ederef (.Ebinop .Oadd (.Etempvar arr_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
          (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k) e le m) Events.E0
        (.State f .Sskip
          (.Kseq (.Sset _acc (.Ebinop .Oadd (.Etempvar _acc tint)
            (.Ederef (.Ebinop .Oadd (.Etempvar arr_id tintptr) (.Etempvar _i tint) tintptr) tint) tint))
            (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k)) e le m) :=
      step.step_seq f _ _ (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k) e le m
    have S8 : step2 ge (.State f .Sskip
          (.Kseq (.Sset _acc (.Ebinop .Oadd (.Etempvar _acc tint)
            (.Ederef (.Ebinop .Oadd (.Etempvar arr_id tintptr) (.Etempvar _i tint) tintptr) tint) tint))
            (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k)) e le m) Events.E0
        (.State f (.Sset _acc (.Ebinop .Oadd (.Etempvar _acc tint)
            (.Ederef (.Ebinop .Oadd (.Etempvar arr_id tintptr) (.Etempvar _i tint) tintptr) tint) tint))
          (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k) e le m) :=
      step.step_skip_seq f _ _ e le m
    have S9 : step2 ge (.State f (.Sset _acc (.Ebinop .Oadd (.Etempvar _acc tint)
            (.Ederef (.Ebinop .Oadd (.Etempvar arr_id tintptr) (.Etempvar _i tint) tintptr) tint) tint))
          (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k) e le m) Events.E0
        (.State f .Sskip (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k) e le1 m) :=
      step.step_set f _acc _ (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k) e le m _ hnewacc
    have S10 : step2 ge (.State f .Sskip (.Kloop1 (acc_body (.Etempvar arr_id tintptr)) acc_incr k) e le1 m) Events.E0
        (.State f acc_incr (.Kloop2 (acc_body (.Etempvar arr_id tintptr)) acc_incr k) e le1 m) :=
      step.step_skip_or_continue_loop1 f (acc_body (.Etempvar arr_id tintptr)) acc_incr k e le1 m .Sskip (.inl rfl)
    have S11 : step2 ge (.State f acc_incr (.Kloop2 (acc_body (.Etempvar arr_id tintptr)) acc_incr k) e le1 m) Events.E0
        (.State f .Sskip
          (.Kseq (.Sset _i (.Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (CompCert.Int.repr 1) tint) tint))
            (.Kloop2 (acc_body (.Etempvar arr_id tintptr)) acc_incr k)) e le1 m) :=
      step.step_seq f _ _ (.Kloop2 (acc_body (.Etempvar arr_id tintptr)) acc_incr k) e le1 m
    have S12 : step2 ge (.State f .Sskip
          (.Kseq (.Sset _i (.Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (CompCert.Int.repr 1) tint) tint))
            (.Kloop2 (acc_body (.Etempvar arr_id tintptr)) acc_incr k)) e le1 m) Events.E0
        (.State f (.Sset _i (.Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (CompCert.Int.repr 1) tint) tint))
          (.Kloop2 (acc_body (.Etempvar arr_id tintptr)) acc_incr k) e le1 m) :=
      step.step_skip_seq f _ _ e le1 m
    have S13 : step2 ge (.State f (.Sset _i (.Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (CompCert.Int.repr 1) tint) tint))
          (.Kloop2 (acc_body (.Etempvar arr_id tintptr)) acc_incr k) e le1 m) Events.E0
        (.State f .Sskip (.Kloop2 (acc_body (.Etempvar arr_id tintptr)) acc_incr k) e le2 m) :=
      step.step_set f _i _ (.Kloop2 (acc_body (.Etempvar arr_id tintptr)) acc_incr k) e le1 m _ hnewi
    have S14 : step2 ge (.State f .Sskip (.Kloop2 (acc_body (.Etempvar arr_id tintptr)) acc_incr k) e le2 m) Events.E0
        (.State f (.Sloop (acc_body (.Etempvar arr_id tintptr)) acc_incr) k e le2 m) :=
      step.step_skip_loop2 f (acc_body (.Etempvar arr_id tintptr)) acc_incr k e le2 m
    exact step_then _ _ _ _ _ S1 (step_then _ _ _ _ _ S2 (step_then _ _ _ _ _ S3
      (step_then _ _ _ _ _ S4 (step_then _ _ _ _ _ S5 (step_then _ _ _ _ _ S6
      (step_then _ _ _ _ _ S7 (step_then _ _ _ _ _ S8 (step_then _ _ _ _ _ S9
      (step_then _ _ _ _ _ S10 (step_then _ _ _ _ _ S11 (step_then _ _ _ _ _ S12
      (step_then _ _ _ _ _ S13 (step_then _ _ _ _ _ S14 (Smallstep.star.star_refl _))))))))))))))

/-- The full accumulate loop, run from index `i` up to `n`, by induction on
    the number of remaining iterations `d = n - i`. -/
theorem accumulate_loop_full (ge : genv) (f : function) (k : cont) (e : env)
    (b : block) (arr_id : ident) (n : Nat) (vs : Nat → CompCert.Int) (c0 : CompCert.Int)
    (harr_ne_i : arr_id ≠ _i) (harr_ne_acc : arr_id ≠ _acc) (hn30 : n < 2^30) :
    ∀ (d i : Nat), i + d = n → ∀ (le : temp_env) (m : Memory.mem),
      le.get? _i = some (.Vint (CompCert.Int.repr (i:Int))) →
      le.get? _n = some (.Vint (CompCert.Int.repr (n:Int))) →
      le.get? _acc = some (.Vint (CompCert.Int.add c0 (isum i vs))) →
      le.get? arr_id = some (.Vptr b Ptrofs.zero) →
      int_array_at m b n vs →
      ∃ le' : temp_env,
        le'.get? _i = some (.Vint (CompCert.Int.repr (n:Int))) ∧
        le'.get? _n = some (.Vint (CompCert.Int.repr (n:Int))) ∧
        le'.get? _acc = some (.Vint (CompCert.Int.add c0 (isum n vs))) ∧
        le'.get? arr_id = some (.Vptr b Ptrofs.zero) ∧
        (∀ x, x ≠ _i → x ≠ _acc → le'.get? x = le.get? x) ∧
        star step2 ge (.State f (.Sloop (acc_body (.Etempvar arr_id tintptr)) acc_incr) k e le m) Events.E0
          (.State f (.Sloop (acc_body (.Etempvar arr_id tintptr)) acc_incr) k e le' m) := by
  intro d
  induction d with
  | zero =>
      intro i hi le m hi_get hn_get hacc_get haptr_get harr
      have : i = n := by omega
      subst this
      exact ⟨le, hi_get, hn_get, hacc_get, haptr_get, fun _ _ _ => rfl, .star_refl _⟩
  | succ d' ih =>
      intro i hi le m hi_get hn_get hacc_get haptr_get harr
      have hlt : i < n := by omega
      obtain ⟨le1, hle1_i, hle1_acc, hle1_frame, hstep1⟩ :=
        accumulate_loop_iter ge f k e le m b arr_id i n vs c0 hi_get hn_get hacc_get haptr_get
          harr_ne_i harr_ne_acc harr hlt hn30
      have hle1_n : le1.get? _n = some (.Vint (CompCert.Int.repr (n:Int))) := by
        rw [hle1_frame _n (by decide) (by decide)]; exact hn_get
      have hle1_arr : le1.get? arr_id = some (.Vptr b Ptrofs.zero) := by
        rw [hle1_frame arr_id harr_ne_i harr_ne_acc]; exact haptr_get
      obtain ⟨le2, hle2_i, hle2_n, hle2_acc, hle2_arr, hle2_frame, hstep2⟩ :=
        ih (i+1) (by omega) le1 m hle1_i hle1_n hle1_acc hle1_arr harr
      refine ⟨le2, hle2_i, hle2_n, hle2_acc, hle2_arr,
        fun x hxi hxacc => (hle2_frame x hxi hxacc).trans (hle1_frame x hxi hxacc),
        star_trans _ _ _ _ _ hstep1 _ _ _ (by convert hstep2 using 2) (by simp)⟩
abbrev mutate_body (a_id b_id : ident) : statement :=
  .Ssequence
    (.Ssequence .Sskip
      (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak))
    (.Ssequence .Sskip
      (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
        (.Ebinop .Oadd
          (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
          (.Ederef (.Ebinop .Oadd (.Etempvar b_id tintptr) (.Etempvar _i tint) tintptr) tint)
          tint)))

abbrev mutate_incr : statement :=
  .Ssequence .Sskip
    (.Sset _i (.Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (CompCert.Int.repr 1) tint) tint))

def mut_cur (i0 : Nat) (a_vals b_vals : Nat → CompCert.Int) (j : Nat) : CompCert.Int :=
  if j < i0 then CompCert.Int.add (a_vals j) (b_vals j) else a_vals j

theorem load_store_same_int (m : Memory.mem) (b : block) (ofs : Int) (v : CompCert.Int) (m' : Memory.mem)
    (hstore : Memory.store .Mint32 m b ofs (.Vint v) = some m') :
    Memory.load .Mint32 m' b ofs = some (.Vint v) := by
  have hls := Memory.load_store_same .Mint32 m b ofs (.Vint v) m' hstore
  rw [hls]
  have h1 : ∀ b' ofs', (val.Vint v) ≠ .Vptr b' ofs' := by intro b' ofs' h; cases h
  have h2 : Memory.encode_bytes .Mint32 (.Vint v) ≠ [] := by unfold Memory.encode_bytes; simp
  rw [Memory.Properties.encode_decode_roundtrip .Mint32 (.Vint v) h1 h2]
  rfl

theorem load_store_other_block (m : Memory.mem) (b1 : block) (ofs1 : Int) (v : val) (m' : Memory.mem)
    (b2 : block) (n : Nat) (vs : Nat → CompCert.Int) (hb : b1 ≠ b2)
    (hstore : Memory.store .Mint32 m b1 ofs1 v = some m') :
    int_array_at m b2 n vs → int_array_at m' b2 n vs := by
  intro harr j hj
  rw [Memory.load_store_other .Mint32 .Mint32 m b1 ofs1 v b2 (4 * (j:Int)) m' hstore (.inl hb)]
  exact harr j hj

theorem load_store_other_idx (m : Memory.mem) (b : block) (i : Nat) (v : val) (m' : Memory.mem)
    (j : Nat) (hij : i ≠ j)
    (hstore : Memory.store .Mint32 m b (4 * (i:Int)) v = some m') :
    Memory.load .Mint32 m' b (4 * (j:Int)) = Memory.load .Mint32 m b (4 * (j:Int)) := by
  apply Memory.load_store_other .Mint32 .Mint32 m b (4 * (i:Int)) v b (4 * (j:Int)) m' hstore
  right
  simp only [Memory.size_chunk]
  omega

theorem int_array_at_mut_cur_step (m : Memory.mem) (b : block) (i n : Nat)
    (a_vals b_vals : Nat → CompCert.Int) (m' : Memory.mem)
    (hi : i < n) (harr : int_array_at m b n (mut_cur i a_vals b_vals))
    (hstore : Memory.store .Mint32 m b (4*(i:Int)) (.Vint (CompCert.Int.add (a_vals i) (b_vals i))) = some m') :
    int_array_at m' b n (mut_cur (i+1) a_vals b_vals) := by
  intro j hj
  by_cases hij : j = i
  · subst hij
    have := load_store_same_int m b (4*(j:Int)) (CompCert.Int.add (a_vals j) (b_vals j)) m' hstore
    rw [this]
    congr 1
    unfold mut_cur
    simp
  · rw [load_store_other_idx m b i (.Vint (CompCert.Int.add (a_vals i) (b_vals i))) m' j
      (fun h => hij h.symm) hstore]
    rw [harr j hj]
    unfold mut_cur
    split_ifs with h1 h2 h2 <;> first | rfl | omega

theorem mutate_loop_iter (ge : genv) (f : function) (k : cont) (e : env) (le : temp_env)
    (m : Memory.mem) (a_blk b_blk : block) (a_id b_id : ident) (i n : Nat)
    (a_vals b_vals : Nat → CompCert.Int)
    (hi_get : le.get? _i = some (.Vint (CompCert.Int.repr (i:Int))))
    (hn_get : le.get? _n = some (.Vint (CompCert.Int.repr (n:Int))))
    (ha_get : le.get? a_id = some (.Vptr a_blk Ptrofs.zero))
    (hb_get : le.get? b_id = some (.Vptr b_blk Ptrofs.zero))
    (ha_ne_i : a_id ≠ _i) (ha_ne_n : a_id ≠ _n) (hb_ne_i : b_id ≠ _i) (hb_ne_n : b_id ≠ _n)
    (hab_disj : a_blk ≠ b_blk)
    (harr_a : int_array_at m a_blk n (mut_cur i a_vals b_vals))
    (harr_b : int_array_at m b_blk n b_vals)
    (hlt : i < n) (hn30 : n < 2^30) :
    ∃ (le' : temp_env) (m' : Memory.mem),
      le'.get? _i = some (.Vint (CompCert.Int.repr ((i+1:Nat):Int))) ∧
      (∀ x, x ≠ _i → le'.get? x = le.get? x) ∧
      int_array_at m' a_blk n (mut_cur (i+1) a_vals b_vals) ∧
      int_array_at m' b_blk n b_vals ∧
      star step2 ge (.State f (.Sloop (mutate_body a_id b_id) mutate_incr) k e le m) Events.E0
        (.State f (.Sloop (mutate_body a_id b_id) mutate_incr) k e le' m') := by
  have hne : _i ≠ _acc := by decide -- unused, kept for parity; harmless
  have heval_i : eval_expr ge e le m (.Etempvar _i tint) (.Vint (CompCert.Int.repr (i:Int))) :=
    eval_expr.eval_Etempvar _i tint _ hi_get
  have heval_n : eval_expr ge e le m (.Etempvar _n tint) (.Vint (CompCert.Int.repr (n:Int))) :=
    eval_expr.eval_Etempvar _n tint _ hn_get
  have heval_a : eval_expr ge e le m (.Etempvar a_id tintptr) (.Vptr a_blk Ptrofs.zero) :=
    eval_expr.eval_Etempvar a_id tintptr _ ha_get
  have heval_b : eval_expr ge e le m (.Etempvar b_id tintptr) (.Vptr b_blk Ptrofs.zero) :=
    eval_expr.eval_Etempvar b_id tintptr _ hb_get
  have hcond : eval_expr ge e le m
      (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) (Val.of_bool true) := by
    have hcmp : CompCert.Int.cmp .Clt (CompCert.Int.repr (i:Int)) (CompCert.Int.repr (n:Int)) = true := by
      rw [int_cmp_lt_repr i n (by omega) (by omega)]; simp [hlt]
    have := eval_expr.eval_Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint
      (.Vint (CompCert.Int.repr (i:Int))) (.Vint (CompCert.Int.repr (n:Int)))
      (Val.of_bool (CompCert.Int.cmp .Clt (CompCert.Int.repr (i:Int)) (CompCert.Int.repr (n:Int))))
      heval_i heval_n (sem_cmp_lt_tint ge _ _ m)
    rwa [hcmp] at this
  have hbool : bool_val (Val.of_bool true) tint m = some true := bool_val_of_bool true m
  have hreadA : eval_expr ge e le m
      (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
      (.Vint (mut_cur i a_vals b_vals i)) :=
    eval_read_array ge e le m (.Etempvar a_id tintptr) (.Etempvar _i tint) a_blk i n
      (mut_cur i a_vals b_vals) heval_a heval_i rfl rfl harr_a hlt hn30
  have hreadB : eval_expr ge e le m
      (.Ederef (.Ebinop .Oadd (.Etempvar b_id tintptr) (.Etempvar _i tint) tintptr) tint)
      (.Vint (b_vals i)) :=
    eval_read_array ge e le m (.Etempvar b_id tintptr) (.Etempvar _i tint) b_blk i n
      b_vals heval_b heval_i rfl rfl harr_b hlt hn30
  have hval : mut_cur i a_vals b_vals i = a_vals i := by unfold mut_cur; simp
  have haval : eval_expr ge e le m
      (.Ebinop .Oadd
        (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
        (.Ederef (.Ebinop .Oadd (.Etempvar b_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)
      (.Vint (CompCert.Int.add (a_vals i) (b_vals i))) := by
    have := eval_expr.eval_Ebinop .Oadd
      (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
      (.Ederef (.Ebinop .Oadd (.Etempvar b_id tintptr) (.Etempvar _i tint) tintptr) tint) tint
      (.Vint (mut_cur i a_vals b_vals i)) (.Vint (b_vals i))
      (.Vint (CompCert.Int.add (mut_cur i a_vals b_vals i) (b_vals i)))
      hreadA hreadB (sem_add_tint_tint ge _ _ m)
    rwa [hval] at this
  obtain ⟨m1, hstoreOK, hassignStep⟩ :=
    step_write_array ge f e le m (.Etempvar a_id tintptr) (.Etempvar _i tint)
      (.Ebinop .Oadd
        (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
        (.Ederef (.Ebinop .Oadd (.Etempvar b_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)
      (.Kloop1 (mutate_body a_id b_id) mutate_incr k) a_blk i n
      (CompCert.Int.add (a_vals i) (b_vals i)) (mut_cur i a_vals b_vals) heval_a heval_i
      haval rfl rfl rfl harr_a hlt hn30
  have harr_a' : int_array_at m1 a_blk n (mut_cur (i+1) a_vals b_vals) :=
    int_array_at_mut_cur_step m a_blk i n a_vals b_vals m1 hlt harr_a hstoreOK
  have harr_b' : int_array_at m1 b_blk n b_vals :=
    load_store_other_block m a_blk (4*(i:Int)) (.Vint (CompCert.Int.add (a_vals i) (b_vals i))) m1
      b_blk n b_vals hab_disj hstoreOK harr_b
  have heval_i1 : eval_expr ge e le m1 (.Etempvar _i tint) (.Vint (CompCert.Int.repr (i:Int))) :=
    eval_expr.eval_Etempvar _i tint _ hi_get
  have heval_one : eval_expr ge e le m1 (.Econst_int (CompCert.Int.repr 1) tint) (.Vint (CompCert.Int.repr 1)) :=
    eval_expr.eval_Econst_int (CompCert.Int.repr 1) tint
  have hnewi : eval_expr ge e le m1
      (.Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (CompCert.Int.repr 1) tint) tint)
      (.Vint (CompCert.Int.repr ((i+1:Nat):Int))) := by
    have := eval_expr.eval_Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (CompCert.Int.repr 1) tint) tint
      (.Vint (CompCert.Int.repr (i:Int))) (.Vint (CompCert.Int.repr 1))
      (.Vint (CompCert.Int.add (CompCert.Int.repr (i:Int)) (CompCert.Int.repr 1)))
      heval_i1 heval_one (sem_add_tint_tint ge _ _ m1)
    rwa [int_repr_succ i (by omega)] at this
  set le2 : temp_env := le.insert _i (.Vint (CompCert.Int.repr ((i+1:Nat):Int))) with hle2_def
  refine ⟨le2, m1, ?_, ?_, harr_a', harr_b', ?_⟩
  · rw [hle2_def]; exact temp_env_get_insert_self _ _ _
  · intro x hxi
    rw [hle2_def, temp_env_get_insert_ne _ _ _ _ hxi]
  · have S1 : step2 ge (.State f (.Sloop (mutate_body a_id b_id) mutate_incr) k e le m) Events.E0
        (.State f (mutate_body a_id b_id) (.Kloop1 (mutate_body a_id b_id) mutate_incr k) e le m) :=
      step.step_loop f (mutate_body a_id b_id) mutate_incr k e le m
    have S2 : step2 ge (.State f (mutate_body a_id b_id) (.Kloop1 (mutate_body a_id b_id) mutate_incr k) e le m) Events.E0
        (.State f (.Ssequence .Sskip (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak))
          (.Kseq (.Ssequence .Sskip (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
            (.Ebinop .Oadd (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
              (.Ederef (.Ebinop .Oadd (.Etempvar b_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
            (.Kloop1 (mutate_body a_id b_id) mutate_incr k)) e le m) :=
      step.step_seq f _ _ (.Kloop1 (mutate_body a_id b_id) mutate_incr k) e le m
    have S3 : step2 ge (.State f (.Ssequence .Sskip (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak))
          (.Kseq (.Ssequence .Sskip (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
            (.Ebinop .Oadd (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
              (.Ederef (.Ebinop .Oadd (.Etempvar b_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
            (.Kloop1 (mutate_body a_id b_id) mutate_incr k)) e le m) Events.E0
        (.State f .Sskip
          (.Kseq (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)
            (.Kseq (.Ssequence .Sskip (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
              (.Ebinop .Oadd (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
                (.Ederef (.Ebinop .Oadd (.Etempvar b_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
              (.Kloop1 (mutate_body a_id b_id) mutate_incr k))) e le m) :=
      step.step_seq f _ _ _ e le m
    have S4 : step2 ge (.State f .Sskip
          (.Kseq (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)
            (.Kseq (.Ssequence .Sskip (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
              (.Ebinop .Oadd (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
                (.Ederef (.Ebinop .Oadd (.Etempvar b_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
              (.Kloop1 (mutate_body a_id b_id) mutate_incr k))) e le m) Events.E0
        (.State f (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)
          (.Kseq (.Ssequence .Sskip (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
            (.Ebinop .Oadd (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
              (.Ederef (.Ebinop .Oadd (.Etempvar b_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
            (.Kloop1 (mutate_body a_id b_id) mutate_incr k)) e le m) :=
      step.step_skip_seq f _ _ e le m
    have S5 : step2 ge (.State f (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)
          (.Kseq (.Ssequence .Sskip (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
            (.Ebinop .Oadd (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
              (.Ederef (.Ebinop .Oadd (.Etempvar b_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
            (.Kloop1 (mutate_body a_id b_id) mutate_incr k)) e le m) Events.E0
        (.State f .Sskip
          (.Kseq (.Ssequence .Sskip (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
            (.Ebinop .Oadd (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
              (.Ederef (.Ebinop .Oadd (.Etempvar b_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
            (.Kloop1 (mutate_body a_id b_id) mutate_incr k)) e le m) :=
      step.step_ifthenelse f (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint)
        .Sskip .Sbreak (.Kseq (.Ssequence .Sskip (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
          (.Ebinop .Oadd (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
            (.Ederef (.Ebinop .Oadd (.Etempvar b_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
          (.Kloop1 (mutate_body a_id b_id) mutate_incr k)) e le m (Val.of_bool true) true hcond hbool
    have S6 : step2 ge (.State f .Sskip
          (.Kseq (.Ssequence .Sskip (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
            (.Ebinop .Oadd (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
              (.Ederef (.Ebinop .Oadd (.Etempvar b_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
            (.Kloop1 (mutate_body a_id b_id) mutate_incr k)) e le m) Events.E0
        (.State f (.Ssequence .Sskip (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
            (.Ebinop .Oadd (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
              (.Ederef (.Ebinop .Oadd (.Etempvar b_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
          (.Kloop1 (mutate_body a_id b_id) mutate_incr k) e le m) :=
      step.step_skip_seq f _ _ e le m
    have S7 : step2 ge (.State f (.Ssequence .Sskip (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
            (.Ebinop .Oadd (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
              (.Ederef (.Ebinop .Oadd (.Etempvar b_id tintptr) (.Etempvar _i tint) tintptr) tint) tint)))
          (.Kloop1 (mutate_body a_id b_id) mutate_incr k) e le m) Events.E0
        (.State f .Sskip
          (.Kseq (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
            (.Ebinop .Oadd (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
              (.Ederef (.Ebinop .Oadd (.Etempvar b_id tintptr) (.Etempvar _i tint) tintptr) tint) tint))
            (.Kloop1 (mutate_body a_id b_id) mutate_incr k)) e le m) :=
      step.step_seq f _ _ (.Kloop1 (mutate_body a_id b_id) mutate_incr k) e le m
    have S8 : step2 ge (.State f .Sskip
          (.Kseq (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
            (.Ebinop .Oadd (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
              (.Ederef (.Ebinop .Oadd (.Etempvar b_id tintptr) (.Etempvar _i tint) tintptr) tint) tint))
            (.Kloop1 (mutate_body a_id b_id) mutate_incr k)) e le m) Events.E0
        (.State f (.Sassign (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
            (.Ebinop .Oadd (.Ederef (.Ebinop .Oadd (.Etempvar a_id tintptr) (.Etempvar _i tint) tintptr) tint)
              (.Ederef (.Ebinop .Oadd (.Etempvar b_id tintptr) (.Etempvar _i tint) tintptr) tint) tint))
          (.Kloop1 (mutate_body a_id b_id) mutate_incr k) e le m) :=
      step.step_skip_seq f _ _ e le m
    have S10 : step2 ge (.State f .Sskip (.Kloop1 (mutate_body a_id b_id) mutate_incr k) e le m1) Events.E0
        (.State f mutate_incr (.Kloop2 (mutate_body a_id b_id) mutate_incr k) e le m1) :=
      step.step_skip_or_continue_loop1 f (mutate_body a_id b_id) mutate_incr k e le m1 .Sskip (.inl rfl)
    have S11 : step2 ge (.State f mutate_incr (.Kloop2 (mutate_body a_id b_id) mutate_incr k) e le m1) Events.E0
        (.State f .Sskip
          (.Kseq (.Sset _i (.Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (CompCert.Int.repr 1) tint) tint))
            (.Kloop2 (mutate_body a_id b_id) mutate_incr k)) e le m1) :=
      step.step_seq f _ _ (.Kloop2 (mutate_body a_id b_id) mutate_incr k) e le m1
    have S12 : step2 ge (.State f .Sskip
          (.Kseq (.Sset _i (.Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (CompCert.Int.repr 1) tint) tint))
            (.Kloop2 (mutate_body a_id b_id) mutate_incr k)) e le m1) Events.E0
        (.State f (.Sset _i (.Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (CompCert.Int.repr 1) tint) tint))
          (.Kloop2 (mutate_body a_id b_id) mutate_incr k) e le m1) :=
      step.step_skip_seq f _ _ e le m1
    have S13 : step2 ge (.State f (.Sset _i (.Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (CompCert.Int.repr 1) tint) tint))
          (.Kloop2 (mutate_body a_id b_id) mutate_incr k) e le m1) Events.E0
        (.State f .Sskip (.Kloop2 (mutate_body a_id b_id) mutate_incr k) e le2 m1) :=
      step.step_set f _i _ (.Kloop2 (mutate_body a_id b_id) mutate_incr k) e le m1 _ hnewi
    have S14 : step2 ge (.State f .Sskip (.Kloop2 (mutate_body a_id b_id) mutate_incr k) e le2 m1) Events.E0
        (.State f (.Sloop (mutate_body a_id b_id) mutate_incr) k e le2 m1) :=
      step.step_skip_loop2 f (mutate_body a_id b_id) mutate_incr k e le2 m1
    exact step_then _ _ _ _ _ S1 (step_then _ _ _ _ _ S2 (step_then _ _ _ _ _ S3
      (step_then _ _ _ _ _ S4 (step_then _ _ _ _ _ S5 (step_then _ _ _ _ _ S6
      (step_then _ _ _ _ _ S7 (step_then _ _ _ _ _ S8 (step_then _ _ _ _ _ hassignStep
      (step_then _ _ _ _ _ S10 (step_then _ _ _ _ _ S11 (step_then _ _ _ _ _ S12
      (step_then _ _ _ _ _ S13 (step_then _ _ _ _ _ S14 (Smallstep.star.star_refl _))))))))))))))

theorem mutate_loop_full (ge : genv) (f : function) (k : cont) (e : env)
    (a_blk b_blk : block) (a_id b_id : ident) (n : Nat) (a_vals b_vals : Nat → CompCert.Int)
    (ha_ne_i : a_id ≠ _i) (ha_ne_n : a_id ≠ _n) (hb_ne_i : b_id ≠ _i) (hb_ne_n : b_id ≠ _n)
    (hab_disj : a_blk ≠ b_blk) (hn30 : n < 2^30) :
    ∀ (d i : Nat), i + d = n → ∀ (le : temp_env) (m : Memory.mem),
      le.get? _i = some (.Vint (CompCert.Int.repr (i:Int))) →
      le.get? _n = some (.Vint (CompCert.Int.repr (n:Int))) →
      le.get? a_id = some (.Vptr a_blk Ptrofs.zero) →
      le.get? b_id = some (.Vptr b_blk Ptrofs.zero) →
      int_array_at m a_blk n (mut_cur i a_vals b_vals) →
      int_array_at m b_blk n b_vals →
      ∃ (le' : temp_env) (m' : Memory.mem),
        le'.get? _i = some (.Vint (CompCert.Int.repr (n:Int))) ∧
        le'.get? _n = some (.Vint (CompCert.Int.repr (n:Int))) ∧
        le'.get? a_id = some (.Vptr a_blk Ptrofs.zero) ∧
        le'.get? b_id = some (.Vptr b_blk Ptrofs.zero) ∧
        int_array_at m' a_blk n (mut_cur n a_vals b_vals) ∧
        int_array_at m' b_blk n b_vals ∧
        star step2 ge (.State f (.Sloop (mutate_body a_id b_id) mutate_incr) k e le m) Events.E0
          (.State f (.Sloop (mutate_body a_id b_id) mutate_incr) k e le' m') := by
  intro d
  induction d with
  | zero =>
      intro i hi le m hi_get hn_get ha_get hb_get harr_a harr_b
      have : i = n := by omega
      subst this
      exact ⟨le, m, hi_get, hn_get, ha_get, hb_get, harr_a, harr_b, .star_refl _⟩
  | succ d' ih =>
      intro i hi le m hi_get hn_get ha_get hb_get harr_a harr_b
      have hlt : i < n := by omega
      obtain ⟨le1, m1, hle1_i, hle1_frame, harr_a1, harr_b1, hstep1⟩ :=
        mutate_loop_iter ge f k e le m a_blk b_blk a_id b_id i n a_vals b_vals
          hi_get hn_get ha_get hb_get ha_ne_i ha_ne_n hb_ne_i hb_ne_n hab_disj harr_a harr_b hlt hn30
      have hle1_n : le1.get? _n = some (.Vint (CompCert.Int.repr (n:Int))) := by
        rw [hle1_frame _n (by decide)]; exact hn_get
      have hle1_a : le1.get? a_id = some (.Vptr a_blk Ptrofs.zero) := by
        rw [hle1_frame a_id ha_ne_i]; exact ha_get
      have hle1_b : le1.get? b_id = some (.Vptr b_blk Ptrofs.zero) := by
        rw [hle1_frame b_id hb_ne_i]; exact hb_get
      obtain ⟨le2, m2, hle2_i, hle2_n, hle2_a, hle2_b, harr_a2, harr_b2, hstep2⟩ :=
        ih (i+1) (by omega) le1 m1 hle1_i hle1_n hle1_a hle1_b harr_a1 harr_b1
      exact ⟨le2, m2, hle2_i, hle2_n, hle2_a, hle2_b, harr_a2, harr_b2,
        star_trans _ _ _ _ _ hstep1 _ _ _ (by convert hstep2 using 2) (by simp)⟩

theorem int_add_swap (w x y z : CompCert.Int) :
    (w + x) + (y + z) = (w + y) + (x + z) := by
  rw [CompCert.Int.add_assoc, CompCert.Int.add_assoc, CompCert.Int.add_commut x (y + z),
    CompCert.Int.add_commut x z, ← CompCert.Int.add_assoc y z x]

/-- The pure-arithmetic fact making the equivalence theorem true: summing the
    elementwise sums equals the sum of the sums, regardless of grouping. -/
theorem isum_add_distrib (n : Nat) (a b : Nat → CompCert.Int) :
    isum n (fun j => CompCert.Int.add (a j) (b j)) = CompCert.Int.add (isum n a) (isum n b) := by
  induction n with
  | zero => unfold isum; simp
  | succ n ih =>
      unfold isum
      simp only [ih]
      exact int_add_swap (isum n a) (isum n b) (a n) (b n)
theorem prologue_step (ge : genv) (f : function) (k : cont) (e : env) (le : temp_env) (m : Memory.mem)
    (id : ident) (val_expr : expr) (v : val) (rest : statement)
    (heval : eval_expr ge e le m val_expr v) :
    star step2 ge (.State f (.Ssequence (.Ssequence .Sskip (.Sset id val_expr)) rest) k e le m) Events.E0
      (.State f rest k e (le.insert id v) m) := by
  have S1 : step2 ge (.State f (.Ssequence (.Ssequence .Sskip (.Sset id val_expr)) rest) k e le m) Events.E0
      (.State f (.Ssequence .Sskip (.Sset id val_expr)) (.Kseq rest k) e le m) :=
    step.step_seq f (.Ssequence .Sskip (.Sset id val_expr)) rest k e le m
  have S2 : step2 ge (.State f (.Ssequence .Sskip (.Sset id val_expr)) (.Kseq rest k) e le m) Events.E0
      (.State f .Sskip (.Kseq (.Sset id val_expr) (.Kseq rest k)) e le m) :=
    step.step_seq f .Sskip (.Sset id val_expr) (.Kseq rest k) e le m
  have S3 : step2 ge (.State f .Sskip (.Kseq (.Sset id val_expr) (.Kseq rest k)) e le m) Events.E0
      (.State f (.Sset id val_expr) (.Kseq rest k) e le m) :=
    step.step_skip_seq f (.Sset id val_expr) (.Kseq rest k) e le m
  have S4 : step2 ge (.State f (.Sset id val_expr) (.Kseq rest k) e le m) Events.E0
      (.State f .Sskip (.Kseq rest k) e (le.insert id v) m) :=
    step.step_set f id val_expr (.Kseq rest k) e le m v heval
  have S5 : step2 ge (.State f .Sskip (.Kseq rest k) e (le.insert id v) m) Events.E0
      (.State f rest k e (le.insert id v) m) :=
    step.step_skip_seq f rest k e (le.insert id v) m
  have T4 : star step2 ge (.State f .Sskip (.Kseq rest k) e (le.insert id v) m) Events.E0
      (.State f rest k e (le.insert id v) m) := step_then _ _ _ _ _ S5 (.star_refl _)
  have T3 := step_then _ _ _ _ _ S4 T4
  have T2 := step_then _ _ _ _ _ S3 T3
  exact step_then _ _ _ _ _ S1 (step_then _ _ _ _ _ S2 T2)

theorem loop_exit (ge : genv) (f : function) (k : cont) (e : env) (le : temp_env) (m : Memory.mem)
    (body_rest incr : statement) (n : Nat) (hn30 : n < 2^30)
    (hn_get : le.get? _i = some (.Vint (CompCert.Int.repr (n:Int))))
    (hn_get' : le.get? _n = some (.Vint (CompCert.Int.repr (n:Int)))) :
    star step2 ge
      (.State f (.Sloop (.Ssequence (.Ssequence .Sskip
        (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr)
        k e le m) Events.E0
      (.State f .Sskip k e le m) := by
  have heval_i : eval_expr ge e le m (.Etempvar _i tint) (.Vint (CompCert.Int.repr (n:Int))) :=
    eval_expr.eval_Etempvar _i tint _ hn_get
  have heval_n : eval_expr ge e le m (.Etempvar _n tint) (.Vint (CompCert.Int.repr (n:Int))) :=
    eval_expr.eval_Etempvar _n tint _ hn_get'
  have hcond : eval_expr ge e le m
      (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) (Val.of_bool false) := by
    have hcmp : CompCert.Int.cmp .Clt (CompCert.Int.repr (n:Int)) (CompCert.Int.repr (n:Int)) = false := by
      rw [int_cmp_lt_repr n n (by omega) (by omega)]; simp
    have := eval_expr.eval_Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint
      (.Vint (CompCert.Int.repr (n:Int))) (.Vint (CompCert.Int.repr (n:Int)))
      (Val.of_bool (CompCert.Int.cmp .Clt (CompCert.Int.repr (n:Int)) (CompCert.Int.repr (n:Int))))
      heval_i heval_n (sem_cmp_lt_tint ge _ _ m)
    rwa [hcmp] at this
  have hbool : bool_val (Val.of_bool false) tint m = some false := bool_val_of_bool false m
  have S1 : step2 ge (.State f (.Sloop (.Ssequence (.Ssequence .Sskip
      (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr)
      k e le m) Events.E0
      (.State f (.Ssequence (.Ssequence .Sskip
        (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest)
        (.Kloop1 (.Ssequence (.Ssequence .Sskip
          (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k)
        e le m) :=
    step.step_loop f (.Ssequence (.Ssequence .Sskip
      (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k e le m
  have S2 : step2 ge (.State f (.Ssequence (.Ssequence .Sskip
        (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest)
        (.Kloop1 (.Ssequence (.Ssequence .Sskip
          (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k)
        e le m) Events.E0
      (.State f (.Ssequence .Sskip
        (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak))
        (.Kseq body_rest (.Kloop1 (.Ssequence (.Ssequence .Sskip
          (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k))
        e le m) :=
    step.step_seq f (.Ssequence .Sskip
      (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest
      (.Kloop1 (.Ssequence (.Ssequence .Sskip
        (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k) e le m
  have S3 : step2 ge (.State f (.Ssequence .Sskip
        (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak))
        (.Kseq body_rest (.Kloop1 (.Ssequence (.Ssequence .Sskip
          (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k))
        e le m) Events.E0
      (.State f .Sskip
        (.Kseq (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)
          (.Kseq body_rest (.Kloop1 (.Ssequence (.Ssequence .Sskip
            (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k)))
        e le m) :=
    step.step_seq f .Sskip
      (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)
      (.Kseq body_rest (.Kloop1 (.Ssequence (.Ssequence .Sskip
        (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k)) e le m
  have S4 : step2 ge (.State f .Sskip
        (.Kseq (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)
          (.Kseq body_rest (.Kloop1 (.Ssequence (.Ssequence .Sskip
            (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k)))
        e le m) Events.E0
      (.State f (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)
        (.Kseq body_rest (.Kloop1 (.Ssequence (.Ssequence .Sskip
          (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k))
        e le m) :=
    step.step_skip_seq f
      (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)
      (.Kseq body_rest (.Kloop1 (.Ssequence (.Ssequence .Sskip
        (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k)) e le m
  have S5 : step2 ge
      (.State f (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)
        (.Kseq body_rest (.Kloop1 (.Ssequence (.Ssequence .Sskip
          (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k))
        e le m) Events.E0
      (.State f .Sbreak (.Kseq body_rest (.Kloop1 (.Ssequence (.Ssequence .Sskip
        (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k))
        e le m) :=
    step.step_ifthenelse f (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint)
      .Sskip .Sbreak (.Kseq body_rest (.Kloop1 (.Ssequence (.Ssequence .Sskip
        (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k))
      e le m (Val.of_bool false) false hcond hbool
  have S6 : step2 ge (.State f .Sbreak
        (.Kseq body_rest (.Kloop1 (.Ssequence (.Ssequence .Sskip
          (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k))
        e le m) Events.E0
      (.State f .Sbreak (.Kloop1 (.Ssequence (.Ssequence .Sskip
        (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k)
        e le m) :=
    step.step_break_seq f body_rest (.Kloop1 (.Ssequence (.Ssequence .Sskip
      (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k) e le m
  have S7 : step2 ge (.State f .Sbreak (.Kloop1 (.Ssequence (.Ssequence .Sskip
        (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k)
        e le m) Events.E0
      (.State f .Sskip k e le m) :=
    step.step_break_loop1 f (.Ssequence (.Ssequence .Sskip
      (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k e le m
  have T7 : star step2 ge (.State f .Sbreak (.Kloop1 (.Ssequence (.Ssequence .Sskip
      (.Sifthenelse (.Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint) .Sskip .Sbreak)) body_rest) incr k)
      e le m) Events.E0 (.State f .Sskip k e le m) :=
    step_then _ _ _ _ _ S7 (.star_refl _)
  have T6 := step_then _ _ _ _ _ S6 T7
  have T5 := step_then _ _ _ _ _ S5 T6
  have T4 := step_then _ _ _ _ _ S4 T5
  have T3 := step_then _ _ _ _ _ S3 T4
  have T2 := step_then _ _ _ _ _ S2 T3
  exact step_then _ _ _ _ _ S1 T2

theorem sum_inplace_entry (ge : genv) (m : Memory.mem) (a_blk b_blk : block) (nn : Nat) :
    ∃ le0 : temp_env,
      function_entry2 ge f_sum_inplace
        [.Vptr a_blk Ptrofs.zero, .Vptr b_blk Ptrofs.zero, .Vint (CompCert.Int.repr (nn:Int))] m empty_env le0 m ∧
      le0.get? _a = some (.Vptr a_blk Ptrofs.zero) ∧
      le0.get? _b = some (.Vptr b_blk Ptrofs.zero) ∧
      le0.get? _n = some (.Vint (CompCert.Int.repr (nn:Int))) := by
  refine ⟨((create_undef_temps f_sum_inplace.fn_temps).insert _a (.Vptr a_blk Ptrofs.zero)
      |>.insert _b (.Vptr b_blk Ptrofs.zero)).insert _n (.Vint (CompCert.Int.repr (nn:Int))),
    ?_, ?_, ?_, ?_⟩
  · exact .function_entry2_intro (by decide) (by decide) (by decide) (.alloc_variables_nil _ _) rfl
  · rw [temp_env_get_insert_ne _ _ _ _ (by decide), temp_env_get_insert_ne _ _ _ _ (by decide),
      temp_env_get_insert_self]
  · rw [temp_env_get_insert_ne _ _ _ _ (by decide), temp_env_get_insert_self]
  · rw [temp_env_get_insert_self]

theorem isum_ext (n : Nat) (f g : Nat → CompCert.Int) (h : ∀ j, j < n → f j = g j) :
    isum n f = isum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      unfold isum
      rw [ih (fun j hj => h j (by omega)), h n (by omega)]

theorem mut_cur_zero (a_vals b_vals : Nat → CompCert.Int) (j : Nat) :
    mut_cur 0 a_vals b_vals j = a_vals j := by unfold mut_cur; simp

theorem isum_mut_cur_n (n : Nat) (a_vals b_vals : Nat → CompCert.Int) :
    isum n (mut_cur n a_vals b_vals) = isum n (fun j => CompCert.Int.add (a_vals j) (b_vals j)) := by
  apply isum_ext
  intro j hj
  unfold mut_cur
  simp [hj]
/-- Drives `sum_inplace` all the way from its `Callstate` to its `Returnstate`.

    Proof shape: the function body is, in order, (1) a prologue setting
    `i := 0`, (2) the mutate-loop (`a[i] += b[i]` for `i` in `[0,nn)`), (3) a
    prologue setting `acc := 0`, (4) another prologue resetting `i := 0`,
    (5) the accumulate-loop (`acc += a[i]`, now reading the *mutated* `a`),
    (6) `return acc`. We build one `step`/`star` fact per phase, in the
    order the phases actually execute (`S0`, `hstep2`, `hstep3`, `hstep4`,
    `S5`, ...) -- each depending on the *memory*/*temp_env* state produced
    by the previous phase, which is why they have to be `obtain`ed/derived
    forward. Once all of that is in hand, `T2 .. T14` glue those pieces back
    together *tail-first* (`T14` is built directly on the last step `S14`;
    `T13` prepends `S13` to `T14`; ...) via `step_then`/`star_trans`, because
    each `starTrans` needs to already know the tail it's being glued onto.
    The final `exact` is just that whole glued chain, prepended with the
    very first step `S0`. -/
theorem sum_inplace_run (ge : genv) (m : Memory.mem) (a_blk b_blk : block) (nn : Nat)
    (a_vals b_vals : Nat → CompCert.Int) (hab_disj : a_blk ≠ b_blk) (hn30 : nn < 2^30)
    (harr_a : int_array_at m a_blk nn a_vals) (harr_b : int_array_at m b_blk nn b_vals) :
    ∃ m', star step2 ge
      (.Callstate (.Internal f_sum_inplace)
        [.Vptr a_blk Ptrofs.zero, .Vptr b_blk Ptrofs.zero, .Vint (CompCert.Int.repr (nn:Int))] .Kstop m)
      Events.E0
      (.Returnstate (.Vint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j)))) .Kstop m') := by
  -- Materialize `function_entry2`'s call frame: `le0` is `a,b,n` bound to
  -- the actual arguments and `i,acc` still `Vundef`; no local vars means
  -- `e := empty_env` and memory is untouched (`m` in, `m` out).
  obtain ⟨le0, hentry, hle0_a, hle0_b, hle0_n⟩ := sum_inplace_entry ge m a_blk b_blk nn
  -- Callstate -> the initial `State` running the whole function body.
  have S0 : step2 ge (.Callstate (.Internal f_sum_inplace)
      [.Vptr a_blk Ptrofs.zero, .Vptr b_blk Ptrofs.zero, .Vint (CompCert.Int.repr (nn:Int))] .Kstop m) Events.E0
      (.State f_sum_inplace f_sum_inplace.fn_body .Kstop empty_env le0 m) :=
    step.step_internal_function f_sum_inplace
      [.Vptr a_blk Ptrofs.zero, .Vptr b_blk Ptrofs.zero, .Vint (CompCert.Int.repr (nn:Int))] .Kstop m
      empty_env le0 m hentry
  -- Peel off the whole first `Ssequence`: everything up to and including the
  -- mutate-loop becomes the active statement, with "everything after it"
  -- (acc:=0 prologue, i:=0 reset, accumulate-loop, return) pushed onto the
  -- continuation as `k1`.
  have S1 : step2 ge (.State f_sum_inplace f_sum_inplace.fn_body .Kstop empty_env le0 m) Events.E0
      (.State f_sum_inplace
        (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
          (.Sloop (mutate_body _a _b) mutate_incr))
        (.Kseq (.Ssequence (.Ssequence .Sskip (.Sset _acc (.Econst_int (CompCert.Int.repr 0) tint)))
          (.Ssequence
            (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
              (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr))
            (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint)))))) .Kstop)
        empty_env le0 m) :=
    step.step_seq f_sum_inplace _ _ .Kstop empty_env le0 m
  -- `k1` named for reuse below: "run the acc:=0/i:=0 prologues, the
  -- accumulate-loop, then return" -- i.e. everything after the mutate-loop.
  set k1 : cont := .Kseq (.Ssequence (.Ssequence .Sskip (.Sset _acc (.Econst_int (CompCert.Int.repr 0) tint)))
          (.Ssequence
            (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
              (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr))
            (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint)))))) .Kstop with hk1_def
  have heval0 : eval_expr ge empty_env le0 m (.Econst_int (CompCert.Int.repr 0) tint) (.Vint (CompCert.Int.repr 0)) :=
    eval_expr.eval_Econst_int (CompCert.Int.repr 0) tint
  -- Run the `i := 0` prologue: lands right at the mutate-loop's `Sloop` node.
  have hstep2 : star step2 ge
      (.State f_sum_inplace (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
          (.Sloop (mutate_body _a _b) mutate_incr)) k1 empty_env le0 m) Events.E0
      (.State f_sum_inplace (.Sloop (mutate_body _a _b) mutate_incr) k1 empty_env
        (le0.insert _i (.Vint (CompCert.Int.repr 0))) m) :=
    prologue_step ge f_sum_inplace k1 empty_env le0 m _i _ (.Vint (CompCert.Int.repr 0)) _ heval0
  -- `le1`: `le0` with `_i` now `0`. The next four `have`s establish exactly
  -- the four preconditions `mutate_loop_full` needs to start iterating at
  -- `i = 0`: `_n`, `_a`, `_b` survive unchanged because only `_i` was
  -- touched (frame-preservation from `temp_env_get_insert_ne`).
  set le1 : temp_env := le0.insert _i (.Vint (CompCert.Int.repr 0)) with hle1_def
  have hle1_i : le1.get? _i = some (.Vint (CompCert.Int.repr ((0:Nat):Int))) := by
    rw [hle1_def]; simpa using temp_env_get_insert_self le0 _i (.Vint (CompCert.Int.repr 0))
  have hle1_n : le1.get? _n = some (.Vint (CompCert.Int.repr (nn:Int))) := by
    rw [hle1_def, temp_env_get_insert_ne _ _ _ _ (by decide)]; exact hle0_n
  have hle1_a : le1.get? _a = some (.Vptr a_blk Ptrofs.zero) := by
    rw [hle1_def, temp_env_get_insert_ne _ _ _ _ (by decide)]; exact hle0_a
  have hle1_b : le1.get? _b = some (.Vptr b_blk Ptrofs.zero) := by
    rw [hle1_def, temp_env_get_insert_ne _ _ _ _ (by decide)]; exact hle0_b
  -- `mut_cur 0 a_vals b_vals` is (by definition) just `a_vals` pointwise
  -- ("no index has been mutated yet") -- restate `harr_a` in that form so it
  -- matches `mutate_loop_full`'s invariant at `i = 0`.
  have harr_a0 : int_array_at m a_blk nn (mut_cur 0 a_vals b_vals) := by
    intro j hj; rw [mut_cur_zero]; exact harr_a j hj
  -- Run the mutate-loop to completion: `i` walks `0 -> nn`, and at each step
  -- `a[i]` is overwritten with `a[i]+b[i]`. Comes back out with the
  -- post-loop memory `m2`, where `a` now holds `mut_cur nn a_vals b_vals`
  -- (i.e. `a[j]+b[j]` pointwise) and `b` is untouched (blocks are disjoint).
  obtain ⟨le2, m2, hle2_i, hle2_n, hle2_a, hle2_b, harr_a2, harr_b2, hstep3⟩ :=
    mutate_loop_full ge f_sum_inplace k1 empty_env a_blk b_blk _a _b nn a_vals b_vals
      (by decide) (by decide) (by decide) (by decide) hab_disj hn30
      nn 0 (by omega) le1 m hle1_i hle1_n hle1_a hle1_b harr_a0 harr_b
  -- Exit the mutate-loop: `i = n` now, so the guard is false and control
  -- falls through to `Sskip`.
  have hstep4 : star step2 ge (.State f_sum_inplace (.Sloop (mutate_body _a _b) mutate_incr) k1 empty_env le2 m2)
      Events.E0 (.State f_sum_inplace .Sskip k1 empty_env le2 m2) :=
    loop_exit ge f_sum_inplace k1 empty_env le2 m2 _ mutate_incr nn hn30 hle2_i hle2_n
  -- `Sskip` at continuation `k1` unwinds one `Kseq` layer, landing on the
  -- rest of the function: acc:=0 prologue, i:=0 reset, accumulate-loop, return.
  have S5 : step2 ge (.State f_sum_inplace .Sskip k1 empty_env le2 m2) Events.E0
      (.State f_sum_inplace
        (.Ssequence (.Ssequence .Sskip (.Sset _acc (.Econst_int (CompCert.Int.repr 0) tint)))
          (.Ssequence
            (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
              (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr))
            (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint))))))
        .Kstop empty_env le2 m2) := by
    rw [hk1_def]
    exact step.step_skip_seq f_sum_inplace _ .Kstop empty_env le2 m2
  have heval0' : eval_expr ge empty_env le2 m2 (.Econst_int (CompCert.Int.repr 0) tint) (.Vint (CompCert.Int.repr 0)) :=
    eval_expr.eval_Econst_int (CompCert.Int.repr 0) tint
  -- Run the `acc := 0` prologue.
  have hstep6 : star step2 ge
      (.State f_sum_inplace
        (.Ssequence (.Ssequence .Sskip (.Sset _acc (.Econst_int (CompCert.Int.repr 0) tint)))
          (.Ssequence
            (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
              (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr))
            (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint))))))
        .Kstop empty_env le2 m2) Events.E0
      (.State f_sum_inplace
        (.Ssequence
          (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
            (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr))
          (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint)))))
        .Kstop empty_env (le2.insert _acc (.Vint (CompCert.Int.repr 0))) m2) :=
    prologue_step ge f_sum_inplace .Kstop empty_env le2 m2 _acc _ (.Vint (CompCert.Int.repr 0)) _ heval0'
  set le3 : temp_env := le2.insert _acc (.Vint (CompCert.Int.repr 0)) with hle3_def
  -- Peel off the `i:=0`/accumulate-loop pair from the trailing `return`,
  -- pushing `return acc` onto a fresh continuation `k2`.
  have S7 : step2 ge
      (.State f_sum_inplace
        (.Ssequence
          (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
            (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr))
          (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint)))))
        .Kstop empty_env le3 m2) Events.E0
      (.State f_sum_inplace
        (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
          (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr))
        (.Kseq (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint)))) .Kstop) empty_env le3 m2) :=
    step.step_seq f_sum_inplace _ _ .Kstop empty_env le3 m2
  set k2 : cont := .Kseq (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint)))) .Kstop with hk2_def
  have heval0'' : eval_expr ge empty_env le3 m2 (.Econst_int (CompCert.Int.repr 0) tint) (.Vint (CompCert.Int.repr 0)) :=
    eval_expr.eval_Econst_int (CompCert.Int.repr 0) tint
  -- Run the second `i := 0` (this resets `i` for the *second* loop; the
  -- accumulate-loop, unlike the mutate-loop, needs a fresh pass from 0).
  have hstep8 : star step2 ge
      (.State f_sum_inplace (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
        (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr)) k2 empty_env le3 m2) Events.E0
      (.State f_sum_inplace (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr) k2 empty_env
        (le3.insert _i (.Vint (CompCert.Int.repr 0))) m2) :=
    prologue_step ge f_sum_inplace k2 empty_env le3 m2 _i _ (.Vint (CompCert.Int.repr 0)) _ heval0''
  -- `le4`: `le3` with `_i` reset to `0`. As before, thread `_n`/`_a`
  -- forward across each `insert` via frame-preservation, and separately
  -- show `_acc` is exactly `CompCert.Int.zero + isum 0 (...)` -- i.e. `0` in
  -- the shape `accumulate_loop_full` expects at its starting index `0`.
  set le4 : temp_env := le3.insert _i (.Vint (CompCert.Int.repr 0)) with hle4_def
  have hle4_i : le4.get? _i = some (.Vint (CompCert.Int.repr ((0:Nat):Int))) := by
    rw [hle4_def]; simpa using temp_env_get_insert_self le3 _i (.Vint (CompCert.Int.repr 0))
  have hle3_n : le3.get? _n = some (.Vint (CompCert.Int.repr (nn:Int))) := by
    rw [hle3_def, temp_env_get_insert_ne _ _ _ _ (by decide)]; exact hle2_n
  have hle3_a : le3.get? _a = some (.Vptr a_blk Ptrofs.zero) := by
    rw [hle3_def, temp_env_get_insert_ne _ _ _ _ (by decide)]; exact hle2_a
  have hle4_n : le4.get? _n = some (.Vint (CompCert.Int.repr (nn:Int))) := by
    rw [hle4_def, temp_env_get_insert_ne _ _ _ _ (by decide)]; exact hle3_n
  have hle4_a : le4.get? _a = some (.Vptr a_blk Ptrofs.zero) := by
    rw [hle4_def, temp_env_get_insert_ne _ _ _ _ (by decide)]; exact hle3_a
  have hle4_acc : le4.get? _acc = some (.Vint (CompCert.Int.add CompCert.Int.zero (isum 0 (mut_cur nn a_vals b_vals)))) := by
    rw [hle4_def, temp_env_get_insert_ne _ _ _ _ (by decide), hle3_def, temp_env_get_insert_self]
    rfl
  -- Run the accumulate-loop over the *mutated* `a` (i.e. summing
  -- `mut_cur nn a_vals b_vals`, which equals `a[j]+b[j]` for every `j`),
  -- starting the running total (`c0`) at `CompCert.Int.zero`. Comes back
  -- with `acc = isum nn (mut_cur nn a_vals b_vals)`.
  obtain ⟨le5, hle5_i, hle5_n, hle5_acc, hle5_a, _, hstep9⟩ :=
    accumulate_loop_full ge f_sum_inplace k2 empty_env a_blk _a nn (mut_cur nn a_vals b_vals) CompCert.Int.zero
      (by decide) (by decide) hn30 nn 0 (by omega) le4 m2 hle4_i hle4_n hle4_acc hle4_a harr_a2
  -- Exit the accumulate-loop the same way as the mutate-loop above.
  have hstep10 : star step2 ge (.State f_sum_inplace (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr) k2 empty_env le5 m2)
      Events.E0 (.State f_sum_inplace .Sskip k2 empty_env le5 m2) :=
    loop_exit ge f_sum_inplace k2 empty_env le5 m2 _ acc_incr nn hn30 hle5_i hle5_n
  -- Unwind `Sskip`/`Ssequence` down to the bare `Sreturn`.
  have S11 : step2 ge (.State f_sum_inplace .Sskip k2 empty_env le5 m2) Events.E0
      (.State f_sum_inplace (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint)))) .Kstop empty_env le5 m2) := by
    rw [hk2_def]; exact step.step_skip_seq f_sum_inplace _ .Kstop empty_env le5 m2
  have S12 : step2 ge (.State f_sum_inplace (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint)))) .Kstop empty_env le5 m2) Events.E0
      (.State f_sum_inplace .Sskip (.Kseq (.Sreturn (some (.Etempvar _acc tint))) .Kstop) empty_env le5 m2) :=
    step.step_seq f_sum_inplace .Sskip (.Sreturn (some (.Etempvar _acc tint))) .Kstop empty_env le5 m2
  have S13 : step2 ge (.State f_sum_inplace .Sskip (.Kseq (.Sreturn (some (.Etempvar _acc tint))) .Kstop) empty_env le5 m2) Events.E0
      (.State f_sum_inplace (.Sreturn (some (.Etempvar _acc tint))) .Kstop empty_env le5 m2) :=
    step.step_skip_seq f_sum_inplace (.Sreturn (some (.Etempvar _acc tint))) .Kstop empty_env le5 m2
  -- Evaluate `acc` (the return expression), do the trivially-`rfl` `int` ->
  -- `int` cast the return type needs, and confirm freeing the (empty) local
  -- variable list is a no-op -- then take the actual return step.
  have hle5_acc' : le5.get? _acc = some (.Vint (isum nn (mut_cur nn a_vals b_vals))) := by
    rw [hle5_acc]
    congr 2
    show CompCert.Int.zero + isum nn (mut_cur nn a_vals b_vals) = isum nn (mut_cur nn a_vals b_vals)
    rw [CompCert.Int.add_commut]; exact CompCert.Int.add_zero _
  have heval_acc5 : eval_expr ge empty_env le5 m2 (.Etempvar _acc tint) (.Vint (isum nn (mut_cur nn a_vals b_vals))) :=
    eval_expr.eval_Etempvar _acc tint _ hle5_acc'
  have hcast5 : sem_cast (.Vint (isum nn (mut_cur nn a_vals b_vals))) tint f_sum_inplace.fn_return m2
      = some (.Vint (isum nn (mut_cur nn a_vals b_vals))) :=
    sem_cast_tint_tint (isum nn (mut_cur nn a_vals b_vals)) m2
  have hfree5 : Memory.free_list m2 (blocks_of_env ge empty_env) = some m2 := by
    show Memory.free_list m2 ((∅ : Std.HashMap ident (block × type)).toList.map (block_of_binding ge)) = some m2
    rw [Std.HashMap.toList_empty]; rfl
  have S14 : step2 ge (.State f_sum_inplace (.Sreturn (some (.Etempvar _acc tint))) .Kstop empty_env le5 m2) Events.E0
      (.Returnstate (.Vint (isum nn (mut_cur nn a_vals b_vals))) (call_cont .Kstop) m2) :=
    step.step_return_1 f_sum_inplace (.Etempvar _acc tint) .Kstop empty_env le5 m2
      (.Vint (isum nn (mut_cur nn a_vals b_vals))) (.Vint (isum nn (mut_cur nn a_vals b_vals))) m2
      heval_acc5 hcast5 hfree5
  -- The final memory is `m2` (the mutate-loop's memory; the accumulate-loop
  -- never touches memory). The theorem states the result as
  -- `isum nn (fun j => a_vals j + b_vals j)`; rewrite the goal into
  -- `isum nn (mut_cur nn a_vals b_vals)`, which is what we've actually
  -- computed above (`isum_mut_cur_n` shows these two are equal, since
  -- `mut_cur nn a_vals b_vals j = a_vals j + b_vals j` for every `j < nn`).
  refine ⟨m2, ?_⟩
  rw [show isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j)) = isum nn (mut_cur nn a_vals b_vals)
    from (isum_mut_cur_n nn a_vals b_vals).symm]
  -- Assembly: glue every step/`star` fact derived above into one `star`
  -- from `Callstate` to `Returnstate`, tail-first (`T14` is the innermost,
  -- built directly on the return step `S14`; each `Tk` prepends the next
  -- step/`star` fact going backward toward `S0`). This is purely mechanical
  -- bookkeeping -- no new semantic content past this point.
  have T14 : star step2 ge (.State f_sum_inplace (.Sreturn (some (.Etempvar _acc tint))) .Kstop empty_env le5 m2) Events.E0
      (.Returnstate (.Vint (isum nn (mut_cur nn a_vals b_vals))) .Kstop m2) := by
    have hcc : call_cont (.Kstop : cont) = .Kstop := rfl
    rw [← hcc]; exact step_then _ _ _ _ _ S14 (.star_refl _)
  have T13 := step_then _ _ _ _ _ S13 T14
  have T12 := step_then _ _ _ _ _ S12 T13
  have T11 := step_then _ _ _ _ _ S11 T12
  have T10 : star step2 ge (.State f_sum_inplace (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr) k2 empty_env le5 m2)
      Events.E0 (.Returnstate (.Vint (isum nn (mut_cur nn a_vals b_vals))) .Kstop m2) :=
    star_trans _ _ _ _ _ hstep10 _ _ _ T11 rfl
  have T9a : star step2 ge (.State f_sum_inplace (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr) k2 empty_env le4 m2)
      Events.E0 (.Returnstate (.Vint (isum nn (mut_cur nn a_vals b_vals))) .Kstop m2) :=
    star_trans _ _ _ _ _ hstep9 _ _ _ T10 (by simp)
  have T9 : star step2 ge (.State f_sum_inplace (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
        (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr)) k2 empty_env le3 m2) Events.E0
      (.Returnstate (.Vint (isum nn (mut_cur nn a_vals b_vals))) .Kstop m2) :=
    star_trans _ _ _ _ _ hstep8 _ _ _ T9a (by simp)
  have T8 : star step2 ge (.State f_sum_inplace
        (.Ssequence
          (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
            (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr))
          (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint)))))
        .Kstop empty_env le3 m2) Events.E0
      (.Returnstate (.Vint (isum nn (mut_cur nn a_vals b_vals))) .Kstop m2) :=
    step_then _ _ _ _ _ S7 T9
  have T6 : star step2 ge
      (.State f_sum_inplace
        (.Ssequence (.Ssequence .Sskip (.Sset _acc (.Econst_int (CompCert.Int.repr 0) tint)))
          (.Ssequence
            (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
              (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr))
            (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint))))))
        .Kstop empty_env le2 m2) Events.E0
      (.Returnstate (.Vint (isum nn (mut_cur nn a_vals b_vals))) .Kstop m2) :=
    star_trans _ _ _ _ _ hstep6 _ _ _ T8 (by simp)
  have T5 : star step2 ge (.State f_sum_inplace .Sskip k1 empty_env le2 m2) Events.E0
      (.Returnstate (.Vint (isum nn (mut_cur nn a_vals b_vals))) .Kstop m2) :=
    step_then _ _ _ _ _ S5 T6
  have T4 : star step2 ge (.State f_sum_inplace (.Sloop (mutate_body _a _b) mutate_incr) k1 empty_env le2 m2)
      Events.E0 (.Returnstate (.Vint (isum nn (mut_cur nn a_vals b_vals))) .Kstop m2) :=
    star_trans _ _ _ _ _ hstep4 _ _ _ T5 (by simp)
  have T3a : star step2 ge (.State f_sum_inplace (.Sloop (mutate_body _a _b) mutate_incr) k1 empty_env le1 m) Events.E0
      (.Returnstate (.Vint (isum nn (mut_cur nn a_vals b_vals))) .Kstop m2) :=
    star_trans _ _ _ _ _ hstep3 _ _ _ T4 (by simp)
  have T3 : star step2 ge
      (.State f_sum_inplace (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
        (.Sloop (mutate_body _a _b) mutate_incr)) k1 empty_env le0 m) Events.E0
      (.Returnstate (.Vint (isum nn (mut_cur nn a_vals b_vals))) .Kstop m2) :=
    star_trans _ _ _ _ _ hstep2 _ _ _ T3a (by simp)
  have T2 : star step2 ge (.State f_sum_inplace f_sum_inplace.fn_body .Kstop empty_env le0 m) Events.E0
      (.Returnstate (.Vint (isum nn (mut_cur nn a_vals b_vals))) .Kstop m2) :=
    step_then _ _ _ _ _ S1 T3
  exact step_then _ _ _ _ _ S0 T2
theorem sum_separate_entry (ge : genv) (m : Memory.mem) (a_blk b_blk : block) (nn : Nat) :
    ∃ le0 : temp_env,
      function_entry2 ge f_sum_separate
        [.Vptr a_blk Ptrofs.zero, .Vptr b_blk Ptrofs.zero, .Vint (CompCert.Int.repr (nn:Int))] m empty_env le0 m ∧
      le0.get? _a = some (.Vptr a_blk Ptrofs.zero) ∧
      le0.get? _b = some (.Vptr b_blk Ptrofs.zero) ∧
      le0.get? _n = some (.Vint (CompCert.Int.repr (nn:Int))) := by
  refine ⟨((create_undef_temps f_sum_separate.fn_temps).insert _a (.Vptr a_blk Ptrofs.zero)
      |>.insert _b (.Vptr b_blk Ptrofs.zero)).insert _n (.Vint (CompCert.Int.repr (nn:Int))),
    ?_, ?_, ?_, ?_⟩
  · exact .function_entry2_intro (by decide) (by decide) (by decide) (.alloc_variables_nil _ _) rfl
  · rw [temp_env_get_insert_ne _ _ _ _ (by decide), temp_env_get_insert_ne _ _ _ _ (by decide),
      temp_env_get_insert_self]
  · rw [temp_env_get_insert_ne _ _ _ _ (by decide), temp_env_get_insert_self]
  · rw [temp_env_get_insert_self]

/-- Drives `sum_separate` from `Callstate` to `Returnstate`.

    Proof shape: (1) prologue `acc := 0`, (2) prologue `i := 0` + the first
    accumulate-loop (`acc += a[i]`), (3) prologue `i := 0` again + the
    second accumulate-loop (`acc += b[i]`), (4) `return acc`. Both loops
    reuse the *same* `accumulate_loop_full` lemma; the only thing that
    differs between the two calls is the starting offset `c0`: `zero` for
    the first (fresh `acc`), and `isum nn a_vals` for the second (continuing
    the running total left behind by the first loop, rather than resetting
    it -- this is exactly what the `c0` parameter on `accumulate_loop_full`
    was generalized for). No memory is ever mutated here, unlike
    `sum_inplace_run`. As above: build one fact per phase forward, then
    glue them tail-first into a single `star` at the end. -/
theorem sum_separate_run (ge : genv) (m : Memory.mem) (a_blk b_blk : block) (nn : Nat)
    (a_vals b_vals : Nat → CompCert.Int) (hab_disj : a_blk ≠ b_blk) (hn30 : nn < 2^30)
    (harr_a : int_array_at m a_blk nn a_vals) (harr_b : int_array_at m b_blk nn b_vals) :
    ∃ m', star step2 ge
      (.Callstate (.Internal f_sum_separate)
        [.Vptr a_blk Ptrofs.zero, .Vptr b_blk Ptrofs.zero, .Vint (CompCert.Int.repr (nn:Int))] .Kstop m)
      Events.E0
      (.Returnstate (.Vint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j)))) .Kstop m') := by
  -- Call frame: `a,b,n` bound, `i,acc` still `Vundef`, no local vars.
  obtain ⟨le0, hentry, hle0_a, hle0_b, hle0_n⟩ := sum_separate_entry ge m a_blk b_blk nn
  -- Callstate -> initial `State` running the function body.
  have S0 : step2 ge (.Callstate (.Internal f_sum_separate)
      [.Vptr a_blk Ptrofs.zero, .Vptr b_blk Ptrofs.zero, .Vint (CompCert.Int.repr (nn:Int))] .Kstop m) Events.E0
      (.State f_sum_separate f_sum_separate.fn_body .Kstop empty_env le0 m) :=
    step.step_internal_function f_sum_separate
      [.Vptr a_blk Ptrofs.zero, .Vptr b_blk Ptrofs.zero, .Vint (CompCert.Int.repr (nn:Int))] .Kstop m
      empty_env le0 m hentry
  have heval0 : eval_expr ge empty_env le0 m (.Econst_int (CompCert.Int.repr 0) tint) (.Vint (CompCert.Int.repr 0)) :=
    eval_expr.eval_Econst_int (CompCert.Int.repr 0) tint
  -- `fn_body` here is exactly `prologue_step`'s own pattern
  -- (`Ssequence (Ssequence Sskip (Sset _acc 0)) rest`), so run the whole
  -- `acc := 0` prologue in one shot, landing directly on "rest" (both
  -- loops plus the return, still to be split further below).
  have hstep1 : star step2 ge (.State f_sum_separate f_sum_separate.fn_body .Kstop empty_env le0 m) Events.E0
      (.State f_sum_separate
        (.Ssequence
          (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
            (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr))
          (.Ssequence
            (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
              (.Sloop (acc_body (.Etempvar _b tintptr)) acc_incr))
            (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint))))))
        .Kstop empty_env (le0.insert _acc (.Vint (CompCert.Int.repr 0))) m) :=
    prologue_step ge f_sum_separate .Kstop empty_env le0 m _acc _ (.Vint (CompCert.Int.repr 0)) _ heval0
  set le1 : temp_env := le0.insert _acc (.Vint (CompCert.Int.repr 0)) with hle1_def
  -- `k1`: "run the second `i:=0`/loop-over-`b` pair, then return" -- i.e.
  -- everything after the first loop.
  set k1 : cont := .Kseq
      (.Ssequence
        (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
          (.Sloop (acc_body (.Etempvar _b tintptr)) acc_incr))
        (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint))))) .Kstop with hk1_def
  -- Split the first loop off from "everything else" via `k1`.
  have S2 : step2 ge (.State f_sum_separate
      (.Ssequence
        (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
          (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr))
        (.Ssequence
          (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
            (.Sloop (acc_body (.Etempvar _b tintptr)) acc_incr))
          (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint))))))
      .Kstop empty_env le1 m) Events.E0
      (.State f_sum_separate
        (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
          (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr))
        k1 empty_env le1 m) := by
    rw [hk1_def]
    exact step.step_seq f_sum_separate _ _ .Kstop empty_env le1 m
  have heval0' : eval_expr ge empty_env le1 m (.Econst_int (CompCert.Int.repr 0) tint) (.Vint (CompCert.Int.repr 0)) :=
    eval_expr.eval_Econst_int (CompCert.Int.repr 0) tint
  -- Run the `i := 0` prologue for the first loop.
  have hstep3 : star step2 ge
      (.State f_sum_separate (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
        (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr)) k1 empty_env le1 m) Events.E0
      (.State f_sum_separate (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr) k1 empty_env
        (le1.insert _i (.Vint (CompCert.Int.repr 0))) m) :=
    prologue_step ge f_sum_separate k1 empty_env le1 m _i _ (.Vint (CompCert.Int.repr 0)) _ heval0'
  -- `le2`: `_i` reset to `0`; thread `_n`/`_a` forward across both
  -- `insert`s so far (`_acc` then `_i`), and show `_acc = zero + isum 0
  -- a_vals` -- i.e. `0`, in the shape `accumulate_loop_full` wants at its
  -- starting index `0` with a *fresh* running total (`c0 := zero`).
  set le2 : temp_env := le1.insert _i (.Vint (CompCert.Int.repr 0)) with hle2_def
  have hle2_i : le2.get? _i = some (.Vint (CompCert.Int.repr ((0:Nat):Int))) := by
    rw [hle2_def]; simpa using temp_env_get_insert_self le1 _i (.Vint (CompCert.Int.repr 0))
  have hle1_n : le1.get? _n = some (.Vint (CompCert.Int.repr (nn:Int))) := by
    rw [hle1_def, temp_env_get_insert_ne _ _ _ _ (by decide)]; exact hle0_n
  have hle1_a : le1.get? _a = some (.Vptr a_blk Ptrofs.zero) := by
    rw [hle1_def, temp_env_get_insert_ne _ _ _ _ (by decide)]; exact hle0_a
  have hle2_n : le2.get? _n = some (.Vint (CompCert.Int.repr (nn:Int))) := by
    rw [hle2_def, temp_env_get_insert_ne _ _ _ _ (by decide)]; exact hle1_n
  have hle2_a : le2.get? _a = some (.Vptr a_blk Ptrofs.zero) := by
    rw [hle2_def, temp_env_get_insert_ne _ _ _ _ (by decide)]; exact hle1_a
  have hle2_acc : le2.get? _acc = some (.Vint (CompCert.Int.add CompCert.Int.zero (isum 0 a_vals))) := by
    rw [hle2_def, temp_env_get_insert_ne _ _ _ _ (by decide), hle1_def, temp_env_get_insert_self]
    rfl
  -- Run the first accumulate-loop over `a`, `c0 := zero`. Also grab the
  -- generic frame condition `hle3_frame` -- unlike `_a`, the pointer `_b`
  -- was never mentioned to `accumulate_loop_full`, so its value has to be
  -- recovered afterward via this frame fact instead of a dedicated output.
  obtain ⟨le3, hle3_i, hle3_n, hle3_acc, hle3_a, hle3_frame, hstep4⟩ :=
    accumulate_loop_full ge f_sum_separate k1 empty_env a_blk _a nn a_vals CompCert.Int.zero
      (by decide) (by decide) hn30 nn 0 (by omega) le2 m hle2_i hle2_n hle2_acc hle2_a harr_a
  -- Exit the first loop (guard false at `i = n`).
  have hstep5 : star step2 ge (.State f_sum_separate (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr) k1 empty_env le3 m)
      Events.E0 (.State f_sum_separate .Sskip k1 empty_env le3 m) :=
    loop_exit ge f_sum_separate k1 empty_env le3 m _ acc_incr nn hn30 hle3_i hle3_n
  -- Unwind `Sskip` at `k1` -> lands on the second `i:=0`/loop-over-`b` pair
  -- plus the return.
  have S6 : step2 ge (.State f_sum_separate .Sskip k1 empty_env le3 m) Events.E0
      (.State f_sum_separate
        (.Ssequence
          (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
            (.Sloop (acc_body (.Etempvar _b tintptr)) acc_incr))
          (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint)))))
        .Kstop empty_env le3 m) := by
    rw [hk1_def]; exact step.step_skip_seq f_sum_separate _ .Kstop empty_env le3 m
  -- Split the second loop off from the trailing `return`, onto continuation `k2`.
  have S7 : step2 ge (.State f_sum_separate
        (.Ssequence
          (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
            (.Sloop (acc_body (.Etempvar _b tintptr)) acc_incr))
          (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint)))))
        .Kstop empty_env le3 m) Events.E0
      (.State f_sum_separate
        (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
          (.Sloop (acc_body (.Etempvar _b tintptr)) acc_incr))
        (.Kseq (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint)))) .Kstop) empty_env le3 m) :=
    step.step_seq f_sum_separate _ _ .Kstop empty_env le3 m
  set k2 : cont := .Kseq (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint)))) .Kstop with hk2_def
  have heval0'' : eval_expr ge empty_env le3 m (.Econst_int (CompCert.Int.repr 0) tint) (.Vint (CompCert.Int.repr 0)) :=
    eval_expr.eval_Econst_int (CompCert.Int.repr 0) tint
  -- Run the second `i := 0` (fresh pass for the second loop).
  have hstep8 : star step2 ge
      (.State f_sum_separate (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
        (.Sloop (acc_body (.Etempvar _b tintptr)) acc_incr)) k2 empty_env le3 m) Events.E0
      (.State f_sum_separate (.Sloop (acc_body (.Etempvar _b tintptr)) acc_incr) k2 empty_env
        (le3.insert _i (.Vint (CompCert.Int.repr 0))) m) :=
    prologue_step ge f_sum_separate k2 empty_env le3 m _i _ (.Vint (CompCert.Int.repr 0)) _ heval0''
  -- `le4`: `_i` reset to `0` again. Recover `_b`'s value from `le3` via the
  -- generic frame condition (`hle3_frame`, from the first loop's induction)
  -- then thread it across this `insert` too; then show `_acc` at `le4` is
  -- `isum nn a_vals + isum 0 b_vals`, i.e. the first loop's *final* total
  -- plus zero -- this is the "continue accumulating" starting point the
  -- second call to `accumulate_loop_full` needs (`c0 := isum nn a_vals`).
  set le4 : temp_env := le3.insert _i (.Vint (CompCert.Int.repr 0)) with hle4_def
  have hle4_i : le4.get? _i = some (.Vint (CompCert.Int.repr ((0:Nat):Int))) := by
    rw [hle4_def]; simpa using temp_env_get_insert_self le3 _i (.Vint (CompCert.Int.repr 0))
  have hle4_n : le4.get? _n = some (.Vint (CompCert.Int.repr (nn:Int))) := by
    rw [hle4_def, temp_env_get_insert_ne _ _ _ _ (by decide)]; exact hle3_n
  have hle3_b : le3.get? _b = some (.Vptr b_blk Ptrofs.zero) := by
    rw [hle3_frame _b (by decide) (by decide)]
    rw [hle2_def, temp_env_get_insert_ne _ _ _ _ (by decide)]
    rw [hle1_def, temp_env_get_insert_ne _ _ _ _ (by decide)]
    exact hle0_b
  have hle4_b : le4.get? _b = some (.Vptr b_blk Ptrofs.zero) := by
    rw [hle4_def, temp_env_get_insert_ne _ _ _ _ (by decide)]
    exact hle3_b
  have hle4_acc : le4.get? _acc = some (.Vint (CompCert.Int.add (isum nn a_vals) (isum 0 b_vals))) := by
    rw [hle4_def, temp_env_get_insert_ne _ _ _ _ (by decide)]
    rw [hle3_acc]
    have h1 : CompCert.Int.add CompCert.Int.zero (isum nn a_vals) = isum nn a_vals := by
      show CompCert.Int.zero + isum nn a_vals = isum nn a_vals
      rw [CompCert.Int.add_commut]; exact CompCert.Int.add_zero _
    have h2 : isum 0 b_vals = CompCert.Int.zero := rfl
    rw [h1, h2, CompCert.Int.add_zero]
  -- Run the second accumulate-loop over `b`, `c0 := isum nn a_vals`. Comes
  -- back with `acc = isum nn a_vals + isum nn b_vals`.
  obtain ⟨le5, hle5_i, hle5_n, hle5_acc, hle5_b, _, hstep9⟩ :=
    accumulate_loop_full ge f_sum_separate k2 empty_env b_blk _b nn b_vals (isum nn a_vals)
      (by decide) (by decide) hn30 nn 0 (by omega) le4 m hle4_i hle4_n hle4_acc hle4_b harr_b
  -- Exit the second loop and unwind down to the bare `Sreturn`.
  have hstep10 : star step2 ge (.State f_sum_separate (.Sloop (acc_body (.Etempvar _b tintptr)) acc_incr) k2 empty_env le5 m)
      Events.E0 (.State f_sum_separate .Sskip k2 empty_env le5 m) :=
    loop_exit ge f_sum_separate k2 empty_env le5 m _ acc_incr nn hn30 hle5_i hle5_n
  have S11 : step2 ge (.State f_sum_separate .Sskip k2 empty_env le5 m) Events.E0
      (.State f_sum_separate (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint)))) .Kstop empty_env le5 m) := by
    rw [hk2_def]; exact step.step_skip_seq f_sum_separate _ .Kstop empty_env le5 m
  have S12 : step2 ge (.State f_sum_separate (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint)))) .Kstop empty_env le5 m) Events.E0
      (.State f_sum_separate .Sskip (.Kseq (.Sreturn (some (.Etempvar _acc tint))) .Kstop) empty_env le5 m) :=
    step.step_seq f_sum_separate .Sskip (.Sreturn (some (.Etempvar _acc tint))) .Kstop empty_env le5 m
  have S13 : step2 ge (.State f_sum_separate .Sskip (.Kseq (.Sreturn (some (.Etempvar _acc tint))) .Kstop) empty_env le5 m) Events.E0
      (.State f_sum_separate (.Sreturn (some (.Etempvar _acc tint))) .Kstop empty_env le5 m) :=
    step.step_skip_seq f_sum_separate (.Sreturn (some (.Etempvar _acc tint))) .Kstop empty_env le5 m
  -- Rewrite `acc`'s value from `isum nn a_vals + isum nn b_vals` into
  -- `isum nn (fun j => a_vals j + b_vals j)` (via `isum_add_distrib` -- the
  -- one purely-arithmetic fact behind this whole theorem), evaluate the
  -- return expression, do the trivial cast, confirm freeing the (empty)
  -- local list is a no-op, and take the return step.
  have hle5_acc' : le5.get? _acc = some (.Vint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j)))) := by
    rw [hle5_acc, isum_add_distrib]
  have heval_acc5 : eval_expr ge empty_env le5 m (.Etempvar _acc tint)
      (.Vint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j)))) :=
    eval_expr.eval_Etempvar _acc tint _ hle5_acc'
  have hcast5 : sem_cast (.Vint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j))))
      tint f_sum_separate.fn_return m
      = some (.Vint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j)))) :=
    sem_cast_tint_tint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j))) m
  have hfree5 : Memory.free_list m (blocks_of_env ge empty_env) = some m := by
    show Memory.free_list m ((∅ : Std.HashMap ident (block × type)).toList.map (block_of_binding ge)) = some m
    rw [Std.HashMap.toList_empty]; rfl
  have S14 : step2 ge (.State f_sum_separate (.Sreturn (some (.Etempvar _acc tint))) .Kstop empty_env le5 m) Events.E0
      (.Returnstate (.Vint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j)))) (call_cont .Kstop) m) :=
    step.step_return_1 f_sum_separate (.Etempvar _acc tint) .Kstop empty_env le5 m
      (.Vint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j))))
      (.Vint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j)))) m
      heval_acc5 hcast5 hfree5
  -- Final memory is just `m` unchanged (no mutation anywhere in this
  -- function). Assembly: same tail-first gluing as `sum_inplace_run`.
  refine ⟨m, ?_⟩
  have T14 : star step2 ge (.State f_sum_separate (.Sreturn (some (.Etempvar _acc tint))) .Kstop empty_env le5 m) Events.E0
      (.Returnstate (.Vint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j)))) .Kstop m) := by
    have hcc : call_cont (.Kstop : cont) = .Kstop := rfl
    rw [← hcc]; exact step_then _ _ _ _ _ S14 (.star_refl _)
  have T13 := step_then _ _ _ _ _ S13 T14
  have T12 := step_then _ _ _ _ _ S12 T13
  have T11 := step_then _ _ _ _ _ S11 T12
  have T10 : star step2 ge (.State f_sum_separate (.Sloop (acc_body (.Etempvar _b tintptr)) acc_incr) k2 empty_env le5 m)
      Events.E0 (.Returnstate (.Vint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j)))) .Kstop m) :=
    star_trans _ _ _ _ _ hstep10 _ _ _ T11 rfl
  have T9a : star step2 ge (.State f_sum_separate (.Sloop (acc_body (.Etempvar _b tintptr)) acc_incr) k2 empty_env le4 m)
      Events.E0 (.Returnstate (.Vint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j)))) .Kstop m) :=
    star_trans _ _ _ _ _ hstep9 _ _ _ T10 (by simp)
  have T9 : star step2 ge (.State f_sum_separate
        (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
          (.Sloop (acc_body (.Etempvar _b tintptr)) acc_incr)) k2 empty_env le3 m) Events.E0
      (.Returnstate (.Vint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j)))) .Kstop m) :=
    star_trans _ _ _ _ _ hstep8 _ _ _ T9a (by simp)
  have T8 : star step2 ge (.State f_sum_separate
        (.Ssequence
          (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
            (.Sloop (acc_body (.Etempvar _b tintptr)) acc_incr))
          (.Ssequence .Sskip (.Sreturn (some (.Etempvar _acc tint)))))
        .Kstop empty_env le3 m) Events.E0
      (.Returnstate (.Vint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j)))) .Kstop m) :=
    step_then _ _ _ _ _ S7 T9
  have T6 : star step2 ge (.State f_sum_separate .Sskip k1 empty_env le3 m) Events.E0
      (.Returnstate (.Vint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j)))) .Kstop m) :=
    step_then _ _ _ _ _ S6 T8
  have T5 : star step2 ge (.State f_sum_separate (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr) k1 empty_env le3 m)
      Events.E0 (.Returnstate (.Vint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j)))) .Kstop m) :=
    star_trans _ _ _ _ _ hstep5 _ _ _ T6 (by simp)
  have T4 : star step2 ge (.State f_sum_separate (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr) k1 empty_env le2 m)
      Events.E0 (.Returnstate (.Vint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j)))) .Kstop m) :=
    star_trans _ _ _ _ _ hstep4 _ _ _ T5 (by simp)
  have T3 : star step2 ge
      (.State f_sum_separate (.Ssequence (.Ssequence .Sskip (.Sset _i (.Econst_int (CompCert.Int.repr 0) tint)))
        (.Sloop (acc_body (.Etempvar _a tintptr)) acc_incr)) k1 empty_env le1 m) Events.E0
      (.Returnstate (.Vint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j)))) .Kstop m) :=
    star_trans _ _ _ _ _ hstep3 _ _ _ T4 (by simp)
  have T2 : star step2 ge (.State f_sum_separate f_sum_separate.fn_body .Kstop empty_env le0 m) Events.E0
      (.Returnstate (.Vint (isum nn (fun j => CompCert.Int.add (a_vals j) (b_vals j)))) .Kstop m) :=
    star_trans _ _ _ _ _ hstep1 _ _ _ (step_then _ _ _ _ _ S2 T3) (by simp)
  exact step_then _ _ _ _ _ S0 T2

/-- **The equivalence theorem.** `sum_inplace` and `sum_separate` compute the
    same `int` result for all inputs where `a` and `b` denote disjoint,
    fully-readable length-`nn` int arrays: both executions (each witnessed
    directly as a `star`-sequence of the Clight small-step relation, from
    the same initial `Callstate` and memory `m`, through `function_entry2`)
    terminate in a `Returnstate` carrying the identical `result`.

    Note this is a same-return-value equivalence, not a same-final-memory
    one: `sum_inplace` mutates array `a` in place (`m1 ≠ m2` in general),
    matching that `sum_inplace`/`sum_separate` only agree in their observable
    *result*, not in every memory side effect. -/
theorem sum_inplace_sum_separate_equiv (a_blk b_blk : block) (nn : Nat)
    (a_vals b_vals : Nat → CompCert.Int) (hab_disj : a_blk ≠ b_blk) (hn30 : nn < 2^30)
    (m : Memory.mem) (harr_a : int_array_at m a_blk nn a_vals) (harr_b : int_array_at m b_blk nn b_vals) :
    ∃ (result : val) (m1 m2 : Memory.mem),
      star step2 ge (.Callstate (.Internal f_sum_inplace)
        [.Vptr a_blk Ptrofs.zero, .Vptr b_blk Ptrofs.zero, .Vint (CompCert.Int.repr (nn:Int))] .Kstop m)
        Events.E0 (.Returnstate result .Kstop m1) ∧
      star step2 ge (.Callstate (.Internal f_sum_separate)
        [.Vptr a_blk Ptrofs.zero, .Vptr b_blk Ptrofs.zero, .Vint (CompCert.Int.repr (nn:Int))] .Kstop m)
        Events.E0 (.Returnstate result .Kstop m2) := by
  obtain ⟨m1, h1⟩ := sum_inplace_run ge m a_blk b_blk nn a_vals b_vals hab_disj hn30 harr_a harr_b
  obtain ⟨m2, h2⟩ := sum_separate_run ge m a_blk b_blk nn a_vals b_vals hab_disj hn30 harr_a harr_b
  exact ⟨_, m1, m2, h1, h2⟩
