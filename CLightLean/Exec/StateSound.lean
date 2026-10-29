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
Soundness of the executable state-layer helpers with respect to the
authoritative relations in `CLight.lean`.
-/

namespace CLightLean.Exec

variable [Archi]

/-- A successful scalar `assignLoc` computation is an authoritative
`assign_loc_value` derivation. -/
theorem assignLoc_full_value_sound
    (cenv : composite_env) (ty : type) (m : Memory.mem) (b : block) (ofs : ptrofs)
    (v : val) (chunk : memory_chunk) (m' : Memory.mem)
    (hmode : access_mode ty = .By_value chunk)
    (h : assignLoc cenv ty m b ofs .Full v = .ok m') :
    assign_loc cenv ty m b ofs .Full v m' := by
  unfold assignLoc at h
  rw [hmode] at h
  cases hstore : Memory.storev chunk m (.Vptr b ofs) v with
  | none =>
      simp [hstore] at h
  | some stored =>
      simp [hstore] at h
      subst m'
      exact .assign_loc_value v chunk stored hmode hstore

/-- The Boolean aggregate-source/destination alignment check supplies the
    conditional divisibility premise of `assign_loc_copy`. -/
theorem blockCopyAligned_sound
    (cenv : composite_env) (ty : type) (ofs : ptrofs)
    (h : blockCopyAligned cenv ty ofs = true) :
    sizeof cenv ty > 0 → alignof_blockcopy cenv ty ∣ Ptrofs.unsigned ofs := by
  intro hsize
  simp [blockCopyAligned, hsize] at h
  exact h

/-- The Boolean aggregate non-overlap check supplies the disjunction required
    by `assign_loc_copy`. -/
theorem blockCopySeparated_sound
    (cenv : composite_env) (srcBlock : block) (srcOfs : ptrofs)
    (dstBlock : block) (dstOfs : ptrofs) (ty : type)
    (h : blockCopySeparated cenv srcBlock srcOfs dstBlock dstOfs ty = true) :
    srcBlock ≠ dstBlock ∨ Ptrofs.unsigned srcOfs = Ptrofs.unsigned dstOfs
      ∨ Ptrofs.unsigned srcOfs + sizeof cenv ty ≤ Ptrofs.unsigned dstOfs
      ∨ Ptrofs.unsigned dstOfs + sizeof cenv ty ≤ Ptrofs.unsigned srcOfs := by
  simp only [blockCopySeparated, Bool.or_eq_true, bne_iff_ne, beq_iff_eq,
    decide_eq_true_eq] at h
  rcases h with h | hright
  · rcases h with h | hleft
    · rcases h with hne | heq
      · exact Or.inl hne
      · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr (Or.inl hleft))
  · exact Or.inr (Or.inr (Or.inr hright))

/-- A successful bitfield executor call supplies a matching relational
    `store_bitfield` derivation, including its normalized stored value. -/
theorem assignBitfield_sound
    (ty : type) (m : Memory.mem) (b : block) (ofs : ptrofs)
    (sz : intsize) (sg : signedness) (pos width : Int) (v : val) (m' : Memory.mem)
    (h : assignBitfield ty m b ofs sz sg pos width v = .ok m') :
    ∃ v', store_bitfield ty sz sg pos width m (.Vptr b ofs) v m' v' := by
  cases ty with
  | Tint carrierSz carrierSg attr =>
      cases v with
      | Vint n =>
          by_cases hsz : carrierSz = sz
          · by_cases hpos : 0 ≤ pos
            · by_cases hwidth : 0 < width ∧ width ≤ bitsize_intsize sz
              · by_cases hcarrier : pos + width ≤ bitsize_carrier sz
                · by_cases hsg : carrierSg = (if width < bitsize_intsize sz then .Signed else sg)
                  · cases hload : Memory.loadv (chunk_for_carrier sz) m (.Vptr b ofs) with
                    | none =>
                        simp [assignBitfield, hsz, hpos, hwidth, hcarrier, hsg, hload] at h
                    | some loaded =>
                        cases loaded with
                        | Vint carrier =>
                            cases hstore : Memory.storev (chunk_for_carrier sz) m (.Vptr b ofs)
                                (.Vint (CompCert.Int.bitfield_insert
                                  (first_bit sz pos width) width carrier n)) with
                            | none =>
                                simp [assignBitfield, hsz, hpos, hwidth, hcarrier, hsg,
                                  hload, hstore] at h
                            | some stored =>
                                have hm' : m' = stored := by
                                  simpa [assignBitfield, hsz, hpos, hwidth, hcarrier, hsg,
                                    hload, hstore] using h.symm
                                subst m'
                                subst carrierSz
                                exact ⟨.Vint (bitfield_normalize sz sg width n),
                                  .store_bitfield_intro sz carrierSg attr sg pos width m
                                    (.Vptr b ofs) carrier n stored hpos hwidth hcarrier hsg
                                    hload hstore⟩
                        | Vundef =>
                            simp [assignBitfield, hsz, hpos, hwidth, hcarrier, hsg, hload] at h
                        | Vlong n =>
                            simp [assignBitfield, hsz, hpos, hwidth, hcarrier, hsg, hload] at h
                        | Vfloat f =>
                            simp [assignBitfield, hsz, hpos, hwidth, hcarrier, hsg, hload] at h
                        | Vsingle f =>
                            simp [assignBitfield, hsz, hpos, hwidth, hcarrier, hsg, hload] at h
                        | Vptr b ofs =>
                            simp [assignBitfield, hsz, hpos, hwidth, hcarrier, hsg, hload] at h
                  · simp [assignBitfield, hsz, hpos, hwidth, hcarrier, hsg] at h
                · simp [assignBitfield, hsz, hpos, hwidth, hcarrier] at h
              · simp [assignBitfield, hsz, hpos, hwidth] at h
            · simp [assignBitfield, hsz, hpos] at h
          · simp [assignBitfield, hsz] at h
      | Vundef => simp [assignBitfield] at h
      | Vlong n => simp [assignBitfield] at h
      | Vfloat f => simp [assignBitfield] at h
      | Vsingle f => simp [assignBitfield] at h
      | Vptr b ofs => simp [assignBitfield] at h
  | Tvoid => simp [assignBitfield] at h
  | Tlong sg attr => simp [assignBitfield] at h
  | Tfloat sz attr => simp [assignBitfield] at h
  | Tpointer ty attr => simp [assignBitfield] at h
  | Tarray ty n attr => simp [assignBitfield] at h
  | Tfunction params result cc => simp [assignBitfield] at h
  | Tstruct id attr => simp [assignBitfield] at h
  | Tunion id attr => simp [assignBitfield] at h

/-- Every successful functional assignment is an authoritative
    `assign_loc` derivation. -/
theorem assignLoc_sound
    (cenv : composite_env) (ty : type) (m : Memory.mem) (b : block) (ofs : ptrofs)
    (bf : bitfield) (v : val) (m' : Memory.mem)
    (h : assignLoc cenv ty m b ofs bf v = .ok m') :
    assign_loc cenv ty m b ofs bf v m' := by
  cases bf with
  | Full =>
      cases hmode : access_mode ty with
      | By_value chunk =>
          exact assignLoc_full_value_sound cenv ty m b ofs v chunk m' hmode h
      | By_copy =>
          cases v with
          | Vptr srcBlock srcOfs =>
              cases hsrcAligned : blockCopyAligned cenv ty srcOfs with
              | false => simp [assignLoc, hmode, hsrcAligned] at h
              | true =>
                  cases hdstAligned : blockCopyAligned cenv ty ofs with
                  | false => simp [assignLoc, hmode, hsrcAligned, hdstAligned] at h
                  | true =>
                      cases hseparated : blockCopySeparated cenv srcBlock srcOfs b ofs ty with
                      | false =>
                          simp [assignLoc, hmode, hsrcAligned, hdstAligned, hseparated] at h
                      | true =>
                          cases hload : Memory.loadbytes m srcBlock (Ptrofs.unsigned srcOfs)
                              (sizeof cenv ty) with
                          | none =>
                              simp [assignLoc, hmode, hsrcAligned, hdstAligned, hseparated,
                                hload] at h
                          | some bytes =>
                              cases hstore : Memory.storebytes m b (Ptrofs.unsigned ofs) bytes with
                              | none =>
                                  simp [assignLoc, hmode, hsrcAligned, hdstAligned, hseparated,
                                    hload, hstore] at h
                              | some stored =>
                                  have hm' : m' = stored := by
                                    simpa [assignLoc, hmode, hsrcAligned, hdstAligned,
                                      hseparated, hload, hstore] using h.symm
                                  subst m'
                                  exact .assign_loc_copy srcBlock srcOfs bytes stored hmode
                                    (blockCopyAligned_sound cenv ty srcOfs hsrcAligned)
                                    (blockCopyAligned_sound cenv ty ofs hdstAligned)
                                    (blockCopySeparated_sound cenv srcBlock srcOfs b ofs ty
                                      hseparated)
                                    hload hstore
          | Vundef => simp [assignLoc, hmode] at h
          | Vint n => simp [assignLoc, hmode] at h
          | Vlong n => simp [assignLoc, hmode] at h
          | Vfloat f => simp [assignLoc, hmode] at h
          | Vsingle f => simp [assignLoc, hmode] at h
      | By_reference => simp [assignLoc, hmode] at h
      | By_nothing => simp [assignLoc, hmode] at h
  | Bits sz sg pos width =>
      obtain ⟨v', hstore⟩ := assignBitfield_sound ty m b ofs sz sg pos width v m' h
      exact .assign_loc_bitfield sz sg pos width v m' v' hstore

/-- `allocVariables` agrees definitionally with the relational empty-list
allocation constructor. -/
theorem allocVariables_nil_sound (ge : genv) (e : env) (m : Memory.mem) :
    alloc_variables ge e m [] e m :=
  .alloc_variables_nil e m

/-- Successful recursive local allocation is an `alloc_variables` derivation. -/
theorem allocVariables_sound
    (ge : genv) (e : env) (m : Memory.mem) (vars : List (ident × type))
    (locals : LocalState)
    (h : allocVariables ge e m vars = .ok locals) :
    alloc_variables ge e m vars locals.env locals.memory := by
  induction vars generalizing e m locals with
  | nil =>
      have hlocals : locals = { env := e, memory := m } := by
        exact Except.ok.inj h.symm
      subst locals
      exact .alloc_variables_nil e m
  | cons binding vars ih =>
      obtain ⟨id, ty⟩ := binding
      cases halloc : Memory.alloc m 0 (sizeof ge.genv_cenv ty) with
      | mk allocatedBlock allocatedMemory =>
          have htail : allocVariables ge (e.insert id (allocatedBlock, ty)) allocatedMemory vars
              = .ok locals := by
            simpa [allocVariables, halloc] using h
          exact .alloc_variables_cons e m id ty vars allocatedMemory allocatedBlock
            locals.memory locals.env halloc
            (ih (e.insert id (allocatedBlock, ty)) allocatedMemory locals htail)

/-- The executor's temporary-initialization spelling is exactly the existing
Clight helper. -/
theorem createUndefTemps_eq (temps : List (ident × type)) :
    createUndefTemps temps = create_undef_temps temps := rfl

/-- A successful checked temporary parameter bind is exactly a successful use
of the authoritative computational helper. -/
theorem bindParameterTemps_sound
    (formals : List (ident × type)) (args : List val) (temps boundTemps : temp_env)
    (h : bindParameterTemps formals args temps = .ok boundTemps) :
    bind_parameter_temps formals args temps = some boundTemps := by
  unfold bindParameterTemps at h
  cases hbind : bind_parameter_temps formals args temps with
  | none => simp [hbind] at h
  | some result =>
      simp [hbind] at h
      exact congrArg some h

/-- A successful checked `functionEntry2` exactly satisfies the authoritative
    parameter-as-temporaries function-entry relation. -/
theorem functionEntry2_sound
    (ge : genv) (f : function) (args : List val) (m : Memory.mem)
    (entry : FunctionEntryState)
    (h : functionEntry2 ge f args m = .ok entry) :
    function_entry2 ge f args m entry.env entry.temps entry.memory := by
  by_cases hvars : (var_names f.fn_vars).Nodup
  · by_cases hparams : (var_names f.fn_params).Nodup
    · by_cases hseparate : ∀ x ∈ var_names f.fn_params, ∀ y ∈ var_names f.fn_temps, x ≠ y
      · simp only [functionEntry2, dif_pos hvars, dif_pos hparams,
          dif_pos hseparate] at h
        cases hlocals : allocVariables ge empty_env m f.fn_vars with
        | error err =>
            simp [hlocals] at h
        | ok locals =>
            cases htemps : bindParameterTemps f.fn_params args (createUndefTemps f.fn_temps) with
            | error err =>
                simp [hlocals, htemps] at h
            | ok temps =>
                have hentry : entry =
                    { env := locals.env, temps := temps, memory := locals.memory } := by
                  have hresult :
                      ({ env := locals.env, temps := temps, memory := locals.memory } :
                        FunctionEntryState) = entry := by
                    simpa [hlocals, htemps] using h
                  exact hresult.symm
                subst entry
                exact .function_entry2_intro hvars hparams hseparate
                  (allocVariables_sound ge empty_env m f.fn_vars locals hlocals)
                  (bindParameterTemps_sound f.fn_params args (createUndefTemps f.fn_temps)
                    temps htemps)
      · simp only [functionEntry2, dif_pos hvars, dif_pos hparams,
          dif_neg hseparate] at h
        contradiction
    · simp only [functionEntry2, dif_pos hvars, dif_neg hparams] at h
      contradiction
  · simp only [functionEntry2, dif_neg hvars] at h
    contradiction

end CLightLean.Exec
