import ConleyCheck.Gubser.TCIndex

/-!
# The corner `TC^-` in the chart `T = -∞` (`lem:TC`(ii), (iii))

In the chart `u = π̄/T`, `v̂ = 1/|T|` the flow is `eq:flowTm`, with fields `Gu`, `Gv`. The reversor
`S̃` acts by `(u, v, τ) ↦ (-u, v̂, -τ)` and reverses time, and indeed
`Gu c u v τ = Fu c (-u) v (-τ)` and `Gv u v τ = -Fv (-u) v (-τ)`.

* `TCModelMinus`: a flow whose coordinates satisfy `eq:flowTm` near the block, with a cut-off.
  `TCModelMinus.toPlus` turns it into a `TCModel` by reversing time and flipping `u` and `τ`. Hence
  `N^-` is an isolating block with exit set `L^- = {|u| = δ} ∪ {v̂ = δ', τ ≥ 0}` and invariant set
  `TC^-` (`TCModelMinus.isBlock`, `TCModelMinus.isIndexPair`).
* `lem_TC_ii_minus_of`: for every such flow on the doubled chart `XS`, `h(TC^-) = S²`. The index is
  transported from `indexS2` by the homeomorphism `S̃ : XS → XS`.
* `lem_TC_iii_minus_of`: on the interval chart `XI` the index is trivial, for the flow and for the
  reversed flow.
* `modelSm`, `modelIm`: the cut-off flows of `eq:flowTm` on `XS` and `XI`, which are instances.
-/

open Set Filter Topology Metric unitInterval
open ConleyCheck.Conley ConleyCheck.ODE

namespace ConleyCheck.Gubser

theorem Gu_eq (c u v τ : ℝ) : Gu c u v τ = Fu c (-u) v (-τ) := by unfold Gu Fu; ring

theorem Gv_eq (u v τ : ℝ) : Gv u v τ = -Fv (-u) v (-τ) := by unfold Gv Fv; ring

theorem hasDerivAt_comp_neg' {f : ℝ → ℝ} {f' t : ℝ} (hf : HasDerivAt f f' (-t)) :
    HasDerivAt (fun s => f (-s)) (-f') t := by
  have := hf.scomp t (hasDerivAt_neg t)
  simpa [Function.comp_def] using this

theorem Flow.reverse_reverse' {X : Type*} [TopologicalSpace X] (ϕ : Flow ℝ X) :
    ϕ.reverse.reverse = ϕ :=
  Flow.ext fun t x => by simp [Flow.reverse_apply]

/-- A flow on `X` with continuous coordinates `u`, `v̂ ≥ 0`, `τ ∈ [-1, 1]`, along which
`(u, v̂, τ)` solves `eq:flowTm` multiplied by a cut-off `b`, with `b = 1` where `|u|, v̂ < 1/c`. -/
structure TCModelMinus (c : ℝ) (X : Type*) [TopologicalSpace X] where
  ϕ : Flow ℝ X
  u : X → ℝ
  v : X → ℝ
  τ : X → ℝ
  b : X → ℝ
  cu : Continuous u
  cv : Continuous v
  cτ : Continuous τ
  cb : Continuous b
  v_nonneg : ∀ p, 0 ≤ v p
  τ_ge : ∀ p, -1 ≤ τ p
  τ_le : ∀ p, τ p ≤ 1
  b_eq : ∀ p, |u p| < 1 / c → v p < 1 / c → b p = 1
  du : ∀ p t, HasDerivAt (fun s => u (ϕ s p))
    (b (ϕ t p) * Gu c (u (ϕ t p)) (v (ϕ t p)) (τ (ϕ t p))) t
  dv : ∀ p t, HasDerivAt (fun s => v (ϕ s p))
    (b (ϕ t p) * Gv (u (ϕ t p)) (v (ϕ t p)) (τ (ϕ t p))) t
  dτ : ∀ p t, HasDerivAt (fun s => τ (ϕ s p)) (b (ϕ t p) * (v (ϕ t p) * (1 - τ (ϕ t p) ^ 2))) t
  compact : ∀ a a', IsCompact {p | |u p| ≤ a ∧ v p ≤ a'}

namespace TCModelMinus

variable {c δ δ' : ℝ} {X : Type*} [TopologicalSpace X] (M : TCModelMinus c X)

theorem toPlus_du (p : X) (t : ℝ) : HasDerivAt (fun s => -M.u (M.ϕ.reverse s p))
    (M.b (M.ϕ.reverse t p) * Fu c (-M.u (M.ϕ.reverse t p)) (M.v (M.ϕ.reverse t p))
      (-M.τ (M.ϕ.reverse t p))) t := by
  refine (hasDerivAt_comp_neg' (M.du p (-t))).neg.congr_deriv ?_
  simp only [Flow.reverse_apply, Gu_eq]; ring

theorem toPlus_dv (p : X) (t : ℝ) : HasDerivAt (fun s => M.v (M.ϕ.reverse s p))
    (M.b (M.ϕ.reverse t p) * Fv (-M.u (M.ϕ.reverse t p)) (M.v (M.ϕ.reverse t p))
      (-M.τ (M.ϕ.reverse t p))) t := by
  refine (hasDerivAt_comp_neg' (M.dv p (-t))).congr_deriv ?_
  simp only [Flow.reverse_apply, Gv_eq]; ring

/-- `S̃` in coordinates: reversing time and flipping `u` and `τ` gives a chart-`T = +∞` model. -/
def toPlus : TCModel c X where
  ϕ := M.ϕ.reverse
  u p := -M.u p
  v := M.v
  τ p := -M.τ p
  b := M.b
  cu := M.cu.neg
  cv := M.cv
  cτ := M.cτ.neg
  cb := M.cb
  v_nonneg := M.v_nonneg
  τ_ge p := by linarith [M.τ_le p]
  τ_le p := by linarith [M.τ_ge p]
  b_pos p hu hv := by rw [M.b_eq p (by rwa [abs_neg] at hu) hv]; exact one_pos
  du p t _ _ := M.toPlus_du p t
  dv p t _ _ := M.toPlus_dv p t
  dτ p t _ _ := by
    refine (hasDerivAt_comp_neg' (M.dτ p (-t))).neg.congr_deriv ?_
    simp only [Flow.reverse_apply]; ring
  tc_inv := tc_inv_of_global (ϕ := M.ϕ.reverse) (u := fun p => -M.u p) (v := M.v)
    (τ := fun p => -M.τ p) (b := M.b) M.cu.neg M.cv M.cτ.neg M.cb M.toPlus_du M.toPlus_dv
  compact a a' := by simp only [abs_neg]; exact M.compact a a'

/-- The block `N^- = {|u| ≤ δ, v̂ ≤ δ'}`. -/
def N (δ δ' : ℝ) : Set X := {p | |M.u p| ≤ δ ∧ M.v p ≤ δ'}

/-- Its exit set `L^- = {|u| = δ} ∪ {v̂ = δ', τ ≥ 0}`. -/
def L (δ δ' : ℝ) : Set X :=
  {p | |M.u p| ≤ δ ∧ M.v p ≤ δ' ∧ (|M.u p| = δ ∨ (M.v p = δ' ∧ 0 ≤ M.τ p))}

/-- The exit set `{v̂ = δ', τ ≤ 0}` of `N^-` for the reversed flow. -/
def R (δ δ' : ℝ) : Set X := {p | |M.u p| ≤ δ ∧ M.v p = δ' ∧ M.τ p ≤ 0}

/-- The `T`-axis curve `TC^- = {u = v̂ = 0}`. -/
def TC : Set X := {p | M.u p = 0 ∧ M.v p = 0}

theorem toPlus_N : M.toPlus.N δ δ' = M.N δ δ' := by
  ext p; simp [TCModel.N, N, toPlus]

theorem toPlus_E : M.toPlus.E δ δ' = M.L δ δ' := by
  ext p; simp [TCModel.E, L, toPlus]

theorem toPlus_L : M.toPlus.L δ δ' = M.R δ δ' := by
  ext p; simp [TCModel.L, R, toPlus]

theorem toPlus_TC : M.toPlus.TC = M.TC := by
  ext p; simp [TCModel.TC, TC, toPlus]

theorem toPlus_reverse : M.toPlus.ϕ.reverse = M.ϕ := Flow.reverse_reverse' M.ϕ

/-- `N^-` is an isolating block with exit set `L^-`. -/
theorem isBlock (H : TCHyp c δ δ') : IsBlock M.ϕ (M.N δ δ') (M.L δ δ') := by
  have := M.toPlus.isBlock_N_reverse H
  rwa [toPlus_N, toPlus_E, toPlus_reverse] at this

/-- `Inv(N^-) = TC^-`. -/
theorem Inv_N (H : TCHyp c δ δ') : Inv M.ϕ (M.N δ δ') = M.TC := by
  have := M.toPlus.Inv_N_reverse H
  rwa [toPlus_N, toPlus_TC, toPlus_reverse] at this

/-- `(N^-, L^-)` is an index pair for `TC^-`. -/
theorem isIndexPair [T2Space X] (H : TCHyp c δ δ') : IsIndexPair M.ϕ M.TC (M.N δ δ') (M.L δ δ') := by
  have := M.toPlus.isIndexPair_E H
  rwa [toPlus_N, toPlus_E, toPlus_TC, toPlus_reverse] at this

/-- `(N^-, R)` is an index pair for `TC^-` and the reversed flow. -/
theorem isIndexPair_reverse [T2Space X] (H : TCHyp c δ δ') :
    IsIndexPair M.ϕ.reverse M.TC (M.N δ δ') (M.R δ δ') := by
  have := M.toPlus.isIndexPair_L H
  rwa [toPlus_N, toPlus_L, toPlus_TC] at this

end TCModelMinus

/-! ## The reversor on the model spaces -/

/-- `S̃` on `XS`: `(u, v, x, y) ↦ (-u, v, -x, y)`. -/
def sS (q : XS) : XS :=
  ⟨(-uS q, vS q, -xS q, yS q), q.2.1, by show (-xS q) ^ 2 + yS q ^ 2 = 1; rw [neg_sq]; exact q.2.2⟩

/-- `S̃` as a homeomorphism of `XS`. -/
noncomputable def SS : XS ≃ₜ XS where
  toFun := sS
  invFun := sS
  left_inv q := XS_ext (neg_neg _) rfl (neg_neg _) rfl
  right_inv q := XS_ext (neg_neg _) rfl (neg_neg _) rfl
  continuous_toFun := Continuous.subtype_mk (by unfold uS vS xS yS; fun_prop) _
  continuous_invFun := Continuous.subtype_mk (by unfold uS vS xS yS; fun_prop) _

/-- `S̃` on `XI`: `(u, v, τ) ↦ (-u, v, -τ)`. -/
def sI (q : XI) : XI :=
  ⟨(-uI q, vI q, -τI q), q.2.1, by linarith [q.2.2.2], by linarith [q.2.2.1]⟩

/-- `S̃` as a homeomorphism of `XI`. -/
noncomputable def SI : XI ≃ₜ XI where
  toFun := sI
  invFun := sI
  left_inv q := XI_ext (neg_neg _) rfl (neg_neg _)
  right_inv q := XI_ext (neg_neg _) rfl (neg_neg _)
  continuous_toFun := Continuous.subtype_mk (by unfold uI vI τI; fun_prop) _
  continuous_invFun := Continuous.subtype_mk (by unfold uI vI τI; fun_prop) _

/-! ## Indices in the chart `T = -∞` -/

section Index

variable {c δ δ' : ℝ}

/-- Part (ii) of `lem:TC`, for every flow on the doubled chart `XS` whose coordinates satisfy
`eq:flowTm` (with `τ = x`) near `N^-`: `h(TC^-) = S²`. -/
theorem lem_TC_ii_minus_of (M : TCModelMinus c XS) (hu : ∀ q, M.u q = uS q)
    (hv : ∀ q, M.v q = vS q) (hτ : ∀ q, M.τ q = xS q) (H : TCHyp c δ δ') :
    HasIndex M.ϕ M.TC (Sphere 2) (Sphere.pt 2) := by
  obtain ⟨e⟩ := indexS2 H.hδ (H.hδ.trans H.h1).le
  refine ⟨SS ⁻¹' NS δ δ', SS ⁻¹' ES δ δ', ?_,
    ⟨(IndexSpace.preimageEquiv SS (NS δ δ') (ES δ δ')).trans e⟩⟩
  have hN : SS ⁻¹' NS δ δ' = M.N δ δ' := by
    ext q
    show |-uS q| ≤ δ ∧ vS q ≤ δ' ↔ _
    simp only [TCModelMinus.N, mem_ofPred_eq, hu, hv, abs_neg]
  have hL : SS ⁻¹' ES δ δ' = M.L δ δ' := by
    ext q
    show |-uS q| ≤ δ ∧ vS q ≤ δ' ∧ (|-uS q| = δ ∨ (vS q = δ' ∧ -xS q ≤ 0)) ↔ _
    simp only [TCModelMinus.L, mem_ofPred_eq, hu, hv, hτ, abs_neg, neg_nonpos]
  rw [hN, hL]; exact M.isIndexPair H

/-- The reversed flow at `TC^-` has `h(TC^-) = S¹`. -/
theorem lem_TC_i_minus_of (M : TCModelMinus c XS) (hu : ∀ q, M.u q = uS q)
    (hv : ∀ q, M.v q = vS q) (hτ : ∀ q, M.τ q = xS q) (H : TCHyp c δ δ') :
    HasIndex M.ϕ.reverse M.TC (Sphere 1) (Sphere.pt 1) := by
  obtain ⟨e⟩ := indexS1 H.hδ.le (H.hδ.trans H.h1).le
  refine ⟨SS ⁻¹' NS δ δ', SS ⁻¹' LS δ δ', ?_,
    ⟨(IndexSpace.preimageEquiv SS (NS δ δ') (LS δ δ')).trans e⟩⟩
  have hN : SS ⁻¹' NS δ δ' = M.N δ δ' := by
    ext q
    show |-uS q| ≤ δ ∧ vS q ≤ δ' ↔ _
    simp only [TCModelMinus.N, mem_ofPred_eq, hu, hv, abs_neg]
  have hR : SS ⁻¹' LS δ δ' = M.R δ δ' := by
    ext q
    show |-uS q| ≤ δ ∧ vS q = δ' ∧ 0 ≤ -xS q ↔ _
    simp only [TCModelMinus.R, mem_ofPred_eq, hu, hv, hτ, abs_neg, neg_nonneg]
  rw [hN, hR]; exact M.isIndexPair_reverse H

/-- Part (iii) of `lem:TC` in the chart `T = -∞`, for every flow on `XI` whose coordinates satisfy
`eq:flowTm` near `N^-`: `TC^-` has trivial index for the flow and for the reversed flow. -/
theorem lem_TC_iii_minus_of (M : TCModelMinus c XI) (hu : ∀ q, M.u q = uI q)
    (hv : ∀ q, M.v q = vI q) (hτ : ∀ q, M.τ q = τI q) (H : TCHyp c δ δ') :
    IndexTrivial M.ϕ M.TC ∧ IndexTrivial M.ϕ.reverse M.TC := by
  have hδ' : 0 ≤ δ' := (H.hδ.trans H.h1).le
  have hN : SI ⁻¹' NI δ δ' = M.N δ δ' := by
    ext q
    show |-uI q| ≤ δ ∧ vI q ≤ δ' ↔ _
    simp only [TCModelMinus.N, mem_ofPred_eq, hu, hv, abs_neg]
  have hL : SI ⁻¹' EI δ δ' = M.L δ δ' := by
    ext q
    show |-uI q| ≤ δ ∧ vI q ≤ δ' ∧ (|-uI q| = δ ∨ (vI q = δ' ∧ -τI q ≤ 0)) ↔ _
    simp only [TCModelMinus.L, mem_ofPred_eq, hu, hv, hτ, abs_neg, neg_nonpos]
  have hR : SI ⁻¹' LI δ δ' = M.R δ δ' := by
    ext q
    show |-uI q| ≤ δ ∧ vI q = δ' ∧ 0 ≤ -τI q ↔ _
    simp only [TCModelMinus.R, mem_ofPred_eq, hu, hv, hτ, abs_neg, neg_nonneg]
  refine ⟨⟨SI ⁻¹' NI δ δ', SI ⁻¹' EI δ δ', ?_,
      (contractible_EI hδ').of_equiv (IndexSpace.preimageEquiv SI (NI δ δ') (EI δ δ'))⟩,
    ⟨SI ⁻¹' NI δ δ', SI ⁻¹' LI δ δ', ?_,
      (contractible_LI H.hδ.le hδ').of_equiv (IndexSpace.preimageEquiv SI (NI δ δ') (LI δ δ'))⟩⟩
  · rw [hN, hL]; exact M.isIndexPair H
  · rw [hN, hR]; exact M.isIndexPair_reverse H

end Index

/-! ## The cut-off flows of `eq:flowTm` -/

section Flows

/-- The field `(Gu, Gv, v y², -v x y)` on `ℝ⁴`. -/
noncomputable def fieldSm (c : ℝ) (p : E4) : E4 :=
  (Gu c p.1 p.2.1 p.2.2.1, Gv p.1 p.2.1 p.2.2.1, p.2.1 * p.2.2.2 ^ 2, -(p.2.1 * p.2.2.1 * p.2.2.2))

theorem contDiff_fieldSm (c : ℝ) : ContDiff ℝ 1 (fieldSm c) := by
  unfold fieldSm Gu Gv; fun_prop

/-- The global flow of the cut-off field `(Gu, Gv, v y², -v x y)` on `ℝ⁴`. -/
noncomputable def flowSm (c : ℝ) : Flow ℝ E4 :=
  bumpFlow (contDiff_fieldSm c) (radTC c) (radTC_pos c)

theorem hasDerivAt_flowSm (c : ℝ) (p : E4) (t : ℝ) :
    HasDerivAt (fun s => flowSm c s p) (bS c (flowSm c t p) • fieldSm c (flowSm c t p)) t :=
  hasDerivAt_bumpFlow _ p t

theorem isInvariant_XS_m (c : ℝ) : IsInvariant (flowSm c) XS := by
  intro t p hp
  have hγ := hasDerivAt_flowSm c p
  have hcγ : Continuous fun s => flowSm c s p := (flowSm c).continuous continuous_id continuous_const
  refine ⟨?_, ?_⟩
  · have hV : ∀ s, HasDerivAt (fun r => (flowSm c r p).2.1)
        ((bS c (flowSm c s p) * ((flowSm c s p).2.2.1 / 3 * ((flowSm c s p).1 + 2 * (flowSm c s p).2.1)))
          * (flowSm c s p).2.1) s := by
      intro s
      convert hasDerivAt_fst' (hasDerivAt_snd' (hγ s)) using 1
      simp only [Prod.smul_fst, Prod.smul_snd, fieldSm, Gv, smul_eq_mul]; ring
    have h0 : 0 ≤ (flowSm c 0 p).2.1 := by rw [Flow.map_zero_apply]; exact hp.1
    exact nonneg_of_linear_all hV (((continuous_bS c).comp hcγ).mul (by fun_prop)) h0 t
  · have hW : ∀ s, HasDerivAt (fun r => (flowSm c r p).2.2.1 ^ 2 + (flowSm c r p).2.2.2 ^ 2) 0 s := by
      intro s
      have h1 := (hasDerivAt_fst' (hasDerivAt_snd' (hasDerivAt_snd' (hγ s)))).pow 2
      have h2 := (hasDerivAt_snd' (hasDerivAt_snd' (hasDerivAt_snd' (hγ s)))).pow 2
      convert h1.add h2 using 1
      simp only [Prod.smul_fst, Prod.smul_snd, fieldSm, smul_eq_mul, Nat.cast_ofNat]; ring
    have := is_const_of_deriv_eq_zero (fun s => (hW s).differentiableAt) (fun s => (hW s).deriv) t 0
    simp only [Flow.map_zero_apply] at this
    rw [this]; exact hp.2

/-- The cut-off flow of `eq:flowTm` on the doubled chart `XS`. -/
noncomputable def ϕSm (c : ℝ) : Flow ℝ XS := (flowSm c).restrict (isInvariant_XS_m c)

/-- The doubled chart `T = -∞` as a `TCModelMinus`. -/
noncomputable def modelSm (c : ℝ) : TCModelMinus c XS where
  ϕ := ϕSm c
  u q := (q : E4).1
  v q := (q : E4).2.1
  τ q := (q : E4).2.2.1
  b q := bS c q
  cu := by fun_prop
  cv := by fun_prop
  cτ := by fun_prop
  cb := (continuous_bS c).comp continuous_subtype_val
  v_nonneg q := q.2.1
  τ_ge q := (abs_le.1 (abs_le_one_of_sq_add q.2.2)).1
  τ_le q := (abs_le.1 (abs_le_one_of_sq_add q.2.2)).2
  b_eq q hu hv := bS_eq_one q hu hv
  du q t := hasDerivAt_fst' (hasDerivAt_flowSm c q t)
  dv q t := hasDerivAt_fst' (hasDerivAt_snd' (hasDerivAt_flowSm c q t))
  dτ q t := by
    have hq := (ϕSm c t q).2.2
    refine (hasDerivAt_fst' (hasDerivAt_snd' (hasDerivAt_snd' (hasDerivAt_flowSm c q t)))).congr_deriv ?_
    change bS c (flowSm c t q) * ((flowSm c t q).2.1 * (flowSm c t q).2.2.2 ^ 2) =
      bS c (flowSm c t q) * ((flowSm c t q).2.1 * (1 - (flowSm c t q).2.2.1 ^ 2))
    change (flowSm c t q).2.2.1 ^ 2 + (flowSm c t q).2.2.2 ^ 2 = 1 at hq
    rw [show 1 - (flowSm c t q).2.2.1 ^ 2 = (flowSm c t q).2.2.2 ^ 2 by linarith]
  compact a a' := (modelS c).compact a a'

/-- The field `(Gu, Gv, v (1 - τ²))` on `ℝ³`. -/
noncomputable def fieldIm (c : ℝ) (p : E3) : E3 :=
  (Gu c p.1 p.2.1 p.2.2, Gv p.1 p.2.1 p.2.2, p.2.1 * (1 - p.2.2 ^ 2))

theorem contDiff_fieldIm (c : ℝ) : ContDiff ℝ 1 (fieldIm c) := by
  unfold fieldIm Gu Gv; fun_prop

/-- The global flow of the cut-off field `(Gu, Gv, v (1 - τ²))` on `ℝ³`. -/
noncomputable def flowIm (c : ℝ) : Flow ℝ E3 :=
  bumpFlow (contDiff_fieldIm c) (radTC c) (radTC_pos c)

theorem hasDerivAt_flowIm (c : ℝ) (p : E3) (t : ℝ) :
    HasDerivAt (fun s => flowIm c s p) (bI c (flowIm c t p) • fieldIm c (flowIm c t p)) t :=
  hasDerivAt_bumpFlow _ p t

theorem isInvariant_XI_m (c : ℝ) : IsInvariant (flowIm c) XI := by
  intro t p hp
  have hγ := hasDerivAt_flowIm c p
  have hcγ : Continuous fun s => flowIm c s p := (flowIm c).continuous continuous_id continuous_const
  have hb := (continuous_bI c).comp hcγ
  refine ⟨?_, ?_, ?_⟩
  · have hV : ∀ s, HasDerivAt (fun r => (flowIm c r p).2.1)
        ((bI c (flowIm c s p) * ((flowIm c s p).2.2 / 3 * ((flowIm c s p).1 + 2 * (flowIm c s p).2.1)))
          * (flowIm c s p).2.1) s := by
      intro s
      convert hasDerivAt_fst' (hasDerivAt_snd' (hγ s)) using 1
      simp only [Prod.smul_fst, Prod.smul_snd, fieldIm, Gv, smul_eq_mul]; ring
    have h0 : 0 ≤ (flowIm c 0 p).2.1 := by rw [Flow.map_zero_apply]; exact hp.1
    exact nonneg_of_linear_all hV (hb.mul (by fun_prop)) h0 t
  · have hV : ∀ s, HasDerivAt (fun r => 1 + (flowIm c r p).2.2)
        ((bI c (flowIm c s p) * ((flowIm c s p).2.1 * (1 - (flowIm c s p).2.2)))
          * (1 + (flowIm c s p).2.2)) s := by
      intro s
      refine ((hasDerivAt_snd' (hasDerivAt_snd' (hγ s))).const_add 1).congr_deriv ?_
      simp only [Prod.smul_snd, fieldIm, smul_eq_mul]; ring
    have h0 : 0 ≤ 1 + (flowIm c 0 p).2.2 := by rw [Flow.map_zero_apply]; linarith [hp.2.1]
    have := nonneg_of_linear_all hV (hb.mul (by fun_prop)) h0 t
    linarith
  · have hV : ∀ s, HasDerivAt (fun r => 1 - (flowIm c r p).2.2)
        ((-(bI c (flowIm c s p) * ((flowIm c s p).2.1 * (1 + (flowIm c s p).2.2))))
          * (1 - (flowIm c s p).2.2)) s := by
      intro s
      refine ((hasDerivAt_snd' (hasDerivAt_snd' (hγ s))).const_sub 1).congr_deriv ?_
      simp only [Prod.smul_snd, fieldIm, smul_eq_mul]; ring
    have h0 : 0 ≤ 1 - (flowIm c 0 p).2.2 := by rw [Flow.map_zero_apply]; linarith [hp.2.2]
    have := nonneg_of_linear_all hV (hb.mul (by fun_prop)).neg h0 t
    linarith

/-- The cut-off flow of `eq:flowTm` on the interval chart `XI`. -/
noncomputable def ϕIm (c : ℝ) : Flow ℝ XI := (flowIm c).restrict (isInvariant_XI_m c)

/-- The interval chart `T = -∞` as a `TCModelMinus`. -/
noncomputable def modelIm (c : ℝ) : TCModelMinus c XI where
  ϕ := ϕIm c
  u q := (q : E3).1
  v q := (q : E3).2.1
  τ q := (q : E3).2.2
  b q := bI c q
  cu := by fun_prop
  cv := by fun_prop
  cτ := by fun_prop
  cb := (continuous_bI c).comp continuous_subtype_val
  v_nonneg q := q.2.1
  τ_ge q := q.2.2.1
  τ_le q := q.2.2.2
  b_eq q hu hv := bI_eq_one q hu hv
  du q t := hasDerivAt_fst' (hasDerivAt_flowIm c q t)
  dv q t := hasDerivAt_fst' (hasDerivAt_snd' (hasDerivAt_flowIm c q t))
  dτ q t := hasDerivAt_snd' (hasDerivAt_snd' (hasDerivAt_flowIm c q t))
  compact a a' := (modelI c).compact a a'

end Flows

/-! ## `lem:TC`(ii), (iii) in the chart `T = -∞` for the cut-off flows -/

variable {c δ δ' : ℝ}

/-- Part (ii) of `lem:TC`: `h(TC^-) = S²` for the doubled flow in the chart `T = -∞`. -/
theorem lem_TC_ii_minus (H : TCHyp c δ δ') :
    HasIndex (ϕSm c) (modelSm c).TC (Sphere 2) (Sphere.pt 2) :=
  lem_TC_ii_minus_of (modelSm c) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) H

/-- Part (iii) of `lem:TC` in the chart `T = -∞`: trivial index for the flow and its reverse. -/
theorem lem_TC_iii_minus (H : TCHyp c δ δ') :
    IndexTrivial (ϕIm c) (modelIm c).TC ∧ IndexTrivial (ϕIm c).reverse (modelIm c).TC :=
  lem_TC_iii_minus_of (modelIm c) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) H

end ConleyCheck.Gubser
