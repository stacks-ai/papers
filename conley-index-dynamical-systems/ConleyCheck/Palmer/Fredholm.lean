import ConleyCheck.Palmer.HalfLine
import ConleyCheck.Algebra.ExactSeq

/-!
# Palmer's theorem

Let `A : ℝ → E →L[ℝ] E` (`E` finite-dimensional) be continuous and bounded, with hyperbolic limits
`A₊` at `+∞` and `A₋` at `-∞`. The operator `L y = y' - A(t) y : C¹_b → C⁰_b` satisfies:
* `kerEquiv`: `ker L ≅ E^u ∩ E^s`;
* `mem_range_iff`: `h ∈ range L ↔ S₊ h - S₋ h ∈ E^u + E^s`, so the range is closed;
* `cokerEquiv`: `coker L ≅ E/(E^u + E^s)`;
* `isFredholm`, `index_eq`: `L` is Fredholm of index `μ₋ - μ₊` (Proposition `prop:palmer`(ii));
* `transversal_iff_surjective`, `transversal_iff_ker_eq_bot` (Proposition `prop:palmer`(iii)).

`E^u`, `E^s` are the initial values at `t = 0` of solutions of `y' = A(t) y` bounded on
`(-∞, 0]`, `[0, ∞)`, and the connection is *transversal* when `E^u + E^s = E` (`Transversal`).
`C¹_b` is realised as the closed subspace of pairs `(y, y')` in `C⁰_b × C⁰_b`, with the norm
`max ‖y‖ ‖y'‖` of the paper. Hyperbolicity of `A±` is an exponential dichotomy (`Dichotomy`,
eq. `eq:dichotomy`), and `μ±` is the rank of the unstable projection.
-/

namespace ConleyCheck.Palmer

open NormedSpace Set Filter Topology BoundedContinuousFunction Module Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ### Time reversal -/

/-- `Ã(t) = -A(-t)`: `y` solves `y' = A(t) y` iff `y(-t)` solves `ỹ' = Ã(t) ỹ`. -/
def revA (A : ℝ → E →L[ℝ] E) : ℝ → E →L[ℝ] E := fun t => -A (-t)

variable {A : ℝ → E →L[ℝ] E} {M : ℝ}

omit [CompleteSpace E] in
theorem revA_revA : revA (revA A) = A := by
  funext t; simp [revA]

omit [CompleteSpace E] in
theorem IsLinSol.reflect {h y : ℝ → E} (hy : IsLinSol A h y) :
    IsLinSol (revA A) (fun t => -h (-t)) (fun t => y (-t)) := fun t => by
  refine ((hy (-t)).scomp t (hasDerivAt_neg t)).congr_deriv ?_
  simp only [revA, neg_smul, one_smul, _root_.neg_apply, neg_add]

omit [CompleteSpace E] in
theorem IsLinSol.reflect_zero {y : ℝ → E} (hy : IsLinSol A 0 y) :
    IsLinSol (revA A) 0 (fun t => y (-t)) := by
  convert hy.reflect using 1
  funext t; simp

omit [CompleteSpace E] in
theorem continuous_revA (hA : Continuous A) : Continuous (revA A) :=
  (hA.comp continuous_neg).neg

omit [CompleteSpace E] in
theorem norm_revA_le (hM : ∀ t, ‖A t‖ ≤ M) (t : ℝ) : ‖revA A t‖ ≤ M := by
  simpa [revA] using hM (-t)

omit [CompleteSpace E] in
theorem tendsto_revA {Am : E →L[ℝ] E} (hlim : Tendsto A atBot (𝓝 Am)) :
    Tendsto (revA A) atTop (𝓝 (-Am)) :=
  (hlim.comp tendsto_neg_atTop_atBot).neg

omit [CompleteSpace E] in
theorem unstableSub_eq : unstableSub A = stableSub (revA A) := by
  ext ξ
  constructor
  · rintro ⟨y, hy, rfl, C, hC⟩
    exact ⟨fun t => y (-t), hy.reflect_zero, by simp, C, fun t ht => hC (-t) (by
      simp only [mem_Ici, mem_Iic] at ht ⊢; linarith)⟩
  · rintro ⟨y, hy, rfl, C, hC⟩
    have := hy.reflect_zero
    rw [revA_revA] at this
    exact ⟨fun t => y (-t), this, by simp, C, fun t ht => hC (-t) (by
      simp only [mem_Ici, mem_Iic] at ht ⊢; linarith)⟩

/-- `h ↦ -h(-t)`. -/
noncomputable def revBCF : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) :=
  mkBCF (fun h t => -h (-t)) (fun h => (h.continuous.comp continuous_neg).neg)
    (fun _ _ _ => by simp; abel) (fun _ _ _ => by simp) 1
    (fun h t => by simpa using h.norm_coe_le_norm (-t))

/-! ### The space `C¹_b` and the operator `L` -/

variable (E) in
/-- `C¹_b(ℝ, E)`: pairs `(y, z)` of bounded continuous functions with `y' = z`. -/
def C1b : Submodule ℝ ((ℝ →ᵇ E) × (ℝ →ᵇ E)) where
  carrier := {p | ∀ t, HasDerivAt p.1 (p.2 t) t}
  add_mem' hp hq t := by simpa using (hp t).add (hq t)
  zero_mem' t := by simp
  smul_mem' c p hp t := by
    show HasDerivAt (fun x => c • p.1 x) (c • p.2 t) t
    exact (hp t).const_smul c

omit [CompleteSpace E] in
theorem mem_C1b {p : (ℝ →ᵇ E) × (ℝ →ᵇ E)} : p ∈ C1b E ↔ ∀ t, HasDerivAt p.1 (p.2 t) t := Iff.rfl

/-- `g ↦ ∫₀ᵗ g`. -/
noncomputable def intCLM (t : ℝ) : (ℝ →ᵇ E) →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun g => ∫ s in (0 : ℝ)..t, g s
      map_add' := fun g g' => by
        simp only [coe_add, Pi.add_apply]
        exact intervalIntegral.integral_add (g.continuous.intervalIntegrable _ _)
          (g'.continuous.intervalIntegrable _ _)
      map_smul' := fun c g => by
        simp only [coe_smul, RingHom.id_apply]
        exact intervalIntegral.integral_smul c _ }
    |t| fun g => by
      have := intervalIntegral.norm_integral_le_abs_of_norm_le (μ := MeasureTheory.volume)
        (a := 0) (b := t) (f := ⇑g)
        (g := fun _ => ‖g‖) (Eventually.of_forall fun s => g.norm_coe_le_norm s)
        intervalIntegrable_const
      simpa [abs_mul] using this

omit [CompleteSpace E] in
theorem intCLM_apply (t : ℝ) (g : ℝ →ᵇ E) : intCLM t g = ∫ s in (0 : ℝ)..t, g s := rfl

theorem mem_C1b_iff_integral {p : (ℝ →ᵇ E) × (ℝ →ᵇ E)} :
    p ∈ C1b E ↔ ∀ t, p.1 t - p.1 0 = intCLM t p.2 := by
  constructor
  · intro hp t
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hp s)
      (p.2.continuous.intervalIntegrable _ _)).symm
  · intro hp t
    have h1 := (intervalIntegral.integral_hasDerivAt_right (p.2.continuous.intervalIntegrable 0 t)
      (p.2.continuous.stronglyMeasurableAtFilter _ _) p.2.continuous.continuousAt).const_add
      (p.1 0)
    have h2 : (fun t => p.1 0 + ∫ s in (0 : ℝ)..t, p.2 s) = ⇑p.1 :=
      funext fun t => by rw [← intCLM_apply, ← hp t]; abel
    rwa [h2] at h1

theorem isClosed_C1b : IsClosed (C1b E : Set ((ℝ →ᵇ E) × (ℝ →ᵇ E))) := by
  have : (C1b E : Set ((ℝ →ᵇ E) × (ℝ →ᵇ E))) =
      ⋂ t, {p | p.1 t - p.1 0 = intCLM t p.2} := by
    ext p
    simp only [SetLike.mem_coe, mem_C1b_iff_integral, mem_iInter, mem_ofPred_eq]
  rw [this]
  exact isClosed_iInter fun t => isClosed_eq
    (((continuous_eval_const t).comp continuous_fst).sub
      ((continuous_eval_const 0).comp continuous_fst))
    ((intCLM t).continuous.comp continuous_snd)

instance : CompleteSpace (C1b E) := isClosed_C1b.completeSpace_coe

/-- `y ↦ A(t) y(t)`. -/
noncomputable def opA (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M) : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) :=
  mkBCF (fun y t => A t (y t)) (fun y => hA.clm_apply y.continuous) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp) M (fun y t => ((A t).le_opNorm _).trans
      (mul_le_mul (hM t) (y.norm_coe_le_norm t) (norm_nonneg _) ((norm_nonneg _).trans (hM t))))

/-- Palmer's operator `L (y, y') = y' - A(t) y : C¹_b → C⁰_b`. -/
noncomputable def palmerL (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M) :
    C1b E →L[ℝ] (ℝ →ᵇ E) :=
  (ContinuousLinearMap.snd ℝ _ _ - opA hA hM ∘L ContinuousLinearMap.fst ℝ _ _) ∘L
    (C1b E).subtypeL

variable (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M)

omit [CompleteSpace E] in
theorem palmerL_apply (p : C1b E) (t : ℝ) :
    palmerL hA hM p t = (p : (ℝ →ᵇ E) × (ℝ →ᵇ E)).2 t - A t ((p : (ℝ →ᵇ E) × (ℝ →ᵇ E)).1 t) :=
  rfl

omit [CompleteSpace E] in
theorem isLinSol_of_C1b (p : C1b E) :
    IsLinSol A (palmerL hA hM p) (p : (ℝ →ᵇ E) × (ℝ →ᵇ E)).1 := fun t =>
  (p.2 t).congr_deriv (by rw [palmerL_apply]; abel)

/-- A bounded solution of `y' = A(t) y + h(t)` as an element of `C¹_b`. -/
noncomputable def mkC1b (y h : ℝ →ᵇ E) (hy : IsLinSol A h y) : C1b E :=
  ⟨(y, opA hA hM y + h), fun t => by simpa [opA] using hy t⟩

omit [CompleteSpace E] in
theorem palmerL_mkC1b (y h : ℝ →ᵇ E) (hy : IsLinSol A h y) :
    palmerL hA hM (mkC1b hA hM y h hy) = h := by
  ext t
  simp [palmerL_apply, mkC1b, opA]

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem exists_bdd_of_halves {y : ℝ → E} {C D : ℝ} (hC : ∀ t, 0 ≤ t → ‖y t‖ ≤ C)
    (hD : ∀ t, t ≤ 0 → ‖y t‖ ≤ D) : ∀ t, ‖y t‖ ≤ max C D := fun t => by
  rcases le_total 0 t with ht | ht
  · exact (hC t ht).trans (le_max_left _ _)
  · exact (hD t ht).trans (le_max_right _ _)

omit [CompleteSpace E] in
/-- A solution bounded on both half-lines lies in the range of `L`. -/
theorem mem_range_of_bdd {h : ℝ →ᵇ E} {y : ℝ → E} (hy : IsLinSol A h y) {C D : ℝ}
    (hC : ∀ t, 0 ≤ t → ‖y t‖ ≤ C) (hD : ∀ t, t ≤ 0 → ‖y t‖ ≤ D) :
    ∃ p : C1b E, palmerL hA hM p = h ∧ (p : (ℝ →ᵇ E) × (ℝ →ᵇ E)).1 0 = y 0 := by
  let yb : ℝ →ᵇ E := ofNormedAddCommGroup y hy.continuous _ (exists_bdd_of_halves hC hD)
  exact ⟨mkC1b hA hM yb h hy, palmerL_mkC1b hA hM yb h hy, rfl⟩

/-! ### Kernel, range and cokernel -/

section Palmer

variable {Ap Am : E →L[ℝ] E} (Hp : HalfData A Ap) (Hm : HalfData (revA A) (-Am))

/-- `S₋ h = S̃₊ (-h(-·))`. -/
noncomputable def Sminus : (ℝ →ᵇ E) →L[ℝ] E := Hm.Splus ∘L revBCF

/-- A solution of `y' = A(t) y + h(t)` is bounded on `(-∞, 0]` iff `y(0) - S₋ h ∈ E^u`. -/
theorem bdd_neg_iff {h : ℝ →ᵇ E} {y : ℝ → E} (hy : IsLinSol A h y) :
    (∃ C, ∀ t, t ≤ 0 → ‖y t‖ ≤ C) ↔ y 0 - Sminus Hm h ∈ unstableSub A := by
  have h1 := Hm.bdd_iff_mem_stableSub (h := revBCF h) (y := fun t => y (-t)) hy.reflect
  rw [neg_zero] at h1
  rw [unstableSub_eq, Sminus, ContinuousLinearMap.comp_apply, ← h1]
  constructor
  · rintro ⟨C, hC⟩; exact ⟨C, fun t ht => hC (-t) (by linarith)⟩
  · rintro ⟨C, hC⟩; exact ⟨C, fun t ht => by simpa using hC (-t) (by linarith)⟩

/-- `C⁰_b → E/(E^u + E^s)`, `h ↦ [S₊ h - S₋ h]`; its kernel is the range of `L`. -/
noncomputable def cokerMap : (ℝ →ᵇ E) →ₗ[ℝ] E ⧸ (unstableSub A ⊔ stableSub A) :=
  (unstableSub A ⊔ stableSub A).mkQ ∘ₗ ((Hp.Splus - Sminus Hm : (ℝ →ᵇ E) →L[ℝ] E) :
    (ℝ →ᵇ E) →ₗ[ℝ] E)

include hA hM

/-- `ker L → E^u ∩ E^s`, `y ↦ y(0)`. -/
noncomputable def kerToInter :
    (palmerL hA hM).ker →ₗ[ℝ] ↥(unstableSub A ⊓ stableSub A) where
  toFun p := ⟨p.1.1.1 0, by
    have hy : IsLinSol A 0 p.1.1.1 := by
      have := isLinSol_of_C1b hA hM p.1
      have hk : palmerL hA hM p.1 = 0 := p.2
      rwa [hk] at this
    exact ⟨⟨_, hy, rfl, ‖p.1.1.1‖, fun t _ => p.1.1.1.norm_coe_le_norm t⟩,
      ⟨_, hy, rfl, ‖p.1.1.1‖, fun t _ => p.1.1.1.norm_coe_le_norm t⟩⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [CompleteSpace E] in
theorem kerToInter_bijective : Bijective (kerToInter hA hM) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro ⟨⟨⟨y, z⟩, hp⟩, hk⟩ h0
    have hy : IsLinSol A 0 y := by
      have := isLinSol_of_C1b hA hM ⟨(y, z), hp⟩
      have hk' : palmerL hA hM ⟨(y, z), hp⟩ = 0 := hk
      rwa [hk'] at this
    have hy0 : ⇑y = 0 := hy.eq_zero hM (t₀ := 0) (congrArg Subtype.val h0)
    have hz : z = 0 := by
      ext t
      have := hp t
      simp only [hy0] at this
      exact this.unique (hasDerivAt_const t 0)
    have hy' : y = 0 := DFunLike.coe_injective hy0
    subst hy' hz
    rfl
  · rintro ⟨ξ, ⟨yu, hyu, hyu0, Cu, hCu⟩, ⟨ys, hys, rfl, Cs, hCs⟩⟩
    have he : yu = ys := hyu.eq_of_eq hM hys (t₀ := 0) hyu0
    subst he
    have hy : IsLinSol A ⇑(0 : ℝ →ᵇ E) yu := hyu
    obtain ⟨p, hp, hp0⟩ := mem_range_of_bdd hA hM hy (fun t ht => hCs t ht) (fun t ht => hCu t ht)
    exact ⟨⟨p, hp⟩, Subtype.ext hp0⟩

/-- `ker L ≅ E^u ∩ E^s`. -/
noncomputable def kerEquiv :
    (palmerL hA hM).ker ≃ₗ[ℝ] ↥(unstableSub A ⊓ stableSub A) :=
  LinearEquiv.ofBijective _ (kerToInter_bijective hA hM)

include Hp Hm

theorem mem_range_iff (h : ℝ →ᵇ E) :
    h ∈ (palmerL hA hM).range ↔
      Hp.Splus h - Sminus Hm h ∈ unstableSub A ⊔ stableSub A := by
  constructor
  · rintro ⟨p, rfl⟩
    have hy := isLinSol_of_C1b hA hM p
    have hs := (Hp.bdd_iff_mem_stableSub hy).1
      ⟨_, fun t _ => (p : (ℝ →ᵇ E) × (ℝ →ᵇ E)).1.norm_coe_le_norm t⟩
    have hu := (bdd_neg_iff Hm hy).1
      ⟨_, fun t _ => (p : (ℝ →ᵇ E) × (ℝ →ᵇ E)).1.norm_coe_le_norm t⟩
    have := Submodule.sub_mem _ (Submodule.mem_sup_left hu) (Submodule.mem_sup_right hs)
    rwa [sub_sub_sub_cancel_left] at this
  · intro hmem
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem
    have hy := linSol_spec hA hM h.continuous h.norm_coe_le_norm 0 (Hp.Splus h - b)
    obtain ⟨C, hC⟩ := (Hp.bdd_iff_mem_stableSub hy.1).2 (by
      rw [hy.2, sub_sub_cancel_left]; exact Submodule.neg_mem _ hb)
    obtain ⟨D, hD⟩ := (bdd_neg_iff Hm hy.1).2 (by
      rw [hy.2]
      convert ha using 1
      rw [eq_sub_of_add_eq hab]; abel)
    obtain ⟨p, hp, -⟩ := mem_range_of_bdd hA hM hy.1 hC hD
    exact ⟨p, hp⟩

/-- The range of `L` is closed. -/
theorem isClosed_range_palmerL [FiniteDimensional ℝ E] :
    IsClosed ((palmerL hA hM).range : Set (ℝ →ᵇ E)) := by
  have : ((palmerL hA hM).range : Set (ℝ →ᵇ E)) =
      (Hp.Splus - Sminus Hm) ⁻¹' (unstableSub A ⊔ stableSub A : Submodule ℝ E) := by
    ext h
    simp only [SetLike.mem_coe, mem_range_iff hA hM Hp Hm, mem_preimage,
      _root_.sub_apply]
  rw [this]
  exact (Submodule.closed_of_finiteDimensional _).preimage (Hp.Splus - Sminus Hm).continuous

/-- The cutoff construction: every `ξ` is `S₊ h - S₋ h` modulo `E^u + E^s`. -/
theorem exists_cutoff (ξ : E) :
    ∃ h : ℝ →ᵇ E, Hp.Splus h - Sminus Hm h - ξ ∈ unstableSub A ⊔ stableSub A := by
  obtain ⟨z, hz⟩ : ∃ z, IsLinSol A 0 z ∧ z 0 = ξ :=
    ⟨_, linSol_spec hA hM (h := 0) (H := 0) continuous_const (fun _ => by simp) 0 ξ⟩
  set χ := Real.smoothTransition
  have hχ : ∀ t, HasDerivAt χ (deriv χ t) t := fun t =>
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero t).hasDerivAt
  have hχc : Continuous (deriv χ) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hχ0 : ∀ t, t ∉ Icc (0 : ℝ) 1 → deriv χ t = 0 := fun t ht => by
    rcases lt_or_ge t 0 with h | h
    · rw [Filter.EventuallyEq.deriv_eq (f := fun _ => (0 : ℝ))
        ((eventually_lt_nhds h).mono fun s hs => Real.smoothTransition.zero_of_nonpos hs.le)]
      exact deriv_const t 0
    · have h1 : 1 < t := not_le.1 fun h1 => ht ⟨h, h1⟩
      rw [Filter.EventuallyEq.deriv_eq (f := fun _ => (1 : ℝ))
        ((eventually_gt_nhds h1).mono fun s hs => Real.smoothTransition.one_of_one_le hs.le)]
      exact deriv_const t 1
  set f : ℝ → E := fun t => -(deriv χ t • z t)
  have hfc : Continuous f := (hχc.smul hz.1.continuous).neg
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hfc.continuousOn
  let h : ℝ →ᵇ E := ofNormedAddCommGroup f hfc (max C 0) fun t => by
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · exact (hC t ht).trans (le_max_left _ _)
    · simp [f, hχ0 t ht]
  have hp : IsLinSol A h (fun t => (1 - χ t) • z t) := fun t => by
    refine (((hχ t).const_sub 1).smul (hz.1 t)).congr_deriv ?_
    simp only [h, coe_ofNormedAddCommGroup, f, Pi.zero_apply, add_zero, map_smul, neg_smul]
  have hm : IsLinSol A h (fun t => -(χ t • z t)) := fun t => by
    refine ((hχ t).smul (hz.1 t)).neg.congr_deriv ?_
    simp only [h, coe_ofNormedAddCommGroup, f, Pi.zero_apply, add_zero, map_smul, map_neg]
    abel
  have hpc : Continuous fun t => (1 - χ t) • z t :=
    (continuous_const.sub Real.smoothTransition.continuous).smul hz.1.continuous
  obtain ⟨Cp, hCp⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hpc.continuousOn
  have hs := (Hp.bdd_iff_mem_stableSub hp).1 ⟨max Cp 0, fun t ht => by
    by_cases ht1 : t ≤ 1
    · exact (hCp t ⟨ht, ht1⟩).trans (le_max_left _ _)
    · simp [χ, Real.smoothTransition.one_of_one_le (not_le.1 ht1).le]⟩
  have hu := (bdd_neg_iff Hm hm).1 ⟨0, fun t ht => by
    simp [χ, Real.smoothTransition.zero_of_nonpos ht]⟩
  simp only [χ, Real.smoothTransition.zero, sub_zero, one_smul, zero_smul, neg_zero,
    hz.2] at hs hu
  refine ⟨h, ?_⟩
  have := Submodule.sub_mem _ (Submodule.mem_sup_left hu) (Submodule.mem_sup_right hs)
  convert this using 1
  abel

theorem ker_cokerMap : LinearMap.ker (cokerMap Hp Hm) = (palmerL hA hM).range := by
  ext h
  simp only [LinearMap.mem_ker, cokerMap, LinearMap.coe_comp, comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, ContinuousLinearMap.coe_coe, _root_.sub_apply,
    mem_range_iff hA hM Hp Hm]

theorem cokerMap_surjective : Surjective (cokerMap Hp Hm) := by
  intro q
  obtain ⟨ξ, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨h, hh⟩ := exists_cutoff hA hM Hp Hm ξ
  exact ⟨h, (Submodule.Quotient.eq _).2 hh⟩

/-- `coker L ≅ E/(E^u + E^s)`. -/
noncomputable def cokerEquiv :
    ((ℝ →ᵇ E) ⧸ (palmerL hA hM).range) ≃ₗ[ℝ] E ⧸ (unstableSub A ⊔ stableSub A) :=
  (Submodule.quotEquivOfEq _ _ (ker_cokerMap hA hM Hp Hm).symm).trans
    ((cokerMap Hp Hm).quotKerEquivOfSurjective (cokerMap_surjective hA hM Hp Hm))

variable [FiniteDimensional ℝ E]

theorem isStrictMap_palmerL : IsStrictMap (palmerL hA hM) := by
  have hc := isClosed_range_palmerL hA hM Hp Hm
  have : CompleteSpace ((palmerL hA hM).range) := hc.completeSpace_coe
  let g : C1b E →L[ℝ] (palmerL hA hM).range :=
    (palmerL hA hM).codRestrict _ fun p => LinearMap.mem_range_self _ p
  have hg : Surjective g := fun ⟨_, p, hp⟩ => ⟨p, Subtype.ext hp⟩
  exact (LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict
    (f := (palmerL hA hM : C1b E →ₗ[ℝ] (ℝ →ᵇ E)))).2 ⟨hg, g.continuous, g.isOpenMap hg⟩

/-- **Palmer's theorem**, Proposition `prop:palmer`(ii): `L` is Fredholm. -/
theorem isFredholm : (palmerL hA hM).IsFredholm where
  isStrictMap := isStrictMap_palmerL hA hM Hp Hm
  isClosed_range := isClosed_range_palmerL hA hM Hp Hm
  finite_ker := by
    have := Module.Finite.equiv (kerEquiv hA hM).symm
    exact this
  finite_coker := Module.Finite.equiv (cokerEquiv hA hM Hp Hm).symm
  closedComplemented_ker := by
    have := Module.Finite.equiv (kerEquiv hA hM).symm
    exact Submodule.ClosedComplemented.of_finiteDimensional _

omit hA hM Hp [FiniteDimensional ℝ E] in
theorem finrank_unstableSub :
    finrank ℝ (unstableSub A) = finrank ℝ (LinearMap.range (Hm.d.P : E →ₗ[ℝ] E)) := by
  rw [unstableSub_eq]; exact Hm.finrank_stableSub

/-- The index of `L` is `dim E^u + dim E^s - n`, i.e. `μ₋ - μ₊`. -/
theorem index_eq :
    (palmerL hA hM).index = (finrank ℝ (LinearMap.range (Hm.d.P : E →ₗ[ℝ] E)) : ℤ) - Hp.d.μ := by
  have := (isFredholm hA hM Hp Hm).finite_ker
  rw [LinearMap.index, (kerEquiv hA hM).finrank_eq, (cokerEquiv hA hM Hp Hm).finrank_eq]
  have hq := Submodule.finrank_quotient_add_finrank (unstableSub A ⊔ stableSub A)
  have hi := fredholm_index_eq (unstableSub A) (stableSub A)
  have hp := Hp.d.finrank_add_μ
  rw [finrank_unstableSub Hm, Hp.finrank_stableSub] at hi
  omega

/-! ### Transversality -/

/-- The connection is transversal when `E^u + E^s = E`. -/
def Transversal (A : ℝ → E →L[ℝ] E) : Prop := unstableSub A ⊔ stableSub A = ⊤

omit [FiniteDimensional ℝ E] in
/-- Proposition `prop:palmer`(iii): transversal iff `L` is onto. -/
theorem transversal_iff_surjective : Transversal A ↔ Surjective (palmerL hA hM) := by
  constructor
  · intro hT h
    exact (mem_range_iff hA hM Hp Hm h).2 (hT ▸ Submodule.mem_top)
  · intro hs
    refine eq_top_iff.2 fun ξ _ => ?_
    obtain ⟨h, hh⟩ := exists_cutoff hA hM Hp Hm ξ
    have hr := (mem_range_iff hA hM Hp Hm h).1 (hs h)
    have := Submodule.sub_mem _ hr hh
    rwa [sub_sub_cancel] at this

/-- If `μ₋ = μ₊`, transversal iff `ker L = 0`. -/
theorem transversal_iff_ker_eq_bot
    (hμ : finrank ℝ (LinearMap.range (Hm.d.P : E →ₗ[ℝ] E)) = Hp.d.μ) :
    Transversal A ↔ (palmerL hA hM).ker = ⊥ := by
  have := (isFredholm hA hM Hp Hm).finite_ker
  have hdim : finrank ℝ (unstableSub A) + finrank ℝ (stableSub A) = finrank ℝ E := by
    rw [finrank_unstableSub Hm, Hp.finrank_stableSub, hμ, add_comm]
    exact Hp.d.finrank_add_μ
  rw [Transversal, sup_eq_top_iff_inf_eq_bot hdim, ← Submodule.finrank_eq_zero,
    ← Submodule.finrank_eq_zero, (kerEquiv hA hM).finrank_eq]

/-- If `μ₋ = μ₊` and the connection is transversal, `L` is invertible. -/
noncomputable def palmerEquiv (hμ : finrank ℝ (LinearMap.range (Hm.d.P : E →ₗ[ℝ] E)) = Hp.d.μ)
    (hT : Transversal A) : C1b E ≃L[ℝ] (ℝ →ᵇ E) :=
  ContinuousLinearEquiv.ofBijective (palmerL hA hM)
    ((transversal_iff_ker_eq_bot hA hM Hp Hm hμ).1 hT)
    (LinearMap.range_eq_top.2 ((transversal_iff_surjective hA hM Hp Hm).1 hT))

end Palmer

/-! ### Statement in terms of the limits -/

variable [FiniteDimensional ℝ E] {Am Ap : E →L[ℝ] E}

/-- **Palmer's theorem** (Proposition `prop:palmer`(ii), (iii)). If `A` is continuous and bounded
with `A(t) → A±` as `t → ±∞`, and `A±` have exponential dichotomies `d±` with unstable ranks
`μ±`, then `L y = y' - A(t) y : C¹_b → C⁰_b` is Fredholm of index `μ₋ - μ₊`, `L` is onto iff
the connection is transversal, and if `μ₋ = μ₊` this holds iff `ker L = 0`. -/
theorem palmer (dm : Dichotomy Am) (dp : Dichotomy Ap) (hlimm : Tendsto A atBot (𝓝 Am))
    (hlimp : Tendsto A atTop (𝓝 Ap)) :
    (palmerL hA hM).IsFredholm ∧ (palmerL hA hM).index = (dm.μ : ℤ) - dp.μ ∧
      (Transversal A ↔ Surjective (palmerL hA hM)) ∧
      (dm.μ = dp.μ → (Transversal A ↔ (palmerL hA hM).ker = ⊥)) := by
  obtain ⟨Hp, rfl⟩ := HalfData.exists_of_tendsto dp hA hM hlimp
  obtain ⟨Hm, hHm⟩ := HalfData.exists_of_tendsto dm.neg (continuous_revA hA) (norm_revA_le hM)
    (tendsto_revA hlimm)
  have hμ : finrank ℝ (LinearMap.range (Hm.d.P : E →ₗ[ℝ] E)) = dm.μ := by rw [hHm]; rfl
  refine ⟨isFredholm hA hM Hp Hm, by rw [index_eq hA hM Hp Hm, hμ],
    transversal_iff_surjective hA hM Hp Hm, fun h => ?_⟩
  exact transversal_iff_ker_eq_bot hA hM Hp Hm (hμ.trans h)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem ker_palmerL_eq_bot (h0 : ∀ y : ℝ → E, IsLinSol A 0 y → (∃ C, ∀ t, ‖y t‖ ≤ C) → y = 0) :
    (palmerL hA hM).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  rintro ⟨⟨y, z⟩, hyz⟩ hp
  have hp' : palmerL hA hM ⟨(y, z), hyz⟩ = 0 := hp
  have hy := isLinSol_of_C1b hA hM ⟨(y, z), hyz⟩
  rw [hp'] at hy
  have hy0 : ⇑y = 0 := h0 _ hy ⟨‖y‖, y.norm_coe_le_norm⟩
  have hz : z = 0 := by
    ext t
    have := hyz t
    simp only [hy0] at this
    exact this.unique (hasDerivAt_const t 0)
  have hy' : y = 0 := DFunLike.coe_injective hy0
  subst hy' hz
  rfl

/-- If `μ₋ = μ₊` and `y' = A(t) y` has no nonzero solution bounded on `ℝ`, the connection is
transversal and `L` is an isomorphism `C¹_b ≅ C⁰_b`. -/
theorem transversal_of_bdd_eq_zero (dm : Dichotomy Am) (dp : Dichotomy Ap)
    (hlimm : Tendsto A atBot (𝓝 Am)) (hlimp : Tendsto A atTop (𝓝 Ap)) (hμ : dm.μ = dp.μ)
    (h0 : ∀ y : ℝ → E, IsLinSol A 0 y → (∃ C, ∀ t, ‖y t‖ ≤ C) → y = 0) :
    Transversal A ∧ ∃ e : C1b E ≃L[ℝ] (ℝ →ᵇ E), ∀ p, e p = palmerL hA hM p := by
  obtain ⟨-, -, hs, hk⟩ := palmer hA hM dm dp hlimm hlimp
  have hker := ker_palmerL_eq_bot hA hM h0
  have hT := (hk hμ).2 hker
  exact ⟨hT, ContinuousLinearEquiv.ofBijective (palmerL hA hM) hker
    (LinearMap.range_eq_top.2 (hs.1 hT)), fun _ => rfl⟩

omit [FiniteDimensional ℝ E] in
/-- For constant hyperbolic `A₀`, the only solution of `y' = A₀ y` bounded on `ℝ` is zero. -/
theorem Dichotomy.eq_zero_of_bdd {A₀ : E →L[ℝ] E} (d : Dichotomy A₀) {y : ℝ → E}
    (hy : IsLinSol (fun _ => A₀) 0 y) {C : ℝ} (hC : ∀ t, ‖y t‖ ≤ C) : y = 0 := by
  have he : ∀ t, y t = exp (t • A₀) (y 0) := fun t => by
    have := hy.eq_of_eq (M := ‖A₀‖) (fun _ => le_rfl) (isLinSol_exp_sub A₀ (y 0) 0) (t₀ := 0)
      (by simp)
    rw [this]; simp
  have hlim : Tendsto (fun s => d.K * C * Real.exp (-(d.α * s))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop d.hα)).const_mul (d.K * C)
    simpa using this
  have hbd : ∀ s (v : E), ‖v‖ ≤ C →
      d.K * Real.exp (-(d.α * s)) * ‖v‖ ≤ d.K * C * Real.exp (-(d.α * s)) := fun s v hv => by
    calc d.K * Real.exp (-(d.α * s)) * ‖v‖ ≤ d.K * Real.exp (-(d.α * s)) * C :=
          mul_le_mul_of_nonneg_left hv (mul_nonneg d.hK.le (Real.exp_pos _).le)
      _ = _ := by ring
  have hQ : y 0 - d.P (y 0) = 0 := by
    refine norm_le_zero_iff.1 (ge_of_tendsto hlim (eventually_atTop.2 ⟨0, fun s hs => ?_⟩))
    have h1 : y 0 - d.P (y 0) = exp ((-s) • A₀) (y s - d.P (y s)) := by
      rw [he s, ← d.exp_P, ← map_sub, ← clm_mul_apply, exp_neg_mul_smul]; rfl
    rw [h1]
    exact (d.norm_exp_Q_le hs _).trans (hbd s _ (hC s))
  have hP : d.P (y 0) = 0 := by
    refine norm_le_zero_iff.1 (ge_of_tendsto hlim (eventually_atTop.2 ⟨0, fun s hs => ?_⟩))
    have h1 : d.P (y 0) = exp (s • A₀) (d.P (y (-s))) := by
      rw [he (-s), d.exp_P, ← clm_mul_apply (exp (s • A₀)), exp_smul_mul_neg]; rfl
    rw [h1]
    exact (d.norm_exp_P_le hs _).trans (hbd s _ (hC (-s)))
  have h0 : y 0 = 0 := by rw [← sub_add_cancel (y 0) (d.P (y 0)), hQ, hP, add_zero]
  funext t
  rw [he t, h0, map_zero]; rfl

/-- A connection with constant hyperbolic coefficients is transversal, and `L` is invertible. -/
theorem transversal_const {A₀ : E →L[ℝ] E} (d : Dichotomy A₀) :
    Transversal (fun _ : ℝ => A₀) ∧ ∃ e : C1b E ≃L[ℝ] (ℝ →ᵇ E),
      ∀ p, e p = palmerL (A := fun _ => A₀) continuous_const (M := ‖A₀‖) (fun _ => le_rfl) p :=
  transversal_of_bdd_eq_zero continuous_const (fun _ => le_rfl) d d tendsto_const_nhds
    tendsto_const_nhds rfl fun _ hy ⟨_, hC⟩ => d.eq_zero_of_bdd hy hC

end ConleyCheck.Palmer
