import ConleyCheck.Palmer.LinearODE

/-!
# Hyperbolic linear maps

A `Dichotomy A₀` is an exponential dichotomy of `y' = A₀ y` on `ℝ`: a projection `P` commuting with
`A₀` such that `‖exp(t A₀) P‖ ≤ K e^{-αt}` and `‖exp(-t A₀)(1 - P)‖ ≤ K e^{-αt}` for `t ≥ 0`. This
is the dynamical form of hyperbolicity of `A₀`. The unstable dimension `μ = dim range (1 - P)` is
the Morse index of a hyperbolic equilibrium with linearization `A₀`.

`Dichotomy.ofBasis` produces a dichotomy from an eigenbasis with nonzero real eigenvalues, with
`μ` the number of positive eigenvalues (`Dichotomy.ofBasis_μ`), and `Dichotomy.neg` is the dichotomy
of `-A₀`, which exchanges the stable and unstable parts.
-/

namespace ConleyCheck.Palmer

open NormedSpace Set Filter Topology Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exp_mem_ball (x : E →L[ℝ] E) :
    x ∈ Metric.eball (0 : E →L[ℝ] E) (expSeries ℝ (E →L[ℝ] E)).radius :=
  (expSeries_radius_eq_top ℝ (E →L[ℝ] E)).symm ▸ edist_lt_top _ _

theorem clm_mul_apply (f g : E →L[ℝ] E) (v : E) : (f * g) v = f (g v) := rfl

theorem clm_one_sub_apply (f : E →L[ℝ] E) (v : E) : (1 - f) v = v - f v := rfl

section Exp

variable [CompleteSpace E]

theorem exp_add_smul (A : E →L[ℝ] E) (s t : ℝ) :
    exp ((s + t) • A) = exp (s • A) * exp (t • A) := by
  rw [add_smul, exp_add_of_commute_of_mem_ball (((Commute.refl A).smul_left _).smul_right _)
    (exp_mem_ball _) (exp_mem_ball _)]

theorem exp_smul_mul_neg (A : E →L[ℝ] E) (t : ℝ) : exp (t • A) * exp ((-t) • A) = 1 := by
  rw [← exp_add_smul, add_neg_cancel, zero_smul, exp_zero]

theorem exp_neg_mul_smul (A : E →L[ℝ] E) (t : ℝ) : exp ((-t) • A) * exp (t • A) = 1 := by
  rw [← exp_add_smul, neg_add_cancel, zero_smul, exp_zero]

theorem exp_sub_smul_apply (A : E →L[ℝ] E) (τ s : ℝ) (v : E) :
    exp ((τ - s) • A) v = exp (τ • A) (exp ((-s) • A) v) := by
  rw [sub_eq_add_neg, exp_add_smul]; rfl

theorem hasDerivAt_exp_smul_apply (A : E →L[ℝ] E) (v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • A) v) (A (exp (t • A) v)) t :=
  (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t)

theorem hasDerivAt_exp_sub_smul_apply (A : E →L[ℝ] E) (v : E) (T τ : ℝ) :
    HasDerivAt (fun τ => exp ((τ - T) • A) v) (A (exp ((τ - T) • A) v)) τ := by
  have := (hasDerivAt_exp_smul_apply A v (τ - T)).scomp τ ((hasDerivAt_id τ).sub_const T)
  convert this using 1
  · rfl
  · simp

theorem isLinSol_exp_sub (A : E →L[ℝ] E) (v : E) (T : ℝ) :
    IsLinSol (fun _ => A) 0 fun τ => exp ((τ - T) • A) v := fun τ => by
  simpa using hasDerivAt_exp_sub_smul_apply A v T τ

theorem continuous_exp_smul (A : E →L[ℝ] E) : Continuous fun t : ℝ => exp (t • A) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t).continuousAt

/-- On an eigenvector, `exp(t A₀) v = e^{t λ} v`. -/
theorem exp_smul_apply_of_eigen {A₀ : E →L[ℝ] E} {v : E} {l : ℝ} (hv : A₀ v = l • v) (t : ℝ) :
    exp (t • A₀) v = Real.exp (t * l) • v := by
  have h1 : IsLinSol (fun _ => A₀) 0 fun s => exp (s • A₀) v := fun s => by
    simpa using hasDerivAt_exp_smul_apply A₀ v s
  have h2 : IsLinSol (fun _ => A₀) 0 fun s => Real.exp (s * l) • v := fun s => by
    have := ((Real.hasDerivAt_exp _).comp s ((hasDerivAt_id s).mul_const l)).smul_const v
    refine this.congr_deriv ?_
    simp only [id, one_mul, Pi.zero_apply, add_zero, map_smul, hv, smul_smul]
  have := h1.eq_of_eq (M := ‖A₀‖) (fun _ => le_rfl) h2 (t₀ := 0) (by simp)
  exact congrFun this t

end Exp

/-- An exponential dichotomy of `y' = A₀ y` on `ℝ`. -/
structure Dichotomy (A₀ : E →L[ℝ] E) where
  P : E →L[ℝ] E
  K : ℝ
  α : ℝ
  hK : 0 < K
  hα : 0 < α
  idem : P * P = P
  comm : Commute A₀ P
  stable : ∀ t, 0 ≤ t → ‖exp (t • A₀) * P‖ ≤ K * Real.exp (-(α * t))
  unstable : ∀ t, 0 ≤ t → ‖exp ((-t) • A₀) * (1 - P)‖ ≤ K * Real.exp (-(α * t))

/-- `A₀` is hyperbolic: `y' = A₀ y` has an exponential dichotomy on `ℝ`. -/
def IsHyperbolic (A₀ : E →L[ℝ] E) : Prop := Nonempty (Dichotomy A₀)

namespace Dichotomy

variable {A₀ : E →L[ℝ] E} (d : Dichotomy A₀)

/-- The unstable dimension, i.e. the Morse index. -/
noncomputable def μ : ℕ := finrank ℝ (LinearMap.range ((1 - d.P : E →L[ℝ] E) : E →ₗ[ℝ] E))

theorem P_apply_P (v : E) : d.P (d.P v) = d.P v := by
  have := congrArg (fun f : E →L[ℝ] E => f v) d.idem
  simpa using this

theorem P_Q (v : E) : d.P (v - d.P v) = 0 := by
  rw [map_sub, d.P_apply_P, sub_self]

theorem commute_exp (t : ℝ) : Commute (exp (t • A₀)) d.P :=
  ((d.comm.symm.smul_right t).exp_right).symm

theorem exp_P (t : ℝ) (v : E) : exp (t • A₀) (d.P v) = d.P (exp (t • A₀) v) := by
  have := congrArg (fun f : E →L[ℝ] E => f v) (d.commute_exp t).eq
  simpa using this

theorem norm_exp_P_le {t : ℝ} (ht : 0 ≤ t) (v : E) :
    ‖exp (t • A₀) (d.P v)‖ ≤ d.K * Real.exp (-(d.α * t)) * ‖v‖ := by
  have := (exp (t • A₀) * d.P).le_opNorm v
  exact this.trans (mul_le_mul_of_nonneg_right (d.stable t ht) (norm_nonneg _))

theorem norm_exp_P_le' {t : ℝ} (ht : 0 ≤ t) (v : E) : ‖exp (t • A₀) (d.P v)‖ ≤ d.K * ‖v‖ := by
  have he : Real.exp (-(d.α * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [d.hα])
  calc _ ≤ d.K * Real.exp (-(d.α * t)) * ‖v‖ := d.norm_exp_P_le ht v
    _ ≤ d.K * 1 * ‖v‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he d.hK.le) (norm_nonneg _)
    _ = d.K * ‖v‖ := by ring

theorem norm_exp_Q_le {t : ℝ} (ht : 0 ≤ t) (v : E) :
    ‖exp ((-t) • A₀) (v - d.P v)‖ ≤ d.K * Real.exp (-(d.α * t)) * ‖v‖ := by
  have := (exp ((-t) • A₀) * (1 - d.P)).le_opNorm v
  refine le_trans (le_of_eq ?_) (this.trans
    (mul_le_mul_of_nonneg_right (d.unstable t ht) (norm_nonneg _)))
  simp

/-- The dichotomy of `-A₀`: stable and unstable parts are exchanged. -/
noncomputable def neg : Dichotomy (-A₀) where
  P := 1 - d.P
  K := d.K
  α := d.α
  hK := d.hK
  hα := d.hα
  idem := by
    rw [sub_mul, one_mul, mul_sub, mul_one, d.idem, sub_self, sub_zero]
  comm := ((Commute.one_right A₀).sub_right d.comm).neg_left
  stable t ht := by
    rw [smul_neg, ← neg_smul]
    exact d.unstable t ht
  unstable t ht := by
    rw [smul_neg, neg_smul, neg_neg, sub_sub_cancel]
    exact d.stable t ht

theorem range_one_sub_eq_ker :
    LinearMap.range ((1 - d.P : E →L[ℝ] E) : E →ₗ[ℝ] E) = LinearMap.ker (d.P : E →ₗ[ℝ] E) := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    show d.P ((1 - d.P) w) = 0
    simpa using d.P_Q w
  · intro h
    have h' : d.P v = 0 := h
    exact ⟨v, show (1 - d.P) v = v by simp [h']⟩

theorem finrank_add_μ [FiniteDimensional ℝ E] :
    finrank ℝ (LinearMap.range (d.P : E →ₗ[ℝ] E)) + d.μ = finrank ℝ E := by
  rw [μ, range_one_sub_eq_ker]
  exact LinearMap.finrank_range_add_finrank_ker _

theorem neg_μ : d.neg.μ = finrank ℝ (LinearMap.range (d.P : E →ₗ[ℝ] E)) := by
  exact congrArg (fun f : E →L[ℝ] E => finrank ℝ (LinearMap.range (f : E →ₗ[ℝ] E)))
    (sub_sub_cancel 1 d.P)

end Dichotomy

theorem exists_pos_le_abs {ι : Type*} [Fintype ι] (l : ι → ℝ) (h : ∀ i, l i ≠ 0) :
    ∃ α > 0, ∀ i, α ≤ |l i| := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty (fun i => |l i|), ?_, fun i =>
      Finset.inf'_le _ (Finset.mem_univ i)⟩
    rw [gt_iff_lt, Finset.lt_inf'_iff]
    exact fun i _ => abs_pos.2 (h i)

section Basis

variable [FiniteDimensional ℝ E] {A₀ : E →L[ℝ] E} {ι : Type*} [Fintype ι]
  (b : Basis ι ℝ E) (l : ι → ℝ)

/-- The projection onto the span of the `b i` with `l i < 0`. -/
noncomputable def basisProj : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    (∑ i ∈ Finset.univ.filter (fun i => l i < 0), (b.coord i).smulRight (b i))

theorem basisProj_apply (v : E) :
    basisProj b l v = ∑ i ∈ Finset.univ.filter (fun i => l i < 0), b.repr v i • b i := by
  simp [basisProj]

theorem basisProj_basis [DecidableEq ι] (j : ι) :
    basisProj b l (b j) = if l j < 0 then b j else 0 := by
  rw [basisProj_apply]
  simp only [Basis.repr_self]
  split_ifs with hj
  · rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [Ne.symm hij]
    · intro hj'; simp [hj] at hj'
  · refine Finset.sum_eq_zero fun i hi => ?_
    have hij : j ≠ i := fun h => hj (h ▸ (Finset.mem_filter.1 hi).2)
    simp [hij]

theorem one_sub_basisProj_apply (v : E) :
    v - basisProj b l v = ∑ i ∈ Finset.univ.filter (fun i => ¬ l i < 0), b.repr v i • b i := by
  rw [basisProj_apply, sub_eq_iff_eq_add', Finset.sum_filter_add_sum_filter_not]
  exact (b.sum_repr v).symm

omit [Fintype ι] in
theorem norm_repr_le (v : E) (i : ι) :
    ‖b.repr v i‖ ≤ ‖LinearMap.toContinuousLinearMap (b.coord i)‖ * ‖v‖ :=
  (LinearMap.toContinuousLinearMap (b.coord i)).le_opNorm v

/-- The constant of the eigenbasis estimates. -/
noncomputable def basisConst : ℝ :=
  1 + ∑ i, ‖LinearMap.toContinuousLinearMap (b.coord i)‖ * ‖b i‖

theorem basisConst_pos : 0 < basisConst b := by
  unfold basisConst; positivity

theorem norm_sum_le_basisConst (c : ι → ℝ) (s : Finset ι) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ i ∈ s, 0 ≤ c i ∧ c i ≤ C) (v : E) :
    ‖∑ i ∈ s, (c i * b.repr v i) • b i‖ ≤ C * basisConst b * ‖v‖ := by
  calc ‖∑ i ∈ s, (c i * b.repr v i) • b i‖
      ≤ ∑ i ∈ s, ‖(c i * b.repr v i) • b i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, C * (‖LinearMap.toContinuousLinearMap (b.coord i)‖ * ‖b i‖) * ‖v‖ := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_smul, norm_mul, Real.norm_of_nonneg (hc i hi).1]
        have := norm_repr_le b v i
        have h2 := (hc i hi).2
        calc c i * ‖b.repr v i‖ * ‖b i‖
            ≤ C * (‖LinearMap.toContinuousLinearMap (b.coord i)‖ * ‖v‖) * ‖b i‖ := by
              gcongr
          _ = _ := by ring
    _ ≤ ∑ i, C * (‖LinearMap.toContinuousLinearMap (b.coord i)‖ * ‖b i‖) * ‖v‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => by positivity)
    _ ≤ C * basisConst b * ‖v‖ := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, basisConst]
        gcongr
        linarith

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem clm_ext_basis {f g : E →L[ℝ] E} (h : ∀ j, f (b j) = g (b j)) : f = g :=
  ContinuousLinearMap.coe_injective (b.ext h)

variable {b l}

theorem exp_basisProj (hb : ∀ i, A₀ (b i) = l i • b i) (t : ℝ) (v : E) :
    exp (t • A₀) (basisProj b l v) =
      ∑ i ∈ Finset.univ.filter (fun i => l i < 0), (Real.exp (t * l i) * b.repr v i) • b i := by
  have := FiniteDimensional.complete ℝ E
  rw [basisProj_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, exp_smul_apply_of_eigen (hb i), smul_smul, mul_comm]

theorem exp_one_sub_basisProj (hb : ∀ i, A₀ (b i) = l i • b i) (t : ℝ) (v : E) :
    exp (t • A₀) (v - basisProj b l v) =
      ∑ i ∈ Finset.univ.filter (fun i => ¬ l i < 0), (Real.exp (t * l i) * b.repr v i) • b i := by
  have := FiniteDimensional.complete ℝ E
  rw [one_sub_basisProj_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, exp_smul_apply_of_eigen (hb i), smul_smul, mul_comm]

/-- The dichotomy of a map with an eigenbasis and nonzero real eigenvalues. -/
noncomputable def Dichotomy.ofBasis [DecidableEq ι] (hb : ∀ i, A₀ (b i) = l i • b i)
    (hl : ∀ i, l i ≠ 0) : Dichotomy A₀ where
  P := basisProj b l
  K := basisConst b
  α := (exists_pos_le_abs l hl).choose
  hK := basisConst_pos b
  hα := (exists_pos_le_abs l hl).choose_spec.1
  idem := clm_ext_basis b fun j => by
    rw [clm_mul_apply, basisProj_basis]
    split_ifs with hj
    · simp [basisProj_basis, hj]
    · rw [map_zero]
  comm := clm_ext_basis b fun j => by
    rw [clm_mul_apply, clm_mul_apply, basisProj_basis, hb,
      map_smul, basisProj_basis]
    split_ifs <;> simp [hb]
  stable t ht := by
    have hα := (exists_pos_le_abs l hl).choose_spec
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (basisConst_pos b).le (Real.exp_pos _).le) fun v => ?_
    rw [clm_mul_apply, exp_basisProj hb]
    refine (norm_sum_le_basisConst b _ _ (Real.exp_pos _).le (fun i hi => ⟨(Real.exp_pos _).le,
      Real.exp_le_exp.2 ?_⟩) v).trans (le_of_eq (by ring))
    have h1 := (Finset.mem_filter.1 hi).2
    have h2 := hα.2 i
    rw [abs_of_neg h1] at h2
    nlinarith
  unstable t ht := by
    have hα := (exists_pos_le_abs l hl).choose_spec
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (basisConst_pos b).le (Real.exp_pos _).le) fun v => ?_
    rw [clm_mul_apply, clm_one_sub_apply, exp_one_sub_basisProj hb]
    refine (norm_sum_le_basisConst b _ _ (Real.exp_pos _).le (fun i hi => ⟨(Real.exp_pos _).le,
      Real.exp_le_exp.2 ?_⟩) v).trans (le_of_eq (by ring))
    have h1 := (Finset.mem_filter.1 hi).2
    have h0 : 0 < l i := lt_of_le_of_ne (not_lt.1 h1) (hl i).symm
    have h2 := hα.2 i
    rw [abs_of_pos h0] at h2
    nlinarith

/-- The Morse index of `ofBasis` is the number of positive eigenvalues. -/
theorem Dichotomy.ofBasis_μ [DecidableEq ι] (hb : ∀ i, A₀ (b i) = l i • b i)
    (hl : ∀ i, l i ≠ 0) :
    (Dichotomy.ofBasis hb hl).μ = (Finset.univ.filter fun i => 0 < l i).card := by
  have hr : LinearMap.range (((1 - basisProj b l : E →L[ℝ] E)) : E →ₗ[ℝ] E) =
      Submodule.span ℝ (Set.range fun i : {i // 0 < l i} => b i) := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      show (1 - basisProj b l) v ∈ _
      rw [clm_one_sub_apply, one_sub_basisProj_apply]
      refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      have h1 := (Finset.mem_filter.1 hi).2
      exact ⟨⟨i, lt_of_le_of_ne (not_lt.1 h1) (hl i).symm⟩, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨⟨i, hi⟩, rfl⟩
      refine ⟨b i, ?_⟩
      show (1 - basisProj b l) (b i) = b i
      simp [basisProj_basis, not_lt.2 hi.le]
  rw [Dichotomy.μ]
  show finrank ℝ (LinearMap.range (((1 - basisProj b l : E →L[ℝ] E)) : E →ₗ[ℝ] E)) = _
  have hli : LinearIndependent ℝ (fun i : {i // 0 < l i} => b i) :=
    b.linearIndependent.comp _ Subtype.val_injective
  rw [hr, finrank_span_eq_card hli, Fintype.card_subtype]

end Basis

end ConleyCheck.Palmer
