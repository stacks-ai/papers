import ConleyCheck.Palmer.Hyperbolic

/-!
# The Green operator of a hyperbolic constant-coefficient system

For a dichotomy `d` of `A₀`, a base time `T` and `g : ℝ →ᵇ E`,
`gr d T g τ = ∫_T^τ e^{(τ-s)A₀} P g(s) ds - ∫_τ^∞ e^{(τ-s)A₀} (1 - P) g(s) ds`.
It solves `y' = A₀ y + g` (`hasDerivAt_gr`), satisfies `‖gr d T g τ‖ ≤ (2K/α) ‖g‖` for `τ ≥ T`
(`norm_gr_le`), is linear in `g`, and `P (gr d T g T) = 0` (`P_gr_T`).
-/

namespace ConleyCheck.Palmer

open NormedSpace Set Filter Topology MeasureTheory BoundedContinuousFunction Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section MkBCF

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A continuous linear map into `ℝ →ᵇ E` given pointwise. -/
noncomputable def mkBCF (f : X → ℝ → E) (hc : ∀ x, Continuous (f x))
    (hadd : ∀ x x' t, f (x + x') t = f x t + f x' t)
    (hsmul : ∀ (c : ℝ) x t, f (c • x) t = c • f x t)
    (C : ℝ) (hb : ∀ x t, ‖f x t‖ ≤ C * ‖x‖) : X →L[ℝ] (ℝ →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := fun x => BoundedContinuousFunction.ofNormedAddCommGroup (f x) (hc x) (C * ‖x‖) (hb x)
      map_add' := fun x x' => by ext t; simp [hadd]
      map_smul' := fun c x => by ext t; simp [hsmul] }
    C (fun x => BoundedContinuousFunction.norm_ofNormedAddCommGroup_le (hc x)
      ((norm_nonneg _).trans (hb x 0)) (hb x))

variable {f : X → ℝ → E} {hc : ∀ x, Continuous (f x)}
  {hadd : ∀ x x' t, f (x + x') t = f x t + f x' t} {hsmul : ∀ (c : ℝ) x t, f (c • x) t = c • f x t}
  {C : ℝ} {hb : ∀ x t, ‖f x t‖ ≤ C * ‖x‖}

@[simp]
theorem mkBCF_apply (x : X) (t : ℝ) : mkBCF f hc hadd hsmul C hb x t = f x t := rfl

theorem norm_mkBCF_le (hC : 0 ≤ C) : ‖mkBCF f hc hadd hsmul C hb‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

end MkBCF

omit [NormedSpace ℝ E] in
theorem integrableOn_Ioi_of_le_exp {φ : ℝ → E} (hφ : Continuous φ)
    {C α τ : ℝ} (hα : 0 < α) (hb : ∀ s, τ ≤ s → ‖φ s‖ ≤ C * Real.exp (-(α * (s - τ)))) :
    IntegrableOn φ (Ioi τ) := by
  have hg : IntegrableOn (fun s => C * Real.exp (α * τ) * Real.exp (-α * s)) (Ioi τ) :=
    (exp_neg_integrableOn_Ioi τ hα).const_mul _
  refine Integrable.mono' hg hφ.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
  refine (hb s (le_of_lt hs)).trans (le_of_eq ?_)
  rw [mul_assoc, ← Real.exp_add]; ring_nf

theorem integral_exp_Ioi_sub {α : ℝ} (hα : 0 < α) (τ : ℝ) :
    ∫ s in Ioi τ, Real.exp (-(α * (s - τ))) = 1 / α := by
  have : (fun s => Real.exp (-(α * (s - τ)))) = fun s => Real.exp (α * τ) * Real.exp (-α * s) := by
    funext s; rw [← Real.exp_add]; ring_nf
  rw [this, integral_const_mul, integral_exp_mul_Ioi (by linarith) τ, neg_div_neg_eq,
    ← mul_div_assoc, ← Real.exp_add, show α * τ + -α * τ = 0 by ring, Real.exp_zero]

theorem integral_exp_Icc_sub {α : ℝ} (hα : 0 < α) (T τ : ℝ) :
    ∫ s in T..τ, Real.exp (-(α * (τ - s))) = (1 - Real.exp (-(α * (τ - T)))) / α := by
  have hd : ∀ s, HasDerivAt (fun s => Real.exp (-(α * (τ - s))) / α)
      (Real.exp (-(α * (τ - s)))) s :=
    fun s => by
      have h1 : HasDerivAt (fun s => -(α * (τ - s))) α s := by
        convert ((hasDerivAt_id s).const_mul α).sub_const (α * τ) using 1
        · funext x; simp only [id]; ring
        · ring
      convert ((Real.hasDerivAt_exp _).comp s h1).div_const α using 1
      · rfl
      · field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    ((by fun_prop : Continuous fun s => Real.exp (-(α * (τ - s)))).intervalIntegrable _ _)]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero]
  ring

variable [CompleteSpace E] {A₀ : E →L[ℝ] E} (d : Dichotomy A₀) (T : ℝ)

/-- The stable part of the Green operator, `∫_T^τ e^{(τ-s)A₀} P g(s) ds`. -/
noncomputable def grP (g : ℝ →ᵇ E) (τ : ℝ) : E := ∫ s in T..τ, exp ((τ - s) • A₀) (d.P (g s))

/-- The unstable part of the Green operator, `∫_τ^∞ e^{(τ-s)A₀} (1 - P) g(s) ds`. -/
noncomputable def grQ (g : ℝ →ᵇ E) (τ : ℝ) : E :=
  ∫ s in Ioi τ, exp ((τ - s) • A₀) (g s - d.P (g s))

/-- The Green operator. -/
noncomputable def gr (g : ℝ →ᵇ E) (τ : ℝ) : E := grP d T g τ - grQ d g τ

variable {d T}

theorem continuous_grP_integrand (g : ℝ →ᵇ E) (τ : ℝ) :
    Continuous fun s => exp ((τ - s) • A₀) (d.P (g s)) :=
  ((continuous_exp_smul A₀).comp (continuous_const.sub continuous_id)).clm_apply
    (d.P.continuous.comp g.continuous)

theorem continuous_grQ_integrand (g : ℝ →ᵇ E) (τ : ℝ) :
    Continuous fun s => exp ((τ - s) • A₀) (g s - d.P (g s)) :=
  ((continuous_exp_smul A₀).comp (continuous_const.sub continuous_id)).clm_apply
    (g.continuous.sub (d.P.continuous.comp g.continuous))

omit [CompleteSpace E] in
theorem norm_grQ_integrand_le (g : ℝ →ᵇ E) {τ s : ℝ} (hs : τ ≤ s) :
    ‖exp ((τ - s) • A₀) (g s - d.P (g s))‖ ≤ d.K * ‖g‖ * Real.exp (-(d.α * (s - τ))) := by
  rw [← neg_sub s τ]
  refine (d.norm_exp_Q_le (sub_nonneg.2 hs) (g s)).trans ?_
  calc _ ≤ d.K * Real.exp (-(d.α * (s - τ))) * ‖g‖ := mul_le_mul_of_nonneg_left
        (g.norm_coe_le_norm s) (mul_nonneg d.hK.le (Real.exp_pos _).le)
    _ = _ := by ring

omit [CompleteSpace E] in
theorem norm_grP_integrand_le (g : ℝ →ᵇ E) {τ s : ℝ} (hs : s ≤ τ) :
    ‖exp ((τ - s) • A₀) (d.P (g s))‖ ≤ d.K * ‖g‖ * Real.exp (-(d.α * (τ - s))) := by
  refine (d.norm_exp_P_le (sub_nonneg.2 hs) (g s)).trans ?_
  calc _ ≤ d.K * Real.exp (-(d.α * (τ - s))) * ‖g‖ := mul_le_mul_of_nonneg_left
        (g.norm_coe_le_norm s) (mul_nonneg d.hK.le (Real.exp_pos _).le)
    _ = _ := by ring

theorem integrableOn_grQ (g : ℝ →ᵇ E) (τ : ℝ) :
    IntegrableOn (fun s => exp ((τ - s) • A₀) (g s - d.P (g s))) (Ioi τ) :=
  integrableOn_Ioi_of_le_exp (continuous_grQ_integrand g τ) d.hα fun _ hs =>
    norm_grQ_integrand_le g hs

omit [CompleteSpace E] in
theorem norm_grQ_le (g : ℝ →ᵇ E) (τ : ℝ) : ‖grQ d g τ‖ ≤ d.K / d.α * ‖g‖ := by
  have hint : IntegrableOn (fun s => d.K * ‖g‖ * Real.exp (-(d.α * (s - τ)))) (Ioi τ) :=
    integrableOn_Ioi_of_le_exp (by fun_prop) d.hα fun s _ => by
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg d.hK.le (norm_nonneg _))
        (Real.exp_pos _).le)]
  refine (norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall fun s hs => norm_grQ_integrand_le g (le_of_lt hs)))).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_Ioi_sub d.hα]
  ring

omit [CompleteSpace E] in
theorem norm_grP_le (g : ℝ →ᵇ E) {τ : ℝ} (hτ : T ≤ τ) : ‖grP d T g τ‖ ≤ d.K / d.α * ‖g‖ := by
  have hK := d.hK
  have hα := d.hα
  refine (intervalIntegral.norm_integral_le_of_norm_le hτ (Eventually.of_forall fun s hs =>
    norm_grP_integrand_le g hs.2) ((by fun_prop : Continuous fun s =>
      d.K * ‖g‖ * Real.exp (-(d.α * (τ - s)))).intervalIntegrable _ _)).trans ?_
  rw [intervalIntegral.integral_const_mul, integral_exp_Icc_sub d.hα]
  have h1 : 0 < Real.exp (-(d.α * (τ - T))) := Real.exp_pos _
  calc d.K * ‖g‖ * ((1 - Real.exp (-(d.α * (τ - T)))) / d.α) ≤ d.K * ‖g‖ * (1 / d.α) := by
        gcongr; linarith
    _ = d.K / d.α * ‖g‖ := by ring

omit [CompleteSpace E] in
theorem norm_gr_le (g : ℝ →ᵇ E) {τ : ℝ} (hτ : T ≤ τ) :
    ‖gr d T g τ‖ ≤ 2 * d.K / d.α * ‖g‖ :=
  (norm_sub_le _ _).trans (by
    have := norm_grP_le (d := d) g hτ
    have := norm_grQ_le (d := d) g τ
    calc _ ≤ d.K / d.α * ‖g‖ + d.K / d.α * ‖g‖ := add_le_add ‹_› ‹_›
      _ = _ := by ring)

theorem grP_add (g g' : ℝ →ᵇ E) (τ : ℝ) : grP d T (g + g') τ = grP d T g τ + grP d T g' τ := by
  simp only [grP, coe_add, Pi.add_apply, map_add]
  exact intervalIntegral.integral_add ((continuous_grP_integrand g τ).intervalIntegrable _ _)
    ((continuous_grP_integrand g' τ).intervalIntegrable _ _)

theorem grQ_add (g g' : ℝ →ᵇ E) (τ : ℝ) : grQ d (g + g') τ = grQ d g τ + grQ d g' τ := by
  have h : ∀ s, exp ((τ - s) • A₀) ((g + g') s - d.P ((g + g') s)) =
      exp ((τ - s) • A₀) (g s - d.P (g s)) + exp ((τ - s) • A₀) (g' s - d.P (g' s)) := fun s => by
    rw [← map_add]; congr 1; simp only [coe_add, Pi.add_apply, map_add]; abel
  simp only [grQ, h]
  exact integral_add (integrableOn_grQ g τ) (integrableOn_grQ g' τ)

theorem gr_add (g g' : ℝ →ᵇ E) (τ : ℝ) : gr d T (g + g') τ = gr d T g τ + gr d T g' τ := by
  simp only [gr, grP_add, grQ_add]; abel

omit [CompleteSpace E] in
theorem gr_smul (c : ℝ) (g : ℝ →ᵇ E) (τ : ℝ) : gr d T (c • g) τ = c • gr d T g τ := by
  simp only [gr, grP, grQ, coe_smul, map_smul, ← smul_sub,
    intervalIntegral.integral_smul, integral_smul]

/-- `P` kills `gr d T g T`. -/
theorem P_gr_T (g : ℝ →ᵇ E) : d.P (gr d T g T) = 0 := by
  rw [gr, grP, intervalIntegral.integral_same, zero_sub, map_neg, grQ,
    ← ContinuousLinearMap.integral_comp_comm _ (integrableOn_grQ g T)]
  simp [d.exp_P, d.P_Q]

theorem grP_eq (g : ℝ →ᵇ E) (τ : ℝ) :
    grP d T g τ = exp (τ • A₀) (∫ s in T..τ, exp ((-s) • A₀) (d.P (g s))) := by
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm]
  · simp only [grP, exp_sub_smul_apply]
  · exact (((continuous_exp_smul A₀).comp continuous_neg).clm_apply
      (d.P.continuous.comp g.continuous)).intervalIntegrable _ _

theorem integrableOn_grQ' (g : ℝ →ᵇ E) (τ : ℝ) :
    IntegrableOn (fun s => exp ((-s) • A₀) (g s - d.P (g s))) (Ioi τ) := by
  have := (exp ((-τ) • A₀)).integrable_comp (integrableOn_grQ (d := d) g τ)
  refine this.congr (Eventually.of_forall fun s => ?_)
  show exp ((-τ) • A₀) (exp ((τ - s) • A₀) _) = _
  rw [exp_sub_smul_apply, ← clm_mul_apply (exp ((-τ) • A₀)), exp_neg_mul_smul]
  rfl

theorem grQ_eq (g : ℝ →ᵇ E) (τ : ℝ) :
    grQ d g τ = exp (τ • A₀) (∫ s in Ioi τ, exp ((-s) • A₀) (g s - d.P (g s))) := by
  rw [← ContinuousLinearMap.integral_comp_comm _ (integrableOn_grQ' g τ)]
  simp only [grQ, exp_sub_smul_apply]

theorem hasDerivAt_integral_Ioi {φ : ℝ → E} (hφ : Continuous φ)
    (hi : ∀ a, IntegrableOn φ (Ioi a)) (τ : ℝ) :
    HasDerivAt (fun τ => ∫ s in Ioi τ, φ s) (-φ τ) τ := by
  have hF : ∀ t, ∫ s in Ioi t, φ s = (∫ s in t..0, φ s) + ∫ s in Ioi 0, φ s := fun t =>
    (intervalIntegral.integral_interval_add_Ioi (hi t) (hi 0)).symm
  have hd1 : HasDerivAt (fun t => ∫ s in t..0, φ s) (-φ τ) τ :=
    intervalIntegral.integral_hasDerivAt_left (hφ.intervalIntegrable _ _)
      (hφ.stronglyMeasurableAtFilter _ _) hφ.continuousAt
  rw [show (fun τ => ∫ s in Ioi τ, φ s) = fun t => (∫ s in t..0, φ s) + ∫ s in Ioi 0, φ s from
    funext hF]
  exact hd1.add_const _

/-- `gr d T g` solves `y' = A₀ y + g`. -/
theorem hasDerivAt_gr (g : ℝ →ᵇ E) (τ : ℝ) :
    HasDerivAt (gr d T g) (A₀ (gr d T g τ) + g τ) τ := by
  set ψ : ℝ → E := fun s => exp ((-s) • A₀) (d.P (g s))
  set φ : ℝ → E := fun s => exp ((-s) • A₀) (g s - d.P (g s))
  have hψ : Continuous ψ := ((continuous_exp_smul A₀).comp continuous_neg).clm_apply
    (d.P.continuous.comp g.continuous)
  have hφ : Continuous φ := ((continuous_exp_smul A₀).comp continuous_neg).clm_apply
    (g.continuous.sub (d.P.continuous.comp g.continuous))
  have hc : HasDerivAt (fun τ => (∫ s in T..τ, ψ s) - ∫ s in Ioi τ, φ s) (ψ τ - -φ τ) τ :=
    (intervalIntegral.integral_hasDerivAt_right (hψ.intervalIntegrable _ _)
      (hψ.stronglyMeasurableAtFilter _ _) hψ.continuousAt).sub
      (hasDerivAt_integral_Ioi hφ (integrableOn_grQ' g) τ)
  have he := hasDerivAt_exp_smul_const' (𝕂 := ℝ) A₀ τ
  have hgr : gr d T g = fun τ => exp (τ • A₀) ((∫ s in T..τ, ψ s) - ∫ s in Ioi τ, φ s) := by
    funext τ; rw [gr, grP_eq, grQ_eq, map_sub]
  rw [hgr]
  refine (he.clm_apply hc).congr_deriv ?_
  simp only [clm_mul_apply, ψ, φ, sub_neg_eq_add, ← map_add, add_sub_cancel]
  rw [← clm_mul_apply (exp (τ • A₀)), exp_smul_mul_neg]
  rfl

theorem continuous_gr (g : ℝ →ᵇ E) : Continuous (gr d T g) :=
  continuous_iff_continuousAt.2 fun τ => (hasDerivAt_gr g τ).continuousAt

end ConleyCheck.Palmer
