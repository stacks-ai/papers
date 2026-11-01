import Mathlib

/-!
# Quadratic Lyapunov functions for exponentially contracting linear flows

If `Λ s` is a continuous family of operators with `Λ 0 = 1`, `d/ds Λ s a = Λ s (B a)` and
`‖Λ s a‖ ≤ C e^{-cs} ‖a‖` for `s ≥ 0`, then
`P = ∫₀^{T₀} (Λ s)† Λ s ds + τ` is positive definite and
`⟪a, P (B a)⟫ + ⟪B a, P a⟫ ≤ -‖a‖²/2` (`exists_lyapunov`).
-/

namespace ConleyCheck.Conley

open Set Filter Topology intervalIntegral
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem exists_lyapunov {Λ : ℝ → V →L[ℝ] V} (hΛc : Continuous Λ) (hΛ0 : ∀ a, Λ 0 a = a)
    {B : V →L[ℝ] V} (hΛ' : ∀ s a, HasDerivAt (fun s => Λ s a) (Λ s (B a)) s) {C c : ℝ}
    (hc : 0 < c) (hest : ∀ s, 0 ≤ s → ∀ a, ‖Λ s a‖ ≤ C * Real.exp (-(c * s)) * ‖a‖) :
    ∃ P : V →L[ℝ] V, ∃ τ > 0, ∀ a,
      τ * ‖a‖ ^ 2 ≤ ⟪a, P a⟫ ∧ ⟪a, P (B a)⟫ + ⟪B a, P a⟫ ≤ -(1 / 2) * ‖a‖ ^ 2 := by
  set T₀ := Real.log (4 * C ^ 2 + 1) / (2 * c) with hT₀
  have hlog : 0 ≤ Real.log (4 * C ^ 2 + 1) := Real.log_nonneg (by nlinarith [sq_nonneg C])
  have hT₀0 : 0 ≤ T₀ := div_nonneg hlog (by positivity)
  have hexp : C ^ 2 * Real.exp (-(c * T₀)) ^ 2 ≤ 1 / 4 := by
    have h1 : -(c * T₀) + -(c * T₀) = -Real.log (4 * C ^ 2 + 1) := by
      rw [hT₀]; field_simp; ring
    rw [sq (Real.exp _), ← Real.exp_add, h1, Real.exp_neg, Real.exp_log (by positivity),
      ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    nlinarith
  set G : ℝ → V →L[ℝ] V := fun s => (ContinuousLinearMap.adjoint (Λ s)).comp (Λ s) with hG
  have hGc : Continuous G :=
    (ContinuousLinearMap.adjoint.continuous.comp hΛc).clm_comp hΛc
  set P₀ := ∫ s in (0 : ℝ)..T₀, G s with hP₀def
  have hP₀ : ∀ x y, ⟪x, P₀ y⟫ = ∫ s in (0 : ℝ)..T₀, ⟪Λ s x, Λ s y⟫ := by
    intro x y
    rw [ContinuousLinearMap.intervalIntegral_apply (hGc.intervalIntegrable _ _)]
    have hi : IntervalIntegrable (fun s => G s y) MeasureTheory.volume 0 T₀ :=
      (hGc.clm_apply continuous_const).intervalIntegrable _ _
    have := ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℝ x) hi
    simp only [innerSL_apply_apply] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp [hG, ContinuousLinearMap.adjoint_inner_right]
  set τ := 1 / (8 * (‖B‖ + 1)) with hτ
  have hτ0 : 0 < τ := by positivity
  refine ⟨P₀ + τ • ContinuousLinearMap.id ℝ V, τ, hτ0, fun a => ⟨?_, ?_⟩⟩
  · have h1 : 0 ≤ ⟪a, P₀ a⟫ := by
      rw [hP₀]
      exact intervalIntegral.integral_nonneg hT₀0 fun s _ => real_inner_self_nonneg
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    linarith
  · have hcont : ∀ w : V, Continuous fun s => Λ s w := fun w => hΛc.clm_apply continuous_const
    have hder : ∀ s, HasDerivAt (fun s => ⟪Λ s a, Λ s a⟫)
        (⟪Λ s a, Λ s (B a)⟫ + ⟪Λ s (B a), Λ s a⟫) s :=
      fun s => (hΛ' s a).inner ℝ (hΛ' s a)
    have hi1 : IntervalIntegrable (fun s => ⟪Λ s a, Λ s (B a)⟫) MeasureTheory.volume 0 T₀ :=
      ((hcont a).inner (hcont (B a))).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun s => ⟪Λ s (B a), Λ s a⟫) MeasureTheory.volume 0 T₀ :=
      ((hcont (B a)).inner (hcont a)).intervalIntegrable _ _
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hder s)
      (hi1.add hi2)
    rw [intervalIntegral.integral_add hi1 hi2, hΛ0, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq] at hftc
    have hT : ‖Λ T₀ a‖ ^ 2 ≤ 1 / 4 * ‖a‖ ^ 2 := by
      have h := hest T₀ hT₀0 a
      have h2 : ‖Λ T₀ a‖ ^ 2 ≤ (C * Real.exp (-(c * T₀)) * ‖a‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
      calc ‖Λ T₀ a‖ ^ 2 ≤ (C * Real.exp (-(c * T₀)) * ‖a‖) ^ 2 := h2
        _ = C ^ 2 * Real.exp (-(c * T₀)) ^ 2 * ‖a‖ ^ 2 := by ring
        _ ≤ 1 / 4 * ‖a‖ ^ 2 := mul_le_mul_of_nonneg_right hexp (sq_nonneg _)
    have hB : ⟪a, B a⟫ + ⟪B a, a⟫ ≤ 2 * ‖B‖ * ‖a‖ ^ 2 := by
      have h1 := real_inner_le_norm a (B a)
      have h2 := real_inner_le_norm (B a) a
      have h3 := B.le_opNorm a
      nlinarith [norm_nonneg a, norm_nonneg (B a)]
    have hτB : τ * (2 * ‖B‖ * ‖a‖ ^ 2) ≤ 1 / 4 * ‖a‖ ^ 2 := by
      have : τ * (2 * ‖B‖) ≤ 1 / 4 := by
        rw [hτ, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg B]
      nlinarith [sq_nonneg ‖a‖]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, inner_add_right, real_inner_smul_right]
    rw [hP₀, hP₀]
    nlinarith [mul_le_mul_of_nonneg_left hB hτ0.le]

end ConleyCheck.Conley
