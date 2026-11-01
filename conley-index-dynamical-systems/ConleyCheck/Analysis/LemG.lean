import Mathlib

/-!
# The vector field of the double

Lemma `lem:G`. For `g ∈ C³` with `g(±1) = 0` and `g > 0` on `(-1, 1)`, the function
`G(θ) = -g(cos θ)/sin θ` extends to an odd, `2π`-periodic `C¹` function with `G < 0` on `(0, π)`,
`G > 0` on `(-π, 0)`, `G(0) = G(π) = 0`, `G'(0) = g'(1)/2` and `G'(π) = g'(-1)/2`.

The proof factors `g(τ) = (1 - τ²) h(τ)` with `h ∈ C¹` (`exists_div_sub`, applied twice), so that
`G(θ) = -sin θ · h(cos θ)`. Here `g` is assumed `C³` on `ℝ`; only its values on `[-1, 1]` enter.
-/

namespace ConleyCheck

open Set Function Real MeasureTheory

/-- An integral over `[0, 1]` of a jointly `Cⁿ` integrand is `Cⁿ` in the parameter. -/
theorem contDiff_integral_param :
    ∀ (n : ℕ) {F : ℝ → ℝ → ℝ}, ContDiff ℝ n (uncurry F) →
      ContDiff ℝ n (fun x => ∫ t in (0 : ℝ)..1, F x t)
  | 0, F, hF => by
    rw [Nat.cast_zero, contDiff_zero] at hF ⊢
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0 1
  | n + 1, F, hF => by
    set P : ℝ → ℝ → ℝ := fun x t => fderiv ℝ (uncurry F) (x, t) (1, 0)
    have hP : ContDiff ℝ n (uncurry P) :=
      (hF.fderiv_right (m := n) (le_of_eq (Nat.cast_succ n).symm)).clm_apply contDiff_const
    have hFc : Continuous (uncurry F) := hF.continuous
    have hd : ∀ x t, HasDerivAt (fun y => F y t) (P x t) x := fun x t => by
      have h1 : HasFDerivAt (uncurry F) (fderiv ℝ (uncurry F) (x, t)) (x, t) :=
        (hF.differentiable (by simp)).differentiableAt.hasFDerivAt
      have h2 : HasDerivAt (fun y : ℝ => (y, t)) (1, 0) x :=
        (hasDerivAt_id x).prodMk (hasDerivAt_const x t)
      exact h1.comp_hasDerivAt x h2
    have hI : ∀ x, HasDerivAt (fun y => ∫ t in (0 : ℝ)..1, F y t) (∫ t in (0 : ℝ)..1, P x t) x :=
      fun x => by
        obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_Icc (a := (0 : ℝ))
          (b := 1))).exists_bound_of_continuousOn hP.continuous.continuousOn
        refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
          (bound := fun _ => C) (F' := P) (Metric.ball_mem_nhds x one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
        · exact Filter.Eventually.of_forall fun y =>
            (show Continuous (F y) from hFc.comp (continuous_const.prodMk continuous_id))
              |>.aestronglyMeasurable
        · exact (show Continuous (F x) from hFc.comp (continuous_const.prodMk continuous_id))
            |>.intervalIntegrable 0 1
        · exact (show Continuous (P x) from
            hP.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
        · refine Filter.Eventually.of_forall fun t ht y hy =>
            hC (y, t) ⟨Metric.ball_subset_closedBall hy, ?_⟩
          rw [uIoc_of_le zero_le_one] at ht
          exact Ioc_subset_Icc_self ht
        · exact intervalIntegrable_const
        · exact Filter.Eventually.of_forall fun t _ y _ => hd y t
    have hderiv : deriv (fun y => ∫ t in (0 : ℝ)..1, F y t) = fun x => ∫ t in (0 : ℝ)..1, P x t :=
      funext fun x => (hI x).deriv
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hI x).differentiableAt, fun h => absurd h (by simp), ?_⟩
    rw [hderiv]
    exact contDiff_integral_param n hP

/-- Division by a linear factor loses one derivative: `f(x) = f(a) + (x - a) q(x)` with `q ∈ Cⁿ`
for `f ∈ Cⁿ⁺¹`. -/
theorem exists_div_sub {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ ((n : WithTop ℕ∞) + 1) f) (a : ℝ) :
    ∃ q : ℝ → ℝ, ContDiff ℝ n q ∧ ∀ x, f x = f a + (x - a) * q x := by
  have hd : ContDiff ℝ n (deriv f) := (contDiff_succ_iff_deriv.1 hf).2.2
  have hdiff : Differentiable ℝ f := (contDiff_succ_iff_deriv.1 hf).1
  refine ⟨fun x => ∫ t in (0 : ℝ)..1, deriv f (a + t * (x - a)), ?_, fun x => ?_⟩
  · exact contDiff_integral_param n (F := fun x t => deriv f (a + t * (x - a)))
      (hd.comp (contDiff_const.add (contDiff_snd.mul (contDiff_fst.sub contDiff_const))))
  · have hφ : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t => f (a + t * (x - a)))
        (deriv f (a + t * (x - a)) * (x - a)) t := fun t _ => by
      have h1 : HasDerivAt (fun t : ℝ => a + t * (x - a)) (x - a) t := by
        simpa using ((hasDerivAt_id t).mul_const (x - a)).const_add a
      exact (hdiff _).hasDerivAt.comp t h1
    have hint : IntervalIntegrable (fun t => deriv f (a + t * (x - a)) * (x - a)) volume 0 1 :=
      ((hd.continuous.comp (continuous_const.add (continuous_id.mul continuous_const))).mul
        continuous_const).intervalIntegrable 0 1
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hφ hint
    rw [intervalIntegral.integral_mul_const] at h
    simp only [one_mul, zero_mul, add_zero, add_sub_cancel] at h
    show f x = f a + (x - a) * ∫ t in (0 : ℝ)..1, deriv f (a + t * (x - a))
    rw [mul_comm]
    linarith

/-- Lemma `lem:G`. -/
theorem lem_G {g : ℝ → ℝ} (hg : ContDiff ℝ 3 g) (h1 : g 1 = 0) (hm1 : g (-1) = 0)
    (hpos : ∀ τ ∈ Ioo (-1 : ℝ) 1, 0 < g τ) :
    ∃ G : ℝ → ℝ, ContDiff ℝ 1 G ∧ Periodic G (2 * π) ∧ (∀ θ, G (-θ) = -G θ) ∧
      (∀ θ, sin θ ≠ 0 → G θ = -g (cos θ) / sin θ) ∧
      (∀ θ ∈ Ioo 0 π, G θ < 0) ∧ (∀ θ ∈ Ioo (-π) 0, 0 < G θ) ∧ G 0 = 0 ∧ G π = 0 ∧
      deriv G 0 = deriv g 1 / 2 ∧ deriv G π = deriv g (-1) / 2 := by
  obtain ⟨q₁, hq₁, hg₁⟩ := exists_div_sub (n := 2) (hg.of_le (by norm_num)) 1
  have hq₁m : q₁ (-1) = 0 := by
    have := hg₁ (-1)
    rw [hm1, h1] at this
    linarith
  obtain ⟨q₂, hq₂, hg₂⟩ := exists_div_sub (n := 1) (hq₁.of_le (by norm_num)) (-1)
  set h : ℝ → ℝ := fun x => -q₂ x with hh_def
  have hh : ContDiff ℝ 1 h := hq₂.neg.of_le (by norm_num)
  have hgh : ∀ x, g x = (1 - x ^ 2) * h x := fun x => by
    rw [hg₁ x, h1, hg₂ x, hq₁m, hh_def]
    ring
  have hhd : Differentiable ℝ h := hh.differentiable one_ne_zero
  set G : ℝ → ℝ := fun θ => -sin θ * h (cos θ) with hG_def
  have hformula : ∀ θ, sin θ ≠ 0 → G θ = -g (cos θ) / sin θ := fun θ hs => by
    rw [hgh, ← sin_sq, hG_def]
    field_simp
  have hodd : ∀ θ, G (-θ) = -G θ := fun θ => by
    simp only [hG_def, sin_neg, cos_neg]
    ring
  have hneg : ∀ θ ∈ Ioo 0 π, G θ < 0 := fun θ hθ => by
    have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    have hc1 : cos θ < 1 := by
      have := cos_lt_cos_of_nonneg_of_le_pi le_rfl hθ.2.le hθ.1
      rwa [cos_zero] at this
    have hc2 : -1 < cos θ := by
      have := cos_lt_cos_of_nonneg_of_le_pi hθ.1.le le_rfl hθ.2
      rwa [cos_pi] at this
    rw [hformula θ hs.ne']
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (hpos _ ⟨hc2, hc1⟩)) hs
  have hG' : ∀ θ, HasDerivAt G (-cos θ * h (cos θ) + -sin θ * (deriv h (cos θ) * -sin θ)) θ :=
    fun θ => (hasDerivAt_sin θ).neg.mul ((hhd (cos θ)).hasDerivAt.comp θ (hasDerivAt_cos θ))
  have hg' : ∀ x, HasDerivAt g (-(2 * x) * h x + (1 - x ^ 2) * deriv h x) x := fun x => by
    have e : g = fun x => (1 - x ^ 2) * h x := funext hgh
    rw [e]
    have h2 : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_sub 1
    exact h2.mul (hhd x).hasDerivAt
  refine ⟨G, (contDiff_sin.neg).mul (hh.comp contDiff_cos), fun θ => ?_, hodd, hformula, hneg,
    fun θ hθ => ?_, by simp [hG_def], by simp [hG_def], ?_, ?_⟩
  · simp only [hG_def, sin_add_two_pi, cos_add_two_pi]
  · have := hneg (-θ) ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    rw [hodd] at this
    linarith
  · rw [(hG' 0).deriv, (hg' 1).deriv]
    simp
    ring
  · rw [(hG' π).deriv, (hg' (-1)).deriv]
    simp

end ConleyCheck
