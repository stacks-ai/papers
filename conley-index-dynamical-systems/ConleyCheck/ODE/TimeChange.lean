import Mathlib

/-!
# Time changes

`exists_timeChange`: for a continuous `b ≥ b₀ > 0` on `ℝ` there is a `C¹` bijection `ρ` of `ℝ`
with `ρ 0 = 0` and `ρ' = 1/b(ρ)`. If `f' = b · F` along a curve, then `(f ∘ ρ)' = F ∘ ρ`
(`hasDerivAt_timeChange`). This removes a positive time change from a solution.
-/

open Set Filter Topology

namespace ConleyCheck.ODE

theorem exists_timeChange {b : ℝ → ℝ} (hb : Continuous b) {b₀ : ℝ} (hb₀ : 0 < b₀)
    (hbl : ∀ t, b₀ ≤ b t) : ∃ ρ : ℝ → ℝ, ρ 0 = 0 ∧ ∀ s, HasDerivAt ρ (b (ρ s))⁻¹ s := by
  set σ : ℝ → ℝ := fun t => ∫ x in (0 : ℝ)..t, b x
  have hσ : ∀ t, HasDerivAt σ (b t) t := fun t => (hb.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hσc : Continuous σ := continuous_iff_continuousAt.2 fun t => (hσ t).continuousAt
  have hmono : StrictMono σ :=
    strictMono_of_deriv_pos fun t => by rw [(hσ t).deriv]; exact hb₀.trans_le (hbl t)
  have hd : ∀ t, HasDerivAt (fun t => σ t - b₀ * t) (b t - b₀) t := fun t => by
    have := (hσ t).sub ((hasDerivAt_id' t).const_mul b₀)
    simp only [mul_one] at this
    exact this
  have hlin : Monotone fun t => σ t - b₀ * t :=
    monotone_of_deriv_nonneg (fun t => (hd t).differentiableAt)
      fun t => by rw [(hd t).deriv]; linarith [hbl t]
  have hσ0 : σ 0 = 0 := intervalIntegral.integral_same
  have htop : Tendsto σ atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_id.const_mul_atTop hb₀)
    filter_upwards [eventually_ge_atTop 0] with t ht
    have := hlin ht
    simp only [hσ0, mul_zero, sub_zero] at this
    simp only [id]; linarith
  have hbot : Tendsto σ atBot atBot := by
    refine tendsto_atBot_mono' atBot ?_ (tendsto_id.const_mul_atBot hb₀)
    filter_upwards [eventually_le_atBot 0] with t ht
    have := hlin ht
    simp only [hσ0, mul_zero, sub_zero] at this
    simp only [id]; linarith
  have hsurj : Function.Surjective σ := hσc.surjective htop hbot
  set e := StrictMono.orderIsoOfSurjective σ hmono hsurj
  refine ⟨e.symm, ?_, fun s => ?_⟩
  · apply e.injective
    rw [OrderIso.apply_symm_apply]
    exact hσ0.symm
  · have hc : ContinuousAt e.symm s := e.symm.continuous.continuousAt
    have hd := hσ (e.symm s)
    refine HasDerivAt.of_local_left_inverse hc hd (hb₀.trans_le (hbl _)).ne' ?_
    exact Eventually.of_forall fun y => e.apply_symm_apply y

theorem hasDerivAt_timeChange {ρ f b F : ℝ → ℝ} {s : ℝ} (hρ : HasDerivAt ρ (b (ρ s))⁻¹ s)
    (hf : HasDerivAt f (b (ρ s) * F (ρ s)) (ρ s)) (hb : b (ρ s) ≠ 0) :
    HasDerivAt (fun r => f (ρ r)) (F (ρ s)) s := by
  have := hf.comp s hρ
  refine this.congr_deriv ?_
  field_simp

end ConleyCheck.ODE
