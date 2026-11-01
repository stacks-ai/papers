import Mathlib.Probability.Distributions.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The integral of `cosh^{-ν}`

For `ν > 0`, `∫_ℝ cosh^{-ν} ρ dρ = B(ν/2, 1/2) = √π Γ(ν/2) / Γ((ν + 1)/2)`
(`integral_cosh_rpow_neg`), the formula of eq. `eq:gap`. Each half line contributes one half
(`integral_cosh_rpow_neg_Ioi`, `integral_cosh_rpow_neg_Iic`).

The substitution `t = 1 - cosh^{-2} ρ = tanh² ρ` maps `(0, ∞)` onto `(0, 1)` and turns
`∫_0^∞ 2 cosh^{-ν}` into the Beta integral `∫_0^1 t^{-1/2} (1 - t)^{ν/2 - 1} dt`.
-/

open Real MeasureTheory Set Filter Topology

namespace ConleyCheck

/-- The real Beta integral. -/
theorem integral_beta_real {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x in Ioo (0 : ℝ) 1, x ^ (α - 1) * (1 - x) ^ (β - 1) =
      Real.Gamma α * Real.Gamma β / Real.Gamma (α + β) := by
  rw [show Real.Gamma α * Real.Gamma β / Real.Gamma (α + β) = ProbabilityTheory.beta α β from rfl,
    ProbabilityTheory.beta_eq_betaIntegralReal α β hα hβ, Complex.betaIntegral,
    intervalIntegral.integral_of_le zero_le_one, ← integral_Ioc_eq_integral_Ioo,
    ← RCLike.re_to_complex, ← integral_re]
  · refine setIntegral_congr_fun measurableSet_Ioc fun x ⟨hx1, hx₂⟩ ↦ ?_
    norm_cast
    rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow, RCLike.re_to_complex,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    all_goals linarith
  convert Complex.betaIntegral_convergent (u := α) (v := β) (by simpa) (by simpa)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp), IntegrableOn]

theorem sq_rpow {x : ℝ} (hx : 0 < x) (y : ℝ) : (x ^ 2) ^ y = x ^ (2 * y) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num

/-- `cosh^{-ν} ≤ 2^ν e^{-ν|ρ|}`. -/
theorem cosh_rpow_neg_le {ν : ℝ} (hν : 0 ≤ ν) (ρ : ℝ) :
    cosh ρ ^ (-ν) ≤ 2 ^ ν * exp (-(ν * |ρ|)) := by
  have h1 : exp |ρ| / 2 ≤ cosh ρ := by
    rw [← cosh_abs, cosh_eq]
    have := exp_pos (-|ρ|)
    linarith
  have h2 := Real.rpow_le_rpow_of_nonpos (by positivity) h1 (neg_nonpos.2 hν)
  refine h2.trans (le_of_eq ?_)
  rw [Real.div_rpow (exp_pos _).le zero_le_two, ← Real.exp_mul, Real.rpow_neg zero_le_two]
  field_simp

theorem integrableOn_cosh_rpow_neg_Ioi {ν : ℝ} (hν : 0 < ν) :
    IntegrableOn (fun ρ => cosh ρ ^ (-ν)) (Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hν).const_mul (2 ^ ν)) ?_ ?_
  · exact (continuous_cosh.rpow_const fun ρ => Or.inl (cosh_pos ρ).ne').aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun ρ hρ => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (cosh_pos _) _)]
    have := cosh_rpow_neg_le hν.le ρ
    rwa [abs_of_pos (show (0 : ℝ) < ρ from hρ), ← neg_mul] at this

theorem integrableOn_cosh_rpow_neg_Iic {ν : ℝ} (hν : 0 < ν) :
    IntegrableOn (fun ρ => cosh ρ ^ (-ν)) (Iic 0) := by
  refine Integrable.mono' ((integrableOn_exp_mul_Iic hν 0).const_mul (2 ^ ν)) ?_ ?_
  · exact (continuous_cosh.rpow_const fun ρ => Or.inl (cosh_pos ρ).ne').aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Iic fun ρ hρ => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (cosh_pos _) _)]
    have := cosh_rpow_neg_le hν.le ρ
    rwa [abs_of_nonpos (show ρ ≤ 0 from hρ), mul_neg, neg_neg] at this

theorem integrable_cosh_rpow_neg {ν : ℝ} (hν : 0 < ν) :
    Integrable (fun ρ => cosh ρ ^ (-ν)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := 0)]
  exact (integrableOn_cosh_rpow_neg_Iic hν).union (integrableOn_cosh_rpow_neg_Ioi hν)

/-- The substitution `t = 1 - cosh^{-2} ρ`. -/
noncomputable def coshSub (ρ : ℝ) : ℝ := 1 - (cosh ρ ^ 2)⁻¹

theorem hasDerivAt_coshSub (ρ : ℝ) :
    HasDerivAt coshSub (2 * sinh ρ / cosh ρ ^ 3) ρ := by
  have hc := cosh_pos ρ
  have h1 : HasDerivAt (fun x => cosh x ^ 2) (2 * cosh ρ * sinh ρ) ρ := by
    convert (hasDerivAt_cosh ρ).pow 2 using 1; simp
  have h2 := (h1.inv (by positivity : cosh ρ ^ 2 ≠ 0)).const_sub 1
  have h3 : 2 * sinh ρ / cosh ρ ^ 3 = -(-(2 * cosh ρ * sinh ρ) / (cosh ρ ^ 2) ^ 2) := by
    field_simp
  rw [h3]
  exact h2

theorem coshSub_image : coshSub '' Ioi 0 = Ioo 0 1 := by
  ext t
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    have h1 : 1 < cosh ρ := one_lt_cosh.2 (ne_of_gt hρ)
    have h2 : 1 < cosh ρ ^ 2 := by nlinarith
    have h3 : (cosh ρ ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h2
    have h4 : 0 < (cosh ρ ^ 2)⁻¹ := by positivity
    exact ⟨by simp only [coshSub]; linarith, by simp only [coshSub]; linarith⟩
  · rintro ⟨h0, h1⟩
    have hs : √t ∈ Ioo (0 : ℝ) 1 := ⟨Real.sqrt_pos.2 h0, by
      rw [Real.sqrt_lt' one_pos]; simpa using h1⟩
    have hs' : √t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hs.1], hs.2⟩
    refine ⟨artanh √t, artanh_pos hs, ?_⟩
    rw [coshSub, cosh_artanh hs', Real.sq_sqrt h0.le, div_pow, one_pow,
      Real.sq_sqrt (by linarith), inv_div, div_one]
    ring

theorem coshSub_injOn : InjOn coshSub (Ioi 0) := by
  intro x hx y hy hxy
  simp only [coshSub, sub_right_inj, inv_inj] at hxy
  have hc : cosh x = cosh y := (pow_left_inj₀ (cosh_pos x).le (cosh_pos y).le two_ne_zero).1 hxy
  have hx' : |x| = |y| := le_antisymm (cosh_le_cosh.1 hc.le) (cosh_le_cosh.1 hc.ge)
  rwa [abs_of_pos (show (0 : ℝ) < x from hx), abs_of_pos (show (0 : ℝ) < y from hy)] at hx'

theorem coshSub_integrand {ν ρ : ℝ} (hρ : 0 < ρ) :
    |2 * sinh ρ / cosh ρ ^ 3| • (coshSub ρ ^ ((1 : ℝ) / 2 - 1) * (1 - coshSub ρ) ^ (ν / 2 - 1)) =
      2 * cosh ρ ^ (-ν) := by
  have hc := cosh_pos ρ
  have hs : 0 < sinh ρ := sinh_pos_iff.2 hρ
  have e1 : coshSub ρ = (sinh ρ / cosh ρ) ^ 2 := by
    rw [coshSub, div_pow, sinh_sq]
    field_simp
  have e2 : 1 - coshSub ρ = (cosh ρ ^ 2)⁻¹ := by rw [coshSub]; ring
  rw [e2, e1, sq_rpow (div_pos hs hc), Real.inv_rpow (by positivity), sq_rpow hc,
    ← Real.rpow_neg hc.le, abs_of_pos (by positivity), smul_eq_mul]
  rw [show 2 * ((1 : ℝ) / 2 - 1) = -1 by norm_num, Real.rpow_neg_one,
    show -(2 * (ν / 2 - 1)) = 2 + -ν by ring, Real.rpow_add hc,
    show cosh ρ ^ (2 : ℝ) = cosh ρ ^ 2 from Real.rpow_two _]
  have := Real.rpow_pos_of_pos hc (-ν)
  field_simp

/-- `∫_0^∞ cosh^{-ν} = √π Γ(ν/2) / (2 Γ((ν + 1)/2))`. -/
theorem integral_cosh_rpow_neg_Ioi {ν : ℝ} (hν : 0 < ν) :
    ∫ ρ in Ioi 0, cosh ρ ^ (-ν) = √π * Real.Gamma (ν / 2) / Real.Gamma ((ν + 1) / 2) / 2 := by
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun ρ _ => (hasDerivAt_coshSub ρ).hasDerivWithinAt) coshSub_injOn
    (fun t => t ^ ((1 : ℝ) / 2 - 1) * (1 - t) ^ (ν / 2 - 1))
  rw [coshSub_image, integral_beta_real one_half_pos (by positivity), Real.Gamma_one_half_eq,
    setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => coshSub_integrand hρ,
    integral_const_mul, show (1 : ℝ) / 2 + ν / 2 = (ν + 1) / 2 by ring] at key
  linarith

theorem integral_cosh_rpow_neg_Iic {ν : ℝ} (hν : 0 < ν) :
    ∫ ρ in Iic 0, cosh ρ ^ (-ν) = √π * Real.Gamma (ν / 2) / Real.Gamma ((ν + 1) / 2) / 2 := by
  rw [← integral_cosh_rpow_neg_Ioi hν, ← neg_zero, ← integral_comp_neg_Ioi]
  simp [cosh_neg]

/-- Eq. `eq:gap`: `∫_ℝ cosh^{-ν} = √π Γ(ν/2) / Γ((ν + 1)/2)`. -/
theorem integral_cosh_rpow_neg {ν : ℝ} (hν : 0 < ν) :
    ∫ ρ, cosh ρ ^ (-ν) = √π * Real.Gamma (ν / 2) / Real.Gamma ((ν + 1) / 2) := by
  rw [← intervalIntegral.integral_Iic_add_Ioi (integrableOn_cosh_rpow_neg_Iic hν)
    (integrableOn_cosh_rpow_neg_Ioi hν), integral_cosh_rpow_neg_Iic hν,
    integral_cosh_rpow_neg_Ioi hν]
  ring

end ConleyCheck
