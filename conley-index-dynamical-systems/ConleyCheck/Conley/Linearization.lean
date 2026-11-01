import Mathlib

/-!
# Linearization of a flow at an equilibrium

Let `ϕ` be the flow of a vector field `f` with `f` differentiable at a fixed point `e`, and put
`A = Df(e)`. Grönwall's inequality gives the uniform linearization estimate
`‖ϕ t x - e - exp(tA)(x - e)‖ ≤ ε ‖x - e‖` for `t ∈ [0, T]` and `x` close to `e`
(`eventually_norm_flow_sub_exp_le`), and consequently `ϕ t` is differentiable at `e` with
`D(ϕ t)(e) = exp(tA)` for every `t` (`hasFDerivAt_flow`, `fderiv_flow_eq_exp`). No regularity of
the time-`t` maps away from `e` is needed.
-/

namespace ConleyCheck.Conley

open Set Filter Topology NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem gen_fixed {ϕ : Flow ℝ E} {f : E → E} {e : E}
    (hgen : ∀ x t, HasDerivAt (fun s => ϕ s x) (f (ϕ t x)) t) (hfix : ∀ t, ϕ t e = e) :
    f e = 0 := by
  have h := hgen e 0
  simp only [hfix] at h
  exact h.unique (hasDerivAt_const _ _)

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Orbits starting near a fixed point stay near it for `t ∈ [0, T]`. -/
theorem eventually_forall_Icc_dist_lt (ϕ : Flow ℝ E) {e : E} (hfix : ∀ t, ϕ t e = e) (T : ℝ)
    {r : ℝ} (hr : 0 < r) : ∀ᶠ x in 𝓝 e, ∀ t ∈ Icc 0 T, dist (ϕ t x) e < r := by
  refine isCompact_Icc.eventually_forall_of_forall_eventually fun t _ => ?_
  have hc : Continuous fun z : E × ℝ => ϕ z.2 z.1 := ϕ.continuous continuous_snd continuous_fst
  have := (hc.continuousAt (x := (e, t))).eventually (Metric.ball_mem_nhds _ hr)
  simpa [hfix] using this

omit [CompleteSpace E] in
theorem eventually_norm_sub_le {f : E → E} {e : E} {A : E →L[ℝ] E} (hd : HasFDerivAt f A e)
    (hf0 : f e = 0) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ y in 𝓝 e, ‖f y - A (y - e)‖ ≤ ε * ‖y - e‖ := by
  simpa [hf0] using hd.isLittleO.bound hε

theorem gronwallBound_zero_le {K η t : ℝ} (hK : 0 ≤ K) (hη : 0 ≤ η) :
    gronwallBound 0 K η t ≤ η * t * Real.exp (K * t) := by
  rcases hK.eq_or_lt with rfl | hK
  · simp [gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 hK.ne']
    simp only [zero_mul, zero_add]
    have h1 : Real.exp (K * t) - 1 ≤ K * t * Real.exp (K * t) := by
      have h0 := Real.add_one_le_exp (-(K * t))
      have h2 : Real.exp (-(K * t)) * Real.exp (K * t) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [mul_le_mul_of_nonneg_right h0 (Real.exp_pos (K * t)).le]
    rw [div_mul_eq_mul_div, div_le_iff₀ hK]
    nlinarith [mul_le_mul_of_nonneg_left h1 hη]

theorem hasDerivAt_exp_apply (A : E →L[ℝ] E) (v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • A) v) (A (exp (t • A) v)) t :=
  (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t)

theorem exp_neg_smul_mul (A : E →L[ℝ] E) (t : ℝ) : exp ((-t) • A) * exp (t • A) = 1 := by
  have hr : ∀ x : E →L[ℝ] E, x ∈ Metric.eball (0 : E →L[ℝ] E) (expSeries ℝ (E →L[ℝ] E)).radius :=
    fun x => (expSeries_radius_eq_top ℝ (E →L[ℝ] E)).symm ▸ edist_lt_top _ _
  rw [← exp_add_of_commute_of_mem_ball (((Commute.refl A).smul_left _).smul_right _) (hr _) (hr _),
    ← add_smul, neg_add_cancel, zero_smul, exp_zero]

section

variable {ϕ : Flow ℝ E} {f : E → E} {e : E} {A : E →L[ℝ] E}

/-- Uniform linearization near a fixed point, on a compact time interval. -/
theorem eventually_norm_flow_sub_exp_le
    (hgen : ∀ x t, HasDerivAt (fun s => ϕ s x) (f (ϕ t x)) t) (hfix : ∀ t, ϕ t e = e)
    (hd : HasFDerivAt f A e) {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 e, ∀ t ∈ Icc 0 T, ‖ϕ t x - e - exp (t • A) (x - e)‖ ≤ ε * ‖x - e‖ := by
  have hf0 := gen_fixed hgen hfix
  set K₁ := ‖A‖ + 1 with hK₁
  set η := ε / ((T + 1) * Real.exp (K₁ * T) * Real.exp (‖A‖ * T)) with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1
    ((eventually_norm_sub_le hd hf0 one_pos).and (eventually_norm_sub_le hd hf0 hη))
  filter_upwards [eventually_forall_Icc_dist_lt ϕ hfix T hr] with x hx t ht
  have hy' : ∀ s, HasDerivAt (fun s => ϕ s x - e) (f (ϕ s x)) s :=
    fun s => (hgen x s).sub_const e
  have hcont : Continuous fun s => ϕ s x - e :=
    continuous_iff_continuousAt.2 fun s => (hy' s).continuousAt
  have hb1 : ∀ s ∈ Ico 0 T, ‖f (ϕ s x)‖ ≤ K₁ * ‖ϕ s x - e‖ + 0 := by
    intro s hs
    have h1 := (hball (hx s (Ico_subset_Icc_self hs))).1
    calc ‖f (ϕ s x)‖ ≤ ‖A (ϕ s x - e)‖ + ‖f (ϕ s x) - A (ϕ s x - e)‖ := norm_le_insert' _ _
      _ ≤ ‖A‖ * ‖ϕ s x - e‖ + 1 * ‖ϕ s x - e‖ := add_le_add (A.le_opNorm _) h1
      _ = K₁ * ‖ϕ s x - e‖ + 0 := by ring
  have hbd : ∀ s ∈ Icc 0 T, ‖ϕ s x - e‖ ≤ ‖x - e‖ * Real.exp (K₁ * s) := by
    intro s hs
    have := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun s => ϕ s x - e)
      (f' := fun s => f (ϕ s x)) (δ := ‖x - e‖) (a := 0) (b := T) hcont.continuousOn
      (fun s _ => (hy' s).hasDerivWithinAt) (by simp) hb1 s hs
    simpa [gronwallBound_ε0] using this
  have hz' : ∀ s, HasDerivAt (fun s => ϕ s x - e - exp (s • A) (x - e))
      (f (ϕ s x) - A (exp (s • A) (x - e))) s :=
    fun s => (hy' s).sub (hasDerivAt_exp_apply A (x - e) s)
  have hzc : Continuous fun s => ϕ s x - e - exp (s • A) (x - e) :=
    continuous_iff_continuousAt.2 fun s => (hz' s).continuousAt
  have hb2 : ∀ s ∈ Ico 0 T, ‖f (ϕ s x) - A (exp (s • A) (x - e))‖ ≤
      ‖A‖ * ‖ϕ s x - e - exp (s • A) (x - e)‖ + η * Real.exp (K₁ * T) * ‖x - e‖ := by
    intro s hs
    have hs' := Ico_subset_Icc_self hs
    have h2 := (hball (hx s hs')).2
    have h3 := hbd s hs'
    have h4 : Real.exp (K₁ * s) ≤ Real.exp (K₁ * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs'.2 (by positivity))
    have e1 : f (ϕ s x) - A (exp (s • A) (x - e)) =
        A (ϕ s x - e - exp (s • A) (x - e)) + (f (ϕ s x) - A (ϕ s x - e)) := by
      simp only [map_sub]; abel
    rw [e1]
    calc _ ≤ ‖A (ϕ s x - e - exp (s • A) (x - e))‖ + ‖f (ϕ s x) - A (ϕ s x - e)‖ :=
          norm_add_le _ _
      _ ≤ ‖A‖ * ‖ϕ s x - e - exp (s • A) (x - e)‖ + η * (‖x - e‖ * Real.exp (K₁ * T)) :=
          add_le_add (A.le_opNorm _) (h2.trans (mul_le_mul_of_nonneg_left
            (h3.trans (mul_le_mul_of_nonneg_left h4 (norm_nonneg _))) hη.le))
      _ = _ := by ring
  have hz0 : ‖ϕ 0 x - e - exp ((0 : ℝ) • A) (x - e)‖ ≤ 0 := by simp
  have hz := norm_le_gronwallBound_of_norm_deriv_right_le hzc.continuousOn
    (fun s _ => (hz' s).hasDerivWithinAt) hz0 hb2 t ht
  rw [sub_zero] at hz
  refine hz.trans ((gronwallBound_zero_le (norm_nonneg A) (by positivity)).trans ?_)
  have key : η * ((T + 1) * Real.exp (K₁ * T) * Real.exp (‖A‖ * T)) = ε :=
    div_mul_cancel₀ _ (by positivity)
  calc η * Real.exp (K₁ * T) * ‖x - e‖ * t * Real.exp (‖A‖ * t)
      ≤ η * Real.exp (K₁ * T) * ‖x - e‖ * (T + 1) * Real.exp (‖A‖ * T) := by
        gcongr <;> linarith [ht.2]
    _ = ε * ‖x - e‖ := by rw [← key]; ring

theorem hasFDerivAt_flow_of_nonneg
    (hgen : ∀ x t, HasDerivAt (fun s => ϕ s x) (f (ϕ t x)) t) (hfix : ∀ t, ϕ t e = e)
    (hd : HasFDerivAt f A e) {t : ℝ} (ht : 0 ≤ t) : HasFDerivAt (ϕ t) (exp (t • A)) e := by
  refine HasFDerivAt.of_isLittleO (Asymptotics.isLittleO_iff.2 fun ε hε => ?_)
  filter_upwards [eventually_norm_flow_sub_exp_le hgen hfix hd ht hε] with x hx
  simpa [hfix] using hx t ⟨ht, le_rfl⟩

/-- The time-`t` map of the flow is differentiable at a fixed point, with derivative `exp(tA)`,
`A = Df(e)`. Negative times reduce to the reversed flow, generated by `-f`. -/
theorem hasFDerivAt_flow
    (hgen : ∀ x t, HasDerivAt (fun s => ϕ s x) (f (ϕ t x)) t) (hfix : ∀ t, ϕ t e = e)
    (hd : HasFDerivAt f A e) (t : ℝ) : HasFDerivAt (ϕ t) (exp (t • A)) e := by
  rcases le_total 0 t with ht | ht
  · exact hasFDerivAt_flow_of_nonneg hgen hfix hd ht
  · have hgen' : ∀ x t, HasDerivAt (fun s => ϕ.reverse s x) ((-f) (ϕ.reverse t x)) t := by
      intro x s
      have h := (hgen x (-s)).scomp s (hasDerivAt_neg s)
      simp only [Function.comp_def, neg_one_smul] at h
      simpa [Flow.reverse_apply] using h
    have hfix' : ∀ t, ϕ.reverse t e = e := fun s => hfix (-s)
    have h := hasFDerivAt_flow_of_nonneg hgen' hfix' hd.neg (neg_nonneg.2 ht)
    have hrev : ϕ.reverse (-t) = ϕ t := funext fun x => by simp [Flow.reverse_apply]
    rwa [hrev, neg_smul_neg] at h

/-- The linearized flow at a fixed point is `exp(tA)` with `A = Df(e)`. -/
theorem fderiv_flow_eq_exp
    (hgen : ∀ x t, HasDerivAt (fun s => ϕ s x) (f (ϕ t x)) t) (hfix : ∀ t, ϕ t e = e)
    (hd : HasFDerivAt f A e) (t : ℝ) : fderiv ℝ (ϕ t) e = exp (t • A) :=
  (hasFDerivAt_flow hgen hfix hd t).fderiv

end

end ConleyCheck.Conley
