import Mathlib

/-!
# Proposition `prop:Hcrit`(ii)

Under Hypothesis H, namely `f (t, x) = F (σ t, x)` with `σ' = g ∘ σ`, the time derivative of `f` is
bounded on compacts by a multiple of `σ'`, `σ'` is integrable with total integral `2`, and `σ'`
decays exponentially at `±∞` when `g'(±1) ≠ 0`.
-/

open Set Filter Topology MeasureTheory Function

namespace ConleyCheck

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- The chain rule bound `sup_K |∂ₜ f| ≤ C_K σ'`. -/
theorem hcrit_bound {g σ : ℝ → ℝ} {F : ℝ → E → E'} (hF : ContDiff ℝ 1 (uncurry F))
    (hσ : ∀ t, HasDerivAt σ (g (σ t)) t) (hσm : ∀ t, σ t ∈ Icc (-1 : ℝ) 1)
    (hg : ∀ τ ∈ Icc (-1 : ℝ) 1, 0 ≤ g τ) {K : Set E} (hK : IsCompact K) :
    ∃ C, ∀ t, ∀ x ∈ K,
      HasDerivAt (fun s => F (σ s) x) (g (σ t) • fderiv ℝ (uncurry F) (σ t, x) (1, 0)) t ∧
      ‖deriv (fun s => F (σ s) x) t‖ ≤ C * g (σ t) := by
  set P : ℝ × E → E' := fun p => fderiv ℝ (uncurry F) p (1, 0)
  have hPc : Continuous P := (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hPc.continuousOn
  have hd : ∀ t x, HasDerivAt (fun s => F (σ s) x) (g (σ t) • P (σ t, x)) t := by
    intro t x
    have h1 : HasFDerivAt (uncurry F) (fderiv ℝ (uncurry F) (σ t, x)) (σ t, x) :=
      ((hF.differentiable one_ne_zero) _).hasFDerivAt
    have h2 : HasDerivAt (fun s => (σ s, x)) (g (σ t), (0 : E)) t :=
      (hσ t).prodMk (hasDerivAt_const t x)
    have h3 := h1.comp_hasDerivAt t h2
    have e : ((g (σ t), (0 : E)) : ℝ × E) = g (σ t) • ((1 : ℝ), (0 : E)) := by simp
    rw [e, map_smul] at h3
    exact h3
  refine ⟨C, fun t x hx => ⟨hd t x, ?_⟩⟩
  rw [(hd t x).deriv, norm_smul, Real.norm_of_nonneg (hg _ (hσm t)), mul_comm]
  exact mul_le_mul_of_nonneg_right (hC _ ⟨hσm t, hx⟩) (hg _ (hσm t))

/-- `σ'` is integrable over `ℝ` with `∫ σ' = 2`. -/
theorem hcrit_integrable {g σ : ℝ → ℝ} (hgc : Continuous g)
    (hσ : ∀ t, HasDerivAt σ (g (σ t)) t) (hσm : ∀ t, σ t ∈ Icc (-1 : ℝ) 1)
    (hg : ∀ τ ∈ Icc (-1 : ℝ) 1, 0 ≤ g τ)
    (htop : Tendsto σ atTop (𝓝 1)) (hbot : Tendsto σ atBot (𝓝 (-1))) :
    Integrable (fun t => g (σ t)) ∧ ∫ t, g (σ t) = 2 := by
  have hσc : Continuous σ := continuous_iff_continuousAt.2 fun t => (hσ t).continuousAt
  have hc : Continuous fun t => g (σ t) := hgc.comp hσc
  have hint : Integrable (fun t => g (σ t)) := by
    refine integrable_of_intervalIntegral_norm_bounded (l := atTop) (a := fun n : ℝ => -n)
      (b := id) 2 (fun i => hc.integrableOn_Ioc) tendsto_neg_atTop_atBot tendsto_id ?_
    filter_upwards [eventually_ge_atTop 0] with n _
    have : ∫ x in -n..id n, ‖g (σ x)‖ = ∫ x in -n..id n, g (σ x) :=
      intervalIntegral.integral_congr fun x _ => Real.norm_of_nonneg (hg _ (hσm x))
    rw [this, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hσ x)
      (hc.intervalIntegrable _ _)]
    linarith [(hσm (id n)).2, (hσm (-n)).1]
  refine ⟨hint, ?_⟩
  rw [integral_of_hasDerivAt_of_tendsto hσ hint hbot htop]
  norm_num

/-- Exponential decay of `σ'` as `t → +∞` when `g'(1) ≠ 0`. -/
theorem hcrit_decay_top {g σ : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hσ : ∀ t, HasDerivAt σ (g (σ t)) t) (hσm : ∀ t, σ t ∈ Ioo (-1 : ℝ) 1)
    (htop : Tendsto σ atTop (𝓝 1)) (hg1 : g 1 = 0)
    (hgpos : ∀ τ ∈ Ioo (-1 : ℝ) 1, 0 < g τ) (hd : deriv g 1 ≠ 0) :
    ∃ C κ, 0 < κ ∧ ∀ t, 0 ≤ t → g (σ t) ≤ C * Real.exp (-κ * t) := by
  have hgd : ∀ τ, HasDerivAt g (deriv g τ) τ :=
    fun τ => ((hg.differentiable one_ne_zero) τ).hasDerivAt
  have hsl : Tendsto (slope g 1) (𝓝[<] 1) (𝓝 (deriv g 1)) :=
    (hasDerivAt_iff_tendsto_slope.1 (hgd 1)).mono_left
      (nhdsWithin_mono _ fun τ (h : τ ∈ Iio 1) => (ne_of_lt h : τ ≠ 1))
  have hle : deriv g 1 ≤ 0 := by
    refine le_of_tendsto hsl ?_
    filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with τ hτ
    rw [slope_def_field, hg1, sub_zero]
    exact (div_neg_of_pos_of_neg (hgpos τ hτ) (by linarith [hτ.2])).le
  have hneg : deriv g 1 < 0 := lt_of_le_of_ne hle hd
  set κ := -deriv g 1 / 2 with hκ
  have hκpos : 0 < κ := by rw [hκ]; linarith
  -- lower bound `g τ ≥ κ (1 - τ)` near `1`
  have hev : ∀ᶠ τ in 𝓝[<] 1, slope g 1 τ < deriv g 1 / 2 := hsl (Iio_mem_nhds (by linarith))
  obtain ⟨l, hl1, hl⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  have hlow : ∀ τ ∈ Ioo l 1, κ * (1 - τ) < g τ := by
    intro τ hτ
    have h := hl hτ
    simp only [mem_setOf_eq, slope_def_field, hg1, sub_zero] at h
    rw [div_lt_iff_of_neg (by linarith [hτ.2])] at h
    rw [hκ]; linarith
  -- upper bounds on `[-1, 1]`
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hg.continuous_deriv le_rfl).continuousOn (s := Icc (-1 : ℝ) 1)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuous.continuousOn
    (s := Icc (-1 : ℝ) 1)
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL 1 ⟨by norm_num, le_rfl⟩)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 1 ⟨by norm_num, le_rfl⟩)
  have hup : ∀ τ ∈ Icc (-1 : ℝ) 1, g τ ≤ L * (1 - τ) := by
    intro τ hτ
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => (hgd x).differentiableAt)
      hL (convex_Icc _ _) hτ ⟨by norm_num, le_rfl⟩
    rw [hg1, zero_sub, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ 1 - τ by linarith [hτ.2])] at h
    exact le_trans (le_abs_self _) h
  have hσ1 : ∀ t, σ t ∈ Icc (-1 : ℝ) 1 := fun t => Ioo_subset_Icc_self (hσm t)
  -- the time after which `σ` stays in `(l, 1)`
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (htop (Ioi_mem_nhds hl1))
  set T := max T₀ 0
  set u : ℝ → ℝ := fun t => (1 - σ t) * Real.exp (κ * t)
  have hu : ∀ t, HasDerivAt u ((-g (σ t)) * Real.exp (κ * t) + (1 - σ t) * (Real.exp (κ * t) * κ)) t := by
    intro t
    have h1 : HasDerivAt (fun s => 1 - σ s) (-g (σ t)) t := by
      simpa using (hσ t).const_sub 1
    have h2 : HasDerivAt (fun s => Real.exp (κ * s)) (Real.exp (κ * t) * κ) t := by
      simpa using ((hasDerivAt_id t).const_mul κ).exp
    exact h1.mul h2
  have hanti : AntitoneOn u (Ici T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici T)
      (fun t _ => (hu t).continuousAt.continuousWithinAt)
      (fun t _ => (hu t).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [interior_Ici] at ht
    rw [(hu t).deriv]
    have hσl : σ t ∈ Ioo l 1 := ⟨hT₀ t (le_trans (le_max_left _ _) (le_of_lt ht)), (hσm t).2⟩
    have := hlow _ hσl
    have he := Real.exp_pos (κ * t)
    nlinarith
  refine ⟨max (L * u T) (M * Real.exp (κ * T)), κ, hκpos, fun t ht => ?_⟩
  have hexp : Real.exp (-κ * t) * Real.exp (κ * t) = 1 := by
    rw [← Real.exp_add]; simp
  rcases le_or_gt T t with hTt | htT
  · have h1 : u t ≤ u T := hanti (mem_Ici.2 le_rfl) (mem_Ici.2 hTt) hTt
    have h2 : 1 - σ t ≤ u T * Real.exp (-κ * t) := by
      have : 1 - σ t = u t * Real.exp (-κ * t) := by
        simp only [u]; rw [mul_assoc, mul_comm (Real.exp _), hexp, mul_one]
      rw [this]
      exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    calc g (σ t) ≤ L * (1 - σ t) := hup _ (hσ1 t)
      _ ≤ L * (u T * Real.exp (-κ * t)) := mul_le_mul_of_nonneg_left h2 hL0
      _ = (L * u T) * Real.exp (-κ * t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · have h1 : g (σ t) ≤ M := le_trans (le_abs_self _) (hM _ (hσ1 t))
    have h2 : 1 ≤ Real.exp (κ * T) * Real.exp (-κ * t) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    calc g (σ t) ≤ M := h1
      _ ≤ M * (Real.exp (κ * T) * Real.exp (-κ * t)) := le_mul_of_one_le_right hM0 h2
      _ = (M * Real.exp (κ * T)) * Real.exp (-κ * t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- Exponential decay of `σ'` as `t → -∞` when `g'(-1) ≠ 0`, by reflection. -/
theorem hcrit_decay_bot {g σ : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hσ : ∀ t, HasDerivAt σ (g (σ t)) t) (hσm : ∀ t, σ t ∈ Ioo (-1 : ℝ) 1)
    (hbot : Tendsto σ atBot (𝓝 (-1))) (hgm1 : g (-1) = 0)
    (hgpos : ∀ τ ∈ Ioo (-1 : ℝ) 1, 0 < g τ) (hd : deriv g (-1) ≠ 0) :
    ∃ C κ, 0 < κ ∧ ∀ t, t ≤ 0 → g (σ t) ≤ C * Real.exp (κ * t) := by
  have hσ' : ∀ t, HasDerivAt (fun s => -σ (-s)) ((fun τ => g (-τ)) (-σ (-t))) t := by
    intro t
    have h := ((hσ (-t)).comp t (hasDerivAt_neg t)).neg
    exact h.congr_deriv (by simp)
  have hm' : ∀ t, -σ (-t) ∈ Ioo (-1 : ℝ) 1 := fun t =>
    ⟨by linarith [(hσm (-t)).2], by linarith [(hσm (-t)).1]⟩
  have htop' : Tendsto (fun s => -σ (-s)) atTop (𝓝 1) := by
    have := (hbot.comp tendsto_neg_atTop_atBot).neg
    simpa using this
  have hd' : deriv (fun τ => g (-τ)) 1 ≠ 0 := by
    rw [deriv_comp_neg]; simpa using hd
  obtain ⟨C, κ, hκ, hC⟩ := hcrit_decay_top (hg.comp contDiff_neg) hσ' hm' htop' (by simpa using hgm1)
    (fun τ hτ => hgpos _ ⟨by linarith [hτ.2], by linarith [hτ.1]⟩) hd'
  refine ⟨C, κ, hκ, fun t ht => ?_⟩
  have := hC (-t) (by linarith)
  simpa using this

/-- Proposition `prop:Hcrit`(ii). -/
theorem prop_Hcrit_ii {g σ : ℝ → ℝ} {F : ℝ → E → E'} (hF : ContDiff ℝ 1 (uncurry F))
    (hg : ContDiff ℝ 1 g) (hg1 : g 1 = 0) (hgm1 : g (-1) = 0)
    (hgpos : ∀ τ ∈ Ioo (-1 : ℝ) 1, 0 < g τ)
    (hσ : ∀ t, HasDerivAt σ (g (σ t)) t) (hσm : ∀ t, σ t ∈ Ioo (-1 : ℝ) 1)
    (htop : Tendsto σ atTop (𝓝 1)) (hbot : Tendsto σ atBot (𝓝 (-1))) {K : Set E}
    (hK : IsCompact K) :
    (∃ C, ∀ t, ∀ x ∈ K, ‖deriv (fun s => F (σ s) x) t‖ ≤ C * deriv σ t) ∧
    Integrable (deriv σ) ∧ ∫ t, deriv σ t = 2 ∧
    (deriv g 1 ≠ 0 → ∃ C κ, 0 < κ ∧ ∀ t, 0 ≤ t → deriv σ t ≤ C * Real.exp (-κ * t)) ∧
    (deriv g (-1) ≠ 0 → ∃ C κ, 0 < κ ∧ ∀ t, t ≤ 0 → deriv σ t ≤ C * Real.exp (κ * t)) := by
  have hds : deriv σ = fun t => g (σ t) := funext fun t => (hσ t).deriv
  have hσ1 : ∀ t, σ t ∈ Icc (-1 : ℝ) 1 := fun t => Ioo_subset_Icc_self (hσm t)
  have hg0 : ∀ τ ∈ Icc (-1 : ℝ) 1, 0 ≤ g τ := by
    intro τ hτ
    rcases eq_or_lt_of_le hτ.1 with h | h
    · rw [← h, hgm1]
    rcases eq_or_lt_of_le hτ.2 with h' | h'
    · rw [h', hg1]
    exact (hgpos τ ⟨h, h'⟩).le
  obtain ⟨C, hC⟩ := hcrit_bound hF hσ hσ1 hg0 hK
  obtain ⟨hi, hI⟩ := hcrit_integrable hg.continuous hσ hσ1 hg0 htop hbot
  rw [hds]
  exact ⟨⟨C, fun t x hx => (hC t x hx).2⟩, hi, hI,
    fun hd => hcrit_decay_top hg hσ hσm htop hg1 hgpos hd,
    fun hd => hcrit_decay_bot hg hσ hσm hbot hgm1 hgpos hd⟩

end ConleyCheck
