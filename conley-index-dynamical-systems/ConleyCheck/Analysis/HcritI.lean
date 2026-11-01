import Mathlib

/-!
# Proposition `prop:Hcrit`(i)

If `∂ₜ f` decays like `e^{-c|t|}` uniformly on compacts and `Dₓ f(t, ·)` converges locally
uniformly as `t → ±∞`, then `f` is asymptotically autonomous with `C¹` limits `f±`, and
`F (τ, x) = f (artanh τ / κ, x)`, `F (±1, ·) = f±`, is `C¹` on `[-1, 1] × E` for every
`κ ∈ (0, c/2)`. Here `f (t, x) = F (tanh (κ t), x)` and `σ = tanh (κ ·)` solves
`σ' = κ (1 - σ²)`.
-/

open Set Filter Topology Function

namespace ConleyCheck

noncomputable section

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-! ### Locally uniform convergence -/

theorem tlu_tendsto {ι α β : Type*} [TopologicalSpace α] [MetricSpace β] {F : ι → α → β}
    {f : α → β} {p : Filter ι} {x : α} (h : TendstoLocallyUniformly F f p)
    (hf : ContinuousAt f x) :
    Tendsto (fun q : ι × α => F q.1 q.2) (p ×ˢ 𝓝 x) (𝓝 (f x)) := by
  have h1 := tendsto_uniformity_iff_dist_tendsto_zero.1
    (tendstoLocallyUniformly_iff_forall_tendsto.1 h x)
  have h2 : Tendsto (fun q : ι × α => f q.2) (p ×ˢ 𝓝 x) (𝓝 (f x)) := hf.tendsto.comp tendsto_snd
  rw [tendsto_iff_dist_tendsto_zero] at h2 ⊢
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine squeeze_zero (fun _ => dist_nonneg) (fun q => ?_) h3
  calc dist (F q.1 q.2) (f x) ≤ dist (F q.1 q.2) (f q.2) + dist (f q.2) (f x) :=
        dist_triangle _ _ _
    _ = dist (f q.2) (F q.1 q.2) + dist (f q.2) (f x) := by rw [dist_comm (F q.1 q.2)]

theorem tlu_comp_index {ι ι' α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : ι → α → β} {f : α → β} {p : Filter ι} {p' : Filter ι'} {φ : ι' → ι}
    (h : TendstoLocallyUniformly F f p) (hφ : Tendsto φ p' p) :
    TendstoLocallyUniformly (fun i => F (φ i)) f p' := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto] at h ⊢
  exact fun x => (h x).comp (hφ.prodMap tendsto_id)

theorem continuousWithinAt_of_split {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {g : α → β} {S s T U : Set α} {y : α} (hU : U ∈ 𝓝 y) (hsub : S ∩ U ⊆ s ∪ T)
    (h1 : Tendsto g (𝓝[s] y) (𝓝 (g y))) (h2 : Tendsto g (𝓝[T] y) (𝓝 (g y))) :
    ContinuousWithinAt g S y := by
  unfold ContinuousWithinAt
  rw [nhdsWithin_restrict' S hU]
  have : 𝓝[S ∩ U] y ≤ 𝓝[s ∪ T] y := nhdsWithin_mono _ hsub
  rw [nhdsWithin_union] at this
  exact (tendsto_sup.2 ⟨h1, h2⟩).mono_left this

/-! ### Partial derivatives -/

section Partial

variable {f : ℝ → E → E'} (hf : ContDiff ℝ 1 (uncurry f))
include hf

theorem hasDerivAt_time (t : ℝ) (x : E) :
    HasDerivAt (fun s => f s x) (fderiv ℝ (uncurry f) (t, x) (1, 0)) t := by
  have h1 : HasFDerivAt (uncurry f) (fderiv ℝ (uncurry f) (t, x)) (t, x) :=
    ((hf.differentiable one_ne_zero) _).hasFDerivAt
  have h2 : HasDerivAt (fun s => (s, x)) ((1 : ℝ), (0 : E)) t :=
    (hasDerivAt_id' t).prodMk (hasDerivAt_const t x)
  exact h1.comp_hasDerivAt t h2

theorem hasFDerivAt_space (t : ℝ) (x : E) :
    HasFDerivAt (f t) ((fderiv ℝ (uncurry f) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) x := by
  have h1 : HasFDerivAt (uncurry f) (fderiv ℝ (uncurry f) (t, x)) (t, x) :=
    ((hf.differentiable one_ne_zero) _).hasFDerivAt
  exact h1.comp x (hasFDerivAt_prodMk_right t x)

theorem contDiff_slice (t : ℝ) : ContDiff ℝ 1 (f t) :=
  hf.comp (contDiff_const.prodMk contDiff_id)

end Partial

/-- The hypotheses of `prop:Hcrit`(i). -/
structure HcritHyp (f : ℝ → E → E') (c : ℝ) (Dp Dm : E → E →L[ℝ] E') : Prop where
  smooth : ContDiff ℝ 1 (uncurry f)
  pos : 0 < c
  decay : ∀ K, IsCompact K → ∃ A, ∀ t, ∀ x ∈ K,
    ‖deriv (fun s => f s x) t‖ ≤ A * Real.exp (-(c * |t|))
  dtop : TendstoLocallyUniformly (fun t => fderiv ℝ (f t)) Dp atTop
  dbot : TendstoLocallyUniformly (fun t => fderiv ℝ (f t)) Dm atBot

/-! ### The limits `f±` -/

section Limit

variable {f : ℝ → E → E'} {c : ℝ}

theorem tendsto_exp_neg_mul {c : ℝ} (hc : 0 < c) (A : ℝ) :
    Tendsto (fun t : ℝ => A / c * Real.exp (-(c * t))) atTop (𝓝 0) := by
  have : Tendsto (fun t : ℝ => Real.exp (-(c * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hc))
  have h := this.const_mul (A / c)
  rw [mul_zero] at h
  exact h

theorem hcrit_cauchy (hs : ContDiff ℝ 1 (uncurry f)) (hc : 0 < c) {K : Set E} {A : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀ t, ∀ x ∈ K, ‖deriv (fun s => f s x) t‖ ≤ A * Real.exp (-(c * |t|))) :
    ∀ x ∈ K, ∀ t s, 0 ≤ t → t ≤ s → ‖f s x - f t x‖ ≤ A / c * Real.exp (-(c * t)) := by
  intro x hx t s ht hts
  have hd : ∀ r, HasDerivAt (fun s => f s x) (deriv (fun s => f s x) r) r := fun r =>
    (hasDerivAt_time hs r x).differentiableAt.hasDerivAt
  have hB : ∀ r, HasDerivAt (fun r => A / c * (Real.exp (-(c * t)) - Real.exp (-(c * r))))
      (A * Real.exp (-(c * r))) r := by
    intro r
    have h1 : HasDerivAt (fun r => Real.exp (-(c * r))) (Real.exp (-(c * r)) * (-c)) r := by
      simpa using ((hasDerivAt_id' r).const_mul c).neg.exp
    have h2 := (h1.const_sub (Real.exp (-(c * t)))).const_mul (A / c)
    convert h2 using 1
    field_simp
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun r => f r x - f t x) (a := t) (b := s) (f' := fun r => deriv (fun s => f s x) r)
    (fun r _ => ((hd r).sub_const _).continuousAt.continuousWithinAt)
    (fun r _ => ((hd r).sub_const _).hasDerivWithinAt) (by simp) hB
    (fun r hr => by
      have := hA r x hx
      rwa [abs_of_nonneg (le_trans ht hr.1)] at this) (right_mem_Icc.2 hts)
  refine le_trans key ?_
  have h1 := Real.exp_pos (-(c * s))
  have h2 : 0 ≤ A / c := div_nonneg hA0 hc.le
  nlinarith

theorem hcrit_limit (hs : ContDiff ℝ 1 (uncurry f)) (hc : 0 < c) [CompleteSpace E']
    (hd : ∀ K, IsCompact K → ∃ A, ∀ t, ∀ x ∈ K,
      ‖deriv (fun s => f s x) t‖ ≤ A * Real.exp (-(c * |t|))) :
    ∃ fp : E → E', (∀ x, Tendsto (fun t => f t x) atTop (𝓝 (fp x))) ∧
      ∀ K, IsCompact K → ∃ A, 0 ≤ A ∧ ∀ x ∈ K, ∀ t, 0 ≤ t →
        ‖fp x - f t x‖ ≤ A / c * Real.exp (-(c * t)) := by
  have hd' : ∀ K, IsCompact K → ∃ A, 0 ≤ A ∧ ∀ x ∈ K, ∀ t s, 0 ≤ t → t ≤ s →
      ‖f s x - f t x‖ ≤ A / c * Real.exp (-(c * t)) := by
    intro K hK
    obtain ⟨A, hA⟩ := hd K hK
    refine ⟨max A 0, le_max_right _ _, hcrit_cauchy hs hc (le_max_right _ _) fun t x hx => ?_⟩
    exact le_trans (hA t x hx) (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hcs : ∀ x, CauchySeq (fun t => f t x) := by
    intro x
    obtain ⟨A, -, hA⟩ := hd' {x} isCompact_singleton
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN0, hN⟩ :=
      ((eventually_ge_atTop 0).and ((tendsto_exp_neg_mul hc A).eventually (gt_mem_nhds hε))).exists
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hA x (mem_singleton x) N n hN0 hn) hN
  have hlim : ∀ x, Tendsto (fun t => f t x) atTop (𝓝 (limUnder atTop fun t => f t x)) :=
    fun x => tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hcs x))
  refine ⟨fun x => limUnder atTop fun t => f t x, hlim, fun K hK => ?_⟩
  obtain ⟨A, hA0, hA⟩ := hd' K hK
  refine ⟨A, hA0, fun x hx t ht => ?_⟩
  have h1 : Tendsto (fun s => ‖f s x - f t x‖) atTop
      (𝓝 ‖(limUnder atTop fun t => f t x) - f t x‖) := ((hlim x).sub_const _).norm
  exact le_of_tendsto h1 (by filter_upwards [eventually_ge_atTop t] with s hs using hA x hx t s ht hs)

omit [NormedSpace ℝ E] [NormedSpace ℝ E'] in
theorem hcrit_tlu [ProperSpace E] {fp : E → E'} (hc : 0 < c)
    (hb : ∀ K, IsCompact K → ∃ A, 0 ≤ A ∧ ∀ x ∈ K, ∀ t, 0 ≤ t →
      ‖fp x - f t x‖ ≤ A / c * Real.exp (-(c * t))) :
    TendstoLocallyUniformly f fp atTop := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro x₀
  rw [tendsto_uniformity_iff_dist_tendsto_zero]
  obtain ⟨A, -, hA⟩ := hb _ (isCompact_closedBall x₀ 1)
  have hexp : Tendsto (fun q : ℝ × E => A / c * Real.exp (-(c * q.1))) (atTop ×ˢ 𝓝 x₀) (𝓝 0) :=
    (tendsto_exp_neg_mul hc A).comp tendsto_fst
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hexp
  filter_upwards [prod_mem_prod (Ici_mem_atTop (0 : ℝ)) (Metric.closedBall_mem_nhds x₀ one_pos)]
    with q hq
  rw [dist_eq_norm]
  exact hA q.2 hq.2 q.1 hq.1

theorem hcrit_limit_top [ProperSpace E] [CompleteSpace E'] (hs : ContDiff ℝ 1 (uncurry f))
    (hc : 0 < c)
    (hd : ∀ K, IsCompact K → ∃ A, ∀ t, ∀ x ∈ K,
      ‖deriv (fun s => f s x) t‖ ≤ A * Real.exp (-(c * |t|))) :
    ∃ fp : E → E', (∀ x, Tendsto (fun t => f t x) atTop (𝓝 (fp x))) ∧
      TendstoLocallyUniformly f fp atTop := by
  obtain ⟨fp, h1, h2⟩ := hcrit_limit hs hc hd
  exact ⟨fp, h1, hcrit_tlu hc h2⟩

theorem hcrit_limit_bot [ProperSpace E] [CompleteSpace E'] (hs : ContDiff ℝ 1 (uncurry f))
    (hc : 0 < c)
    (hd : ∀ K, IsCompact K → ∃ A, ∀ t, ∀ x ∈ K,
      ‖deriv (fun s => f s x) t‖ ≤ A * Real.exp (-(c * |t|))) :
    ∃ fm : E → E', (∀ x, Tendsto (fun t => f t x) atBot (𝓝 (fm x))) ∧
      TendstoLocallyUniformly f fm atBot := by
  have hs' : ContDiff ℝ 1 (uncurry fun t => f (-t)) :=
    hs.comp (contDiff_fst.neg.prodMk contDiff_snd)
  have hd' : ∀ K, IsCompact K → ∃ A, ∀ t, ∀ x ∈ K,
      ‖deriv (fun s => f (-s) x) t‖ ≤ A * Real.exp (-(c * |t|)) := by
    intro K hK
    obtain ⟨A, hA⟩ := hd K hK
    refine ⟨A, fun t x hx => ?_⟩
    rw [deriv_comp_neg (f := fun s => f s x), norm_neg]
    simpa using hA (-t) x hx
  obtain ⟨fm, h1, h2⟩ := hcrit_limit_top hs' hc hd'
  refine ⟨fm, fun x => ?_, ?_⟩
  · have := (h1 x).comp tendsto_neg_atBot_atTop
    simp only [Function.comp_def, neg_neg] at this
    exact this
  · have := tlu_comp_index h2 tendsto_neg_atBot_atTop
    simp only [neg_neg] at this
    exact this

theorem hcrit_limit_C1 {l : Filter ℝ} [NeBot l] {fp : E → E'} {D : E → E →L[ℝ] E'}
    (hs : ContDiff ℝ 1 (uncurry f)) (hfp : ∀ x, Tendsto (fun t => f t x) l (𝓝 (fp x)))
    (hD : TendstoLocallyUniformly (fun t => fderiv ℝ (f t)) D l) :
    Continuous D ∧ (∀ x, HasFDerivAt fp (D x) x) ∧ ContDiff ℝ 1 fp := by
  have hDc : Continuous D := hD.continuous (Frequently.of_forall fun t =>
    (contDiff_slice hs t).continuous_fderiv one_ne_zero)
  have hder : ∀ x, HasFDerivAt fp (D x) x := fun x =>
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ (tendstoLocallyUniformlyOn_univ.2 hD)
      (fun t y _ => ((contDiff_slice hs t).differentiable one_ne_zero y).hasFDerivAt)
      (fun y _ => hfp y) (mem_univ x)
  exact ⟨hDc, hder, contDiff_one_iff_hasFDerivAt.2 ⟨D, hDc, hder⟩⟩

end Limit

/-! ### Estimates in the `t` coordinate -/

section Estimates

variable {f : ℝ → E → E'} {c κ : ℝ}

theorem cosh_sq_le_exp (hκ : 0 < κ) (t : ℝ) :
    Real.cosh (κ * t) ^ 2 ≤ Real.exp (2 * κ * |t|) := by
  have h1 : Real.cosh (κ * t) ≤ Real.exp (κ * |t|) := by
    rw [← Real.cosh_abs, abs_mul, abs_of_pos hκ, Real.cosh_eq]
    have := Real.exp_le_exp.2 (show -(κ * |t|) ≤ κ * |t| by nlinarith [abs_nonneg t])
    linarith
  calc Real.cosh (κ * t) ^ 2 ≤ Real.exp (κ * |t|) ^ 2 :=
        pow_le_pow_left₀ (Real.cosh_pos _).le h1 2
    _ = Real.exp (2 * κ * |t|) := by rw [sq, ← Real.exp_add]; congr 1; ring

theorem hcrit_time_small [ProperSpace E] {l : Filter ℝ} (hl : Tendsto (fun t : ℝ => |t|) l atTop)
    (hs : ContDiff ℝ 1 (uncurry f)) (hκ : 0 < κ) (hκc : 2 * κ < c)
    (hd : ∀ K, IsCompact K → ∃ A, ∀ t, ∀ x ∈ K,
      ‖deriv (fun s => f s x) t‖ ≤ A * Real.exp (-(c * |t|))) (x₀ : E) :
    Tendsto (fun q : ℝ × E => Real.cosh (κ * q.1) ^ 2 / κ * ‖fderiv ℝ (uncurry f) q (1, 0)‖)
      (l ×ˢ 𝓝 x₀) (𝓝 0) := by
  obtain ⟨A, hA⟩ := hd _ (isCompact_closedBall x₀ 1)
  have hlim : Tendsto (fun q : ℝ × E => |A| / κ * Real.exp (-((c - 2 * κ) * |q.1|)))
      (l ×ˢ 𝓝 x₀) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => Real.exp (-((c - 2 * κ) * |t|))) l (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (hl.const_mul_atTop (by linarith)))
    have h := (this.const_mul (|A| / κ)).comp (tendsto_fst (f := l) (g := 𝓝 x₀))
    rw [mul_zero] at h
    exact h
  refine squeeze_zero' (Eventually.of_forall fun q => by positivity) ?_ hlim
  filter_upwards [tendsto_snd (Metric.closedBall_mem_nhds x₀ one_pos)] with q hq
  have hD : fderiv ℝ (uncurry f) q (1, 0) = deriv (fun s => f s q.2) q.1 :=
    (hasDerivAt_time hs q.1 q.2).deriv.symm
  rw [hD]
  have h1 := hA q.1 q.2 hq
  have h2 : A * Real.exp (-(c * |q.1|)) ≤ |A| * Real.exp (-(c * |q.1|)) :=
    mul_le_mul_of_nonneg_right (le_abs_self A) (Real.exp_pos _).le
  calc Real.cosh (κ * q.1) ^ 2 / κ * ‖deriv (fun s => f s q.2) q.1‖
      ≤ Real.exp (2 * κ * |q.1|) / κ * (|A| * Real.exp (-(c * |q.1|))) :=
        mul_le_mul (div_le_div_of_nonneg_right (cosh_sq_le_exp hκ _) hκ.le) (h1.trans h2)
          (norm_nonneg _) (by positivity)
    _ = |A| / κ * Real.exp (-((c - 2 * κ) * |q.1|)) := by
        rw [show -((c - 2 * κ) * |q.1|) = 2 * κ * |q.1| + -(c * |q.1|) by ring, Real.exp_add]
        ring

theorem hcrit_space_lim {l : Filter ℝ} (hs : ContDiff ℝ 1 (uncurry f)) {D : E → E →L[ℝ] E'}
    (hDc : Continuous D) (hD : TendstoLocallyUniformly (fun t => fderiv ℝ (f t)) D l) (x₀ : E) :
    Tendsto (fun q : ℝ × E => (fderiv ℝ (uncurry f) q).comp (ContinuousLinearMap.inr ℝ ℝ E))
      (l ×ˢ 𝓝 x₀) (𝓝 (D x₀)) :=
  (tlu_tendsto hD hDc.continuousAt).congr fun q => (hasFDerivAt_space hs q.1 q.2).fderiv

end Estimates

/-! ### The `τ` coordinate -/

section Chart

theorem artanh_eq_log_sub {τ : ℝ} (hτ : τ ∈ Ioo (-1 : ℝ) 1) :
    Real.artanh τ = 1 / 2 * (Real.log (1 + τ) - Real.log (1 - τ)) := by
  rw [Real.artanh_eq_half_log (Ioo_subset_Icc_self hτ),
    Real.log_div (by linarith [hτ.1]) (by linarith [hτ.2])]

theorem hasDerivAt_artanh {τ : ℝ} (hτ : τ ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - τ ^ 2)) τ := by
  have h1 : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + τ)) τ := by
    simpa using ((hasDerivAt_id' τ).const_add 1).log (by linarith [hτ.1])
  have h2 : HasDerivAt (fun y => Real.log (1 - y)) (-1 / (1 - τ)) τ := by
    simpa using ((hasDerivAt_id' τ).const_sub 1).log (by linarith [hτ.2])
  have h3 := (h1.sub h2).const_mul (1 / 2)
  have he : Real.artanh =ᶠ[𝓝 τ] fun y => 1 / 2 * (Real.log (1 + y) - Real.log (1 - y)) :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hτ) fun y hy => artanh_eq_log_sub hy
  refine (h3.congr_of_eventuallyEq he).congr_deriv ?_
  have h4 : (1 + τ) ≠ 0 := by linarith [hτ.1]
  have h5 : (1 - τ) ≠ 0 := by linarith [hτ.2]
  have h6 : (1 - τ ^ 2) ≠ 0 := by nlinarith [hτ.1, hτ.2]
  field_simp
  ring

theorem contDiffOn_artanh : ContDiffOn ℝ 1 Real.artanh (Ioo (-1 : ℝ) 1) := by
  have h1 : ContDiffOn ℝ 1 (fun y : ℝ => Real.log (1 + y)) (Ioo (-1) 1) :=
    (contDiff_const.add contDiff_id).contDiffOn.log fun y hy => by
      simp only [id]; linarith [hy.1]
  have h2 : ContDiffOn ℝ 1 (fun y : ℝ => Real.log (1 - y)) (Ioo (-1) 1) :=
    (contDiff_const.sub contDiff_id).contDiffOn.log fun y hy => by
      simp only [id]; linarith [hy.2]
  exact (contDiffOn_const.mul (h1.sub h2)).congr fun y hy => artanh_eq_log_sub hy

theorem cosh_artanh_sq {κ τ : ℝ} (hκ : 0 < κ) (hτ : τ ∈ Ioo (-1 : ℝ) 1) :
    1 / (1 - τ ^ 2) / κ = Real.cosh (κ * (Real.artanh τ / κ)) ^ 2 / κ := by
  have : κ * (Real.artanh τ / κ) = Real.artanh τ := by field_simp
  rw [this, Real.cosh_artanh hτ, div_pow, one_pow,
    Real.sq_sqrt (by nlinarith [hτ.1, hτ.2])]

theorem tendsto_artanh_top {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun τ => Real.artanh τ / κ) (𝓝[<] 1) atTop := by
  refine tendsto_atTop.2 fun M => ?_
  filter_upwards [Ioo_mem_nhdsLT (Real.tanh_lt_one (κ * M))] with τ hτ
  have h := Real.artanh_lt_artanh (Real.neg_one_lt_tanh _) hτ.2 hτ.1
  rw [Real.artanh_tanh] at h
  rw [le_div_iff₀ hκ]
  linarith

theorem tendsto_artanh_bot {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun τ => Real.artanh τ / κ) (𝓝[>] (-1)) atBot := by
  refine tendsto_atBot.2 fun M => ?_
  filter_upwards [Ioo_mem_nhdsGT (Real.neg_one_lt_tanh (κ * M))] with τ hτ
  have h := Real.artanh_lt_artanh hτ.1 (Real.tanh_lt_one _) hτ.2
  rw [Real.artanh_tanh] at h
  rw [div_le_iff₀ hκ]
  linarith

omit [NormedSpace ℝ E] in
theorem tendsto_chart_top {κ : ℝ} (hκ : 0 < κ) (x₀ : E) :
    Tendsto (fun p : ℝ × E => (Real.artanh p.1 / κ, p.2))
      (𝓝[Ioo (-1) 1 ×ˢ univ] ((1 : ℝ), x₀)) (atTop ×ˢ 𝓝 x₀) := by
  have h1 : 𝓝[Ioo (-1) 1 ×ˢ univ] ((1 : ℝ), x₀) ≤ 𝓝[<] (1 : ℝ) ×ˢ 𝓝 x₀ := by
    have : 𝓝[<] (1 : ℝ) ×ˢ 𝓝 x₀ = 𝓝[Iio 1 ×ˢ univ] ((1 : ℝ), x₀) := by
      rw [nhdsWithin_prod_eq, nhdsWithin_univ]
    rw [this]
    exact nhdsWithin_mono _ (prod_mono (fun τ h => h.2) subset_rfl)
  exact ((tendsto_artanh_top hκ).prodMap tendsto_id).mono_left h1

omit [NormedSpace ℝ E] in
theorem tendsto_chart_bot {κ : ℝ} (hκ : 0 < κ) (x₀ : E) :
    Tendsto (fun p : ℝ × E => (Real.artanh p.1 / κ, p.2))
      (𝓝[Ioo (-1) 1 ×ˢ univ] ((-1 : ℝ), x₀)) (atBot ×ˢ 𝓝 x₀) := by
  have h1 : 𝓝[Ioo (-1) 1 ×ˢ univ] ((-1 : ℝ), x₀) ≤ 𝓝[>] (-1 : ℝ) ×ˢ 𝓝 x₀ := by
    have : 𝓝[>] (-1 : ℝ) ×ˢ 𝓝 x₀ = 𝓝[Ioi (-1) ×ˢ univ] ((-1 : ℝ), x₀) := by
      rw [nhdsWithin_prod_eq, nhdsWithin_univ]
    rw [this]
    exact nhdsWithin_mono _ (prod_mono (fun τ h => h.1) subset_rfl)
  exact ((tendsto_artanh_bot hκ).prodMap tendsto_id).mono_left h1

theorem hasFDerivAt_chart {κ : ℝ} {p : ℝ × E} (hp : p.1 ∈ Ioo (-1 : ℝ) 1) :
    HasFDerivAt (fun p : ℝ × E => (Real.artanh p.1 / κ, p.2))
      (((1 / (1 - p.1 ^ 2) / κ) • ContinuousLinearMap.fst ℝ ℝ E).prod
        (ContinuousLinearMap.snd ℝ ℝ E)) p := by
  have h1 := ((hasDerivAt_artanh hp).div_const κ).hasFDerivAt.comp p (hasFDerivAt_fst (p := p))
  refine (h1.prodMk hasFDerivAt_snd).congr_fderiv ?_
  ext q <;> simp [mul_comm]

theorem opNorm_chart_le (D : ℝ × E →L[ℝ] E') (a : ℝ) (B : E →L[ℝ] E') :
    ‖D.comp ((a • ContinuousLinearMap.fst ℝ ℝ E).prod (ContinuousLinearMap.snd ℝ ℝ E)) -
        B.comp (ContinuousLinearMap.snd ℝ ℝ E)‖ ≤
      |a| * ‖D (1, 0)‖ + ‖D.comp (ContinuousLinearMap.inr ℝ ℝ E) - B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun q => ?_
  have hq : (D.comp ((a • ContinuousLinearMap.fst ℝ ℝ E).prod (ContinuousLinearMap.snd ℝ ℝ E)) -
      B.comp (ContinuousLinearMap.snd ℝ ℝ E)) q =
      (a * q.1) • D (1, 0) + (D.comp (ContinuousLinearMap.inr ℝ ℝ E) - B) q.2 := by
    have : ((a * q.1, q.2) : ℝ × E) = (a * q.1) • ((1 : ℝ), (0 : E)) + ((0 : ℝ), q.2) := by
      ext <;> simp
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
      ContinuousLinearMap.inr_apply]
    rw [this, map_add, map_smul]
    abel
  rw [hq]
  have h1 : |q.1| ≤ ‖q‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le q
  have h2 : ‖q.2‖ ≤ ‖q‖ := norm_snd_le q
  calc ‖(a * q.1) • D (1, 0) + (D.comp (ContinuousLinearMap.inr ℝ ℝ E) - B) q.2‖
      ≤ ‖(a * q.1) • D (1, 0)‖ + ‖(D.comp (ContinuousLinearMap.inr ℝ ℝ E) - B) q.2‖ :=
        norm_add_le _ _
    _ ≤ |a| * ‖q‖ * ‖D (1, 0)‖ + ‖D.comp (ContinuousLinearMap.inr ℝ ℝ E) - B‖ * ‖q‖ := by
        gcongr
        · rw [norm_smul, Real.norm_eq_abs, abs_mul]
          gcongr
        · exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
    _ = _ := by ring

end Chart

/-! ### Behavior at an end `τ = e ∈ {±1}` -/

theorem hcrit_end [ProperSpace E] {f F : ℝ → E → E'} {c κ : ℝ} (hκ : 0 < κ) (hκc : 2 * κ < c)
    (hs : ContDiff ℝ 1 (uncurry f))
    (hd : ∀ K, IsCompact K → ∃ A, ∀ t, ∀ x ∈ K,
      ‖deriv (fun s => f s x) t‖ ≤ A * Real.exp (-(c * |t|)))
    (hF : ∀ p ∈ Ioo (-1 : ℝ) 1 ×ˢ (univ : Set E), uncurry F p = f (Real.artanh p.1 / κ) p.2)
    {l : Filter ℝ} (hl : Tendsto (fun t : ℝ => |t|) l atTop) {fe : E → E'}
    {De : E → E →L[ℝ] E'} (hfe : Continuous fe) (htl : TendstoLocallyUniformly f fe l)
    (hDe : Continuous De) (hD : TendstoLocallyUniformly (fun t => fderiv ℝ (f t)) De l)
    {e : ℝ} (x₀ : E)
    (hchart : Tendsto (fun p : ℝ × E => (Real.artanh p.1 / κ, p.2))
      (𝓝[Ioo (-1) 1 ×ˢ univ] (e, x₀)) (l ×ˢ 𝓝 x₀)) :
    Tendsto (uncurry F) (𝓝[Ioo (-1) 1 ×ˢ univ] (e, x₀)) (𝓝 (fe x₀)) ∧
    Tendsto (fderiv ℝ (uncurry F)) (𝓝[Ioo (-1) 1 ×ˢ univ] (e, x₀))
      (𝓝 ((De x₀).comp (ContinuousLinearMap.snd ℝ ℝ E))) := by
  set s : Set (ℝ × E) := Ioo (-1 : ℝ) 1 ×ˢ univ with hs_def
  have hs_open : IsOpen s := isOpen_Ioo.prod isOpen_univ
  have hev : ∀ᶠ p in 𝓝[s] (e, x₀), p ∈ s := self_mem_nhdsWithin
  constructor
  · refine ((tlu_tendsto htl hfe.continuousAt).comp hchart).congr' ?_
    filter_upwards [hev] with p hp
    exact (hF p hp).symm
  -- the derivative on `s`
  set L : ℝ × E → ℝ × E →L[ℝ] E' := fun p =>
    (fderiv ℝ (uncurry f) (Real.artanh p.1 / κ, p.2)).comp
      (((1 / (1 - p.1 ^ 2) / κ) • ContinuousLinearMap.fst ℝ ℝ E).prod
        (ContinuousLinearMap.snd ℝ ℝ E)) with hL
  have hFL : ∀ p ∈ s, fderiv ℝ (uncurry F) p = L p := by
    intro p hp
    have h1 : HasFDerivAt (uncurry f) (fderiv ℝ (uncurry f) (Real.artanh p.1 / κ, p.2))
        (Real.artanh p.1 / κ, p.2) := ((hs.differentiable one_ne_zero) _).hasFDerivAt
    have h2 := h1.comp p (hasFDerivAt_chart (κ := κ) hp.1)
    have he : uncurry F =ᶠ[𝓝 p] (uncurry f ∘ fun p : ℝ × E => (Real.artanh p.1 / κ, p.2)) :=
      Filter.mem_of_superset (hs_open.mem_nhds hp) fun q hq => hF q hq
    exact (h2.congr_of_eventuallyEq he).fderiv
  -- the bound
  set b : ℝ × E → ℝ := fun q => Real.cosh (κ * q.1) ^ 2 / κ * ‖fderiv ℝ (uncurry f) q (1, 0)‖ +
    ‖(fderiv ℝ (uncurry f) q).comp (ContinuousLinearMap.inr ℝ ℝ E) - De x₀‖ with hb
  have hblim : Tendsto b (l ×ˢ 𝓝 x₀) (𝓝 0) := by
    have h1 := hcrit_time_small hl hs hκ hκc hd x₀
    have h2 := (tendsto_iff_norm_sub_tendsto_zero.1 (hcrit_space_lim hs hDe hD x₀))
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact h3
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (hblim.comp hchart)
  filter_upwards [hev] with p hp
  rw [hFL p hp]
  have h1 := opNorm_chart_le (fderiv ℝ (uncurry f) (Real.artanh p.1 / κ, p.2))
    (1 / (1 - p.1 ^ 2) / κ) (De x₀)
  have hpos : 0 ≤ 1 / (1 - p.1 ^ 2) / κ := by
    have : 0 < 1 - p.1 ^ 2 := by nlinarith [hp.1.1, hp.1.2]
    positivity
  refine le_trans h1 (le_of_eq ?_)
  show _ = Real.cosh (κ * (Real.artanh p.1 / κ)) ^ 2 / κ * _ + _
  rw [abs_of_nonneg hpos, cosh_artanh_sq hκ hp.1]

/-! ### Proposition `prop:Hcrit`(i) -/

theorem hasDerivAt_tanh_mul (κ t : ℝ) :
    HasDerivAt (fun t => Real.tanh (κ * t)) (κ * (1 - Real.tanh (κ * t) ^ 2)) t := by
  have hc := (Real.cosh_pos (κ * t)).ne'
  have h1 := ((Real.hasDerivAt_sinh (κ * t)).comp t ((hasDerivAt_id' t).const_mul κ)).div
    ((Real.hasDerivAt_cosh (κ * t)).comp t ((hasDerivAt_id' t).const_mul κ)) hc
  have he : (fun t => Real.tanh (κ * t)) = fun t => Real.sinh (κ * t) / Real.cosh (κ * t) :=
    funext fun t => Real.tanh_eq_sinh_div_cosh _
  rw [he]
  refine h1.congr_deriv ?_
  simp only [Function.comp_apply]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem prop_Hcrit_i [ProperSpace E] [CompleteSpace E'] {f : ℝ → E → E'} {c : ℝ}
    {Dp Dm : E → E →L[ℝ] E'} (h : HcritHyp f c Dp Dm) {κ : ℝ} (hκ : 0 < κ) (hκc : 2 * κ < c) :
    ∃ fp fm : E → E', ContDiff ℝ 1 fp ∧ ContDiff ℝ 1 fm ∧
      TendstoLocallyUniformly f fp atTop ∧ TendstoLocallyUniformly f fm atBot ∧
      (∀ t, HasDerivAt (fun t => Real.tanh (κ * t)) (κ * (1 - Real.tanh (κ * t) ^ 2)) t) ∧
      ∃ F : ℝ → E → E', ContDiffOn ℝ 1 (uncurry F) (Icc (-1) 1 ×ˢ univ) ∧
        F 1 = fp ∧ F (-1) = fm ∧ ∀ t x, f t x = F (Real.tanh (κ * t)) x := by
  obtain ⟨fp, hfp, htp⟩ := hcrit_limit_top h.smooth h.pos h.decay
  obtain ⟨fm, hfm, htm⟩ := hcrit_limit_bot h.smooth h.pos h.decay
  obtain ⟨hDpc, -, hfpC⟩ := hcrit_limit_C1 h.smooth hfp h.dtop
  obtain ⟨hDmc, -, hfmC⟩ := hcrit_limit_C1 h.smooth hfm h.dbot
  set F : ℝ → E → E' := fun τ x =>
    if τ = 1 then fp x else if τ = -1 then fm x else f (Real.artanh τ / κ) x with hFdef
  have hF1 : F 1 = fp := funext fun x => by simp [F]
  have hFm1 : F (-1) = fm := funext fun x => by norm_num [F]
  refine ⟨fp, fm, hfpC, hfmC, htp, htm, hasDerivAt_tanh_mul κ, F, ?_, hF1, hFm1, fun t x => ?_⟩
  swap
  · have h1 : Real.tanh (κ * t) ≠ 1 := (Real.tanh_lt_one _).ne
    have h2 : Real.tanh (κ * t) ≠ -1 := (Real.neg_one_lt_tanh _).ne'
    simp only [F, h1, h2, ↓reduceIte, Real.artanh_tanh]
    field_simp
  set s : Set (ℝ × E) := Ioo (-1 : ℝ) 1 ×ˢ univ with hs_def
  set S : Set (ℝ × E) := Icc (-1 : ℝ) 1 ×ˢ univ with hS_def
  have hs_open : IsOpen s := isOpen_Ioo.prod isOpen_univ
  have hclos : closure s = S := by
    rw [hs_def, hS_def, closure_prod_eq, closure_Ioo (by norm_num), closure_univ]
  have hF : ∀ p ∈ s, uncurry F p = f (Real.artanh p.1 / κ) p.2 := by
    intro p hp
    have h1 : p.1 ≠ 1 := hp.1.2.ne
    have h2 : p.1 ≠ -1 := hp.1.1.ne'
    simp only [uncurry, F, h1, h2, ↓reduceIte]
  have hsm : ContDiffOn ℝ 1 (uncurry F) s := by
    have hc : ContDiffOn ℝ 1 (fun p : ℝ × E => (Real.artanh p.1 / κ, p.2)) s :=
      ((contDiffOn_artanh.comp contDiff_fst.contDiffOn fun p hp => hp.1).div_const κ).prodMk
        contDiff_snd.contDiffOn
    exact (h.smooth.comp_contDiffOn hc).congr hF
  have hdiff : DifferentiableOn ℝ (uncurry F) s := hsm.differentiableOn one_ne_zero
  have htop := fun x₀ => hcrit_end hκ hκc h.smooth h.decay hF tendsto_abs_atTop_atTop
    hfpC.continuous htp hDpc h.dtop x₀ (tendsto_chart_top hκ x₀)
  have hbot := fun x₀ => hcrit_end hκ hκc h.smooth h.decay hF tendsto_abs_atBot_atTop
    hfmC.continuous htm hDmc h.dbot x₀ (tendsto_chart_bot hκ x₀)
  -- points of `S`
  have hcases : ∀ p ∈ S, p ∈ s ∨ p = (1, p.2) ∨ p = (-1, p.2) := by
    rintro ⟨τ, x⟩ ⟨⟨h1, h2⟩, -⟩
    rcases eq_or_lt_of_le h2 with rfl | h2'
    · exact Or.inr (Or.inl rfl)
    rcases eq_or_lt_of_le h1 with rfl | h1'
    · exact Or.inr (Or.inr rfl)
    exact Or.inl ⟨⟨h1', h2'⟩, mem_univ _⟩
  have hcont : ∀ y ∈ closure s, ContinuousWithinAt (uncurry F) s y := by
    intro y hy
    rw [hclos] at hy
    rcases hcases y hy with hy | hy | hy
    · exact (hdiff.differentiableAt (hs_open.mem_nhds hy)).continuousAt.continuousWithinAt
    · rw [hy]
      unfold ContinuousWithinAt
      have : uncurry F (1, y.2) = fp y.2 := by simp [uncurry, F]
      rw [this]
      exact (htop y.2).1
    · rw [hy]
      unfold ContinuousWithinAt
      have : uncurry F (-1, y.2) = fm y.2 := by norm_num [uncurry, F]
      rw [this]
      exact (hbot y.2).1
  have hconv : Convex ℝ s := (convex_Ioo _ _).prod convex_univ
  set DF : ℝ × E → ℝ × E →L[ℝ] E' := fun p =>
    if p.1 = 1 then (Dp p.2).comp (ContinuousLinearMap.snd ℝ ℝ E)
    else if p.1 = -1 then (Dm p.2).comp (ContinuousLinearMap.snd ℝ ℝ E)
    else fderiv ℝ (uncurry F) p with hDF
  have hDFs : ∀ p ∈ s, DF p = fderiv ℝ (uncurry F) p := by
    intro p hp
    simp only [DF, hp.1.2.ne, hp.1.1.ne', ↓reduceIte]
  have hDF1 : ∀ x, DF (1, x) = (Dp x).comp (ContinuousLinearMap.snd ℝ ℝ E) := by
    intro x; simp [DF]
  have hDFm1 : ∀ x, DF (-1, x) = (Dm x).comp (ContinuousLinearMap.snd ℝ ℝ E) := by
    intro x; norm_num [DF]
  have hder : ∀ p ∈ S, HasFDerivWithinAt (uncurry F) (DF p) S p := by
    intro p hp
    rcases hcases p hp with hp' | hp' | hp'
    · rw [hDFs p hp']
      exact (hdiff.differentiableAt (hs_open.mem_nhds hp')).hasFDerivAt.hasFDerivWithinAt
    · rw [hp', hDF1, ← hclos]
      exact hasFDerivWithinAt_closure_of_tendsto_fderiv hdiff hconv hs_open hcont (htop p.2).2
    · rw [hp', hDFm1, ← hclos]
      exact hasFDerivWithinAt_closure_of_tendsto_fderiv hdiff hconv hs_open hcont (hbot p.2).2
  have hfd : ContinuousOn (fderiv ℝ (uncurry F)) s :=
    hsm.continuousOn_fderiv_of_isOpen hs_open le_rfl
  have hDFcont : ContinuousOn DF S := by
    intro p hp
    rcases hcases p hp with hp' | hp' | hp'
    · have he : DF =ᶠ[𝓝 p] fderiv ℝ (uncurry F) :=
        Filter.mem_of_superset (hs_open.mem_nhds hp') fun q hq => hDFs q hq
      exact ((hfd.continuousAt (hs_open.mem_nhds hp')).congr he.symm).continuousWithinAt
    · rw [hp']
      refine continuousWithinAt_of_split (s := s) (U := Ioi (0 : ℝ) ×ˢ univ)
        (T := {(1 : ℝ)} ×ˢ univ)
        (prod_mem_nhds (Ioi_mem_nhds (by norm_num)) univ_mem) ?_ ?_ ?_
      · rintro ⟨τ, x⟩ ⟨⟨⟨h1, h2⟩, -⟩, ⟨h3, -⟩⟩
        rcases eq_or_lt_of_le h2 with rfl | h2'
        · exact Or.inr ⟨rfl, mem_univ _⟩
        · exact Or.inl ⟨⟨by linarith [show (0 : ℝ) < τ from h3], h2'⟩, mem_univ _⟩
      · rw [hDF1]
        refine ((htop p.2).2).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with q hq
        exact (hDFs q hq).symm
      · rw [hDF1]
        have hc : Continuous fun q : ℝ × E => (Dp q.2).comp (ContinuousLinearMap.snd ℝ ℝ E) :=
          (hDpc.comp continuous_snd).clm_comp continuous_const
        refine (hc.tendsto (1, p.2)).mono_left nhdsWithin_le_nhds |>.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with q hq
        obtain ⟨hq1, -⟩ := hq
        rw [show q = (1, q.2) from Prod.ext hq1 rfl, hDF1]
    · rw [hp']
      refine continuousWithinAt_of_split (s := s) (U := Iio (0 : ℝ) ×ˢ univ)
        (T := {(-1 : ℝ)} ×ˢ univ)
        (prod_mem_nhds (Iio_mem_nhds (by norm_num)) univ_mem) ?_ ?_ ?_
      · rintro ⟨τ, x⟩ ⟨⟨⟨h1, h2⟩, -⟩, ⟨h3, -⟩⟩
        rcases eq_or_lt_of_le h1 with h1' | h1'
        · exact Or.inr ⟨h1'.symm, mem_univ _⟩
        · exact Or.inl ⟨⟨h1', by linarith [show τ < (0 : ℝ) from h3]⟩, mem_univ _⟩
      · rw [hDFm1]
        refine ((hbot p.2).2).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with q hq
        exact (hDFs q hq).symm
      · rw [hDFm1]
        have hc : Continuous fun q : ℝ × E => (Dm q.2).comp (ContinuousLinearMap.snd ℝ ℝ E) :=
          (hDmc.comp continuous_snd).clm_comp continuous_const
        refine (hc.tendsto (-1, p.2)).mono_left nhdsWithin_le_nhds |>.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with q hq
        obtain ⟨hq1, -⟩ := hq
        rw [show q = (-1, q.2) from Prod.ext hq1 rfl, hDFm1]
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_hasFDerivWithinAt (by simp)]
  intro p hp
  refine ⟨S, ?_, fun h => absurd h (by simp), DF, hder, contDiffOn_zero.2 hDFcont⟩
  rw [insert_eq_of_mem hp]
  exact self_mem_nhdsWithin

end

end ConleyCheck
