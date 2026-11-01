import ConleyCheck.Gubser.GlobalBarrier
import ConleyCheck.Conley.OrbitLimits

/-!
# Limit sets of the global flow

* Along every orbit `w` converges, so `w` is constant along every orbit in a limit set
  (`w_const_of_omegaLim`).
* Such an orbit is a curve of the fiber field `fieldF c τ` with `τ` constant, so it converges to an
  equilibrium (`lem:fiber` (iii) for `τ ≠ 0`, and a direct monotonicity argument at infinity for
  `τ = 0`).
* Hence every `ω`- and `α`-limit set contains an equilibrium (`exists_fixed_omegaLim`,
  `exists_fixed_alphaLim`).
-/

open Set Filter Topology
open ConleyCheck.Conley ConleyCheck.ODE

namespace ConleyCheck.Gubser

variable {c : ℝ}

theorem isReversor_revΩ (c : ℝ) : IsReversor (ϕG c) revΩ :=
  ⟨continuous_revΩ, revΩ_revΩ, fun t x => ϕG_rev c t x⟩

/-- A zero of `fieldG` is fixed by the flow. -/
theorem ϕG_fixed {e : OmG} (he : fieldG c e = 0) (t : ℝ) : ϕG c t e = e := by
  have hsol : IsSol (bumpField (fieldG c) 2 two_pos) (fun _ => (e : EG)) := fun s => by
    have : bumpField (fieldG c) 2 two_pos (e : EG) = 0 := by simp [bumpField, he]
    rw [this]; exact hasDerivAt_const s (e : EG)
  have : flowG c t ((fun _ => (e : EG)) 0) = (fun _ => (e : EG)) (t + 0) :=
    flowOf_eq_of_isSol _ _ hsol 0 t
  exact Subtype.ext this

/-- A fixed point is a zero of `fieldG`. -/
theorem fieldG_eq_zero {e : OmG} (he : ∀ t, ϕG c t e = e) : fieldG c e = 0 := by
  have h := hasDerivAt_ϕG c e 0
  rw [Flow.map_zero_apply] at h
  have h' : HasDerivAt (fun s => (ϕG c s e : EG)) 0 0 := by
    have : (fun s => (ϕG c s e : EG)) = fun _ => (e : EG) := funext fun s => by rw [he]
    rw [this]; exact hasDerivAt_const _ _
  exact h.unique h'

theorem deriv_zero_of_const {f : ℝ → ℝ} {d t : ℝ} (hf : HasDerivAt f d t)
    (hc : ∀ s, f s = f t) : d = 0 :=
  hf.unique ((hasDerivAt_const t (f t)).congr_of_eventuallyEq (Eventually.of_forall hc))

theorem gw2_neg (p : OmG) (h : gw2 p < 0) (t : ℝ) : gw2 (ϕG c t p) < 0 := by
  by_contra h'
  push Not at h'
  rcases h'.eq_or_lt with h0 | h0
  · have := gw2_zero c (ϕG c t p) h0.symm (-t)
    rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply] at this
    linarith
  · have := gw2_pos c (ϕG c t p) h0 (-t)
    rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply] at this
    linarith

/-! ## Convergence of `w` -/

theorem tendsto_gw1 (c : ℝ) (p : OmG) : ∃ L, Tendsto (fun t => gw1 (ϕG c t p)) atTop (𝓝 L) :=
  ⟨_, tendsto_atTop_ciSup (monotone_gw1 c p) ⟨1, by rintro _ ⟨t, rfl⟩; exact (gw1_mem _).2⟩⟩

theorem gw2_eq_sqrt {q : OmG} (h : 0 ≤ gw2 q) : gw2 q = Real.sqrt (1 - gw1 q ^ 2) := by
  rw [← circle_G q, add_sub_cancel_left, Real.sqrt_sq h]

theorem tendsto_gw2 (c : ℝ) (p : OmG) : ∃ L, Tendsto (fun t => gw2 (ϕG c t p)) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := tendsto_gw1 c p
  have hs : Tendsto (fun t => Real.sqrt (1 - gw1 (ϕG c t p) ^ 2)) atTop
      (𝓝 (Real.sqrt (1 - L ^ 2))) :=
    ((Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 2))).tendsto L).comp hL
  rcases lt_trichotomy (gw2 p) 0 with h | h | h
  · refine ⟨-Real.sqrt (1 - L ^ 2), hs.neg.congr fun t => ?_⟩
    have h1 := gw2_neg (c := c) p h t
    have hsq : gw2 (ϕG c t p) ^ 2 = 1 - gw1 (ϕG c t p) ^ 2 := by linarith [circle_G (ϕG c t p)]
    rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_neg h1, neg_neg]
  · exact ⟨0, tendsto_const_nhds.congr fun t => (gw2_zero c p h t).symm⟩
  · exact ⟨_, hs.congr fun t => (gw2_eq_sqrt (gw2_pos c p h t).le).symm⟩

/-- Along every orbit in an `ω`-limit set, `w` is constant. -/
theorem w_const_of_omegaLim {x z : OmG} (hz : z ∈ omegaLim (ϕG c) x) (t : ℝ) :
    gw1 (ϕG c t z) = gw1 z ∧ gw2 (ϕG c t z) = gw2 z := by
  obtain ⟨L₁, h₁⟩ := tendsto_gw1 c x
  obtain ⟨L₂, h₂⟩ := tendsto_gw2 c x
  have s₁ := omegaLim_subset_level (ϕG c) continuous_gw1 h₁
  have s₂ := omegaLim_subset_level (ϕG c) continuous_gw2 h₂
  have hz' := omegaLim_invariant (ϕG c) hz t
  exact ⟨(s₁ hz').trans (s₁ hz).symm, (s₂ hz').trans (s₂ hz).symm⟩

/-! ## Orbits with constant `w` -/

section Const

variable (z : OmG) (hw : ∀ t, gw1 (ϕG c t z) = gw1 z ∧ gw2 (ϕG c t z) = gw2 z)
include hw

theorem w_eq_of_const (t : ℝ) : (ϕG c t z : EG).2 = (z : EG).2 :=
  Prod.ext (hw t).1 (hw t).2

theorem fieldG_zero_of_const {t : ℝ} (he : fieldF c (gw1 z) (ϕG c t z : EG).1 = 0) :
    fieldG c (ϕG c t z) = 0 := by
  have d1 := deriv_zero_of_const (hasDerivAt_gw1 c z t) fun s => by rw [(hw s).1, (hw t).1]
  have d2 := deriv_zero_of_const (hasDerivAt_gw2 c z t) fun s => by rw [(hw s).2, (hw t).2]
  have hcirc := circle_G (ϕG c t z)
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show fieldF c (gw1 (ϕG c t z)) (ϕG c t z : EG).1 = 0
    rw [(hw t).1]; exact he
  · show gy3 (ϕG c t z) * gw2 (ϕG c t z) ^ 2 = 0
    rw [show gw2 (ϕG c t z) ^ 2 = 1 - gw1 (ϕG c t z) ^ 2 by linarith]; exact d1
  · show -(gy3 (ϕG c t z) * gw1 (ϕG c t z) * gw2 (ϕG c t z)) = 0
    linear_combination d2

/-- An orbit with constant `w` is a curve of the fiber field. -/
noncomputable def curveG : FiberCurve c (gw1 z) where
  γ t := (ϕG c t z : EG).1
  β _ := 1
  cβ := continuous_const
  pos _ _ := one_pos
  mem t := (ϕG c t z).2.1
  deriv t := by
    rw [one_smul, ← (hw t).1]
    exact hasDerivAt_y c z t
  rest e he t ht s := by
    have hf := fieldG_zero_of_const z hw (t := t) (by rw [ht]; exact he)
    show (ϕG c s z : EG).1 = e
    rw [show s = (s - t) + t by ring, Flow.map_add, ϕG_fixed hf]
    exact ht

/-- At infinity with `τ = 0`, `y₁` is nondecreasing and `y₂` has constant sign, so `y` converges. -/
theorem tendsto_y_zero (hc : 0 < c) (h0 : gw1 z = 0) :
    ∃ e, Tendsto (fun t => (ϕG c t z : EG).1) atTop (𝓝 e) := by
  have hτ : ∀ t, gw1 (ϕG c t z) = 0 := fun t => by rw [(hw t).1, h0]
  have hy3 : ∀ t, gy3 (ϕG c t z) = 0 := fun t => by
    have := deriv_zero_of_const (hasDerivAt_gw1 c z t) fun s => by rw [hτ s, hτ t]
    rw [hτ t] at this
    simpa using this
  have hS : ∀ t, gS c (ϕG c t z) = -(gy1 (ϕG c t z) * gy2 (ϕG c t z) ^ 2 / c) := fun t => by
    simp only [gS, fS, fP1, fP2, ← gy1.eq_def, ← gy2.eq_def, ← gy3.eq_def, hτ t]
    ring
  have hd1 : ∀ t, HasDerivAt (fun s => gy1 (ϕG c s z))
      (gy1 (ϕG c t z) ^ 2 * gy2 (ϕG c t z) ^ 2 / c) t := fun t =>
    (hasDerivAt_gy1 c z t).congr_deriv (by
      rw [hS t]
      simp only [gP1, fP1, ← gy1.eq_def, hτ t]
      ring)
  have hmono : Monotone fun s => gy1 (ϕG c s z) :=
    monotone_of_deriv_nonneg (fun s => (hd1 s).differentiableAt) fun s => by
      rw [(hd1 s).deriv]; positivity
  have hb : BddAbove (range fun s => gy1 (ϕG c s z)) := ⟨1, by
    rintro _ ⟨t, rfl⟩
    have := sphere_G (ϕG c t z)
    nlinarith [sq_nonneg (gy2 (ϕG c t z)), sq_nonneg (gy3 (ϕG c t z)),
      sq_nonneg (gy1 (ϕG c t z) - 1)]⟩
  obtain ⟨L, hL⟩ : ∃ L, Tendsto (fun s => gy1 (ϕG c s z)) atTop (𝓝 L) :=
    ⟨_, tendsto_atTop_ciSup hmono hb⟩
  have hd2 : ∀ t, HasDerivAt (fun s => gy2 (ϕG c s z))
      ((-(gy1 (ϕG c t z) / c) + gy1 (ϕG c t z) * gy2 (ϕG c t z) ^ 2 / c) * gy2 (ϕG c t z)) t :=
    fun t => (hasDerivAt_gy2 c z t).congr_deriv (by
      rw [hS t]
      simp only [gP2, fP2, ← gy1.eq_def, ← gy2.eq_def, ← gy3.eq_def, hτ t]
      ring)
  have hk : Continuous fun t => -(gy1 (ϕG c t z) / c) + gy1 (ϕG c t z) * gy2 (ϕG c t z) ^ 2 / c :=
    continuous_k c z _ (((continuous_gy1.div_const c).neg).add
      ((continuous_gy1.mul (continuous_gy2.pow 2)).div_const c))
  have hcirc : ∀ t, gy2 (ϕG c t z) ^ 2 = 1 - gy1 (ϕG c t z) ^ 2 := fun t => by
    have := sphere_G (ϕG c t z); rw [hy3 t] at this; linarith
  have hs : Tendsto (fun t => Real.sqrt (1 - gy1 (ϕG c t z) ^ 2)) atTop
      (𝓝 (Real.sqrt (1 - L ^ 2))) :=
    ((Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 2))).tendsto L).comp hL
  have h3 : Tendsto (fun t => gy3 (ϕG c t z)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun t => (hy3 t).symm
  have hz0 : gy3 z = 0 := by simpa using hy3 0
  rcases lt_trichotomy (gy2 z) 0 with h | h | h
  · have hneg : ∀ t, gy2 (ϕG c t z) < 0 := fun t => by
      have := pos_of_linear_all (T := fun s => -gy2 (ϕG c s z)) (fun s => (hd2 s).neg.congr_deriv
        (by ring)) hk (s₀ := 0) (by simp only [Flow.map_zero_apply]; linarith) t
      linarith
    refine ⟨(L, -Real.sqrt (1 - L ^ 2), 0), hL.prodMk_nhds ((hs.neg.congr fun t => ?_).prodMk_nhds h3)⟩
    rw [← hcirc t, Real.sqrt_sq_eq_abs, abs_of_neg (hneg t), neg_neg]
    rfl
  · refine ⟨(L, 0, 0), hL.prodMk_nhds ((tendsto_const_nhds.congr fun t => ?_).prodMk_nhds h3)⟩
    exact (eq_zero_of_linear_all hd2 hk (s₀ := 0) (by simpa using h) t).symm
  · have hpos : ∀ t, 0 < gy2 (ϕG c t z) := fun t =>
      pos_of_linear_all hd2 hk (s₀ := 0) (by simpa using h) t
    refine ⟨(L, Real.sqrt (1 - L ^ 2), 0), hL.prodMk_nhds ((hs.congr fun t => ?_).prodMk_nhds h3)⟩
    rw [← hcirc t, Real.sqrt_sq (hpos t).le]
    rfl

/-- An orbit with constant `w` converges to a fixed point. -/
theorem tendsto_fixed_of_const (hc : 0 < c) :
    ∃ e : OmG, (∀ t, ϕG c t e = e) ∧ Tendsto (fun t => ϕG c t z) atTop (𝓝 e) := by
  obtain ⟨e, he⟩ : ∃ e, Tendsto (fun t => (ϕG c t z : EG).1) atTop (𝓝 e) := by
    by_cases h0 : gw1 z = 0
    · exact tendsto_y_zero z hw hc h0
    · obtain ⟨e, -, -, he⟩ := (curveG z hw).tendsto_atTop hc.ne' h0
      exact ⟨e, he⟩
  have hE : Tendsto (fun t => (ϕG c t z : EG)) atTop (𝓝 (e, (z : EG).2)) :=
    he.prodMk_nhds (tendsto_const_nhds.congr fun t => (w_eq_of_const z hw t).symm)
  have hmem : (e, (z : EG).2) ∈ OmG :=
    isCompact_OmG.isClosed.mem_of_tendsto hE (Eventually.of_forall fun t => (ϕG c t z).2)
  have hT : Tendsto (fun t => ϕG c t z) atTop (𝓝 (⟨_, hmem⟩ : OmG)) :=
    tendsto_subtype_rng.2 hE
  exact ⟨_, fixed_of_tendsto (ϕG c) hT, hT⟩

end Const

/-! ## Equilibria in limit sets -/

/-- Every `ω`-limit set contains a fixed point. -/
theorem exists_fixed_omegaLim (hc : 0 < c) (x : OmG) :
    ∃ e ∈ omegaLim (ϕG c) x, ∀ t, ϕG c t e = e := by
  obtain ⟨z, hz⟩ := omegaLim_nonempty' (ϕG c) x
  obtain ⟨e, hfix, hT⟩ := tendsto_fixed_of_const z (w_const_of_omegaLim hz) hc
  refine ⟨e, ?_, hfix⟩
  exact omegaLim_subset_of_invariant (ϕG c) (isClosed_omegaLim _ x)
    (fun _ hq t => omegaLim_invariant _ hq t) hz (mem_omegaLim_of_tendsto _ hT)

/-- Every `α`-limit set contains a fixed point. -/
theorem exists_fixed_alphaLim (hc : 0 < c) (x : OmG) :
    ∃ e ∈ alphaLim (ϕG c) x, ∀ t, ϕG c t e = e := by
  obtain ⟨e, he, hfix⟩ := exists_fixed_omegaLim hc (revΩ x)
  have := (isReversor_revΩ c).alphaLim_eq (revΩ x)
  rw [revΩ_revΩ] at this
  refine ⟨revΩ e, this ▸ mem_image_of_mem _ he, fun t => ?_⟩
  rw [ϕG_rev, hfix]

end ConleyCheck.Gubser
