import ConleyCheck.ON.Flow

/-!
# Lemma `lem:ONstructure`(iii), (iv) and Corollary `cor:ON`(i)

* `lem_ONstructure_iii`: the closed quadrant `Q = {y₁ ≤ 0, y₂ ≤ 0}` is positively invariant, for
  solutions of `eq:ONy` on any interval `[0, T)`.
* `lem_ONstructure_iv_fst`, `lem_ONstructure_iv_snd`: a solution on `[0, T)` starting at a point
  with `y₁ < -1/9`, or at a point of `Q` with `y₂ < -1/(N+2)`, has `T` bounded by an explicit
  constant, that is, it blows up in finite time.
* `cor_ON_i`: the explicit solutions `ς(t) (1, k)` with `ς(t) = -1/(α_k + e^t)` on the three
  invariant lines connect `Σ_I`, `Σ_H` and `Σ_C` to `Σ_G`.
-/

open Set Filter Topology Real

namespace ConleyCheck.ON

open ConleyCheck.ODE

variable {N : ℝ}

/-- Blow-up: if `g' ≥ g (k g - 1)` while `g ≥ g(0) > 1/k`, then a solution on `[0, T)` has
`T ≤ 1/(k g(0) - 1)`. -/
theorem blowup_time {g g' : ℝ → ℝ} {T k : ℝ} (hk : 0 < k)
    (hg : ∀ s ∈ Ico 0 T, HasDerivAt g (g' s) s) (h1 : 1 < k * g 0)
    (hd : ∀ s ∈ Ico 0 T, g 0 ≤ g s → g s * (k * g s - 1) ≤ g' s) :
    T ≤ 1 / (k * g 0 - 1) := by
  set a := g 0
  have ha : 0 < a := by
    by_contra h; push Not at h; nlinarith
  have hsub : ∀ t ∈ Ico 0 T, Icc 0 t ⊆ Ico 0 T := fun t ht s hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  -- `g ≥ a` on `[0, T)`
  have hge : ∀ t ∈ Ico 0 T, a ≤ g t := by
    intro t ht
    refine image_le_of_deriv_right_lt_deriv_boundary' (a := 0) (b := t) (f := fun _ => a)
      (f' := fun _ => 0) continuousOn_const (fun s _ => hasDerivWithinAt_const _ _ _) le_rfl
      (fun s hs => (hg s (hsub t ht hs)).continuousAt.continuousWithinAt)
      (fun s hs => (hg s (hsub t ht (Ico_subset_Icc_self hs))).hasDerivWithinAt)
      (fun s hs hgs => ?_) ⟨ht.1, le_rfl⟩
    have := hd s (hsub t ht (Ico_subset_Icc_self hs)) hgs.le
    rw [← hgs] at this
    nlinarith
  -- `1/g ≤ 1/a - c t` with `c = k - 1/a`
  set c := k - 1 / a
  have hc : 0 < c := by
    simp only [c]
    have : 1 / a < k := by rw [div_lt_iff₀ ha]; linarith
    linarith
  by_contra hT
  push Not at hT
  set τ := 1 / (k * a - 1)
  have hτ : τ ∈ Ico 0 T := ⟨by positivity, hT⟩
  have hgpos : ∀ s ∈ Ico 0 T, 0 < g s := fun s hs => ha.trans_le (hge s hs)
  have hu : ∀ s ∈ Ico 0 T, HasDerivAt (fun s => (g s)⁻¹) (-g' s / g s ^ 2) s := fun s hs =>
    (hg s hs).inv (hgpos s hs).ne'
  have hl : ∀ s, HasDerivAt (fun s => 1 / a - c * s) (-c) s := fun s => by
    simpa using ((hasDerivAt_id s).const_mul c).const_sub (1 / a)
  have := image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := τ)
    (f := fun s => (g s)⁻¹) (f' := fun s => -g' s / g s ^ 2) (B := fun s => 1 / a - c * s)
    (B' := fun _ => -c)
    (fun s hs => (hu s (hsub τ hτ hs)).continuousAt.continuousWithinAt)
    (fun s hs => (hu s (hsub τ hτ (Ico_subset_Icc_self hs))).hasDerivWithinAt)
    (by show a⁻¹ ≤ 1 / a - c * 0; simp)
    (fun s _ => (hl s).continuousAt.continuousWithinAt)
    (fun s _ => (hl s).hasDerivWithinAt)
    (fun s hs => ?_) ⟨hτ.1, le_rfl⟩
  · have hτc : 1 / a - c * τ = 0 := by
      have hne : k * a - 1 ≠ 0 := by linarith
      have e : c = (k * a - 1) / a := by simp only [c]; field_simp
      rw [e]
      simp only [τ]
      rw [div_mul_div_comm, mul_one, mul_comm a, ← div_div, div_self hne]
      ring
    have h' : (g τ)⁻¹ ≤ 1 / a - c * τ := this
    rw [hτc] at h'
    have := inv_pos.2 (hgpos τ hτ)
    linarith
  · have hs' := hsub τ hτ (Ico_subset_Icc_self hs)
    have hgs := hgpos s hs'
    have hag := hge s hs'
    have hdg := hd s hs' hag
    show -g' s / g s ^ 2 ≤ -c
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    have : 1 / a * g s ^ 2 ≥ g s := by
      rw [ge_iff_le, div_mul_eq_mul_div, one_mul, le_div_iff₀ ha]
      nlinarith
    simp only [c]
    nlinarith

/-! ## Lemma `lem:ONstructure`(iii) -/

/-- Lemma `lem:ONstructure`(iii): `Q = {y₁ ≤ 0, y₂ ≤ 0}` is positively invariant. -/
theorem lem_ONstructure_iii (hN : 1 < N) {γ : ℝ → ℝ × ℝ} {T : ℝ}
    (hγ : ∀ t ∈ Ico 0 T, HasDerivAt γ (field N (γ t)) t) (h0 : γ 0 ∈ Iic (0 : ℝ) ×ˢ Iic 0) :
    ∀ t ∈ Ico 0 T, γ t ∈ Iic (0 : ℝ) ×ˢ Iic 0 := by
  intro t ht
  have hsub : Icc 0 t ⊆ Ico 0 T := fun s hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  have h1 : ∀ s ∈ Icc 0 t, HasDerivAt (fun s => (γ s).1) (f₁ N (γ s).1 (γ s).2) s :=
    fun s hs => by
      have h := (hasFDerivAt_fst (𝕜 := ℝ) (p := γ s)).comp_hasDerivAt s (hγ s (hsub hs))
      exact h
  have h2 : ∀ s ∈ Icc 0 t, HasDerivAt (fun s => (γ s).2) (f₂ N (γ s).1 (γ s).2) s :=
    fun s hs => by
      have h := (hasFDerivAt_snd (𝕜 := ℝ) (p := γ s)).comp_hasDerivAt s (hγ s (hsub hs))
      exact h
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun s => (γ s).1) fun s hs => (h1 s hs).continuousAt.continuousWithinAt
  refine ⟨nonpos_of_fence (C := 0) ht.1 h1 h0.1 fun s _ hpos => ?_,
    nonpos_of_fence (C := 6 * M + 2) ht.1 h2 h0.2 fun s hs hpos => ?_⟩
  · simp only [f₁, zero_mul]
    have : 0 ≤ (N - 1) * (γ s).2 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    nlinarith
  · have hMs := hM s (Ico_subset_Icc_self hs)
    rw [Real.norm_eq_abs] at hMs
    have hy1 : -(γ s).1 ≤ M := by linarith [neg_abs_le (γ s).1]
    simp only [f₂]
    have : 0 ≤ (N + 2) * (γ s).2 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_right hy1 hpos.le]

/-! ## Lemma `lem:ONstructure`(iv) -/

/-- Lemma `lem:ONstructure`(iv), first part: a solution on `[0, T)` with `y₁(0) < -1/9` has
`T ≤ 1/(-9 y₁(0) - 1)`. -/
theorem lem_ONstructure_iv_fst (hN : 1 < N) {γ : ℝ → ℝ × ℝ} {T : ℝ}
    (hγ : ∀ t ∈ Ico 0 T, HasDerivAt γ (field N (γ t)) t) (h0 : (γ 0).1 < -1 / 9) :
    T ≤ 1 / (9 * -(γ 0).1 - 1) := by
  refine blowup_time (g := fun s => -(γ s).1) (g' := fun s => -f₁ N (γ s).1 (γ s).2)
    (by norm_num) (fun s hs => ?_) (by show 1 < 9 * -(γ 0).1; linarith) (fun s _ _ => ?_)
  · have h := (hasFDerivAt_fst (𝕜 := ℝ) (p := γ s)).comp_hasDerivAt s (hγ s hs)
    exact h.neg
  · have := blowup_x (N := N) (y₁ := (γ s).1) (y₂ := (γ s).2) hN.le
    linarith

/-- Lemma `lem:ONstructure`(iv), second part: a solution on `[0, T)` starting in `Q` with
`y₂(0) < -1/(N+2)` has `T ≤ 1/(-(N+2) y₂(0) - 1)`. -/
theorem lem_ONstructure_iv_snd (hN : 1 < N) {γ : ℝ → ℝ × ℝ} {T : ℝ}
    (hγ : ∀ t ∈ Ico 0 T, HasDerivAt γ (field N (γ t)) t) (hQ : γ 0 ∈ Iic (0 : ℝ) ×ˢ Iic 0)
    (h0 : (γ 0).2 < -1 / (N + 2)) : T ≤ 1 / ((N + 2) * -(γ 0).2 - 1) := by
  have hk : 0 < N + 2 := by linarith
  have hQt := lem_ONstructure_iii hN hγ hQ
  refine blowup_time (g := fun s => -(γ s).2) (g' := fun s => -f₂ N (γ s).1 (γ s).2)
    hk (fun s hs => ?_) ?_ (fun s hs _ => ?_)
  · have h := (hasFDerivAt_snd (𝕜 := ℝ) (p := γ s)).comp_hasDerivAt s (hγ s hs)
    exact h.neg
  · show 1 < (N + 2) * -(γ 0).2
    have : 1 / (N + 2) < -(γ 0).2 := by rw [neg_div] at h0; linarith
    rw [div_lt_iff₀ hk] at this
    linarith
  · have := blowup_w_ge (N := N) (hQt s hs).1 (hQt s hs).2
    linarith

/-! ## Corollary `cor:ON`(i): connecting orbits along the invariant lines -/

/-- The solution `ς(t) (1, k)` with `ς(t) = -1/(α + e^t)`. -/
noncomputable def lineSol (α k : ℝ) (t : ℝ) : ℝ × ℝ :=
  (-(α + exp t)⁻¹, k * -(α + exp t)⁻¹)

theorem isSol_lineSol {k : ℝ} (hk : ∀ y, f₂ N y (k * y) - k * f₁ N y (k * y) = 0)
    (hα : 0 < 9 + (N - 1) * k ^ 2) : IsSol (field N) (lineSol (9 + (N - 1) * k ^ 2) k) := by
  intro t
  set α := 9 + (N - 1) * k ^ 2
  have hne : α + exp t ≠ 0 := by positivity
  have hς : HasDerivAt (fun t => -(α + exp t)⁻¹) (exp t / (α + exp t) ^ 2) t := by
    have := (((hasDerivAt_exp t).const_add α).inv hne).neg
    exact this.congr_deriv (by ring)
  have hval : f₁ N (-(α + exp t)⁻¹) (k * -(α + exp t)⁻¹) = exp t / (α + exp t) ^ 2 := by
    rw [reduced_line_flow]
    field_simp
    ring
  have hval2 : f₂ N (-(α + exp t)⁻¹) (k * -(α + exp t)⁻¹) = k * (exp t / (α + exp t) ^ 2) := by
    have := hk (-(α + exp t)⁻¹)
    rw [← hval]
    linarith
  show HasDerivAt (fun t => (-(α + exp t)⁻¹, k * -(α + exp t)⁻¹))
    (f₁ N (-(α + exp t)⁻¹) (k * -(α + exp t)⁻¹), f₂ N (-(α + exp t)⁻¹) (k * -(α + exp t)⁻¹)) t
  rw [hval, hval2]
  exact hς.prodMk (hς.const_mul k)

theorem tendsto_lineSol_atTop (α k : ℝ) :
    Tendsto (lineSol α k) atTop (𝓝 (0, 0)) := by
  have h : Tendsto (fun t => -(α + exp t)⁻¹) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ α tendsto_exp_atTop)).neg
    simpa using this
  have := h.prodMk_nhds (h.const_mul k)
  rw [mul_zero] at this
  exact this

theorem tendsto_lineSol_atBot {α : ℝ} (hα : 0 < α) (k : ℝ) :
    Tendsto (lineSol α k) atBot (𝓝 (-α⁻¹, k * -α⁻¹)) := by
  have h : Tendsto (fun t => -(α + exp t)⁻¹) atBot (𝓝 (-α⁻¹)) := by
    have h1 : Tendsto (fun t => α + exp t) atBot (𝓝 (α + 0)) :=
      tendsto_exp_atBot.const_add α
    rw [add_zero] at h1
    exact (h1.inv₀ hα.ne').neg
  exact h.prodMk_nhds (h.const_mul k)

theorem bounded_lineSol {α : ℝ} (hα : 0 < α) (k : ℝ) :
    Bornology.IsBounded (range (lineSol α k)) := by
  refine (Metric.isBounded_Icc (-α⁻¹) 0 |>.prod (Metric.isBounded_Icc (-(|k| * α⁻¹))
    (|k| * α⁻¹))).subset ?_
  rintro _ ⟨t, rfl⟩
  simp only [lineSol, mem_prod, mem_Icc]
  have hpos : 0 < α + exp t := by positivity
  have h1 : (α + exp t)⁻¹ ≤ α⁻¹ := inv_anti₀ hα (by linarith [exp_pos t])
  have h0 : 0 < (α + exp t)⁻¹ := inv_pos.2 hpos
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  have habs : |k * -(α + exp t)⁻¹| ≤ |k| * α⁻¹ := by
    rw [abs_mul, abs_neg, abs_of_pos h0]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg k)
  exact abs_le.1 habs

/-- Corollary `cor:ON`(i): for every `N > 1` there are connecting orbits `Σ_I → Σ_G`,
`Σ_H → Σ_G` and `Σ_C → Σ_G` along the three invariant lines. They are bounded full solutions, so
they lie in `B_N`. -/
theorem cor_ON_i (hN : 1 < N) :
    (∃ γ, IsSol (field N) γ ∧ Bornology.IsBounded (range γ) ∧ (∀ t, (γ t).2 = 0) ∧
      Tendsto γ atBot (𝓝 ptI) ∧ Tendsto γ atTop (𝓝 ptG)) ∧
    (∃ γ, IsSol (field N) γ ∧ Bornology.IsBounded (range γ) ∧ (∀ t, (γ t).2 = (γ t).1) ∧
      Tendsto γ atBot (𝓝 (ptH N)) ∧ Tendsto γ atTop (𝓝 ptG)) ∧
    (∃ γ, IsSol (field N) γ ∧ Bornology.IsBounded (range γ) ∧
      (∀ t, (γ t).2 = 3 / (N - 1) * (γ t).1) ∧
      Tendsto γ atBot (𝓝 (ptC N)) ∧ Tendsto γ atTop (𝓝 ptG)) := by
  have hN1 : N - 1 ≠ 0 := by linarith
  have hN0 : N ≠ 0 := by linarith
  have hpos : ∀ k : ℝ, 0 < 9 + (N - 1) * k ^ 2 := fun k => by
    have : 0 ≤ (N - 1) * k ^ 2 := mul_nonneg (by linarith) (sq_nonneg k)
    linarith
  have hline : ∀ k, (k = 0 ∨ k = 1 ∨ k = 3 / (N - 1)) →
      ∀ y, f₂ N y (k * y) - k * f₁ N y (k * y) = 0 := fun k hk =>
    (line_invariant_iff hN).2 hk
  have hG : ((0 : ℝ), (0 : ℝ)) = ptG := rfl
  refine ⟨⟨_, isSol_lineSol (hline 0 (Or.inl rfl)) (hpos 0), bounded_lineSol (hpos 0) 0,
      fun t => by simp [lineSol], ?_, hG ▸ tendsto_lineSol_atTop _ _⟩,
    ⟨_, isSol_lineSol (hline 1 (Or.inr (Or.inl rfl))) (hpos 1), bounded_lineSol (hpos 1) 1,
      fun t => by simp [lineSol], ?_, hG ▸ tendsto_lineSol_atTop _ _⟩,
    ⟨_, isSol_lineSol (hline _ (Or.inr (Or.inr rfl))) (hpos _), bounded_lineSol (hpos _) _,
      fun t => by simp [lineSol], ?_, hG ▸ tendsto_lineSol_atTop _ _⟩⟩
  · convert tendsto_lineSol_atBot (hpos 0) 0 using 2
    simp [ptI]; norm_num
  · convert tendsto_lineSol_atBot (hpos 1) 1 using 2
    simp only [ptH, one_pow, mul_one, one_mul, Prod.mk.injEq]
    constructor <;> ring_nf
  · convert tendsto_lineSol_atBot (hpos (3 / (N - 1))) (3 / (N - 1)) using 2
    rw [alpha_third hN]
    simp only [ptC, Prod.mk.injEq, inv_div]
    constructor <;> field_simp <;> ring

end ConleyCheck.ON
