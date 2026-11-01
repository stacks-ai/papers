import ConleyCheck.ODE.Fence

/-!
# Affine differential inequalities

Solutions of `g' = k g + m` with `m ≥ 0` keep the signs `g ≥ 0` and `g > 0` in forward time
(`affine_nonneg`, `affine_pos`), and those with `m ≤ 0` keep `g ≤ 0` and `g < 0`.

An excursion of a continuous function above zero (`exists_excursion`) starts with a nonnegative and
ends with a nonpositive derivative (`deriv_nonneg_of_excursion`, `deriv_nonpos_of_excursion`).
-/

open Set

namespace ConleyCheck.ODE

variable {g k m : ℝ → ℝ} {a b : ℝ}

theorem affine_nonneg (hg : ∀ s, HasDerivAt g (k s * g s + m s) s) (hk : Continuous k)
    (hab : a ≤ b) (hm : ∀ s ∈ Icc a b, 0 ≤ m s) (h0 : 0 ≤ g a) : 0 ≤ g b := by
  have := fence_affine (g := fun s => -g (a + s)) (g' := fun s => -(k (a + s) * g (a + s) +
      m (a + s))) (m := fun s => m (a + s)) (k := fun s => k (a + s)) (t := b - a) (by linarith)
    (fun s _ => ((hg (a + s)).comp_const_add a s).neg) (by simpa using h0)
    (fun s _ => by ring) (fun s hs => hm _ ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    (hk.comp (continuous_const.add continuous_id)).continuousOn
  simp only [add_sub_cancel] at this
  linarith

theorem affine_pos (hg : ∀ s, HasDerivAt g (k s * g s + m s) s) (hk : Continuous k)
    (hab : a ≤ b) (hm : ∀ s ∈ Icc a b, 0 ≤ m s) (h0 : 0 < g a) : 0 < g b := by
  by_contra hb
  push Not at hb
  have := fence_affine (g := fun s => g (b - s)) (g' := fun s => -(k (b - s) * g (b - s) +
      m (b - s))) (m := fun s => m (b - s)) (k := fun s => -k (b - s)) (t := b - a) (by linarith)
    (fun s _ => by
      have := (hg (b - s)).comp s ((hasDerivAt_id s).const_sub b)
      exact this.congr_deriv (by ring)) (by simpa using hb)
    (fun s _ => by ring) (fun s hs => hm _ ⟨by linarith [hs.2], by linarith [hs.1]⟩)
    ((hk.comp (continuous_const.sub continuous_id)).neg).continuousOn
  simp only [sub_sub_cancel] at this
  linarith

theorem affine_nonpos (hg : ∀ s, HasDerivAt g (k s * g s + m s) s) (hk : Continuous k)
    (hab : a ≤ b) (hm : ∀ s ∈ Icc a b, m s ≤ 0) (h0 : g a ≤ 0) : g b ≤ 0 := by
  have := affine_nonneg (g := fun s => -g s) (k := k) (m := fun s => -m s)
    (fun s => ((hg s).neg).congr_deriv (by ring)) hk hab (fun s hs => by linarith [hm s hs])
    (by linarith)
  linarith

theorem affine_neg (hg : ∀ s, HasDerivAt g (k s * g s + m s) s) (hk : Continuous k)
    (hab : a ≤ b) (hm : ∀ s ∈ Icc a b, m s ≤ 0) (h0 : g a < 0) : g b < 0 := by
  have := affine_pos (g := fun s => -g s) (k := k) (m := fun s => -m s)
    (fun s => ((hg s).neg).congr_deriv (by ring)) hk hab (fun s hs => by linarith [hm s hs])
    (by linarith)
  linarith

/-- A solution of `g' = k g + m` with `g(a) ≥ 0`, `m ≥ 0` on `[a, b]` and `m(b) > 0` is positive
at `b > a`. -/
theorem affine_pos_of_end (hg : ∀ s, HasDerivAt g (k s * g s + m s) s) (hk : Continuous k)
    (hab : a < b) (hm : ∀ s ∈ Icc a b, 0 ≤ m s) (hmb : 0 < m b) (h0 : 0 ≤ g a) : 0 < g b := by
  have hnn : ∀ s ∈ Icc a b, 0 ≤ g s := fun s hs =>
    affine_nonneg hg hk hs.1 (fun r hr => hm r ⟨hr.1, hr.2.trans hs.2⟩) h0
  by_contra hb
  push Not at hb
  have hb0 : g b = 0 := le_antisymm hb (hnn b ⟨hab.le, le_rfl⟩)
  have hd : 0 < k b * g b + m b := by rw [hb0, mul_zero, zero_add]; exact hmb
  have := (eventually_sign (hg b).neg (neg_lt_zero.2 hd)).2
  obtain ⟨s, hs, hsb⟩ := (this.and (Ioo_mem_nhdsLT hab)).exists
  simp only [Pi.neg_apply, hb0, neg_zero, neg_pos] at hs
  linarith [hnn s ⟨hsb.1.le, hsb.2.le⟩]

/-! ## Excursions -/

/-- A continuous function that is `≤ 0` at `t₁` and `t₃` and positive at `t₂ ∈ [t₁, t₃]` has an
excursion `(s₁, s₂) ∋ t₂` above zero with `f(s₁) = f(s₂) = 0`. -/
theorem exists_excursion {f : ℝ → ℝ} (hf : Continuous f) {t₁ t₂ t₃ : ℝ} (h12 : t₁ ≤ t₂)
    (h23 : t₂ ≤ t₃) (h1 : f t₁ ≤ 0) (h2 : 0 < f t₂) (h3 : f t₃ ≤ 0) :
    ∃ s₁ s₂, t₁ ≤ s₁ ∧ s₁ < s₂ ∧ s₂ ≤ t₃ ∧ f s₁ = 0 ∧ f s₂ = 0 ∧ ∀ s ∈ Ioo s₁ s₂, 0 < f s := by
  have hA : IsCompact {s ∈ Icc t₁ t₂ | f s ≤ 0} :=
    isCompact_Icc.inter_right (isClosed_le hf continuous_const)
  have hB : IsCompact {s ∈ Icc t₂ t₃ | f s ≤ 0} :=
    isCompact_Icc.inter_right (isClosed_le hf continuous_const)
  obtain ⟨s₁, ⟨hs₁, hf₁⟩, hmax⟩ := hA.exists_isGreatest ⟨t₁, ⟨le_rfl, h12⟩, h1⟩
  obtain ⟨s₂, ⟨hs₂, hf₂⟩, hmin⟩ := hB.exists_isLeast ⟨t₃, ⟨h23, le_rfl⟩, h3⟩
  have hs₁2 : s₁ < t₂ := lt_of_le_of_ne hs₁.2 fun h => by rw [h] at hf₁; linarith
  have hs₂2 : t₂ < s₂ := lt_of_le_of_ne hs₂.1 fun h => by rw [← h] at hf₂; linarith
  have hpos : ∀ s ∈ Ioo s₁ s₂, 0 < f s := by
    intro s hs
    by_contra hneg
    push Not at hneg
    rcases le_total s t₂ with h | h
    · have := hmax ⟨⟨hs₁.1.trans hs.1.le, h⟩, hneg⟩
      linarith [hs.1]
    · have := hmin ⟨⟨h, hs.2.le.trans hs₂.2⟩, hneg⟩
      linarith [hs.2]
  have hge : ∀ {s : ℝ} {g : ℝ → ℝ}, Continuous g → ∀ {a b : ℝ}, a < b → (∀ r ∈ Ioo a b, 0 < g r) →
      (s = a ∨ s = b) → 0 ≤ g s := by
    intro s g hg a b hab hg' hs
    have hcl : closure (Ioo a b) ⊆ {r | 0 ≤ g r} :=
      closure_minimal (fun r hr => (hg' r hr).le) (isClosed_le continuous_const hg)
    rw [closure_Ioo hab.ne] at hcl
    rcases hs with rfl | rfl
    · exact hcl ⟨le_rfl, hab.le⟩
    · exact hcl ⟨hab.le, le_rfl⟩
  refine ⟨s₁, s₂, hs₁.1, hs₁2.trans hs₂2, hs₂.2, ?_, ?_, hpos⟩
  · exact le_antisymm hf₁ (hge hf (hs₁2.trans hs₂2) hpos (Or.inl rfl))
  · exact le_antisymm hf₂ (hge hf (hs₁2.trans hs₂2) hpos (Or.inr rfl))

theorem deriv_nonneg_of_excursion {f : ℝ → ℝ} {d s₁ s₂ : ℝ} (hd : HasDerivAt f d s₁)
    (h0 : f s₁ = 0) (hs : s₁ < s₂) (hpos : ∀ s ∈ Ioo s₁ s₂, 0 < f s) : 0 ≤ d := by
  by_contra h
  push Not at h
  obtain ⟨s, hs1, hs2⟩ := ((eventually_sign hd h).1.and (Ioo_mem_nhdsGT hs)).exists
  linarith [hpos s hs2]

theorem deriv_nonpos_of_excursion {f : ℝ → ℝ} {d s₁ s₂ : ℝ} (hd : HasDerivAt f d s₂)
    (h0 : f s₂ = 0) (hs : s₁ < s₂) (hpos : ∀ s ∈ Ioo s₁ s₂, 0 < f s) : d ≤ 0 := by
  by_contra h
  push Not at h
  obtain ⟨s, hs1, hs2⟩ := ((eventually_sign hd.neg (neg_lt_zero.2 h)).2.and
    (Ioo_mem_nhdsLT hs)).exists
  simp only [Pi.neg_apply, h0, neg_zero] at hs1
  linarith [hpos s hs2]

/-- A function with no excursions above zero inside `[t₁, t₃]` stays `≤ 0` there. -/
theorem nonpos_of_no_excursion {f : ℝ → ℝ} (hf : Continuous f) {t₁ t₂ t₃ : ℝ} (h12 : t₁ ≤ t₂)
    (h23 : t₂ ≤ t₃) (h1 : f t₁ ≤ 0) (h3 : f t₃ ≤ 0)
    (hno : ∀ s₁ s₂, t₁ ≤ s₁ → s₁ < s₂ → s₂ ≤ t₃ → f s₁ = 0 → f s₂ = 0 →
      (∀ s ∈ Ioo s₁ s₂, 0 < f s) → False) : f t₂ ≤ 0 := by
  by_contra h
  push Not at h
  obtain ⟨s₁, s₂, h1', h12', h23', hf1, hf2, hpos⟩ := exists_excursion hf h12 h23 h1 h h3
  exact hno s₁ s₂ h1' h12' h23' hf1 hf2 hpos

end ConleyCheck.ODE
