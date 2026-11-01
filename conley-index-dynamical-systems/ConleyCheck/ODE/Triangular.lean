import ConleyCheck.ODE.Affine

/-!
# Bounded solutions of triangular systems

* `not_bdd_of_growth`, `not_bdd_of_growth_back`: a positive solution of `f' = k f + m` with
  `k ≥ c > 0` and `m ≥ 0` grows at least linearly, in forward time, and the time-reversed
  statement.
* `lin_zero_of_ge`, `lin_zero_of_le`: a bounded solution of `x' = h x` with `h ≥ c > 0` or
  `h ≤ -c < 0` everywhere vanishes.
* `tri_zero`: a bounded solution of `x' = h x`, `y' = κ y + a x` with `a > 0`, `κ ≥ c` near `+∞`
  and `κ ≤ -c` near `-∞` vanishes. If `x > 0`, then `y` can cross `0` only upward, so `y < 0` before
  any time with `y ≤ 0`, which forces backward growth, and `y > 0` everywhere forces forward growth.
-/

open Set

namespace ConleyCheck.ODE

private theorem monotoneOn_Ici_of_deriv {f f' : ℝ → ℝ} {t₀ : ℝ} (hf : ∀ s, HasDerivAt f (f' s) s)
    (h : ∀ s ≥ t₀, 0 ≤ f' s) : MonotoneOn f (Ici t₀) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici t₀)
    (fun s _ => (hf s).continuousAt.continuousWithinAt)
    (fun s _ => (hf s).hasDerivWithinAt)
    (fun s hs => h s (interior_subset hs))

/-- A positive solution of `f' = k f + m` with `k ≥ c > 0` and `m ≥ 0` after `t₀` is unbounded. -/
theorem not_bdd_of_growth {f k m : ℝ → ℝ} {c B t₀ : ℝ}
    (hf : ∀ s, HasDerivAt f (k s * f s + m s) s) (hk : Continuous k) (hc : 0 < c)
    (hkc : ∀ s ≥ t₀, c ≤ k s) (hm : ∀ s ≥ t₀, 0 ≤ m s) (h0 : 0 < f t₀) (hB : ∀ s, f s ≤ B) :
    False := by
  have hpos : ∀ s ≥ t₀, 0 < f s := fun s hs =>
    affine_pos hf hk hs (fun r hr => hm r hr.1) h0
  have hmono : MonotoneOn f (Ici t₀) := monotoneOn_Ici_of_deriv hf fun s hs => by
    have := hkc s hs; have := hpos s hs; have := hm s hs; nlinarith
  have hlin : MonotoneOn (fun s => f s - c * f t₀ * s) (Ici t₀) :=
    monotoneOn_Ici_of_deriv (f' := fun s => k s * f s + m s - c * f t₀)
      (fun s => (hf s).sub ((hasDerivAt_id s).const_mul (c * f t₀) |>.congr_deriv (mul_one _)))
      fun s hs => by
        have h1 := hkc s hs; have h2 := hpos s hs; have h3 := hm s hs
        have h4 : f t₀ ≤ f s := hmono self_mem_Ici hs hs
        nlinarith
  set s := t₀ + (|B| + 1) / (c * f t₀) with hs
  have hst : t₀ ≤ s := by
    have : 0 ≤ (|B| + 1) / (c * f t₀) := by positivity
    linarith
  have := hlin self_mem_Ici hst hst
  simp only at this
  have hcs : c * f t₀ * s = c * f t₀ * t₀ + (|B| + 1) := by
    rw [hs, mul_add, mul_div_cancel₀ _ (by positivity)]
  have := hB s
  have := le_abs_self B
  linarith

/-- The time-reversed statement: `k ≤ -c < 0` and `m ≤ 0` before `t₀`. -/
theorem not_bdd_of_growth_back {f k m : ℝ → ℝ} {c B t₀ : ℝ}
    (hf : ∀ s, HasDerivAt f (k s * f s + m s) s) (hk : Continuous k) (hc : 0 < c)
    (hkc : ∀ s ≤ t₀, k s ≤ -c) (hm : ∀ s ≤ t₀, m s ≤ 0) (h0 : 0 < f t₀) (hB : ∀ s, f s ≤ B) :
    False := by
  refine not_bdd_of_growth (f := fun r => f (-r)) (k := fun r => -k (-r)) (m := fun r => -m (-r))
    (c := c) (B := B) (t₀ := -t₀) (fun r => ?_) (hk.comp continuous_neg).neg hc
    (fun r hr => by have := hkc (-r) (by linarith); linarith)
    (fun r hr => by have := hm (-r) (by linarith); linarith) (by simpa using h0) (fun r => hB _)
  have := (hf (-r)).comp r (hasDerivAt_neg r)
  exact this.congr_deriv (by ring)

/-- A bounded solution of `x' = h x` with `h ≥ c > 0` vanishes. -/
theorem lin_zero_of_ge {x h : ℝ → ℝ} {c B : ℝ} (hc : 0 < c)
    (hx : ∀ t, HasDerivAt x (h t * x t) t) (hh : Continuous h) (hb : ∀ t, |x t| ≤ B)
    (hge : ∀ t, c ≤ h t) (t : ℝ) : x t = 0 := by
  rcases lt_trichotomy (x t) 0 with hlt | heq | hgt
  · exact (not_bdd_of_growth (f := fun s => -x s) (m := fun _ => 0) (B := B) (t₀ := t)
      (fun s => ((hx s).neg).congr_deriv (by ring)) hh hc (fun s _ => hge s) (fun _ _ => le_rfl)
      (by linarith) (fun s => (neg_le_abs _).trans (hb s))).elim
  · exact heq
  · exact (not_bdd_of_growth (m := fun _ => 0) (B := B) (t₀ := t)
      (fun s => (hx s).congr_deriv (by ring)) hh hc (fun s _ => hge s) (fun _ _ => le_rfl)
      hgt (fun s => (le_abs_self _).trans (hb s))).elim

/-- A bounded solution of `x' = h x` with `h ≤ -c < 0` vanishes. -/
theorem lin_zero_of_le {x h : ℝ → ℝ} {c B : ℝ} (hc : 0 < c)
    (hx : ∀ t, HasDerivAt x (h t * x t) t) (hh : Continuous h) (hb : ∀ t, |x t| ≤ B)
    (hle : ∀ t, h t ≤ -c) (t : ℝ) : x t = 0 := by
  rcases lt_trichotomy (x t) 0 with hlt | heq | hgt
  · exact (not_bdd_of_growth_back (f := fun s => -x s) (m := fun _ => 0) (B := B) (t₀ := t)
      (fun s => ((hx s).neg).congr_deriv (by ring)) hh hc (fun s _ => hle s) (fun _ _ => le_rfl)
      (by linarith) (fun s => (neg_le_abs _).trans (hb s))).elim
  · exact heq
  · exact (not_bdd_of_growth_back (m := fun _ => 0) (B := B) (t₀ := t)
      (fun s => (hx s).congr_deriv (by ring)) hh hc (fun s _ => hle s) (fun _ _ => le_rfl)
      hgt (fun s => (le_abs_self _).trans (hb s))).elim

/-- A solution of `x' = h x` that is positive at one time is positive at all times. -/
theorem lin_pos_of_pos {x h : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (h t * x t) t) (hh : Continuous h)
    {t₀ : ℝ} (h0 : 0 < x t₀) (t : ℝ) : 0 < x t := by
  have hx' : ∀ s, HasDerivAt x (h s * x s + 0) s := fun s => (hx s).congr_deriv (by ring)
  rcases le_total t₀ t with h1 | h1
  · exact affine_pos hx' hh h1 (fun _ _ => le_rfl) h0
  · by_contra hn
    push Not at hn
    have := affine_nonpos hx' hh h1 (fun _ _ => le_rfl) hn
    linarith

/-- A bounded solution of `x' = h x` with `h ≤ -c < 0` on `(-∞, T]` vanishes. -/
theorem lin_zero_of_le_back {x h : ℝ → ℝ} {c B T : ℝ} (hc : 0 < c)
    (hx : ∀ t, HasDerivAt x (h t * x t) t) (hh : Continuous h) (hb : ∀ t, |x t| ≤ B)
    (hle : ∀ t ≤ T, h t ≤ -c) (t : ℝ) : x t = 0 := by
  have key : ∀ {f : ℝ → ℝ}, (∀ s, HasDerivAt f (h s * f s) s) → (∀ s, |f s| ≤ B) →
      ¬ 0 < f t := fun {f} hf hb hpos => by
    have h3 : 0 < f (min T t) := lin_pos_of_pos hf hh hpos _
    exact not_bdd_of_growth_back (m := fun _ => 0) (B := B) (t₀ := min T t)
      (fun s => (hf s).congr_deriv (by ring)) hh hc
      (fun s hs => hle s (hs.trans (min_le_left _ _))) (fun _ _ => le_rfl) h3
      (fun s => (le_abs_self _).trans (hb s))
  rcases lt_trichotomy (x t) 0 with hlt | heq | hgt
  · exact absurd (by linarith : 0 < -x t) (key (f := fun s => -x s)
      (fun s => ((hx s).neg).congr_deriv (by ring)) (fun s => by rw [abs_neg]; exact hb s))
  · exact heq
  · exact absurd hgt (key hx hb)

section Tri

variable {x y h κ : ℝ → ℝ} {a c B T : ℝ}

/-- The case `x > 0` is impossible. -/
theorem tri_pos_false (ha : 0 < a) (hc : 0 < c)
    (hx : ∀ t, HasDerivAt x (h t * x t) t) (hh : Continuous h)
    (hy : ∀ t, HasDerivAt y (κ t * y t + a * x t) t) (hκ : Continuous κ)
    (hby : ∀ t, |y t| ≤ B) (hT1 : ∀ t ≥ T, c ≤ κ t) (hT2 : ∀ t ≤ -T, κ t ≤ -c)
    {t₀ : ℝ} (h0 : 0 < x t₀) : False := by
  have hx' : ∀ s, HasDerivAt x (h s * x s + 0) s := fun s => (hx s).congr_deriv (by ring)
  have xpos : ∀ t, 0 < x t := by
    intro t
    rcases le_total t₀ t with h1 | h1
    · exact affine_pos hx' hh h1 (fun _ _ => le_rfl) h0
    · by_contra hn
      push Not at hn
      have := affine_nonpos hx' hh h1 (fun _ _ => le_rfl) hn
      linarith
  have ypos : ∀ t, 0 < y t := by
    intro t₁
    by_contra hn
    push Not at hn
    have hneg : ∀ s ≤ t₁, s < t₁ → y s < 0 := by
      intro s _ hs
      by_contra hn'
      push Not at hn'
      have := affine_pos_of_end hy hκ hs (fun r _ => (mul_pos ha (xpos r)).le)
        (mul_pos ha (xpos t₁)) hn'
      linarith
    set t₂ := min (t₁ - 1) (-T)
    have ht₂ : t₂ < t₁ := (min_le_left _ _).trans_lt (by linarith)
    exact not_bdd_of_growth_back (f := fun s => -y s) (k := κ) (m := fun s => -(a * x s))
      (B := B) (t₀ := t₂) (fun s => ((hy s).neg).congr_deriv (by ring)) hκ hc
      (fun s hs => hT2 s (hs.trans (min_le_right _ _)))
      (fun s _ => by have := mul_pos ha (xpos s); linarith)
      (by have := hneg t₂ ht₂.le ht₂; linarith) (fun s => (neg_le_abs _).trans (hby s))
  exact not_bdd_of_growth (f := y) (k := κ) (m := fun s => a * x s) (B := B) (t₀ := max T 0) hy
    hκ hc (fun s hs => hT1 s ((le_max_left _ _).trans hs)) (fun s _ => (mul_pos ha (xpos s)).le)
    (ypos _) (fun s => (le_abs_self _).trans (hby s))

/-- A bounded solution of `x' = h x`, `y' = κ y + a x` with `a > 0`, `κ ≥ c` after `T` and
`κ ≤ -c` before `-T` vanishes. -/
theorem tri_zero (ha : 0 < a) (hc : 0 < c)
    (hx : ∀ t, HasDerivAt x (h t * x t) t) (hh : Continuous h)
    (hy : ∀ t, HasDerivAt y (κ t * y t + a * x t) t) (hκ : Continuous κ)
    (hby : ∀ t, |y t| ≤ B) (hT1 : ∀ t ≥ T, c ≤ κ t) (hT2 : ∀ t ≤ -T, κ t ≤ -c) (t : ℝ) :
    x t = 0 ∧ y t = 0 := by
  have hx0 : ∀ t, x t = 0 := by
    intro t
    rcases lt_trichotomy (x t) 0 with hlt | heq | hgt
    · exact (tri_pos_false (x := fun s => -x s) (y := fun s => -y s) (h := h) (κ := κ) ha hc
        (fun s => ((hx s).neg).congr_deriv (by ring)) hh
        (fun s => ((hy s).neg).congr_deriv (by ring)) hκ (fun s => by rw [abs_neg]; exact hby s)
        hT1 hT2 (t₀ := t) (by linarith)).elim
    · exact heq
    · exact (tri_pos_false ha hc hx hh hy hκ hby hT1 hT2 hgt).elim
  refine ⟨hx0 t, ?_⟩
  have hy' : ∀ s, HasDerivAt y (κ s * y s + 0) s := fun s => by
    have := hy s
    rwa [hx0 s, mul_zero] at this
  have key : ∀ {f : ℝ → ℝ}, (∀ s, HasDerivAt f (κ s * f s + 0) s) → (∀ s, |f s| ≤ B) →
      ¬ 0 < f t := fun {f} hf hb hpos => by
    have h3 : 0 < f (max T t) := affine_pos hf hκ (le_max_right _ _) (fun _ _ => le_rfl) hpos
    exact not_bdd_of_growth (m := fun _ => 0) (B := B) (t₀ := max T t) hf hκ hc
      (fun s hs => hT1 s ((le_max_left _ _).trans hs)) (fun _ _ => le_rfl) h3
      (fun s => (le_abs_self _).trans (hb s))
  rcases lt_trichotomy (y t) 0 with hlt | heq | hgt
  · exact absurd (by linarith : 0 < -y t) (key (f := fun s => -y s)
      (fun s => ((hy' s).neg).congr_deriv (by ring)) (fun s => by rw [abs_neg]; exact hby s))
  · exact heq
  · exact absurd hgt (key hy' hby)

end Tri

end ConleyCheck.ODE
