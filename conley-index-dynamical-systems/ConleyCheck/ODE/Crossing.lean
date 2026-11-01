import ConleyCheck.ODE.Fence

/-!
# Crossing lemmas for scalar functions of time

* `neg_forward`: a strict forward barrier.
* `quadrant_forward`: an open quadrant `{G > 0, K > 0}` whose edges are crossed inward, and whose
  corner is never reached, is positively invariant.
* `tendsto_trichotomy`: if, for every level `ℓ` off a set with dense complement, `x` eventually
  crosses `ℓ` in one fixed direction, then `x` converges in `[-∞, ∞]`.
* `deriv_tendsto_zero`: if `x` and `x'` both converge, `x' → 0`.
* `tendsto_of_monotoneOn_Ici`, `tendsto_of_antitoneOn_Ici`: monotone convergence.
* `dense_compl_quadratic`: the zero set of a quadratic polynomial has dense complement.
-/

open Set Filter Topology

namespace ConleyCheck.ODE

/-- A strict forward barrier: if `g(a) < 0` and `g' < 0` wherever `g = 0` after `a`, then
`g < 0` after `a`. -/
theorem neg_forward {g g' : ℝ → ℝ} (hg : ∀ s, HasDerivAt g (g' s) s) {a : ℝ} (h0 : g a < 0)
    (h : ∀ s, a ≤ s → g s = 0 → g' s < 0) {b : ℝ} (hab : a ≤ b) : g b < 0 := by
  have hle : ∀ t, a ≤ t → g t ≤ 0 := fun t ht =>
    nonpos_forward hg ht h0.le (fun s hs => h s hs.1)
  rcases (hle b hab).lt_or_eq with hb | hb
  · exact hb
  · exfalso
    have hab' : a < b := lt_of_le_of_ne hab (by rintro rfl; linarith)
    obtain ⟨s, hs, hsb⟩ := ((eventually_sign (hg b) (h b hab hb)).2.and (Ioo_mem_nhdsLT hab')).exists
    rw [hb] at hs
    linarith [hle s hsb.1.le]

/-- If `f ≥ 0` on `[a, b]` with `a < b`, and `f' > 0` where `f(b) = 0`, then `f(b) > 0`. -/
theorem pos_of_nonneg_left {f : ℝ → ℝ} {d a b : ℝ} (hf : HasDerivAt f d b) (hab : a < b)
    (hnn : ∀ s ∈ Icc a b, 0 ≤ f s) (hd : f b = 0 → 0 < d) : 0 < f b := by
  rcases (hnn b ⟨hab.le, le_rfl⟩).lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨s, hs, hsb⟩ :=
      ((eventually_sign hf.neg (neg_lt_zero.2 (hd h.symm))).2.and (Ioo_mem_nhdsLT hab)).exists
    have hs' : -f b < -f s := hs
    linarith [hnn s ⟨hsb.1.le, hsb.2.le⟩]

/-- If `f(x) ≥ 0` and `f' > 0` where `f(x) = 0`, then `f ≥ 0` just after `x`. -/
theorem eventually_nonneg_right {f : ℝ → ℝ} {d x : ℝ} (hf : HasDerivAt f d x) (h0 : 0 ≤ f x)
    (hd : f x = 0 → 0 < d) : ∀ᶠ t in 𝓝[>] x, 0 ≤ f t := by
  rcases h0.lt_or_eq with h | h
  · exact nhdsWithin_le_nhds ((hf.continuousAt.eventually (Ioi_mem_nhds h)).mono
      fun _ h => le_of_lt h)
  · exact (eventually_sign hf.neg (neg_lt_zero.2 (hd h.symm))).1.mono fun t ht => by
      have ht' : -f t < -f x := ht
      linarith

/-- An open quadrant `{G > 0, K > 0}` is positively invariant if its edges are crossed inward and
its corner is never reached. -/
theorem quadrant_forward {G G' K K' : ℝ → ℝ} (hG : ∀ s, HasDerivAt G (G' s) s)
    (hK : ∀ s, HasDerivAt K (K' s) s) {a : ℝ} (hG0 : 0 < G a) (hK0 : 0 < K a)
    (hGb : ∀ s, a ≤ s → G s = 0 → 0 < K s → 0 < G' s)
    (hKb : ∀ s, a ≤ s → K s = 0 → 0 < G s → 0 < K' s)
    (hcorner : ∀ s, a ≤ s → ¬(G s = 0 ∧ K s = 0)) {b : ℝ} (hab : a ≤ b) :
    0 < G b ∧ 0 < K b := by
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun s => (hG s).continuousAt
  have hKc : Continuous K := continuous_iff_continuousAt.2 fun s => (hK s).continuousAt
  have hnn : Icc a b ⊆ {t | 0 ≤ G t ∧ 0 ≤ K t} := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin ?_ ⟨hG0.le, hK0.le⟩ ?_
    · exact ((isClosed_le continuous_const hGc).inter (isClosed_le continuous_const hKc)).inter
        isClosed_Icc
    · rintro x ⟨⟨hGx, hKx⟩, hx⟩
      have h1 := eventually_nonneg_right (hG x) hGx fun h => hGb x hx.1 h
        (lt_of_le_of_ne hKx fun h' => hcorner x hx.1 ⟨h, h'.symm⟩)
      have h2 := eventually_nonneg_right (hK x) hKx fun h => hKb x hx.1 h
        (lt_of_le_of_ne hGx fun h' => hcorner x hx.1 ⟨h'.symm, h⟩)
      filter_upwards [h1, h2] with t ht1 ht2 using ⟨ht1, ht2⟩
  rcases hab.lt_or_eq with hab' | rfl
  · refine ⟨pos_of_nonneg_left (hG b) hab' (fun s hs => (hnn hs).1) fun h => hGb b hab h ?_,
      pos_of_nonneg_left (hK b) hab' (fun s hs => (hnn hs).2) fun h => hKb b hab h ?_⟩
    · exact lt_of_le_of_ne (hnn ⟨hab, le_rfl⟩).2 fun h' => hcorner b hab ⟨h, h'.symm⟩
    · exact lt_of_le_of_ne (hnn ⟨hab, le_rfl⟩).1 fun h' => hcorner b hab ⟨h'.symm, h⟩
  · exact ⟨hG0, hK0⟩

theorem eventually_gt_of_cross_pos {x h : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (h t) t) {ℓ t₀ : ℝ}
    (hc : ∀ t, t₀ ≤ t → x t = ℓ → 0 < h t) :
    (∀ᶠ t in atTop, ℓ < x t) ∨ ∀ᶠ t in atTop, x t < ℓ := by
  by_cases hex : ∃ s, t₀ ≤ s ∧ ℓ < x s
  · obtain ⟨s, hs, hxs⟩ := hex
    left
    refine eventually_atTop.2 ⟨s, fun t ht => ?_⟩
    have := neg_forward (g := fun t => ℓ - x t) (g' := fun t => -h t)
      (fun r => ((hasDerivAt_const r ℓ).sub (hx r)).congr_deriv (zero_sub _)) (a := s) (by linarith)
      (fun r hr hr0 => by linarith [hc r (hs.trans hr) (by linarith)]) ht
    linarith
  · push Not at hex
    right
    refine eventually_atTop.2 ⟨t₀, fun t ht => (hex t ht).lt_of_ne fun hxt => ?_⟩
    obtain ⟨s, hs, hst⟩ :=
      ((eventually_sign (hx t).neg (neg_lt_zero.2 (hc t ht hxt))).1.and self_mem_nhdsWithin).exists
    have hs' : -x s < -x t := hs
    have hst' : t < s := hst
    linarith [hex s (ht.trans hst'.le)]

/-- If `x` eventually crosses the level `ℓ` in one fixed direction, then `x` is eventually on one
side of `ℓ`. -/
theorem eventually_lt_or_gt {x h : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (h t) t) {ℓ t₀ : ℝ}
    (hc : (∀ t, t₀ ≤ t → x t = ℓ → 0 < h t) ∨ (∀ t, t₀ ≤ t → x t = ℓ → h t < 0)) :
    (∀ᶠ t in atTop, ℓ < x t) ∨ ∀ᶠ t in atTop, x t < ℓ := by
  rcases hc with hc | hc
  · exact eventually_gt_of_cross_pos hx hc
  · rcases eventually_gt_of_cross_pos (x := fun t => -x t) (h := fun t => -h t) (ℓ := -ℓ)
      (fun t => (hx t).neg) (fun t ht hxt => by linarith [hc t ht (by linarith)]) with h | h
    · exact Or.inr (h.mono fun t ht => by linarith)
    · exact Or.inl (h.mono fun t ht => by linarith)

/-- **Convergence by one-way crossings.** If, for every level `ℓ` outside a set `Z` with dense
complement, `x` eventually crosses `ℓ` in one fixed direction, then `x` converges in
`[-∞, ∞]`. -/
theorem tendsto_trichotomy {x h : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (h t) t) {Z : Set ℝ}
    (hZ : ∀ p q, p < q → ∃ ℓ ∈ Ioo p q, ℓ ∉ Z)
    (hc : ∀ ℓ ∉ Z, ∃ t₀, (∀ t, t₀ ≤ t → x t = ℓ → 0 < h t) ∨ (∀ t, t₀ ≤ t → x t = ℓ → h t < 0)) :
    Tendsto x atTop atTop ∨ Tendsto x atTop atBot ∨ ∃ L, Tendsto x atTop (𝓝 L) := by
  have hD : ∀ ℓ ∉ Z, (∀ᶠ t in atTop, ℓ < x t) ∨ ∀ᶠ t in atTop, x t < ℓ := fun ℓ hℓ => by
    obtain ⟨t₀, h⟩ := hc ℓ hℓ
    exact eventually_lt_or_gt hx h
  set U := {ℓ | ∀ᶠ t in atTop, ℓ < x t}
  by_cases hU : BddAbove U
  · by_cases hne : U.Nonempty
    · refine Or.inr (Or.inr ⟨sSup U, tendsto_order.2 ⟨fun a' ha' => ?_, fun a' ha' => ?_⟩⟩)
      · obtain ⟨u, hu, hau⟩ := exists_lt_of_lt_csSup hne ha'
        exact (show ∀ᶠ t in atTop, u < x t from hu).mono fun t ht => hau.trans ht
      · obtain ⟨ℓ, hℓ, hℓZ⟩ := hZ _ _ ha'
        rcases hD ℓ hℓZ with h | h
        · exact absurd (le_csSup hU h) (not_le.2 hℓ.1)
        · exact h.mono fun t ht => ht.trans hℓ.2
    · refine Or.inr (Or.inl (tendsto_atBot.2 fun M => ?_))
      obtain ⟨ℓ, hℓ, hℓZ⟩ := hZ (M - 1) M (by linarith)
      rcases hD ℓ hℓZ with h | h
      · exact absurd ⟨ℓ, h⟩ hne
      · exact h.mono fun t ht => (ht.trans hℓ.2).le
  · refine Or.inl (tendsto_atTop.2 fun M => ?_)
    rw [not_bddAbove_iff] at hU
    obtain ⟨u, hu, hMu⟩ := hU M
    exact (show ∀ᶠ t in atTop, u < x t from hu).mono fun t ht => (hMu.trans ht).le

/-- The crossing hypothesis of `tendsto_trichotomy` at one level, when `x' = m k` at that level
with `m > 0` and `k → K ≠ 0`. -/
theorem cross_of_tendsto {x h m k : ℝ → ℝ} {ℓ K : ℝ} (hm : ∀ t, 0 < m t)
    (hh : ∀ t, x t = ℓ → h t = m t * k t) (hk : Tendsto k atTop (𝓝 K)) (hK : K ≠ 0) :
    ∃ t₀, (∀ t, t₀ ≤ t → x t = ℓ → 0 < h t) ∨ (∀ t, t₀ ≤ t → x t = ℓ → h t < 0) := by
  rcases lt_or_gt_of_ne hK with hK | hK
  · obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 (hk.eventually (Iio_mem_nhds hK))
    exact ⟨t₀, Or.inr fun t ht hxt => by
      rw [hh t hxt]; exact mul_neg_of_pos_of_neg (hm t) (ht₀ t ht)⟩
  · obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 (hk.eventually (Ioi_mem_nhds hK))
    exact ⟨t₀, Or.inl fun t ht hxt => by rw [hh t hxt]; exact mul_pos (hm t) (ht₀ t ht)⟩

theorem deriv_tendsto_zero_aux {x h : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (h t) t) {L H : ℝ}
    (hxL : Tendsto x atTop (𝓝 L)) (hH : Tendsto h atTop (𝓝 H)) (hpos : 0 < H) : False := by
  obtain ⟨t₁, ht₁⟩ := eventually_atTop.1 ((hH.eventually (Ioi_mem_nhds (half_lt_self hpos))).and
    (hxL.eventually (Iio_mem_nhds (lt_add_one L))))
  have hgrow := growth_fwd hx (t₀ := t₁) (c := H / 2) (by positivity)
    (fun t ht _ => (ht₁ t ht).1.le)
  set t := t₁ + 4 * (|L + 1 - x t₁| + 1) / H
  have htt : t₁ ≤ t := by
    have : 0 ≤ 4 * (|L + 1 - x t₁| + 1) / H := by positivity
    linarith
  have h1 := hgrow t htt
  have h2 := (ht₁ t htt).2
  have h3 : H / 2 / 2 * (t - t₁) = |L + 1 - x t₁| + 1 := by
    simp only [t, add_sub_cancel_left]; field_simp; ring
  linarith [le_abs_self (L + 1 - x t₁)]

/-- If `x` and `x'` both converge as `t → ∞`, then `x' → 0`. -/
theorem deriv_tendsto_zero {x h : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (h t) t) {L H : ℝ}
    (hxL : Tendsto x atTop (𝓝 L)) (hH : Tendsto h atTop (𝓝 H)) : H = 0 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hn | hp
  · exact deriv_tendsto_zero_aux (x := fun t => -x t) (h := fun t => -h t) (fun t => (hx t).neg)
      hxL.neg hH.neg (by linarith)
  · exact deriv_tendsto_zero_aux hx hxL hH hp

theorem tendsto_of_monotoneOn_Ici {f : ℝ → ℝ} {a : ℝ} (hf : MonotoneOn f (Ici a)) :
    Tendsto f atTop atTop ∨ ∃ L, Tendsto f atTop (𝓝 L) := by
  have hg : Monotone fun t => f (max t a) := fun s t hst =>
    hf (mem_Ici.2 (le_max_right _ _)) (mem_Ici.2 (le_max_right _ _)) (max_le_max hst le_rfl)
  have heq : (fun t => f (max t a)) =ᶠ[atTop] f :=
    (eventually_ge_atTop a).mono fun t ht => by simp [max_eq_left ht]
  by_cases hb : BddAbove (range fun t => f (max t a))
  · exact Or.inr ⟨_, (tendsto_atTop_ciSup hg hb).congr' heq⟩
  · refine Or.inl ((tendsto_atTop_atTop_of_monotone hg fun b => ?_).congr' heq)
    rw [not_bddAbove_iff] at hb
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hb b
    exact ⟨t, ht.le⟩

theorem tendsto_of_antitoneOn_Ici {f : ℝ → ℝ} {a : ℝ} (hf : AntitoneOn f (Ici a))
    (hlow : ∀ t, 0 ≤ f t) : ∃ L, Tendsto f atTop (𝓝 L) := by
  rcases tendsto_of_monotoneOn_Ici (f := fun t => -f t) (a := a)
      (fun s hs t ht hst => neg_le_neg (hf hs ht hst)) with h | ⟨L, h⟩
  · obtain ⟨t, ht⟩ := (h.eventually (eventually_gt_atTop 0)).exists
    linarith [hlow t]
  · exact ⟨-L, by simpa using h.neg⟩

theorem monotoneOn_Ici_of_deriv {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) {a : ℝ}
    (h : ∀ t, a ≤ t → 0 ≤ f' t) : MonotoneOn f (Ici a) :=
  monotoneOn_of_deriv_nonneg (convex_Ici a) (fun t _ => (hf t).continuousAt.continuousWithinAt)
    (fun t _ => (hf t).differentiableAt.differentiableWithinAt)
    fun t ht => by rw [(hf t).deriv]; exact h t (interior_subset ht)

theorem antitoneOn_Ici_of_deriv {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) {a : ℝ}
    (h : ∀ t, a ≤ t → f' t ≤ 0) : AntitoneOn f (Ici a) :=
  antitoneOn_of_deriv_nonpos (convex_Ici a) (fun t _ => (hf t).continuousAt.continuousWithinAt)
    (fun t _ => (hf t).differentiableAt.differentiableWithinAt)
    fun t ht => by rw [(hf t).deriv]; exact h t (interior_subset ht)

/-- A nonzero quadratic vanishes at no more than two points, so its zero set has dense
complement. -/
theorem dense_compl_quadratic {α β γ : ℝ} (hα : α ≠ 0) :
    ∀ p q, p < q → ∃ ℓ ∈ Ioo p q, ℓ ∉ {ℓ : ℝ | α * ℓ ^ 2 + β * ℓ + γ = 0} := by
  intro p q hpq
  by_contra h
  push Not at h
  set d := (q - p) / 4
  have hd : 0 < d := by simp only [d]; linarith
  have h1 : α * (p + d) ^ 2 + β * (p + d) + γ = 0 := h _ ⟨by linarith, by simp only [d]; linarith⟩
  have h2 : α * (p + 2 * d) ^ 2 + β * (p + 2 * d) + γ = 0 :=
    h _ ⟨by linarith, by simp only [d]; linarith⟩
  have h3 : α * (p + 3 * d) ^ 2 + β * (p + 3 * d) + γ = 0 :=
    h _ ⟨by linarith, by simp only [d]; linarith⟩
  have : α * (2 * d ^ 2) = 0 := by linear_combination h1 - 2 * h2 + h3
  rcases mul_eq_zero.1 this with h | h
  · exact hα h
  · nlinarith

end ConleyCheck.ODE
