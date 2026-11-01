import ConleyCheck.ON.Limits

/-!
# Unstable manifolds of the saddles of the `O(N)`-type model

* `on_line_of_tendsto_atBot`: if the invariant line `y₂ = k y₁` attracts transversally at a fixed
  point `q`, i.e. `(y₂ - k y₁)' = -(y₂ - k y₁) κ(y)` with `κ(q) > 0`, then every orbit of `B_N` whose
  `α`-limit is `q` lies on the line. The proof only uses that `(y₂ - k y₁)²` decreases near `q`.
* `mem_Icc_of_tendsto`: a curve with distinct limits `a` at `-∞` and `b` at `+∞`, which is constant
  as soon as it takes the value `a` or `b`, stays between `a` and `b`.
-/

open Set Filter Topology

namespace ConleyCheck.ON

open ConleyCheck.Conley ConleyCheck.ODE

variable {N : ℝ}

theorem hasDerivAt_fst_of_Inv {x : ℝ × ℝ} (hx : x ∈ Inv (flowON N) blockR) (t : ℝ) :
    HasDerivAt (fun s => (flowON N s x).1) (f₁ N (flowON N t x).1 (flowON N t x).2) t := by
  have hd := hasDerivAt_flowON N x t
  rw [cutField_eq_on_R (hx t)] at hd
  exact (hasFDerivAt_fst (𝕜 := ℝ) (p := flowON N t x)).comp_hasDerivAt t hd

theorem hasDerivAt_snd_of_Inv {x : ℝ × ℝ} (hx : x ∈ Inv (flowON N) blockR) (t : ℝ) :
    HasDerivAt (fun s => (flowON N s x).2) (f₂ N (flowON N t x).1 (flowON N t x).2) t := by
  have hd := hasDerivAt_flowON N x t
  rw [cutField_eq_on_R (hx t)] at hd
  exact (hasFDerivAt_snd (𝕜 := ℝ) (p := flowON N t x)).comp_hasDerivAt t hd

/-- If the line `y₂ = k y₁` attracts transversally at the fixed point `q`, every orbit in `B_N`
with `α`-limit `q` lies on that line. -/
theorem on_line_of_tendsto_atBot {k a b : ℝ}
    (hid : ∀ y₁ y₂, f₂ N y₁ y₂ - k * f₁ N y₁ y₂ = -(y₂ - k * y₁) * (1 + a * y₁ + b * y₂))
    {x q : ℝ × ℝ} (hx : x ∈ Inv (flowON N) blockR)
    (hq : Tendsto (fun t => flowON N t x) atBot (𝓝 q)) (hqline : q.2 = k * q.1)
    (hpos : 0 < 1 + a * q.1 + b * q.2) (t : ℝ) : (flowON N t x).2 = k * (flowON N t x).1 := by
  set W : ℝ → ℝ := fun s => (flowON N s x).2 - k * (flowON N s x).1 with hWdef
  set κ : ℝ → ℝ := fun s => 1 + a * (flowON N s x).1 + b * (flowON N s x).2 with hκdef
  have hW : ∀ s, HasDerivAt W (-κ s * W s) s := fun s => by
    have h := (hasDerivAt_snd_of_Inv hx s).sub ((hasDerivAt_fst_of_Inv hx s).const_mul k)
    convert h using 1
    rw [hid]
    simp only [hWdef, hκdef]
    ring
  have hcont : Continuous fun s => flowON N s x := continuous_orbit x
  have hκc : Continuous κ :=
    continuous_const.add ((continuous_const.mul (continuous_fst.comp hcont))) |>.add
      (continuous_const.mul (continuous_snd.comp hcont))
  have hκlim : Tendsto κ atBot (𝓝 (1 + a * q.1 + b * q.2)) :=
    ((continuous_const.add (continuous_const.mul continuous_fst)).add
      (continuous_const.mul continuous_snd)).continuousAt.tendsto.comp hq
  have hWlim : Tendsto W atBot (𝓝 0) := by
    have : Tendsto W atBot (𝓝 (q.2 - k * q.1)) :=
      (continuous_snd.sub (continuous_const.mul continuous_fst)).continuousAt.tendsto.comp hq
    rwa [hqline, sub_self] at this
  obtain ⟨T, hT⟩ := eventually_atBot.1 (hκlim.eventually (Ioi_mem_nhds hpos))
  have hF : ∀ s, HasDerivAt (fun s => W s ^ 2) (2 * W s * (-κ s * W s)) s := fun s => by
    convert (hW s).pow 2 using 1
    push_cast
    ring
  have hanti : AntitoneOn (fun s => W s ^ 2) (Iic T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Iic T)
      (fun s _ => (hF s).continuousAt.continuousWithinAt)
      (fun s _ => (hF s).differentiableAt.differentiableWithinAt) fun s hs => ?_
    rw [interior_Iic] at hs
    rw [(hF s).deriv]
    have := hT s hs.le
    have : 0 ≤ W s ^ 2 := sq_nonneg _
    nlinarith
  have hWT : W T ^ 2 ≤ 0 := by
    have hlim : Tendsto (fun s => W s ^ 2) atBot (𝓝 0) := by
      simpa using hWlim.pow 2
    exact ge_of_tendsto hlim (eventually_atBot.2 ⟨T, fun s hs => hanti hs (mem_Iic.2 le_rfl) hs⟩)
  have hWT0 : W T = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1
    (le_antisymm hWT (sq_nonneg _))
  have := eq_zero_of_linear_all (T := W) (k := fun s => -κ s) hW hκc.neg hWT0 t
  simp only [hWdef] at this
  linarith

/-- A curve with distinct limits `a` at `-∞` and `b` at `+∞`, which is constant once it takes the
value `a` or `b`, stays above `min a b`. -/
theorem min_le_of_tendsto {c : ℝ → ℝ} (hc : Continuous c) {a b : ℝ} (hab : a ≠ b)
    (ha : Tendsto c atBot (𝓝 a)) (hb : Tendsto c atTop (𝓝 b))
    (hfix : ∀ t, (c t = a ∨ c t = b) → ∀ s, c s = c t) (t : ℝ) : min a b ≤ c t := by
  by_contra hlt
  push Not at hlt
  rcases le_or_gt a b with hle | hlt'
  · have hab' : a < b := lt_of_le_of_ne hle hab
    rw [min_eq_left hle] at hlt
    obtain ⟨T, hT⟩ := ((hb.eventually (Ioi_mem_nhds hab')).and (eventually_ge_atTop t)).exists
    obtain ⟨t₁, -, ht₁⟩ := intermediate_value_Icc hT.2 hc.continuousOn
      (⟨hlt.le, (hT.1 : a < c T).le⟩ : a ∈ Icc (c t) (c T))
    have := hfix t₁ (Or.inl ht₁) t
    linarith
  · rw [min_eq_right hlt'.le] at hlt
    obtain ⟨T, hT⟩ := ((ha.eventually (Ioi_mem_nhds hlt')).and (eventually_le_atBot t)).exists
    obtain ⟨t₁, -, ht₁⟩ := intermediate_value_Icc' hT.2 hc.continuousOn
      (⟨hlt.le, (hT.1 : b < c T).le⟩ : b ∈ Icc (c t) (c T))
    have := hfix t₁ (Or.inr ht₁) t
    linarith

/-- A curve with distinct limits `a` at `-∞` and `b` at `+∞`, which is constant once it takes the
value `a` or `b`, stays between `a` and `b`. -/
theorem mem_Icc_of_tendsto {c : ℝ → ℝ} (hc : Continuous c) {a b : ℝ} (hab : a ≠ b)
    (ha : Tendsto c atBot (𝓝 a)) (hb : Tendsto c atTop (𝓝 b))
    (hfix : ∀ t, (c t = a ∨ c t = b) → ∀ s, c s = c t) (t : ℝ) :
    min a b ≤ c t ∧ c t ≤ max a b := by
  refine ⟨min_le_of_tendsto hc hab ha hb hfix t, ?_⟩
  have := min_le_of_tendsto (c := fun s => -c s) hc.neg (a := -a) (b := -b) (by simpa using hab)
    ha.neg hb.neg (fun t ht s => by
      have := hfix t (by rcases ht with h | h <;> [left; right] <;> linarith) s
      simp only [this]) t
  rw [min_neg_neg] at this
  linarith

end ConleyCheck.ON
