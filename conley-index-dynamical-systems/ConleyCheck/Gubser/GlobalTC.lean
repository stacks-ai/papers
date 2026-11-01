import ConleyCheck.Gubser.Global
import ConleyCheck.Gubser.TCBlock

/-!
# The block `N^+` of `lem:TC` for the doubled compactified flow

Near `TC^+ = {y = (1, 0, 0)}` the chart `eq:chartTp` is `u = y₂/y₁`, `v = y₃/y₁`, and along orbits of
`ϕG` the coordinates `(u, v, τ)` solve `y₁ · eq:flowTp`, `dτ/dt = y₁ v (1 - τ²)`. To obtain coordinates
on all of `Ω` we divide by `max(y₁, κ)` and add to `v` a term that vanishes for `y₁ ≥ κ` and is
`≥ 1/c` for `y₁ ≤ κ/2`, so that `{|u|, v < 1/c}` lies in `{y₁ > κ}`, where the chart is exact.

* `modelG`: `ϕG` near `TC^+` as a `TCModel`.
* `isBlock_NG`, `Inv_NG`: `N^+ = {|u| ≤ δ, v ≤ δ'}` is an isolating block for `ϕG` with exit set
  `L^+ = {v = δ', τ ≥ 0}`, and `Inv(N^+) = TC^+`.
-/

open Set Filter Topology
open ConleyCheck.Conley ConleyCheck.ODE

namespace ConleyCheck.Gubser

variable {c : ℝ}

/-- The cut-off level `κ = min(1/2, c/2)` of the denominator. -/
noncomputable def kapG (c : ℝ) : ℝ := min (1 / 2) (c / 2)

theorem kapG_pos (hc : 0 < c) : 0 < kapG c := lt_min (by norm_num) (by linarith)

theorem kapG_le_half (c : ℝ) : kapG c ≤ 1 / 2 := min_le_left _ _

theorem kapG_le_c (c : ℝ) : kapG c ≤ c / 2 := min_le_right _ _

/-- The denominator `max(y₁, κ)`. -/
noncomputable def gd (c : ℝ) (q : OmG) : ℝ := max (gy1 q) (kapG c)

/-- `u = y₂ / max(y₁, κ)`. -/
noncomputable def gu (c : ℝ) (q : OmG) : ℝ := gy2 q / gd c q

/-- `v = y₃ / max(y₁, κ) + K (max(y₁, κ) - y₁)` with `K = 2/(cκ)`. -/
noncomputable def gv (c : ℝ) (q : OmG) : ℝ :=
  gy3 q / gd c q + 2 / (c * kapG c) * (gd c q - gy1 q)

theorem gd_pos (hc : 0 < c) (q : OmG) : 0 < gd c q := (kapG_pos hc).trans_le (le_max_right _ _)

theorem continuous_gd (c : ℝ) : Continuous (gd c) := continuous_gy1.max continuous_const

theorem continuous_gu (hc : 0 < c) : Continuous (gu c) :=
  continuous_gy2.div (continuous_gd c) fun q => (gd_pos hc q).ne'

theorem continuous_gv (hc : 0 < c) : Continuous (gv c) :=
  (continuous_gy3.div (continuous_gd c) fun q => (gd_pos hc q).ne').add
    (continuous_const.mul ((continuous_gd c).sub continuous_gy1))

theorem gd_eq (q : OmG) (h : kapG c ≤ gy1 q) : gd c q = gy1 q := max_eq_left h

theorem gu_eq (q : OmG) (h : kapG c ≤ gy1 q) : gu c q = gy2 q / gy1 q := by
  rw [gu, gd_eq q h]

theorem gv_eq (q : OmG) (h : kapG c ≤ gy1 q) : gv c q = gy3 q / gy1 q := by
  rw [gv, gd_eq q h, sub_self, mul_zero, add_zero]

theorem gv_nonneg (hc : 0 < c) (q : OmG) : 0 ≤ gv c q := by
  have h1 : 0 ≤ gy3 q / gd c q := div_nonneg (gy3_nonneg q) (gd_pos hc q).le
  have h2 : 0 ≤ 2 / (c * kapG c) * (gd c q - gy1 q) :=
    mul_nonneg (by have := kapG_pos hc; positivity) (sub_nonneg.2 (le_max_left _ _))
  exact add_nonneg h1 h2

/-- `{|u|, v < 1/c}` lies in the region `y₁ > κ` where the chart is exact. -/
theorem kapG_lt_of_W (hc : 0 < c) (q : OmG) (hu : |gu c q| < 1 / c) (hv : gv c q < 1 / c) :
    kapG c < gy1 q := by
  by_contra h
  push Not at h
  have hκ := kapG_pos hc
  have hd : gd c q = kapG c := max_eq_right h
  have h3 := gy3_nonneg q
  have hv' : gy3 q / kapG c + 2 / (c * kapG c) * (kapG c - gy1 q) < 1 / c := by
    rw [gv, hd] at hv; exact hv
  have hA : 0 ≤ gy3 q / kapG c := div_nonneg h3 hκ.le
  have hB : 0 ≤ 2 / (c * kapG c) * (kapG c - gy1 q) :=
    mul_nonneg (by positivity) (sub_nonneg.2 h)
  rcases le_or_gt (gy1 q) (kapG c / 2) with h1 | h1
  · have : 1 / c ≤ 2 / (c * kapG c) * (kapG c - gy1 q) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      rw [div_mul_eq_mul_div, div_le_iff₀ hc]
      nlinarith
    linarith
  · have hκc : kapG c / c ≤ 1 / 2 := by
      rw [div_le_iff₀ hc]; linarith [kapG_le_c c]
    have hu' : |gy2 q| < kapG c / c := by
      rw [gu, hd, abs_div, abs_of_pos hκ, div_lt_div_iff₀ hκ hc] at hu
      rw [lt_div_iff₀ hc]; linarith
    have hv'' : gy3 q < kapG c / c := by
      have : gy3 q / kapG c < 1 / c := by linarith
      rw [div_lt_div_iff₀ hκ hc] at this
      rw [lt_div_iff₀ hc]; linarith
    have hs := sphere_G q
    have h2sq : gy2 q ^ 2 < 1 / 4 := by
      have := abs_lt.1 (hu'.trans_le hκc); nlinarith
    have h3sq : gy3 q ^ 2 < 1 / 4 := by nlinarith
    have h1sq : gy1 q ^ 2 ≤ 1 / 4 := by nlinarith [kapG_le_half c]
    linarith

section Orbit

variable (c) (p : OmG)

theorem eventually_kapG_lt {t : ℝ} (h : kapG c < gy1 (ϕG c t p)) :
    ∀ᶠ s in 𝓝 t, kapG c < gy1 (ϕG c s p) :=
  (continuous_k c p _ continuous_gy1).continuousAt.eventually (lt_mem_nhds h)

variable {c} in
theorem hasDerivAt_gu (hc : 0 < c) {t : ℝ} (h : kapG c < gy1 (ϕG c t p)) :
    HasDerivAt (fun s => gu c (ϕG c s p))
      (gy1 (ϕG c t p) * Fu c (gu c (ϕG c t p)) (gv c (ϕG c t p)) (gw1 (ϕG c t p))) t := by
  have hy1 : gy1 (ϕG c t p) ≠ 0 := ((kapG_pos hc).trans h).ne'
  have hd := (hasDerivAt_gy2 c p t).div (hasDerivAt_gy1 c p t) hy1
  refine (hd.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [eventually_kapG_lt c p h] with s hs
    exact gu_eq _ hs.le
  · rw [gu_eq _ h.le, gv_eq _ h.le]
    simp only [gP1, gP2, gS, fS, fP1, fP2, Fu, gy1, gy2, gy3, gw1] at hy1 ⊢
    field_simp
    ring

variable {c} in
theorem hasDerivAt_gv (hc : 0 < c) {t : ℝ} (h : kapG c < gy1 (ϕG c t p)) :
    HasDerivAt (fun s => gv c (ϕG c s p))
      (gy1 (ϕG c t p) * Fv (gu c (ϕG c t p)) (gv c (ϕG c t p)) (gw1 (ϕG c t p))) t := by
  have hy1 : gy1 (ϕG c t p) ≠ 0 := ((kapG_pos hc).trans h).ne'
  have hd := (hasDerivAt_gy3 c p t).div (hasDerivAt_gy1 c p t) hy1
  refine (hd.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [eventually_kapG_lt c p h] with s hs
    exact gv_eq _ hs.le
  · rw [gu_eq _ h.le, gv_eq _ h.le]
    simp only [gP1, gS, fS, fP1, fP2, Fv, gy1, gy2, gy3, gw1] at hy1 ⊢
    field_simp
    ring

variable {c} in
theorem hasDerivAt_gτ (hc : 0 < c) {t : ℝ} (h : kapG c < gy1 (ϕG c t p)) :
    HasDerivAt (fun s => gw1 (ϕG c s p))
      (gy1 (ϕG c t p) * (gv c (ϕG c t p) * (1 - gw1 (ϕG c t p) ^ 2))) t := by
  have hy1 : gy1 (ϕG c t p) ≠ 0 := ((kapG_pos hc).trans h).ne'
  refine (hasDerivAt_gw1 c p t).congr_deriv ?_
  rw [gv_eq _ h.le]
  field_simp

/-- `TC^+` consists of fixed points, in the sense that `y₂ = y₃ = 0` and `y₁ > 0` are invariant. -/
theorem tc_inv_G (h1 : 0 < gy1 p) (h2 : gy2 p = 0) (h3 : gy3 p = 0) (t : ℝ) :
    gy1 (ϕG c t p) = 1 ∧ gy2 (ϕG c t p) = 0 ∧ gy3 (ϕG c t p) = 0 := by
  have h3' : ∀ s, gy3 (ϕG c s p) = 0 := gy3_zero c p h3
  have h2' : ∀ s, gy2 (ϕG c s p) = 0 := fun s =>
    eq_zero_of_linear_all (T := fun s => gy2 (ϕG c s p))
      (k := fun s => -(4 / 3) * gw1 (ϕG c s p) * gy2 (ϕG c s p) - gy1 (ϕG c s p) / c -
        gS c (ϕG c s p))
      (fun s => (hasDerivAt_gy2 c p s).congr_deriv (by
        have := h3' s
        simp only [gP2, fP2, gy1, gy2, gy3, gw1] at this ⊢
        rw [this]; ring))
      (((continuous_const.mul (continuous_k c p _ continuous_gw1)).mul
        (continuous_k c p _ continuous_gy2)).sub ((continuous_k c p _ continuous_gy1).div_const c)
        |>.sub (continuous_k c p _ (continuous_gS c)))
      (s₀ := 0) (by simpa [Flow.map_zero_apply] using h2) s
  have hp := gy1_pos c p h1 t
  have hs := sphere_G (ϕG c t p)
  rw [h2' t, h3' t] at hs
  refine ⟨?_, h2' t, h3' t⟩
  nlinarith

end Orbit

/-- `TC^+ = {y = (1, 0, 0)}`. -/
def TCp : Set OmG := {q | gy1 q = 1}

theorem TC_iff (hc : 0 < c) (q : OmG) : (gu c q = 0 ∧ gv c q = 0) ↔ gy1 q = 1 := by
  have hκ := kapG_pos hc
  have hs := sphere_G q
  constructor
  · rintro ⟨hu, hv⟩
    have hA : 0 ≤ gy3 q / gd c q := div_nonneg (gy3_nonneg q) (gd_pos hc q).le
    have hB : 0 ≤ 2 / (c * kapG c) * (gd c q - gy1 q) :=
      mul_nonneg (by positivity) (sub_nonneg.2 (le_max_left _ _))
    have hv' : gy3 q / gd c q + 2 / (c * kapG c) * (gd c q - gy1 q) = 0 := hv
    have hB0 : gd c q - gy1 q = 0 := by
      have : 2 / (c * kapG c) * (gd c q - gy1 q) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (by positivity)
      · exact h
    have hy1 : kapG c ≤ gy1 q := by
      have := le_max_right (gy1 q) (kapG c); rw [gd] at hB0; linarith
    have h3 : gy3 q = 0 := by
      have : gy3 q / gd c q = 0 := by linarith
      rcases div_eq_zero_iff.1 this with h | h
      · exact h
      · exact absurd h (gd_pos hc q).ne'
    have h2 : gy2 q = 0 := by
      rw [gu_eq q hy1] at hu
      rcases div_eq_zero_iff.1 hu with h | h
      · exact h
      · exact absurd h (hκ.trans_le hy1).ne'
    rw [h2, h3] at hs
    nlinarith
  · intro h1
    have h23 : gy2 q ^ 2 + gy3 q ^ 2 = 0 := by rw [h1] at hs; linarith
    have h2 : gy2 q = 0 := by nlinarith
    have h3 : gy3 q = 0 := by nlinarith
    have hle : kapG c ≤ gy1 q := by rw [h1]; linarith [kapG_le_half c]
    exact ⟨by rw [gu_eq q hle, h2, zero_div], by rw [gv_eq q hle, h3, zero_div]⟩

theorem TCp_iff (q : OmG) : q ∈ TCp ↔ gy1 q = 1 := Iff.rfl

theorem TCp_coords {q : OmG} (h : gy1 q = 1) : gy2 q = 0 ∧ gy3 q = 0 := by
  have hs := sphere_G q
  rw [h] at hs
  constructor <;> nlinarith

/-- `ϕG` near `TC^+` as a `TCModel`. -/
noncomputable def modelG (hc : 0 < c) : TCModel c OmG where
  ϕ := ϕG c
  u := gu c
  v := gv c
  τ := gw1
  b := gy1
  cu := continuous_gu hc
  cv := continuous_gv hc
  cτ := continuous_gw1
  cb := continuous_gy1
  v_nonneg := gv_nonneg hc
  τ_ge q := (gw1_mem q).1
  τ_le q := (gw1_mem q).2
  b_pos q hu hv := (kapG_pos hc).trans (kapG_lt_of_W hc q hu hv)
  du p t hu hv := hasDerivAt_gu p hc (kapG_lt_of_W hc _ hu hv)
  dv p t hu hv := hasDerivAt_gv p hc (kapG_lt_of_W hc _ hu hv)
  dτ p t hu hv := hasDerivAt_gτ p hc (kapG_lt_of_W hc _ hu hv)
  tc_inv p hu hv t := by
    have h1 := (TC_iff hc p).1 ⟨hu, hv⟩
    obtain ⟨h2, h3⟩ := TCp_coords h1
    exact (TC_iff hc _).2 (tc_inv_G c p (by rw [h1]; exact one_pos) h2 h3 t).1
  compact a a' :=
    ((isClosed_le (continuous_abs.comp (continuous_gu hc)) continuous_const).inter
      (isClosed_le (continuous_gv hc) continuous_const)).isCompact

theorem TCp_eq (hc : 0 < c) : (modelG hc).TC = TCp := by
  ext q
  exact TC_iff hc q

variable {δ δ' : ℝ}

/-- The block `N^+` in `Ω`. -/
def NG (c δ δ' : ℝ) : Set OmG := {q | |gu c q| ≤ δ ∧ gv c q ≤ δ'}

/-- Its exit set `L^+`. -/
def LG (c δ δ' : ℝ) : Set OmG := {q | |gu c q| ≤ δ ∧ gv c q = δ' ∧ 0 ≤ gw1 q}

/-- `lem:TC`(i) for `ϕG`: `N^+` is an isolating block with exit set `L^+`. -/
theorem isBlock_NG (H : TCHyp c δ δ') : IsBlock (ϕG c) (NG c δ δ') (LG c δ δ') :=
  (modelG H.hc).isBlock_N H

/-- `Inv(N^+) = TC^+`. -/
theorem Inv_NG (H : TCHyp c δ δ') : Inv (ϕG c) (NG c δ δ') = TCp := by
  rw [← TCp_eq H.hc]
  exact (modelG H.hc).Inv_N H

/-- On `N^+` the chart is exact. -/
theorem kapG_lt_of_NG (H : TCHyp c δ δ') {q : OmG} (hq : q ∈ NG c δ δ') : kapG c < gy1 q :=
  kapG_lt_of_W H.hc q ((modelG H.hc).mem_W H hq).1 ((modelG H.hc).mem_W H hq).2

end ConleyCheck.Gubser
