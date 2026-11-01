import ConleyCheck.Gubser.ANbhd
import ConleyCheck.Gubser.GlobalTC

/-!
# The repeller `TC⁺` inside `{y₁ > 0}`

When `δ < a δ'`, the block `N = {|u| ≤ δ, v ≤ δ'}` of `TC⁺` is a convex neighborhood. An orbit
that leaves `N` through its exit set satisfies, for all later times, `y₁ > 0`, `y₃ > 0`, `τ > 0`,
`B₂ ≥ 0` and `y₃ > δ' y₁` (`after_exit`), and `H_σ > 0` for every `σ > 0` with `δ < σ δ'`
and `k_σ ≥ 0` (`after_exit_gH`).
-/

open Set Filter Topology
open ConleyCheck.Conley ConleyCheck.ODE

namespace ConleyCheck.Gubser

variable {c a δ δ' : ℝ}

theorem gw1_ge (c : ℝ) (p : OmG) {t : ℝ} (ht : 0 ≤ t) : gw1 p ≤ gw1 (ϕG c t p) := by
  have := monotone_gw1 c p ht
  simpa only [Flow.map_zero_apply] using this

/-- `τ` increases strictly where `y₃ > 0` and `|τ| < 1`. -/
theorem gw1_lt (c : ℝ) {p : OmG} (h3 : 0 < gy3 p) (hw : |gw1 p| < 1) {t : ℝ} (ht : 0 < t) :
    gw1 p < gw1 (ϕG c t p) := by
  by_contra h
  push Not at h
  have hm := monotone_gw1 c p
  have h0 : gw1 (ϕG c 0 p) = gw1 p := by rw [Flow.map_zero_apply]
  have hcst : ∀ s ∈ Icc (0 : ℝ) t, gw1 (ϕG c s p) = gw1 (ϕG c 0 p) := fun s hs => by
    have h1 : gw1 (ϕG c 0 p) ≤ gw1 (ϕG c s p) := hm hs.1
    have h2 : gw1 (ϕG c s p) ≤ gw1 (ϕG c t p) := hm hs.2
    rw [h0] at h1 ⊢
    exact le_antisymm (h2.trans h) h1
  have hD := (hasDerivAt_gw1 c p 0).hasDerivWithinAt (s := Icc 0 t)
  have hC : HasDerivWithinAt (fun s => gw1 (ϕG c s p)) 0 (Icc 0 t) 0 :=
    (hasDerivWithinAt_const 0 (Icc 0 t) (gw1 (ϕG c 0 p))).congr (fun s hs => hcst s hs) rfl
  have := (uniqueDiffOn_Icc ht 0 ⟨le_rfl, ht.le⟩).eq_deriv _ hD hC
  rw [Flow.map_zero_apply] at this
  have : 0 < 1 - gw1 p ^ 2 := by
    have := abs_lt.1 hw
    nlinarith
  nlinarith [mul_pos h3 this]

theorem gw1_pos_after (c : ℝ) {p : OmG} (h3 : 0 < gy3 p) (hw : 0 ≤ gw1 p) {t : ℝ} (ht : 0 < t) :
    0 < gw1 (ϕG c t p) := by
  rcases hw.lt_or_eq with hw | hw
  · exact hw.trans_le (gw1_ge c p ht.le)
  · exact lt_of_eq_of_lt hw (gw1_lt c h3 (by rw [← hw]; norm_num) ht)

theorem LG_coords (H : TCHyp c δ δ') {q : OmG} (hq : q ∈ LG c δ δ') :
    kapG c < gy1 q ∧ gy3 q = δ' * gy1 q ∧ |gy2 q| ≤ δ * gy1 q ∧ 0 ≤ gw1 q := by
  have hk := kapG_lt_of_NG H ⟨hq.1, hq.2.1.le⟩
  have h1 : 0 < gy1 q := (kapG_pos H.hc).trans hk
  have hv := hq.2.1
  have hu := hq.1
  rw [gv_eq q hk.le, div_eq_iff h1.ne'] at hv
  rw [gu_eq q hk.le, abs_div, abs_of_pos h1, div_le_iff₀ h1] at hu
  exact ⟨hk, hv, hu, hq.2.2⟩

theorem NG_psi (H : TCHyp c δ δ') {q : OmG} (hq : q ∈ NG c δ δ') : gy3 q - δ' * gy1 q ≤ 0 := by
  have hk := kapG_lt_of_NG H hq
  have h1 : 0 < gy1 q := (kapG_pos H.hc).trans hk
  have hv := hq.2
  rw [gv_eq q hk.le, div_le_iff₀ h1] at hv
  linarith

section After

variable (H : TCHyp c δ δ') (ha : a ^ 2 = 1 / 5) (ha0 : 0 < a)
include H

theorem after_exit_basic {p : OmG} (hp : p ∈ LG c δ δ') (t : ℝ) :
    0 < gy1 (ϕG c t p) ∧ 0 < gy3 (ϕG c t p) := by
  obtain ⟨hk, h3, -, -⟩ := LG_coords H hp
  have h1 : 0 < gy1 p := (kapG_pos H.hc).trans hk
  exact ⟨gy1_pos c p h1 t, gy3_pos c p (by rw [h3]; exact mul_pos H.hδ' h1) t⟩

include ha ha0

theorem after_exit (hδa : δ < a * δ') {p : OmG} (hp : p ∈ LG c δ δ') {t : ℝ} (ht : 0 < t) :
    0 < gy1 (ϕG c t p) ∧ 0 < gy3 (ϕG c t p) ∧ 0 < gw1 (ϕG c t p) ∧ 0 ≤ gB2 a (ϕG c t p) ∧
      0 < gy3 (ϕG c t p) - δ' * gy1 (ϕG c t p) := by
  obtain ⟨hk, h3, h2, hw⟩ := LG_coords H hp
  have h1 : 0 < gy1 p := (kapG_pos H.hc).trans hk
  have hy3 : 0 < gy3 p := by rw [h3]; exact mul_pos H.hδ' h1
  have hB0 : 0 ≤ gB2 a (ϕG c 0 p) := by
    rw [Flow.map_zero_apply, gB2, h3]
    nlinarith [le_abs_self (gy2 p), mul_lt_mul_of_pos_right hδa h1]
  have hB : ∀ s, 0 ≤ s → 0 ≤ gB2 a (ϕG c s p) := fun s hs =>
    gB2_nonneg (c := c) (p := p) ha ha0 H.hc h1.le hs hB0
  have hτ : ∀ s, 0 ≤ s → 0 ≤ gw1 (ϕG c s p) := fun s hs =>
    hw.trans (gw1_ge c p hs)
  have hb := after_exit_basic H hp
  refine ⟨(hb t).1, (hb t).2, gw1_pos_after c hy3 hw ht, hB t ht.le, ?_⟩
  have hg : ∀ s, HasDerivAt (fun s => -δ' * gy1 (ϕG c s p) + 0 * gy2 (ϕG c s p) +
      1 * gy3 (ϕG c s p)) ((fun s => -gS c (ϕG c s p)) s * (-δ' * gy1 (ϕG c s p) +
        0 * gy2 (ϕG c s p) + 1 * gy3 (ϕG c s p)) + (fun s => -δ' * gP1 (ϕG c s p)) s) s :=
    fun s => (hasDerivAt_lin c p (-δ') 0 1 s).congr_deriv (by ring)
  have hm : ∀ s, 0 ≤ s → 0 ≤ s → 0 ≤ -δ' * gP1 (ϕG c s p) ∧
      (0 < s → 0 < -δ' * gP1 (ϕG c s p)) := fun s hs _ => by
    have hBs := hB s hs
    have hy1 := (hb s).1
    have hy3s := (hb s).2
    rw [gB2] at hBs
    have hlt : 0 < 2 * gy3 (ϕG c s p) - gy2 (ϕG c s p) := by nlinarith [a_lt_one ha ha0]
    have e : -δ' * gP1 (ϕG c s p) = δ' * (gw1 (ϕG c s p) * gy1 (ϕG c s p) *
        (2 * gy3 (ϕG c s p) - gy2 (ϕG c s p))) / 3 := by rw [gP1_eq]; ring
    rw [e]
    exact ⟨div_nonneg (mul_nonneg H.hδ'.le (mul_nonneg (mul_nonneg (hτ s hs) hy1.le) hlt.le))
      (by norm_num), fun hs0 => div_pos (mul_pos H.hδ' (mul_pos (mul_pos
        (gw1_pos_after c hy3 hw hs0) hy1) hlt)) (by norm_num)⟩
  have := affine_pos_of_end hg (continuous_k c p _ (continuous_gS c).neg) ht
    (fun s hs => (hm s hs.1 hs.1).1) ((hm t ht.le ht.le).2 ht)
    (by simp only [Flow.map_zero_apply, h3]; linarith)
  linarith

omit ha0 in
theorem after_exit_gH (hc : 0 < c) {σ : ℝ} (hσ : 0 < σ) (hk : 0 ≤ kS c a σ) (hδσ : δ < σ * δ')
    {p : OmG} (hp : p ∈ LG c δ δ') {t : ℝ} (ht : 0 ≤ t) : 0 < gH σ (ϕG c t p) := by
  obtain ⟨hkp, h3, h2, hw⟩ := LG_coords H hp
  have h1 : 0 < gy1 p := (kapG_pos H.hc).trans hkp
  have hb := after_exit_basic H hp
  have hτ : ∀ s, 0 ≤ s → 0 ≤ gw1 (ϕG c s p) := fun s hs =>
    hw.trans (gw1_ge c p hs)
  refine affine_pos (g := fun s => gH σ (ϕG c s p)) (hasDerivAt_gH c p ha hc.ne' hσ.ne')
    (continuous_k c p _ (continuous_kH c σ)) ht (fun s hs => ?_) ?_
  · have hQ : 0 ≤ gQ c a σ (ϕG c s p) := by
      unfold gQ
      have := hτ s hs.1
      have := (hb s).1
      have := (hb s).2
      positivity
    have := (hb s).2
    positivity
  · simp only [Flow.map_zero_apply, gH, h3]
    nlinarith [neg_abs_le (gy2 p)]

end After

section Convex

variable (H : TCHyp c δ δ')
include H

theorem TCp_subset_interior : TCp ⊆ interior (NG c δ δ') := fun q hq => by
  obtain ⟨hu, hv⟩ := (TC_iff H.hc q).2 hq
  refine interior_maximal (t := {q | |gu c q| < δ ∧ gv c q < δ'})
    (fun q (hq : |gu c q| < δ ∧ gv c q < δ') => (⟨hq.1.le, hq.2.le⟩ : q ∈ NG c δ δ'))
    ((isOpen_lt (continuous_gu H.hc).abs continuous_const).inter
      (isOpen_lt (continuous_gv H.hc) continuous_const)) ?_
  exact ⟨by rw [hu, abs_zero]; exact H.hδ, by rw [hv]; exact H.hδ'⟩

theorem isConvexNbhd_NG (ha : a ^ 2 = 1 / 5) (ha0 : 0 < a) (hδa : δ < a * δ') :
    IsConvexNbhd (ϕG c) TCp (NG c δ δ') where
  isClosed := (isBlock_NG H).isCompact.isClosed
  inv := Inv_NG H
  subset_interior := TCp_subset_interior H
  convex x t₁ t₂ t₃ h12 h23 h1 h3 := by
    by_contra h2
    obtain ⟨s, hs, hL⟩ := IsBlock.exists_exit (ϕG c) (isBlock_NG H) h12 h1 h2
    have := (after_exit H ha ha0 hδa hL (t := t₃ - s) (by linarith [hs.2])).2.2.2.2
    rw [← Flow.map_add, sub_add_cancel] at this
    linarith [NG_psi H h3]

/-- An orbit outside `TC⁺` whose `α`-limit set meets `TC⁺` crosses the exit set of `N`. -/
theorem exists_exit_of_alphaLim (ha : a ^ 2 = 1 / 5) (ha0 : 0 < a) (hδa : δ < a * δ') {x : OmG}
    (hx : (alphaLim (ϕG c) x ∩ TCp).Nonempty) (hxT : x ∉ TCp) :
    ∃ s, ϕG c s x ∈ LG c δ δ' := by
  obtain ⟨T, hT⟩ := eventually_atBot.1
    ((isConvexNbhd_NG H ha ha0 hδa).eventually_of_meets_alpha hx)
  rw [← Inv_NG H] at hxT
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, ϕG c t₀ x ∉ NG c δ δ' := by
    by_contra h
    push Not at h
    exact hxT h
  have hTt : T ≤ t₀ := le_of_not_ge fun h => ht₀ (hT t₀ h)
  obtain ⟨s, -, hs⟩ := IsBlock.exists_exit (ϕG c) (isBlock_NG H) hTt (hT T le_rfl) ht₀
  exact ⟨s, hs⟩

end Convex

end ConleyCheck.Gubser
