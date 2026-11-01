import ConleyCheck.Gubser.GlobalBarrier
import ConleyCheck.Gubser.TCBlock

/-!
# The blocks `K^±` of `thm:M`

In homogeneous coordinates on `Ω`,
    `K^- = {π̄ ≤ -(a - η), π̄ ≤ -δ|T|} = {y₂ + (a - η) y₃ ≤ 0, y₂ ± δ y₁ ≤ 0}`,
    `K^+ = {π̄ ≥ a + η, π̄ ≥ δ|T|} = {(a + η) y₃ - y₂ ≤ 0, ±δ y₁ - y₂ ≤ 0}`.
The faces `u = ∓δ` of `K^∓` near `TC^+` are strict exit faces and those near `TC^-` strict entrance
faces, under the condition (k1) on `δ` (`KHyp`).

* `plane_convex`: an orbit that leaves the half-space `{π̄ ≤ -(a - η)}` never returns to it
  (`convex_Hm`), and the same holds for `{π̄ ≥ a + η}` (`convex_Gp`). Along an excursion out of the
  half-space, `F = T + k τ` is monotone, which is incompatible with the exit and entrance conditions
  `F ≥ 0` and `F ≤ 0`.
* `convex_Km`, `convex_Kp`: hence every orbit meets `K^±` in an interval of times.
-/

open Set Filter Topology
open ConleyCheck.Conley ConleyCheck.ODE

namespace ConleyCheck.Gubser

variable {c a η δ : ℝ}

/-- The conditions on `η` and `δ` in `thm:M`. -/
structure KHyp (c a η δ : ℝ) : Prop where
  hc : 0 < c
  ha : a ^ 2 = 1 / 5
  ha0 : 0 < a
  hη : 0 < η
  hηa : η < a
  hδ : 0 < δ
  k1 : δ * (5 / 3 + 4 / (15 * (a - η) ^ 2) + 2 / (3 * (a - η))) < 1 / c
  k2m : δ * kminus a c η < a - η
  k2p : δ * kplus a c η < a + η
  k3 : 5 * c * δ ≤ 3

namespace KHyp

variable (H : KHyp c a η δ)
include H

theorem a_lt_half : a < 1 / 2 := by nlinarith [H.ha, H.ha0]

theorem haη : 0 < a - η := by linarith [H.hηa]

theorem haη' : 0 < a + η := by linarith [H.hη, H.ha0]

theorem two : a + η < 2 := by linarith [H.a_lt_half, H.hηa]

theorem k1p : δ * (5 / 3 + 4 / (15 * (a + η) ^ 2) + 2 / (3 * (a + η))) < 1 / c := by
  have h1 := H.haη
  have h2 := H.haη'
  have hle : a - η ≤ a + η := by linarith [H.hη]
  have e1 : 4 / (15 * (a + η) ^ 2) ≤ 4 / (15 * (a - η) ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1.le hle 2) (by norm_num))
  have e2 : 2 / (3 * (a + η)) ≤ 2 / (3 * (a - η)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have := H.k1
  have := H.hδ
  nlinarith

theorem kminus_pos : 0 < kS c a (a - η) := by
  rw [kS_minus]
  unfold kminus
  have := H.hc; have := H.hη; have := H.haη
  have : 0 < 2 * a - η := by linarith [H.hηa, H.ha0]
  positivity

theorem kplus_pos : 0 < kS c a (-(a + η)) := by
  rw [kS_plus]
  unfold kplus
  have := H.hc; have := H.hη; have := H.haη'
  have : 0 < 2 * a + η := by linarith [H.hη, H.ha0]
  positivity

end KHyp

/-! ## The sets -/

/-- `ℓ = l₁ y₁ + l₂ y₂`. -/
def gL (l₁ l₂ : ℝ) (q : OmG) : ℝ := l₁ * gy1 q + l₂ * gy2 q

/-- `G_σ = σ y₃ - y₂`, so that `{G_σ ≤ 0} = {π̄ ≥ σ}`. -/
def gG (σ : ℝ) (q : OmG) : ℝ := σ * gy3 q - gy2 q

theorem continuous_gL (l₁ l₂ : ℝ) : Continuous (gL l₁ l₂) :=
  (continuous_const.mul continuous_gy1).add (continuous_const.mul continuous_gy2)

theorem continuous_gG (σ : ℝ) : Continuous (gG σ) :=
  (continuous_const.mul continuous_gy3).sub continuous_gy2

/-- `K^- = {π̄ ≤ -(a - η), π̄ ≤ -δ|T|}`. -/
def Km (a η δ : ℝ) : Set OmG := {q | gH (a - η) q ≤ 0 ∧ gL δ 1 q ≤ 0 ∧ gL (-δ) 1 q ≤ 0}

/-- `K^+ = {π̄ ≥ a + η, π̄ ≥ δ|T|}`. -/
def Kp (a η δ : ℝ) : Set OmG := {q | gG (a + η) q ≤ 0 ∧ gL δ (-1) q ≤ 0 ∧ gL (-δ) (-1) q ≤ 0}

theorem isClosed_Km : IsClosed (Km a η δ) :=
  (isClosed_le (continuous_gH _) continuous_const).inter
    ((isClosed_le (continuous_gL _ _) continuous_const).inter
      (isClosed_le (continuous_gL _ _) continuous_const))

theorem isClosed_Kp : IsClosed (Kp a η δ) :=
  (isClosed_le (continuous_gG _) continuous_const).inter
    ((isClosed_le (continuous_gL _ _) continuous_const).inter
      (isClosed_le (continuous_gL _ _) continuous_const))

/-! ## Derivatives along orbits -/

section Orbit

variable (c) (p : OmG)

theorem hasDerivAt_gL (l₁ l₂ t : ℝ) : HasDerivAt (fun s => gL l₁ l₂ (ϕG c s p))
    (l₁ * gP1 (ϕG c t p) + l₂ * gP2 c (ϕG c t p) - gS c (ϕG c t p) * gL l₁ l₂ (ϕG c t p)) t := by
  have h := hasDerivAt_lin c p l₁ l₂ 0 t
  simp only [zero_mul, add_zero] at h
  exact h

theorem hasDerivAt_gG (ha : a ^ 2 = 1 / 5) (hc : c ≠ 0) {σ : ℝ} (hσ : σ ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => gG σ (ϕG c s p))
      (kH c (-σ) (ϕG c t p) * gG σ (ϕG c t p) +
        σ * gy3 (ϕG c t p) / c * gQ c a (-σ) (ϕG c t p)) t := by
  have h := (hasDerivAt_gH c p ha hc (neg_ne_zero.2 hσ) t).neg
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  · simp only [gG, gH]; ring
  · simp only [gG, gH, Pi.neg_apply]; ring

end Orbit

/-! ## Face signs -/

/-- On a side face, the relevant coordinate `z = ±y₁` is positive. -/
theorem pos_of_face {σ z : ℝ} {q : OmG} (hσ : 0 < σ) (hδ : 0 < δ) (hz : z ^ 2 = gy1 q ^ 2)
    (hy2 : gy2 q = -(δ * z) ∨ gy2 q = δ * z) (h : σ * gy3 q ≤ δ * z) : 0 < z := by
  by_contra h1
  push Not at h1
  have h3 := gy3_nonneg q
  have hz0 : z = 0 := by nlinarith
  have hy3 : gy3 q = 0 := by nlinarith
  have hy1 : gy1 q = 0 := by nlinarith
  have hy2' : gy2 q = 0 := by rcases hy2 with h | h <;> rw [h, hz0] <;> ring
  have := sphere_G q
  rw [hy1, hy2', hy3] at this
  norm_num at this

theorem abs_gw1_le (q : OmG) : |gw1 q| ≤ 1 := abs_le.2 (gw1_mem q)

theorem abs_neg_gw1_le (q : OmG) : |-gw1 q| ≤ 1 := by rw [abs_neg]; exact abs_gw1_le q

namespace KHyp

variable (H : KHyp c a η δ)
include H

/-- The face `u = -δ` of `K^-` is a strict exit face. -/
theorem face_m2 {q : OmG} (h1 : gH (a - η) q ≤ 0) (h2 : gL δ 1 q = 0) :
    0 < δ * gP1 q + 1 * gP2 c q := by
  have hy2 : gy2 q = -(δ * gy1 q) := by simp only [gL] at h2; linarith
  have hσ : (a - η) * gy3 q ≤ δ * gy1 q := by simp only [gH] at h1; linarith
  have hz := pos_of_face H.haη H.hδ rfl (Or.inl hy2) hσ
  have := face_core H.hc H.haη H.hδ H.k1 hz (gy3_nonneg q) hσ (abs_gw1_le q) (abs_gw1_le q)
    (abs_gw1_le q)
  have e : δ * gP1 q + 1 * gP2 c q = δ * gy1 q ^ 2 / c - 5 / 3 * δ ^ 2 * gw1 q * gy1 q ^ 2 +
      4 / 15 * gw1 q * gy3 q ^ 2 - 2 / 3 * δ * gw1 q * gy1 q * gy3 q := by
    rw [gP1_eq, gP2_eq, hy2]; ring
  rw [e]; exact this

/-- The face `u = δ` of `K^-` near `TC^-` is a strict entrance face. -/
theorem face_m3 {q : OmG} (h1 : gH (a - η) q ≤ 0) (h3 : gL (-δ) 1 q = 0) :
    -δ * gP1 q + 1 * gP2 c q < 0 := by
  have hy2 : gy2 q = -(δ * -gy1 q) := by simp only [gL] at h3; linarith
  have hσ : (a - η) * gy3 q ≤ δ * -gy1 q := by simp only [gH] at h1; linarith
  have hz := pos_of_face H.haη H.hδ (by ring) (Or.inl hy2) hσ
  have := face_core H.hc H.haη H.hδ H.k1 hz (gy3_nonneg q) hσ (abs_neg_gw1_le q)
    (abs_neg_gw1_le q) (abs_neg_gw1_le q)
  have e : -δ * gP1 q + 1 * gP2 c q = -(δ * (-gy1 q) ^ 2 / c - 5 / 3 * δ ^ 2 * -gw1 q *
      (-gy1 q) ^ 2 + 4 / 15 * -gw1 q * gy3 q ^ 2 - 2 / 3 * δ * -gw1 q * -gy1 q * gy3 q) := by
    rw [gP1_eq, gP2_eq, hy2]; ring
  rw [e]; linarith

/-- The face `u = δ` of `K^+` near `TC^+` is a strict exit face. -/
theorem face_p2 {q : OmG} (h1 : gG (a + η) q ≤ 0) (h2 : gL δ (-1) q = 0) :
    0 < δ * gP1 q + -1 * gP2 c q := by
  have hy2 : gy2 q = δ * gy1 q := by simp only [gL] at h2; linarith
  have hσ : (a + η) * gy3 q ≤ δ * gy1 q := by simp only [gG] at h1; linarith
  have hz := pos_of_face H.haη' H.hδ rfl (Or.inr hy2) hσ
  have := face_core H.hc H.haη' H.hδ H.k1p hz (gy3_nonneg q) hσ (abs_neg_gw1_le q)
    (abs_neg_gw1_le q) (abs_gw1_le q)
  have e : δ * gP1 q + -1 * gP2 c q = δ * gy1 q ^ 2 / c - 5 / 3 * δ ^ 2 * -gw1 q * gy1 q ^ 2 +
      4 / 15 * -gw1 q * gy3 q ^ 2 - 2 / 3 * δ * gw1 q * gy1 q * gy3 q := by
    rw [gP1_eq, gP2_eq, hy2]; ring
  rw [e]; exact this

/-- The face `u = -δ` of `K^+` near `TC^-` is a strict entrance face. -/
theorem face_p3 {q : OmG} (h1 : gG (a + η) q ≤ 0) (h3 : gL (-δ) (-1) q = 0) :
    -δ * gP1 q + -1 * gP2 c q < 0 := by
  have hy2 : gy2 q = δ * -gy1 q := by simp only [gL] at h3; linarith
  have hσ : (a + η) * gy3 q ≤ δ * -gy1 q := by simp only [gG] at h1; linarith
  have hz := pos_of_face H.haη' H.hδ (by ring) (Or.inr hy2) hσ
  have := face_core H.hc H.haη' H.hδ H.k1p hz (gy3_nonneg q) hσ (abs_gw1_le q)
    (abs_gw1_le q) (abs_neg_gw1_le q)
  have e : -δ * gP1 q + -1 * gP2 c q = -(δ * (-gy1 q) ^ 2 / c - 5 / 3 * δ ^ 2 * gw1 q *
      (-gy1 q) ^ 2 + 4 / 15 * gw1 q * gy3 q ^ 2 - 2 / 3 * δ * -gw1 q * -gy1 q * gy3 q) := by
    rw [gP1_eq, gP2_eq, hy2]; ring
  rw [e]; linarith

end KHyp

/-! ## No return to the half-spaces -/

section Plane

variable (c) (p : OmG)

/-- Along an excursion during which `π̄ < 2`, the function `F = T + k τ` cannot pass from `F ≥ 0`
to `F ≤ 0`. -/
theorem no_F_excursion {σ : ℝ} (hk : 0 < kS c a σ) (h3 : ∀ s, 0 < gy3 (ϕG c s p)) {s₁ s₂ : ℝ}
    (hs : s₁ < s₂) (hF1 : 0 ≤ gF c a σ (ϕG c s₁ p)) (hF2 : gF c a σ (ϕG c s₂ p) ≤ 0)
    (hπ : ∀ s ∈ Icc s₁ s₂, gπ (ϕG c s p) < 2) : False := by
  set F := fun s => gF c a σ (ϕG c s p) with hFdef
  have hF : ∀ s, HasDerivAt F (gy3 (ϕG c s p) * (βT (gT (ϕG c s p)) (gπ (ϕG c s p))
      (gw1 (ϕG c s p)) + kS c a σ * (1 - gw1 (ϕG c s p) ^ 2))) s := fun s =>
    hasDerivAt_gF c p σ (h3 s)
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun s => (hF s).continuousAt
  have hsq : ∀ s, 0 ≤ 1 - gw1 (ϕG c s p) ^ 2 := fun s => by
    have := gw1_mem (ϕG c s p); nlinarith [this.1, this.2]
  have hFe : ∀ s, F s = gT (ϕG c s p) + kS c a σ * gw1 (ϕG c s p) := fun s => rfl
  rcases le_or_gt 0 (gy1 p) with hy | hy
  · have hT : ∀ s, 0 ≤ gT (ϕG c s p) := fun s => div_nonneg (gy1_nonneg_all c hy s) (h3 s).le
    have hτ2 : gw1 (ϕG c s₂ p) ≤ 0 := by
      have := hT s₂
      simp only [gF] at hF2
      by_contra h
      push Not at h
      nlinarith
    have hτ : ∀ s, s ≤ s₂ → gw1 (ϕG c s p) ≤ 0 := fun s hs => (monotone_gw1 c p hs).trans hτ2
    have hd : ∀ s ∈ Icc s₁ s₂, 0 ≤ βT (gT (ϕG c s p)) (gπ (ϕG c s p)) (gw1 (ϕG c s p)) := by
      intro s hs
      simp only [βT]
      exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (hT s) (by norm_num)) (by linarith [hπ s hs])) (hτ s hs.2)
    have hmono : MonotoneOn F (Icc s₁ s₂) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hFc.continuousOn
        (fun s _ => (hF s).differentiableAt.differentiableWithinAt) fun s hs => ?_
      rw [interior_Icc] at hs
      rw [(hF s).deriv]
      exact mul_nonneg (h3 s).le (add_nonneg (hd s (Ioo_subset_Icc_self hs))
        (mul_nonneg hk.le (hsq s)))
    set m := (s₁ + s₂) / 2
    have hm : m ∈ Ioo s₁ s₂ := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
    have hzero : ∀ s ∈ Icc s₁ s₂, F s = 0 := fun s hs => le_antisymm
      ((hmono hs ⟨hs.1.trans hs.2, le_rfl⟩ hs.2).trans hF2)
      (hF1.trans (hmono ⟨le_rfl, hs.1.trans hs.2⟩ hs hs.1))
    have hd0 : HasDerivAt F 0 m := (hasDerivAt_const m (0 : ℝ)).congr_of_eventuallyEq
      (Filter.mem_of_superset (Ioo_mem_nhds hm.1 hm.2) fun s hs =>
        hzero s (Ioo_subset_Icc_self hs))
    have huniq := (hF m).unique hd0
    have hpos := h3 m
    have hsum : βT (gT (ϕG c m p)) (gπ (ϕG c m p)) (gw1 (ϕG c m p)) +
        kS c a σ * (1 - gw1 (ϕG c m p) ^ 2) = 0 := by
      rcases mul_eq_zero.1 huniq with h | h
      · linarith
      · exact h
    have hb := hd m (Ioo_subset_Icc_self hm)
    have hk2 := mul_nonneg hk.le (hsq m)
    have h1 : kS c a σ * (1 - gw1 (ϕG c m p) ^ 2) = 0 := by linarith
    have hτm : gw1 (ϕG c m p) = -1 := by
      rcases mul_eq_zero.1 h1 with h | h
      · linarith
      · have := hτ m hm.2.le
        nlinarith
    have hβ : βT (gT (ϕG c m p)) (gπ (ϕG c m p)) (gw1 (ϕG c m p)) = 0 := by linarith
    have hTm : gT (ϕG c m p) = 0 := by
      simp only [βT, hτm] at hβ
      have := hπ m (Ioo_subset_Icc_self hm)
      rcases mul_eq_zero.1 hβ with h | h
      · rcases mul_eq_zero.1 h with h | h
        · linarith
        · linarith
      · norm_num at h
    have := hzero m (Ioo_subset_Icc_self hm)
    rw [hFe, hTm, hτm] at this
    linarith
  · have hT : ∀ s, gT (ϕG c s p) < 0 := fun s => div_neg_of_neg_of_pos (gy1_neg c p hy s) (h3 s)
    have hτ1 : 0 < gw1 (ϕG c s₁ p) := by
      have := hT s₁
      simp only [gF] at hF1
      by_contra h
      push Not at h
      nlinarith
    have hτ : ∀ s, s₁ ≤ s → 0 < gw1 (ϕG c s p) := fun s hs =>
      hτ1.trans_le (monotone_gw1 c p hs)
    have hmono : StrictMonoOn F (Icc s₁ s₂) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc _ _) hFc.continuousOn fun s hs => ?_
      rw [interior_Icc] at hs
      rw [(hF s).deriv]
      refine mul_pos (h3 s) (add_pos_of_pos_of_nonneg ?_ (mul_nonneg hk.le (hsq s)))
      simp only [βT]
      exact mul_pos (mul_pos_of_neg_of_neg (div_neg_of_neg_of_pos (hT s) (by norm_num))
        (by linarith [hπ s (Ioo_subset_Icc_self hs)])) (hτ s hs.1.le)
    have := hmono ⟨le_rfl, hs.le⟩ ⟨hs.le, le_rfl⟩ hs
    linarith

/-- A half-space `{g ≤ 0}` with `g' = k g + ρ y₃ Q / c` is met by every orbit in an interval of
times, provided `π̄ < 2` along excursions out of it. -/
theorem plane_convex {σ ρ : ℝ} (hc : 0 < c) (hk : 0 < kS c a σ) (hρ : 0 < ρ) {g : ℝ → ℝ}
    (hg : ∀ s, HasDerivAt g (kH c σ (ϕG c s p) * g s +
      ρ * gy3 (ϕG c s p) / c * gQ c a σ (ϕG c s p)) s)
    (hπ : ∀ s₁ s₂, s₁ < s₂ → g s₁ = 0 → g s₂ = 0 → (∀ s ∈ Ioo s₁ s₂, 0 < g s) →
      (∀ s, 0 < gy3 (ϕG c s p)) → ∀ s ∈ Icc s₁ s₂, gπ (ϕG c s p) < 2)
    {t₁ t₂ t₃ : ℝ} (h12 : t₁ ≤ t₂) (h23 : t₂ ≤ t₃) (h1 : g t₁ ≤ 0) (h3 : g t₃ ≤ 0) : g t₂ ≤ 0 := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun s => (hg s).continuousAt
  refine nonpos_of_no_excursion hgc h12 h23 h1 h3 fun s₁ s₂ _ hs _ hz1 hz2 hpos => ?_
  rcases (gy3_nonneg p).eq_or_lt with h0 | h0
  · have hy3 : ∀ s, gy3 (ϕG c s p) = 0 := gy3_zero c p h0.symm
    have := eq_zero_of_linear_all (T := g) (k := fun s => kH c σ (ϕG c s p))
      (fun s => (hg s).congr_deriv (by rw [hy3 s]; ring))
      (continuous_k c p _ (continuous_kH c σ)) (s₀ := s₁) hz1 ((s₁ + s₂) / 2)
    linarith [hpos ((s₁ + s₂) / 2) ⟨by linarith, by linarith⟩]
  · have hy3 : ∀ s, 0 < gy3 (ϕG c s p) := gy3_pos c p h0
    have hA : ∀ s, 0 < ρ * gy3 (ϕG c s p) / c := fun s => div_pos (mul_pos hρ (hy3 s)) hc
    have d1 := deriv_nonneg_of_excursion (hg s₁) hz1 hs hpos
    have d2 := deriv_nonpos_of_excursion (hg s₂) hz2 hs hpos
    rw [hz1, mul_zero, zero_add] at d1
    rw [hz2, mul_zero, zero_add] at d2
    have hQ1 : 0 ≤ gQ c a σ (ϕG c s₁ p) := nonneg_of_mul_nonneg_right d1 (hA s₁)
    have hQ2 : gQ c a σ (ϕG c s₂ p) ≤ 0 := nonpos_of_mul_nonpos_right d2 (hA s₂)
    rw [gQ_eq_gF (hy3 s₁)] at hQ1
    rw [gQ_eq_gF (hy3 s₂)] at hQ2
    exact no_F_excursion c p hk hy3 hs (nonneg_of_mul_nonneg_right hQ1 (hy3 s₁))
      (nonpos_of_mul_nonpos_right hQ2 (hy3 s₂)) (hπ s₁ s₂ hs hz1 hz2 hpos hy3)

end Plane

namespace KHyp

variable (H : KHyp c a η δ)
include H

/-- Lemma M: an orbit that leaves `{π̄ ≤ -(a - η)}` does not return. -/
theorem convex_Hm (p : OmG) {t₁ t₂ t₃ : ℝ} (h12 : t₁ ≤ t₂) (h23 : t₂ ≤ t₃)
    (h1 : gH (a - η) (ϕG c t₁ p) ≤ 0) (h3 : gH (a - η) (ϕG c t₃ p) ≤ 0) :
    gH (a - η) (ϕG c t₂ p) ≤ 0 := by
  refine plane_convex c p H.hc H.kminus_pos H.haη
    (hasDerivAt_gH c p H.ha H.hc.ne' H.haη.ne') (fun s₁ s₂ hs hz1 hz2 _ hy3 s hs' => ?_)
    h12 h23 h1 h3
  have hB : ∀ r, gH (a - η) (ϕG c r p) = 0 → 0 < gB2 a (ϕG c r p) := fun r hr => by
    simp only [gH] at hr
    simp only [gB2]
    nlinarith [hy3 r, H.ha0, H.haη]
  have hle : gy2 (ϕG c s p) ≤ a * gy3 (ϕG c s p) := by
    rcases le_or_gt 0 (gy1 p) with hy | hy
    · have := gB2_nonneg p H.ha H.ha0 H.hc hy hs'.1 (hB s₁ hz1).le
      simp only [gB2] at this; linarith
    · by_contra h
      push Not at h
      have h0 : gB2 a (ϕG c s p) ≤ 0 := by simp only [gB2]; linarith
      have := gB2_nonpos p H.ha H.ha0 H.hc hy.le hs'.2 h0
      linarith [hB s₂ hz2]
  have : gπ (ϕG c s p) ≤ a := by
    simp only [gπ]; rw [div_le_iff₀ (hy3 s)]; linarith
  linarith [H.a_lt_half]

/-- Lemma P: an orbit that leaves `{π̄ ≥ a + η}` does not return. -/
theorem convex_Gp (p : OmG) {t₁ t₂ t₃ : ℝ} (h12 : t₁ ≤ t₂) (h23 : t₂ ≤ t₃)
    (h1 : gG (a + η) (ϕG c t₁ p) ≤ 0) (h3 : gG (a + η) (ϕG c t₃ p) ≤ 0) :
    gG (a + η) (ϕG c t₂ p) ≤ 0 := by
  refine plane_convex c p H.hc H.kplus_pos H.haη'
    (hasDerivAt_gG c p H.ha H.hc.ne' H.haη'.ne') (fun s₁ s₂ hs hz1 hz2 hpos hy3 s hs' => ?_)
    h12 h23 h1 h3
  have hg : 0 ≤ gG (a + η) (ϕG c s p) := by
    rcases hs'.1.eq_or_lt with h | h
    · rw [← h]; exact hz1.ge
    rcases hs'.2.eq_or_lt with h' | h'
    · rw [h']; exact hz2.ge
    exact (hpos s ⟨h, h'⟩).le
  have : gπ (ϕG c s p) ≤ a + η := by
    simp only [gπ, gG] at hg ⊢; rw [div_le_iff₀ (hy3 s)]; linarith
  linarith [H.two]

/-- Every orbit meets `K^-` in an interval of times. -/
theorem convex_Km (p : OmG) {t₁ t₂ t₃ : ℝ} (h12 : t₁ ≤ t₂) (h23 : t₂ ≤ t₃)
    (h1 : ϕG c t₁ p ∈ Km a η δ) (h3 : ϕG c t₃ p ∈ Km a η δ) : ϕG c t₂ p ∈ Km a η δ := by
  have hm1 : ∀ s ∈ Icc t₁ t₃, gH (a - η) (ϕG c s p) ≤ 0 := fun s hs =>
    H.convex_Hm p hs.1 hs.2 h1.1 h3.1
  refine ⟨hm1 t₂ ⟨h12, h23⟩, ?_, ?_⟩
  · refine nonpos_of_no_excursion (continuous_k c p _ (continuous_gL δ 1)) h12 h23 h1.2.1 h3.2.1
      fun s₁ s₂ hs1 hs hs2 hz1 hz2 hpos => ?_
    have hd := deriv_nonpos_of_excursion (hasDerivAt_gL c p δ 1 s₂) hz2 hs hpos
    have := H.face_m2 (hm1 s₂ ⟨hs1.trans hs.le, hs2⟩) hz2
    rw [hz2, mul_zero, sub_zero] at hd
    linarith
  · refine nonpos_of_no_excursion (continuous_k c p _ (continuous_gL (-δ) 1)) h12 h23 h1.2.2
      h3.2.2 fun s₁ s₂ hs1 hs hs2 hz1 hz2 hpos => ?_
    have hd := deriv_nonneg_of_excursion (hasDerivAt_gL c p (-δ) 1 s₁) hz1 hs hpos
    have := H.face_m3 (hm1 s₁ ⟨hs1, hs.le.trans hs2⟩) hz1
    rw [hz1, mul_zero, sub_zero] at hd
    linarith

/-- Every orbit meets `K^+` in an interval of times. -/
theorem convex_Kp (p : OmG) {t₁ t₂ t₃ : ℝ} (h12 : t₁ ≤ t₂) (h23 : t₂ ≤ t₃)
    (h1 : ϕG c t₁ p ∈ Kp a η δ) (h3 : ϕG c t₃ p ∈ Kp a η δ) : ϕG c t₂ p ∈ Kp a η δ := by
  have hm1 : ∀ s ∈ Icc t₁ t₃, gG (a + η) (ϕG c s p) ≤ 0 := fun s hs =>
    H.convex_Gp p hs.1 hs.2 h1.1 h3.1
  refine ⟨hm1 t₂ ⟨h12, h23⟩, ?_, ?_⟩
  · refine nonpos_of_no_excursion (continuous_k c p _ (continuous_gL δ (-1))) h12 h23 h1.2.1
      h3.2.1 fun s₁ s₂ hs1 hs hs2 hz1 hz2 hpos => ?_
    have hd := deriv_nonpos_of_excursion (hasDerivAt_gL c p δ (-1) s₂) hz2 hs hpos
    have := H.face_p2 (hm1 s₂ ⟨hs1.trans hs.le, hs2⟩) hz2
    rw [hz2, mul_zero, sub_zero] at hd
    linarith
  · refine nonpos_of_no_excursion (continuous_k c p _ (continuous_gL (-δ) (-1))) h12 h23 h1.2.2
      h3.2.2 fun s₁ s₂ hs1 hs hs2 hz1 hz2 hpos => ?_
    have hd := deriv_nonneg_of_excursion (hasDerivAt_gL c p (-δ) (-1) s₁) hz1 hs hpos
    have := H.face_p3 (hm1 s₁ ⟨hs1, hs.le.trans hs2⟩) hz1
    rw [hz1, mul_zero, sub_zero] at hd
    linarith

end KHyp

/-! ## The blocks -/

section Block

theorem ev_of_deriv_pos {g : ℝ → ℝ} {d : ℝ} (hg : HasDerivAt g d 0) (hd : 0 < d) (h0 : g 0 = 0) :
    (∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < g t) ∧ ∀ᶠ t in 𝓝[<] (0 : ℝ), g t < 0 := by
  obtain ⟨h1, h2⟩ := eventually_sign hg.neg (neg_lt_zero.2 hd)
  exact ⟨h1.mono fun t ht => by have ht' : -g t < -g 0 := ht; linarith,
    h2.mono fun t ht => by have ht' : -g 0 < -g t := ht; linarith⟩

theorem ev_of_deriv_neg {g : ℝ → ℝ} {d : ℝ} (hg : HasDerivAt g d 0) (hd : d < 0) (h0 : g 0 = 0) :
    (∀ᶠ t in 𝓝[>] (0 : ℝ), g t < 0) ∧ ∀ᶠ t in 𝓝[<] (0 : ℝ), 0 < g t := by
  obtain ⟨h1, h2⟩ := eventually_sign hg hd
  exact ⟨h1.mono fun t ht => by rwa [h0] at ht, h2.mono fun t ht => by rwa [h0] at ht⟩

variable (c)

theorem ev_lt_of_lt {f : OmG → ℝ} (hf : Continuous f) {p : OmG} (h : f p < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f (ϕG c t p) < 0 :=
  nhdsWithin_le_nhds ((continuous_k c p f hf).continuousAt.eventually
    (gt_mem_nhds (by simp only [Flow.map_zero_apply]; exact h)))

/-- A set cut out by a plane face `P ≤ 0` with `P' = k P + ρ y₃ Q / c` and two side faces, a strict
exit face `ℓ₁ = 0` and a strict entrance face `ℓ₂ = 0`, is an isolating block. Its exit set is the
part `Q ≥ 0` of the plane face together with the face `ℓ₁ = 0`. -/
theorem isBlock_K {σ ρ : ℝ} (hc : 0 < c) (hk : 0 < kS c a σ) (hσ : -2 < σ) (hρ : 0 < ρ)
    {P ℓ₁ ℓ₂ : OmG → ℝ} (cP : Continuous P) (c₁ : Continuous ℓ₁) (c₂ : Continuous ℓ₂)
    (hP : ∀ p t, HasDerivAt (fun s => P (ϕG c s p))
      (kH c σ (ϕG c t p) * P (ϕG c t p) + ρ * gy3 (ϕG c t p) / c * gQ c a σ (ϕG c t p)) t)
    (hPH : ∀ q, P q = 0 → gH σ q = 0)
    (h3 : ∀ q, P q = 0 → ℓ₁ q ≤ 0 → ℓ₂ q ≤ 0 → 0 < gy3 q)
    (hex : ∀ q, P q ≤ 0 → ℓ₁ q = 0 → ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < ℓ₁ (ϕG c t q))
    (hen : ∀ q, P q ≤ 0 → ℓ₂ q = 0 →
      (∀ᶠ t in 𝓝[<] (0 : ℝ), 0 < ℓ₂ (ϕG c t q)) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ℓ₂ (ϕG c t q) < 0) :
    IsBlock (ϕG c) {q | P q ≤ 0 ∧ ℓ₁ q ≤ 0 ∧ ℓ₂ q ≤ 0}
      {q | (P q ≤ 0 ∧ ℓ₁ q ≤ 0 ∧ ℓ₂ q ≤ 0) ∧ ((P q = 0 ∧ 0 ≤ gQ c a σ q) ∨ ℓ₁ q = 0)} := by
  set N := {q | P q ≤ 0 ∧ ℓ₁ q ≤ 0 ∧ ℓ₂ q ≤ 0} with hNdef
  have hNc : IsClosed N := (isClosed_le cP continuous_const).inter
    ((isClosed_le c₁ continuous_const).inter (isClosed_le c₂ continuous_const))
  have hP0 : ∀ p, P p = 0 →
      HasDerivAt (fun s => P (ϕG c s p)) (ρ * gy3 p / c * gQ c a σ p) 0 := by
    intro p hp
    have := hP p 0
    simp only [Flow.map_zero_apply, hp, mul_zero, zero_add] at this
    exact this
  refine isBlock_of_eventually hNc.isCompact
    (hNc.inter (((isClosed_eq cP continuous_const).inter
      (isClosed_le continuous_const (continuous_gQ c a σ))).union
        (isClosed_eq c₁ continuous_const)))
    (fun q hq => hq.1) ?_ ?_
  · rintro p ⟨hpN, (⟨hp0, hQ⟩ | h1)⟩
    · have hy3 := h3 p hp0 hpN.2.1 hpN.2.2
      suffices h : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < P (ϕG c t p) from
        h.mono fun t ht hN => ht.not_ge hN.1
      have hA : ∀ s, 0 < ρ * gy3 (ϕG c s p) / c := fun s =>
        div_pos (mul_pos hρ (gy3_pos c p hy3 s)) hc
      rcases hQ.lt_or_eq with hQ | hQ
      · exact (ev_of_deriv_pos (hP0 p hp0) (mul_pos (div_pos (mul_pos hρ hy3) hc) hQ)
          (by simpa [Flow.map_zero_apply] using hp0)).1
      · have hd := hasDerivAt_gQ c p (a := a) σ 0
        simp only [Flow.map_zero_apply] at hd
        obtain ⟨hQpos, -⟩ := ev_of_deriv_pos hd (gQ_deriv_pos hk hσ (hPH p hp0) hQ.symm hy3)
          (by simpa [Flow.map_zero_apply] using hQ.symm)
        obtain ⟨ε, hε, hεQ⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hQpos
        filter_upwards [Ioo_mem_nhdsGT hε] with t ht
        refine affine_pos_of_end (g := fun s => P (ϕG c s p)) (k := fun s => kH c σ (ϕG c s p))
          (m := fun s => ρ * gy3 (ϕG c s p) / c * gQ c a σ (ϕG c s p)) (hP p)
          (continuous_k c p _ (continuous_kH c σ)) ht.1 (fun s hs => ?_)
          (mul_pos (hA t) (hεQ ht)) (by simp only [Flow.map_zero_apply, hp0, le_refl])
        rcases hs.1.eq_or_lt with h | h
        · subst h; simp only [Flow.map_zero_apply, ← hQ, mul_zero, le_refl]
        · exact mul_nonneg (hA s).le (hεQ ⟨h, hs.2.trans_lt ht.2⟩).le
    · exact (hex p hpN.1 h1).mono fun t ht hN => ht.not_ge hN.2.1
  · intro p hpN hint hpL
    have hnot : ¬(P p < 0 ∧ ℓ₁ p < 0 ∧ ℓ₂ p < 0) := fun h => hint (interior_maximal
      (fun q (hq : q ∈ {q | P q < 0 ∧ ℓ₁ q < 0 ∧ ℓ₂ q < 0}) =>
        (⟨hq.1.le, hq.2.1.le, hq.2.2.le⟩ : q ∈ N))
      ((isOpen_lt cP continuous_const).inter
        ((isOpen_lt c₁ continuous_const).inter (isOpen_lt c₂ continuous_const))) h)
    have h1 : ℓ₁ p < 0 := hpN.2.1.lt_of_ne fun h => hpL ⟨hpN, Or.inr h⟩
    have hQ : P p = 0 → gQ c a σ p < 0 := fun h =>
      not_le.1 fun hQ => hpL ⟨hpN, Or.inl ⟨h, hQ⟩⟩
    have hPd : P p = 0 → (∀ᶠ t in 𝓝[>] (0 : ℝ), P (ϕG c t p) < 0) ∧
        ∀ᶠ t in 𝓝[<] (0 : ℝ), 0 < P (ϕG c t p) := fun h =>
      ev_of_deriv_neg (hP0 p h) (mul_neg_of_pos_of_neg
        (div_pos (mul_pos hρ (h3 p h hpN.2.1 hpN.2.2)) hc) (hQ h))
        (by simpa [Flow.map_zero_apply] using h)
    refine ⟨?_, ?_⟩
    · rcases hpN.2.2.lt_or_eq with h2 | h2
      · have hP' : P p = 0 := by
          by_contra hP'
          exact hnot ⟨hpN.1.lt_of_ne hP', h1, h2⟩
        exact (hPd hP').2.mono fun t ht hN => ht.not_ge hN.1
      · exact (hen p hpN.1 h2).1.mono fun t ht hN => ht.not_ge hN.2.2
    · have e1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), P (ϕG c t p) ≤ 0 := by
        rcases hpN.1.lt_or_eq with h | h
        · exact (ev_lt_of_lt c cP h).mono fun _ h => h.le
        · exact (hPd h).1.mono fun _ h => h.le
      have e2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ℓ₁ (ϕG c t p) ≤ 0 :=
        (ev_lt_of_lt c c₁ h1).mono fun _ h => h.le
      have e3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ℓ₂ (ϕG c t p) ≤ 0 := by
        rcases hpN.2.2.lt_or_eq with h | h
        · exact (ev_lt_of_lt c c₂ h).mono fun _ h => h.le
        · exact (hen p hpN.1 h).2.mono fun _ h => h.le
      filter_upwards [e1, e2, e3] with t g1 g2 g3 using ⟨g1, g2, g3⟩

end Block

/-- The exit set of `K^-`, namely the part `Q ≥ 0` of the plane face and the face `u = -δ`. -/
def Lm (c a η δ : ℝ) : Set OmG :=
  {q | q ∈ Km a η δ ∧ ((gH (a - η) q = 0 ∧ 0 ≤ gQ c a (a - η) q) ∨ gL δ 1 q = 0)}

/-- The exit set of `K^+`, namely the part `Q ≥ 0` of the plane face and the face `u = δ`. -/
def Lp (c a η δ : ℝ) : Set OmG :=
  {q | q ∈ Kp a η δ ∧ ((gG (a + η) q = 0 ∧ 0 ≤ gQ c a (-(a + η)) q) ∨ gL δ (-1) q = 0)}

namespace KHyp

variable (H : KHyp c a η δ)
include H

theorem isBlock_Km : IsBlock (ϕG c) (Km a η δ) (Lm c a η δ) := by
  refine isBlock_K c H.hc H.kminus_pos (by linarith [H.haη]) H.haη (continuous_gH _)
    (continuous_gL _ _) (continuous_gL _ _) (hasDerivAt_gH c · H.ha H.hc.ne' H.haη.ne')
    (fun _ h => h) (fun q h0 h1 h2 => ?_) (fun q h1 h0 => ?_) (fun q h1 h0 => ?_)
  · simp only [gH, gL] at h0 h1 h2
    rcases (gy3_nonneg q).eq_or_lt with h | h
    · have hs := sphere_G q
      have := H.hδ
      rw [← h] at h0
      have hy2 : gy2 q = 0 := by linarith
      have hy1 : gy1 q = 0 := by
        rw [hy2] at h1 h2
        nlinarith
      rw [hy1, hy2, ← h] at hs
      norm_num at hs
    · exact h
  · have hd := hasDerivAt_gL c q δ 1 0
    simp only [Flow.map_zero_apply, h0, mul_zero, sub_zero] at hd
    exact (ev_of_deriv_pos hd (H.face_m2 h1 h0) (by simpa [Flow.map_zero_apply] using h0)).1
  · have hd := hasDerivAt_gL c q (-δ) 1 0
    simp only [Flow.map_zero_apply, h0, mul_zero, sub_zero] at hd
    have := ev_of_deriv_neg hd (H.face_m3 h1 h0) (by simpa [Flow.map_zero_apply] using h0)
    exact ⟨this.2, this.1⟩

theorem isBlock_Kp : IsBlock (ϕG c) (Kp a η δ) (Lp c a η δ) := by
  refine isBlock_K c H.hc H.kplus_pos (by linarith [H.two]) H.haη' (continuous_gG _)
    (continuous_gL _ _) (continuous_gL _ _) (hasDerivAt_gG c · H.ha H.hc.ne' H.haη'.ne')
    (fun q h => by simp only [gG] at h; simp only [gH]; linarith)
    (fun q h0 h1 h2 => ?_) (fun q h1 h0 => ?_) (fun q h1 h0 => ?_)
  · simp only [gG, gL] at h0 h1 h2
    rcases (gy3_nonneg q).eq_or_lt with h | h
    · have hs := sphere_G q
      have := H.hδ
      rw [← h] at h0
      have hy2 : gy2 q = 0 := by linarith
      have hy1 : gy1 q = 0 := by
        rw [hy2] at h1 h2
        nlinarith
      rw [hy1, hy2, ← h] at hs
      norm_num at hs
    · exact h
  · have hd := hasDerivAt_gL c q δ (-1) 0
    simp only [Flow.map_zero_apply, h0, mul_zero, sub_zero] at hd
    exact (ev_of_deriv_pos hd (H.face_p2 h1 h0) (by simpa [Flow.map_zero_apply] using h0)).1
  · have hd := hasDerivAt_gL c q (-δ) (-1) 0
    simp only [Flow.map_zero_apply, h0, mul_zero, sub_zero] at hd
    have := ev_of_deriv_neg hd (H.face_p3 h1 h0) (by simpa [Flow.map_zero_apply] using h0)
    exact ⟨this.2, this.1⟩

/-- `K^-` is an orbit-convex neighborhood of `M^- = Inv(K^-)`. -/
theorem isConvexNbhd_Km : IsConvexNbhd (ϕG c) (Inv (ϕG c) (Km a η δ)) (Km a η δ) where
  isClosed := isClosed_Km
  inv := rfl
  subset_interior := fun _ hx => (H.isBlock_Km.Inv_subset_interior_diff hx).1
  convex p _ _ _ h12 h23 h1 h3 := H.convex_Km p h12 h23 h1 h3

/-- `K^+` is an orbit-convex neighborhood of `M^+ = Inv(K^+)`. -/
theorem isConvexNbhd_Kp : IsConvexNbhd (ϕG c) (Inv (ϕG c) (Kp a η δ)) (Kp a η δ) where
  isClosed := isClosed_Kp
  inv := rfl
  subset_interior := fun _ hx => (H.isBlock_Kp.Inv_subset_interior_diff hx).1
  convex p _ _ _ h12 h23 h1 h3 := H.convex_Kp p h12 h23 h1 h3

end KHyp

end ConleyCheck.Gubser
