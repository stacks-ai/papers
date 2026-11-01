import ConleyCheck.Gubser.TCConvex
import ConleyCheck.Gubser.MBlocks

/-!
# The six Morse sets of the global flow

The sets `Σ_I(A)`, `TC⁺`, `M⁻ = Inv(K⁻)`, `M⁺ = Inv(K⁺)`, `TC⁻` and `Σ_U(A)` (`MG`), ranked
`0, 1, 2, 2, 3, 4` (`GM.rank`). Each has a convex neighborhood (`exists_isConvexNbhd`), they are
pairwise disjoint (`disjoint_MG`), and every equilibrium lies in one of them (`fixed_mem_MG`).
The exclusions `no_conn_A`, `no_conn_R`, `no_conn_TCp` and `no_conn_Bm_Bp` rule out the connections
against the order that do not need the analysis of `M⁺ → M⁻`.
-/

open Set Filter Topology
open ConleyCheck.Conley ConleyCheck.ODE

namespace ConleyCheck.Gubser

variable {c a η δ : ℝ}

theorem exists_TC (hc : 0 < c) {σ : ℝ} (hσ : 0 < σ) : ∃ d d', TCHyp c d d' ∧ d < σ * d' := by
  obtain ⟨δ₀, hδ₀, h⟩ := exists_delta hc
  set d := min (δ₀ / 2) (σ ^ 2 / (8 * c)) with hd_def
  have hd : 0 < d := lt_min (by linarith) (by positivity)
  refine ⟨d, Real.sqrt (d / (4 * c)), h d hd (lt_of_le_of_lt (min_le_left _ _) (by linarith)), ?_⟩
  have hq : 0 < d / (4 * c) := by positivity
  refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
  rw [mul_pow, Real.sq_sqrt hq.le]
  have h8 : d * (8 * c) ≤ σ ^ 2 := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  have e : σ ^ 2 * (d / (4 * c)) = d * (σ ^ 2 / (4 * c)) := by ring
  rw [e, sq]
  refine mul_lt_mul_of_pos_left ?_ hd
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [mul_pos hd hc]

/-! ## The index set and the Morse sets -/

/-- Labels of the Morse sets. -/
inductive GM
  | A | Tp | Bm | Bp | Tm | R
  deriving DecidableEq

/-- The rank of a Morse set, so that connections go from higher to lower rank. -/
def GM.rank : GM → ℕ
  | .A => 0
  | .Tp => 1
  | .Bm => 2
  | .Bp => 2
  | .Tm => 3
  | .R => 4

/-- The Morse sets of `thm:M`. -/
def MG (c a η δ : ℝ) : GM → Set OmG
  | .A => SIA c a
  | .Tp => TCp
  | .Bm => Inv (ϕG c) (Km a η δ)
  | .Bp => Inv (ϕG c) (Kp a η δ)
  | .Tm => revΩ ⁻¹' TCp
  | .R => revΩ ⁻¹' SIA c a

theorem mem_Inv_of_fixed {N : Set OmG} {e : OmG} (he : ∀ t, ϕG c t e = e) (h : e ∈ N) :
    e ∈ Inv (ϕG c) N := fun t => by rw [he t]; exact h

theorem fixed_rev {e : OmG} (he : ∀ t, ϕG c t e = e) (t : ℝ) : ϕG c t (revΩ e) = revΩ e := by
  rw [ϕG_rev, he]

theorem Km_coords {q : OmG} (hq : q ∈ Km a η δ) :
    gy2 q + (a - η) * gy3 q ≤ 0 ∧ δ * gy1 q + gy2 q ≤ 0 ∧ -δ * gy1 q + gy2 q ≤ 0 := by
  obtain ⟨h1, h2, h3⟩ := hq
  simp only [gL, one_mul] at h2 h3
  exact ⟨h1, h2, h3⟩

theorem Kp_coords {q : OmG} (hq : q ∈ Kp a η δ) :
    (a + η) * gy3 q - gy2 q ≤ 0 ∧ δ * gy1 q - gy2 q ≤ 0 ∧ -δ * gy1 q - gy2 q ≤ 0 := by
  obtain ⟨h1, h2, h3⟩ := hq
  simp only [gL, gG, neg_one_mul, ← sub_eq_add_neg] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem mem_Km {q : OmG} (h1 : gy2 q + (a - η) * gy3 q ≤ 0) (h2 : δ * gy1 q + gy2 q ≤ 0)
    (h3 : -δ * gy1 q + gy2 q ≤ 0) : q ∈ Km a η δ :=
  ⟨h1, by simp only [gL, one_mul]; exact h2, by simp only [gL, one_mul]; exact h3⟩

theorem mem_Kp {q : OmG} (h1 : (a + η) * gy3 q - gy2 q ≤ 0) (h2 : δ * gy1 q - gy2 q ≤ 0)
    (h3 : -δ * gy1 q - gy2 q ≤ 0) : q ∈ Kp a η δ :=
  ⟨by simp only [gG]; exact h1, by simp only [gL]; linarith, by simp only [gL]; linarith⟩

theorem revΩ_preimage_Km : revΩ ⁻¹' Km a η δ = Km a η δ := by
  ext q
  simp only [mem_preimage]
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := Km_coords h
    simp only [gy1_rev, gy2_rev, gy3_rev] at h1 h2 h3
    exact mem_Km h1 (by linarith) (by linarith)
  · intro h
    obtain ⟨h1, h2, h3⟩ := Km_coords h
    exact mem_Km (by simp only [gy2_rev, gy3_rev]; exact h1)
      (by simp only [gy1_rev, gy2_rev]; linarith) (by simp only [gy1_rev, gy2_rev]; linarith)

theorem revΩ_preimage_Kp : revΩ ⁻¹' Kp a η δ = Kp a η δ := by
  ext q
  simp only [mem_preimage]
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := Kp_coords h
    simp only [gy1_rev, gy2_rev, gy3_rev] at h1 h2 h3
    exact mem_Kp h1 (by linarith) (by linarith)
  · intro h
    obtain ⟨h1, h2, h3⟩ := Kp_coords h
    exact mem_Kp (by simp only [gy2_rev, gy3_rev]; exact h1)
      (by simp only [gy1_rev, gy2_rev]; linarith) (by simp only [gy1_rev, gy2_rev]; linarith)

theorem revΩ_preimage_Mm : revΩ ⁻¹' Inv (ϕG c) (Km a η δ) = Inv (ϕG c) (Km a η δ) := by
  rw [← (isReversor_revΩ c).Inv_preimage, revΩ_preimage_Km]

theorem revΩ_preimage_Mp : revΩ ⁻¹' Inv (ϕG c) (Kp a η δ) = Inv (ϕG c) (Kp a η δ) := by
  rw [← (isReversor_revΩ c).Inv_preimage, revΩ_preimage_Kp]

section Hyp

variable (H : KHyp c a η δ)
include H

theorem gy2_neg_of_Km {q : OmG} (hq : q ∈ Km a η δ) : gy2 q < 0 := by
  obtain ⟨h1, h2, h3⟩ := Km_coords hq
  by_contra h
  push Not at h
  have hd := H.hδ
  have hy1 : gy1 q = 0 := by nlinarith
  have hy2 : gy2 q = 0 := by nlinarith
  have hy3 : gy3 q = 0 := by nlinarith [gy3_nonneg q, H.haη]
  have := sphere_G q
  rw [hy1, hy2, hy3] at this
  norm_num at this

theorem gy2_pos_of_Kp {q : OmG} (hq : q ∈ Kp a η δ) : 0 < gy2 q := by
  obtain ⟨h1, h2, h3⟩ := Kp_coords hq
  by_contra h
  push Not at h
  have hd := H.hδ
  have hy1 : gy1 q = 0 := by nlinarith
  have hy2 : gy2 q = 0 := by nlinarith
  have hy3 : gy3 q = 0 := by nlinarith [gy3_nonneg q, H.haη']
  have := sphere_G q
  rw [hy1, hy2, hy3] at this
  norm_num at this

theorem B2_nonneg_of_Km {q : OmG} (hq : q ∈ Km a η δ) : 0 ≤ gB2 a q := by
  have := gy2_neg_of_Km H hq
  unfold gB2
  nlinarith [gy3_nonneg q, H.ha0]

theorem not_B2_of_Kp {q : OmG} (hq : q ∈ Kp a η δ) (hB : 0 ≤ gB2 a q) : False := by
  obtain ⟨h1, -, -⟩ := Kp_coords hq
  have h2 := gy2_pos_of_Kp H hq
  unfold gB2 at hB
  have : gy3 q = 0 := by nlinarith [gy3_nonneg q, H.hη]
  rw [this] at h1 hB
  linarith

theorem B1_pos_of_Kp {q : OmG} (hq : q ∈ Kp a η δ) : 0 < gB1 a q := by
  have := gy2_pos_of_Kp H hq
  unfold gB1
  nlinarith [gy3_nonneg q, H.ha0]

theorem exists_isConvexNbhd (i : GM) : ∃ N, IsConvexNbhd (ϕG c) (MG c a η δ i) N := by
  obtain ⟨d, d', hT, hd⟩ := exists_TC H.hc H.ha0
  cases i
  · exact ⟨_, isConvexNbhd_NA H.hc H.ha H.ha0⟩
  · exact ⟨_, isConvexNbhd_NG hT H.ha H.ha0 hd⟩
  · exact ⟨_, H.isConvexNbhd_Km⟩
  · exact ⟨_, H.isConvexNbhd_Kp⟩
  · exact ⟨_, (isReversor_revΩ c).isConvexNbhd (isConvexNbhd_NG hT H.ha H.ha0 hd)⟩
  · exact ⟨_, (isReversor_revΩ c).isConvexNbhd (isConvexNbhd_NA H.hc H.ha H.ha0)⟩

/-! ## Coordinates on the Morse sets -/

theorem SIA_coords {q : OmG} (hq : q ∈ SIA c a) :
    0 < gy3 q ∧ gy1 q = 0 ∧ gy2 q = a * gy3 q ∧ gw1 q = 1 :=
  ⟨gy3_pos_of_NA (Inv_subset _ hq), gy1_eq_zero_of_SIA H.ha H.ha0 hq,
    gy2_eq_of_SIA H.ha H.ha0 hq, gw1_eq_one_of_SIA hq⟩

theorem disjoint_MG : Pairwise fun i j => Disjoint (MG c a η δ i) (MG c a η δ j) := by
  have hη := H.hη
  have ha0 := H.ha0
  have hd := H.hδ
  have cA : ∀ q ∈ MG c a η δ .A, 0 < gy3 q ∧ gy1 q = 0 ∧ gy2 q = a * gy3 q ∧ gw1 q = 1 :=
    fun q hq => SIA_coords H hq
  have cR : ∀ q ∈ MG c a η δ .R, 0 < gy3 q ∧ gy1 q = 0 ∧ gy2 q = a * gy3 q ∧ gw1 q = -1 :=
    fun q hq => by
      obtain ⟨h1, h2, h3, h4⟩ := SIA_coords H hq
      simp only [gy1_rev, gy2_rev, gy3_rev, gw1_rev] at h1 h2 h3 h4
      exact ⟨h1, by linarith, h3, by linarith⟩
  have cTp : ∀ q ∈ MG c a η δ .Tp, gy1 q = 1 ∧ gy2 q = 0 ∧ gy3 q = 0 := fun q hq =>
    ⟨hq, TCp_coords hq⟩
  have cTm : ∀ q ∈ MG c a η δ .Tm, gy1 q = -1 ∧ gy2 q = 0 ∧ gy3 q = 0 := fun q hq => by
    obtain ⟨h2, h3⟩ := TCp_coords hq
    have h1 : gy1 (revΩ q) = 1 := hq
    simp only [gy1_rev, gy2_rev, gy3_rev] at h1 h2 h3
    exact ⟨by linarith, h2, h3⟩
  have cBm : ∀ q ∈ MG c a η δ .Bm, gy2 q < 0 ∧ gy2 q + (a - η) * gy3 q ≤ 0 ∧
      δ * gy1 q + gy2 q ≤ 0 ∧ -δ * gy1 q + gy2 q ≤ 0 := fun q hq => by
    have hK : q ∈ Km a η δ := Inv_subset _ hq
    exact ⟨gy2_neg_of_Km H hK, Km_coords hK⟩
  have cBp : ∀ q ∈ MG c a η δ .Bp, 0 < gy2 q ∧ (a + η) * gy3 q - gy2 q ≤ 0 ∧
      δ * gy1 q - gy2 q ≤ 0 ∧ -δ * gy1 q - gy2 q ≤ 0 := fun q hq => by
    have hK : q ∈ Kp a η δ := Inv_subset _ hq
    exact ⟨gy2_pos_of_Kp H hK, Kp_coords hK⟩
  intro i j hij
  rw [Set.disjoint_left]
  intro q hi hj
  cases i <;> cases j <;> first
    | exact hij rfl
    | (first
        | have h1 := cA q hi | have h1 := cR q hi | have h1 := cTp q hi | have h1 := cTm q hi
        | have h1 := cBm q hi | have h1 := cBp q hi
       first
        | have h2 := cA q hj | have h2 := cR q hj | have h2 := cTp q hj | have h2 := cTm q hj
        | have h2 := cBm q hj | have h2 := cBp q hj
       nlinarith [h1, h2])

/-! ## Every equilibrium lies in a Morse set -/

theorem fixed_mem_MG {e : OmG} (he : ∀ t, ϕG c t e = e) : ∃ i, e ∈ MG c a η δ i := by
  have hc := H.hc
  have hd := H.hδ
  have hF := fieldG_eq_zero he
  have e1 : gP1 e - gS c e * gy1 e = 0 := congrArg (fun v : EG => v.1.1) hF
  have e2 : gP2 c e - gS c e * gy2 e = 0 := congrArg (fun v : EG => v.1.2.1) hF
  have e3 : -(gS c e * gy3 e) = 0 := congrArg (fun v : EG => v.1.2.2) hF
  have e4 : gy3 e * gw2 e ^ 2 = 0 := congrArg (fun v : EG => v.2.1) hF
  have hτ := gw1_mem e
  rcases (gy3_nonneg e).lt_or_eq with h3 | h3
  · have hS : gS c e = 0 := by
      rcases mul_eq_zero.1 (neg_eq_zero.1 e3) with h | h
      · exact h
      · exact absurd h h3.ne'
    rw [hS, zero_mul, sub_zero] at e1 e2
    have hw2 : gw2 e = 0 := by
      rcases mul_eq_zero.1 e4 with h | h
      · exact absurd h h3.ne'
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    have hτ2 : gw1 e ^ 2 = 1 := by have := circle_G e; rw [hw2] at this; linarith
    obtain ⟨T, hT⟩ : ∃ T, gy1 e = T * gy3 e := ⟨gy1 e / gy3 e, (div_mul_cancel₀ _ h3.ne').symm⟩
    obtain ⟨π, hπ⟩ : ∃ π, gy2 e = π * gy3 e := ⟨gy2 e / gy3 e, (div_mul_cancel₀ _ h3.ne').symm⟩
    have h3s : gy3 e ^ 2 ≠ 0 := pow_ne_zero 2 h3.ne'
    have hβT : βT T π (gw1 e) = 0 := by
      have : gy3 e ^ 2 * βT T π (gw1 e) = 0 := by
        rw [← e1, gP1_eq, hT, hπ]; unfold βT; ring
      exact (mul_eq_zero.1 this).resolve_left h3s
    have hβπ : βπ c T π (gw1 e) = 0 := by
      have : gy3 e ^ 2 * βπ c T π (gw1 e) = 0 := by
        rw [← e2, gP2_eq, hT, hπ]; unfold βπ; field_simp
      exact (mul_eq_zero.1 this).resolve_left h3s
    have hβτ : βτ (gw1 e) = 0 := by unfold βτ; linarith
    obtain ⟨hτ1, hrest⟩ := (equilibria_iff hc.ne' T π (gw1 e)).1 ⟨hβT, hβπ, hβτ⟩
    rcases hrest with ⟨hT0, hπ2⟩ | ⟨hπ2, hT2⟩
    · have : (π - a) * (π + a) = 0 := by rw [← H.ha] at hπ2; linear_combination hπ2
      rcases mul_eq_zero.1 this with hπa | hπa
      · have hπa : π = a := by linarith
        rcases hτ1 with hτ1 | hτ1
        · exact ⟨.A, mem_SIA_of_fixed H.hc H.ha0 he (by rw [hT, hT0, zero_mul])
            (by rw [hπ, hπa]) h3 hτ1⟩
        · refine ⟨.R, mem_SIA_of_fixed H.hc H.ha0 (fixed_rev he) ?_ ?_ ?_ ?_⟩
          · rw [gy1_rev, hT, hT0, zero_mul, neg_zero]
          · rw [gy2_rev, gy3_rev, hπ, hπa]
          · rwa [gy3_rev]
          · rw [gw1_rev, hτ1, neg_neg]
      · have hπa : π = -a := by linarith
        refine ⟨.Bm, mem_Inv_of_fixed he (mem_Km ?_ ?_ ?_)⟩ <;>
          rw [hπ, hπa] <;> (try rw [hT, hT0]) <;> nlinarith [H.hη, mul_pos H.ha0 h3, mul_pos H.hη h3]
    · refine ⟨.Bp, mem_Inv_of_fixed he (mem_Kp ?_ ?_ ?_)⟩
      · rw [hπ, hπ2]; nlinarith [H.two]
      · rw [hπ, hπ2, hT, hT2]
        rcases hτ1 with h | h <;> rw [h] <;>
          nlinarith [mul_le_mul_of_nonneg_right H.k3 h3.le, mul_pos (mul_pos hc hd) h3]
      · rw [hπ, hπ2, hT, hT2]
        rcases hτ1 with h | h <;> rw [h] <;>
          nlinarith [mul_le_mul_of_nonneg_right H.k3 h3.le, mul_pos (mul_pos hc hd) h3]
  · have hs := sphere_G e
    rw [← h3] at hs
    have cross : gy1 e * gy2 e * (5 / 3 * gw1 e * gy2 e + gy1 e / c) = 0 := by
      rw [gP1_eq, ← h3] at e1
      rw [gP2_eq, ← h3] at e2
      linear_combination gy2 e * e1 - gy1 e * e2
    rcases mul_eq_zero.1 cross with h12 | hD
    · rcases mul_eq_zero.1 h12 with h1 | h2
      · have : (gy2 e - 1) * (gy2 e + 1) = 0 := by rw [h1] at hs; linear_combination hs
        rcases mul_eq_zero.1 this with h | h
        · refine ⟨.Bp, mem_Inv_of_fixed he (mem_Kp ?_ ?_ ?_)⟩ <;>
            (try rw [← h3]) <;> (try rw [h1]) <;> linarith
        · refine ⟨.Bm, mem_Inv_of_fixed he (mem_Km ?_ ?_ ?_)⟩ <;>
            (try rw [← h3]) <;> (try rw [h1]) <;> linarith
      · have : (gy1 e - 1) * (gy1 e + 1) = 0 := by rw [h2] at hs; linear_combination hs
        rcases mul_eq_zero.1 this with h | h
        · exact ⟨.Tp, show gy1 e = 1 by linarith⟩
        · exact ⟨.Tm, show gy1 (revΩ e) = 1 by rw [gy1_rev]; linarith⟩
    · have hy1 : gy1 e = -(5 / 3) * c * gw1 e * gy2 e := by
        field_simp at hD; linarith
      have hk : 5 / 3 * c * δ ≤ 1 := by linarith [H.k3]
      have hcd : 0 ≤ c * δ := by positivity
      have hk1 : 0 ≤ 1 - 5 / 3 * c * δ * gw1 e := by nlinarith [hτ.2]
      have hk2 : 0 ≤ 1 + 5 / 3 * c * δ * gw1 e := by nlinarith [hτ.1]
      rcases le_total (gy2 e) 0 with hy2 | hy2
      · refine ⟨.Bm, mem_Inv_of_fixed he (mem_Km ?_ ?_ ?_)⟩
        · rw [← h3]; linarith
        · rw [hy1]; nlinarith [mul_nonneg (neg_nonneg.2 hy2) hk1]
        · rw [hy1]; nlinarith [mul_nonneg (neg_nonneg.2 hy2) hk2]
      · refine ⟨.Bp, mem_Inv_of_fixed he (mem_Kp ?_ ?_ ?_)⟩
        · rw [← h3]; linarith
        · rw [hy1]; nlinarith [mul_nonneg hy2 hk1]
        · rw [hy1]; nlinarith [mul_nonneg hy2 hk2]

/-! ## Exclusions -/

/-- `Σ_I(A)` is an attractor, so no orbit outside it has its `α`-limit set there. -/
theorem no_conn_A {x : OmG} (hx : x ∉ SIA c a) (hα : (alphaLim (ϕG c) x ∩ SIA c a).Nonempty) :
    False := hx (mem_SIA_of_alphaLim H.hc H.ha H.ha0 hα)

/-- `Σ_U(A)` is a repeller. -/
theorem no_conn_R {x : OmG} (hx : x ∉ revΩ ⁻¹' SIA c a)
    (hω : (omegaLim (ϕG c) x ∩ revΩ ⁻¹' SIA c a).Nonempty) : False := by
  obtain ⟨z, hz, hzS⟩ := hω
  exact hx (mem_SIA_of_alphaLim H.hc H.ha H.ha0
    ⟨revΩ z, (isReversor_revΩ c).mem_alphaLim hz, hzS⟩)

/-- An orbit leaving `TC⁺` does not go to `M⁻`, `M⁺` or `TC⁻`. -/
theorem no_conn_TCp {x : OmG} (hx : x ∉ TCp) (hα : (alphaLim (ϕG c) x ∩ TCp).Nonempty) {i : GM}
    (hi : i = .Bm ∨ i = .Bp ∨ i = .Tm) (hω : (omegaLim (ϕG c) x ∩ MG c a η δ i).Nonempty) :
    False := by
  obtain ⟨d, d', hT, hd⟩ := exists_TC H.hc H.haη
  have hda : d < a * d' := hd.trans_le (mul_le_mul_of_nonneg_right (by linarith [H.hη])
    hT.hδ'.le)
  obtain ⟨s, hs⟩ := exists_exit_of_alphaLim hT H.ha H.ha0 hda hα hx
  have hshift : ∀ t, ϕG c t x = ϕG c (t - s) (ϕG c s x) := fun t => by
    rw [← Flow.map_add, sub_add_cancel]
  have hA : ∀ t, s < t → 0 < gy1 (ϕG c t x) ∧ 0 ≤ gB2 a (ϕG c t x) := fun t ht => by
    have := after_exit hT H.ha H.ha0 hda hs (t := t - s) (by linarith)
    rw [← hshift] at this
    exact ⟨this.1, this.2.2.2.1⟩
  rcases hi with rfl | rfl | rfl
  · obtain ⟨t, hK, ht⟩ := ((H.isConvexNbhd_Km.eventually_of_meets hω).and
      (eventually_gt_atTop s)).exists
    have := after_exit_gH hT H.ha H.hc H.haη H.kminus_pos.le hd hs (t := t - s) (by linarith)
    rw [← hshift] at this
    linarith [(Km_coords hK).1, show gH (a - η) (ϕG c t x) = gy2 (ϕG c t x) +
      (a - η) * gy3 (ϕG c t x) from rfl]
  · obtain ⟨t, hK, ht⟩ := ((H.isConvexNbhd_Kp.eventually_of_meets hω).and
      (eventually_gt_atTop s)).exists
    exact not_B2_of_Kp H hK (hA t ht).2
  · obtain ⟨z, hz, hzT⟩ := hω
    have hsub := omegaLim_subset_of_eventually (ϕG c) (x := x)
      (isClosed_le continuous_const continuous_gy1)
      ((eventually_gt_atTop s).mono fun t ht => (hA t ht).1.le) hz
    have h1 : gy1 (revΩ z) = 1 := hzT
    rw [gy1_rev] at h1
    have : (0 : ℝ) ≤ gy1 z := hsub
    linarith

/-- With `y₁ ≥ 0` there is no connection from `M⁻` to `M⁺`, because `B₂ ≥ 0` on `K⁻` and
`B₂ ≥ 0` is forward invariant. -/
theorem no_conn_Bm_Bp {x : OmG} (hy : 0 ≤ gy1 x)
    (hα : (alphaLim (ϕG c) x ∩ Inv (ϕG c) (Km a η δ)).Nonempty)
    (hω : (omegaLim (ϕG c) x ∩ Inv (ϕG c) (Kp a η δ)).Nonempty) : False := by
  obtain ⟨T, hT⟩ := eventually_atBot.1 (H.isConvexNbhd_Km.eventually_of_meets_alpha hα)
  have hB0 := B2_nonneg_of_Km H (hT T le_rfl)
  obtain ⟨t, hK, ht⟩ := ((H.isConvexNbhd_Kp.eventually_of_meets hω).and
    (eventually_ge_atTop T)).exists
  exact not_B2_of_Kp H hK (gB2_nonneg (c := c) (p := x) H.ha H.ha0 H.hc hy ht hB0)

end Hyp

end ConleyCheck.Gubser
