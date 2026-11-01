import ConleyCheck.Gubser.GlobalLimits

/-!
# The attractor `Σ_I(A)`

The closed set `N_A = {τ ≥ 1/2, |y₁| ≤ (ac/2) y₃, (a/2) y₃ ≤ y₂ ≤ (3a/2) y₃}` is forward invariant,
and its maximal invariant set is contained in `{T = 0, π̄ = a, τ = 1}`, which lies in its
interior (`isConvexNbhd_NA`).
-/

open Set Filter Topology
open ConleyCheck.Conley ConleyCheck.ODE

namespace ConleyCheck.Gubser

variable {c a : ℝ}

/-- The forward invariant neighborhood of the point `A` on `{τ = 1}`. -/
def NA (c a : ℝ) : Set OmG :=
  {q | 1 / 2 ≤ gw1 q ∧ gy1 q - a * c / 2 * gy3 q ≤ 0 ∧ -gy1 q - a * c / 2 * gy3 q ≤ 0 ∧
    gy2 q - 3 * a / 2 * gy3 q ≤ 0 ∧ a / 2 * gy3 q - gy2 q ≤ 0}

/-- The attractor `Σ_I(A) = Inv(N_A)`. -/
def SIA (c a : ℝ) : Set OmG := Inv (ϕG c) (NA c a)

theorem isClosed_NA (c a : ℝ) : IsClosed (NA c a) := by
  have h3 := continuous_gy3
  have h1 := continuous_gy1
  have h2 := continuous_gy2
  simp only [NA, ofPred_and]
  refine (isClosed_le continuous_const continuous_gw1).inter ((isClosed_le ?_ continuous_const).inter
    ((isClosed_le ?_ continuous_const).inter ((isClosed_le ?_ continuous_const).inter
      (isClosed_le ?_ continuous_const)))) <;> fun_prop

theorem gy3_pos_of_NA {q : OmG} (hq : q ∈ NA c a) : 0 < gy3 q := by
  obtain ⟨-, h1, h2, h3, h4⟩ := hq
  refine (gy3_nonneg q).lt_of_ne fun h => ?_
  rw [← h] at h1 h2 h3 h4
  have hs := sphere_G q
  rw [← h] at hs
  have e1 : gy1 q = 0 := by linarith
  have e2 : gy2 q = 0 := by linarith
  rw [e1, e2] at hs
  norm_num at hs

theorem ev_lin_le (c : ℝ) (p : OmG) (l₁ l₂ l₃ : ℝ)
    (h : l₁ * gy1 p + l₂ * gy2 p + l₃ * gy3 p ≤ 0)
    (hd : l₁ * gy1 p + l₂ * gy2 p + l₃ * gy3 p = 0 → l₁ * gP1 p + l₂ * gP2 c p < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), l₁ * gy1 (ϕG c t p) + l₂ * gy2 (ϕG c t p) + l₃ * gy3 (ϕG c t p) ≤ 0 := by
  have hD := hasDerivAt_lin c p l₁ l₂ l₃ 0
  simp only [Flow.map_zero_apply] at hD
  refine eventually_le_right hD (by simpa only [Flow.map_zero_apply] using h) fun h0 => ?_
  have h0' : l₁ * gy1 p + l₂ * gy2 p + l₃ * gy3 p = 0 := by
    simpa only [Flow.map_zero_apply] using h0
  rw [h0', mul_zero, sub_zero]
  exact hd h0'

section Hyp

variable (hc : 0 < c) (ha : a ^ 2 = 1 / 5) (ha0 : 0 < a)
include hc ha ha0

omit hc in
theorem a_lt_one : a < 1 := by nlinarith

theorem NA_local_fwd (p : OmG) (hp : p ∈ NA c a) : ∀ᶠ t in 𝓝[>] (0 : ℝ), ϕG c t p ∈ NA c a := by
  have h3 := gy3_pos_of_NA hp
  obtain ⟨hτ, h1, h2, h3', h4⟩ := hp
  have hτ0 : 0 < gw1 p := by linarith
  have hac : 0 < a * c / 2 := by positivity
  have hu1 : gy1 p / c ≤ a / 2 * gy3 p := by rw [div_le_iff₀ hc]; nlinarith
  have hu2 : -(a / 2 * gy3 p) ≤ gy1 p / c := by rw [le_div_iff₀ hc]; nlinarith
  have hpos : 0 < a ^ 2 * gy3 p ^ 2 := by positivity
  have h5 : gy3 p ^ 2 / 5 = a ^ 2 * gy3 p ^ 2 := by rw [ha]; ring
  have hrw : ∀ y : ℝ, gy1 p * y / c = gy1 p / c * y := fun y => by ring
  have e1 := ev_lin_le c p 1 0 (-(a * c / 2)) (by linarith) fun h0 => by
    have hy : gy1 p = a * c / 2 * gy3 p := by linarith
    have : gw1 p * gy1 p * (gy2 p - 2 * gy3 p) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hτ0 (by rw [hy]; positivity)) (by nlinarith [a_lt_one ha ha0])
    rw [gP1_eq]; linarith
  have e2 := ev_lin_le c p (-1) 0 (-(a * c / 2)) (by linarith) fun h0 => by
    have hy : gy1 p = -(a * c / 2 * gy3 p) := by linarith
    have : gw1 p * gy1 p * (gy2 p - 2 * gy3 p) > 0 :=
      mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hτ0 (by rw [hy]; nlinarith))
        (by nlinarith [a_lt_one ha ha0])
    rw [gP1_eq]; linarith
  have e3 := ev_lin_le c p 0 1 (-(3 * a / 2)) (by linarith) fun h0 => by
    have hy : gy2 p = 3 * a / 2 * gy3 p := by linarith
    rw [gP2_eq, hrw, hy, h5]
    nlinarith [mul_nonneg (sub_nonneg.2 hτ) hpos.le,
      mul_nonneg (by linarith : 0 ≤ gy1 p / c + a / 2 * gy3 p) (mul_pos ha0 h3).le]
  have e4 := ev_lin_le c p 0 (-1) (a / 2) (by linarith) fun h0 => by
    have hy : gy2 p = a / 2 * gy3 p := by linarith
    rw [gP2_eq, hrw, hy, h5]
    nlinarith [mul_nonneg (sub_nonneg.2 hτ) hpos.le,
      mul_nonneg (by linarith : 0 ≤ a / 2 * gy3 p - gy1 p / c) (mul_pos ha0 h3).le]
  filter_upwards [e1, e2, e3, e4, self_mem_nhdsWithin] with t f1 f2 f3 f4 (ht : 0 < t)
  refine ⟨hτ.trans ?_, by linarith, by linarith, by linarith, by linarith⟩
  have := monotone_gw1 c p ht.le
  simpa only [Flow.map_zero_apply] using this

theorem NA_fwd {p : OmG} (hp : p ∈ NA c a) {t : ℝ} (ht : 0 ≤ t) : ϕG c t p ∈ NA c a :=
  mem_of_local_fwd (ϕG c) (isClosed_NA c a) (NA_local_fwd hc ha ha0) hp ht

omit hc ha ha0 in
theorem gπ_le {q : OmG} (hq : q ∈ NA c a) : gπ q ≤ 3 * a / 2 := by
  rw [gπ, div_le_iff₀ (gy3_pos_of_NA hq)]; linarith [hq.2.2.2.1]

omit hc ha ha0 in
theorem le_gπ {q : OmG} (hq : q ∈ NA c a) : a / 2 ≤ gπ q := by
  rw [gπ, le_div_iff₀ (gy3_pos_of_NA hq)]; linarith [hq.2.2.2.2]

omit hc ha ha0 in
theorem continuousOn_ratio {f : OmG → ℝ} (hf : Continuous f) :
    ContinuousOn (fun q => f q / gy3 q) (SIA c a) :=
  hf.continuousOn.div continuous_gy3.continuousOn fun _ hq =>
    (gy3_pos_of_NA (Inv_subset _ hq)).ne'

omit hc ha ha0 in
theorem isCompact_SIA : IsCompact (SIA c a) := isCompact_Inv (isClosed_NA c a).isCompact

omit hc ha ha0 in
theorem SIA_inv {z : OmG} (hz : z ∈ SIA c a) (t : ℝ) : ϕG c t z ∈ SIA c a := flow_mem_Inv hz t

omit hc in
theorem gT_eq_zero_of_SIA {z : OmG} (hz : z ∈ SIA c a) : gT z = 0 := by
  have := nonpos_of_deriv_neg (ϕG c) isCompact_SIA (fun z hz t => SIA_inv hz t)
    (V := fun q => gT q * gT q) ((continuousOn_ratio continuous_gy1).mul
      (continuousOn_ratio continuous_gy1))
    (d := fun q => gy3 q * βT (gT q) (gπ q) (gw1 q) * gT q +
      gT q * (gy3 q * βT (gT q) (gπ q) (gw1 q))) (fun q hq hV => by
      have hN := Inv_subset _ hq
      have h3 := gy3_pos_of_NA hN
      have hD := hasDerivAt_gT c q (t := 0) (by rwa [Flow.map_zero_apply])
      simp only [Flow.map_zero_apply] at hD
      have hz0 : (ϕG c).toFun 0 q = q := (ϕG c).map_zero_apply q
      refine ⟨by have h2 := hD.mul hD; rw [hz0] at h2; exact h2, ?_⟩
      have e : gy3 q * βT (gT q) (gπ q) (gw1 q) * gT q + gT q * (gy3 q * βT (gT q) (gπ q) (gw1 q))
          = 2 / 3 * (gy3 q * (gT q * gT q) * gw1 q) * (gπ q - 2) := by unfold βT; ring
      rw [e]
      exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) (mul_pos (mul_pos h3 hV)
        (by linarith [hN.1]))) (by linarith [gπ_le hN, a_lt_one ha ha0])) z hz
  exact mul_self_eq_zero.1 (le_antisymm this (mul_self_nonneg _))

omit hc in
theorem gy1_eq_zero_of_SIA {z : OmG} (hz : z ∈ SIA c a) : gy1 z = 0 := by
  have := gT_eq_zero_of_SIA ha ha0 hz
  rwa [gT, div_eq_zero_iff, or_iff_left (gy3_pos_of_NA (Inv_subset _ hz)).ne'] at this

omit hc ha ha0 in
theorem gw1_eq_one_of_SIA {z : OmG} (hz : z ∈ SIA c a) : gw1 z = 1 := by
  have := nonpos_of_deriv_neg (ϕG c) isCompact_SIA (fun z hz t => SIA_inv hz t)
    (V := fun q => 1 - gw1 q) (continuous_const.sub continuous_gw1).continuousOn
    (d := fun q => -(gy3 q * (1 - gw1 q ^ 2))) (fun q hq hV => by
      have hN := Inv_subset _ hq
      have h3 := gy3_pos_of_NA hN
      have hD := hasDerivAt_gw1 c q 0
      simp only [Flow.map_zero_apply] at hD
      refine ⟨hD.const_sub 1, ?_⟩
      have hw : 1 / 2 ≤ gw1 q := hN.1
      have : 0 < 1 - gw1 q ^ 2 := by nlinarith
      nlinarith [mul_pos h3 this]) z hz
  linarith [(gw1_mem z).2]

omit hc in
theorem gπ_eq_of_SIA {z : OmG} (hz : z ∈ SIA c a) : gπ z = a := by
  have := nonpos_of_deriv_neg (ϕG c) isCompact_SIA (fun z hz t => SIA_inv hz t)
    (V := fun q => (gπ q - a) * (gπ q - a))
    (((continuousOn_ratio continuous_gy2).sub continuousOn_const).mul
      ((continuousOn_ratio continuous_gy2).sub continuousOn_const))
    (d := fun q => gy3 q * βπ c (gT q) (gπ q) (gw1 q) * (gπ q - a) +
      (gπ q - a) * (gy3 q * βπ c (gT q) (gπ q) (gw1 q))) (fun q hq hV => by
      have hN := Inv_subset _ hq
      have h3 := gy3_pos_of_NA hN
      have hD := hasDerivAt_gπ c q (t := 0) (by rwa [Flow.map_zero_apply])
      simp only [Flow.map_zero_apply] at hD
      have hz0 : (ϕG c).toFun 0 q = q := (ϕG c).map_zero_apply q
      refine ⟨by
        have h2 := (hD.sub_const a).mul (hD.sub_const a); rw [hz0] at h2; exact h2, ?_⟩
      have hT := gT_eq_zero_of_SIA ha ha0 hq
      have hw := gw1_eq_one_of_SIA hq
      have e : gy3 q * βπ c (gT q) (gπ q) (gw1 q) * (gπ q - a) +
          (gπ q - a) * (gy3 q * βπ c (gT q) (gπ q) (gw1 q))
          = -(8 / 3) * (gy3 q * ((gπ q - a) * (gπ q - a))) * (gπ q + a) := by
        unfold βπ; rw [hT, hw, ← ha]; ring
      rw [e]
      have : 0 < gπ q + a := by linarith [le_gπ hN]
      nlinarith [mul_pos (mul_pos h3 hV) this]) z hz
  have h0 := le_antisymm this (mul_self_nonneg _)
  linarith [mul_self_eq_zero.1 h0]

omit hc in
theorem gy2_eq_of_SIA {z : OmG} (hz : z ∈ SIA c a) : gy2 z = a * gy3 z := by
  have h := gπ_eq_of_SIA ha ha0 hz
  rw [gπ, div_eq_iff (gy3_pos_of_NA (Inv_subset _ hz)).ne'] at h
  linarith

omit ha in
/-- The open core of `N_A`. -/
theorem subset_interior_NA {q : OmG} (h1 : gy1 q = 0) (h2 : gy2 q = a * gy3 q) (h3 : 0 < gy3 q)
    (hw : gw1 q = 1) : q ∈ interior (NA c a) := by
  have hU : IsOpen {q : OmG | 1 / 2 < gw1 q ∧ gy1 q - a * c / 2 * gy3 q < 0 ∧
      -gy1 q - a * c / 2 * gy3 q < 0 ∧ gy2 q - 3 * a / 2 * gy3 q < 0 ∧
      a / 2 * gy3 q - gy2 q < 0} := by
    have := continuous_gy1; have := continuous_gy2; have := continuous_gy3
    simp only [ofPred_and]
    refine (isOpen_lt continuous_const continuous_gw1).inter ((isOpen_lt ?_ continuous_const).inter
      ((isOpen_lt ?_ continuous_const).inter ((isOpen_lt ?_ continuous_const).inter
        (isOpen_lt ?_ continuous_const)))) <;> fun_prop
  refine interior_maximal ?_ hU ?_
  · intro q hq
    exact ⟨hq.1.le, hq.2.1.le, hq.2.2.1.le, hq.2.2.2.1.le, hq.2.2.2.2.le⟩
  refine ⟨by rw [hw]; norm_num, ?_, ?_, ?_, ?_⟩
  · rw [h1]; have : 0 < a * c / 2 * gy3 q := by positivity
    linarith
  · rw [h1]; have : 0 < a * c / 2 * gy3 q := by positivity
    linarith
  · rw [h2]; nlinarith
  · rw [h2]; nlinarith

theorem isConvexNbhd_NA : IsConvexNbhd (ϕG c) (SIA c a) (NA c a) :=
  IsConvexNbhd.of_fwd (ϕG c) (isClosed_NA c a) rfl (fun _ hz => subset_interior_NA hc ha0
    (gy1_eq_zero_of_SIA ha ha0 hz) (gy2_eq_of_SIA ha ha0 hz)
    (gy3_pos_of_NA (Inv_subset _ hz)) (gw1_eq_one_of_SIA hz))
    fun _ hx _ ht => NA_fwd hc ha ha0 hx ht

/-- An orbit whose `α`-limit set meets `Σ_I(A)` lies in `Σ_I(A)`. -/
theorem mem_SIA_of_alphaLim {x : OmG} (hx : (alphaLim (ϕG c) x ∩ SIA c a).Nonempty) :
    x ∈ SIA c a := by
  obtain ⟨T, hT⟩ := eventually_atBot.1 ((isConvexNbhd_NA hc ha ha0).eventually_of_meets_alpha hx)
  intro t
  rcases le_total t T with h | h
  · exact hT t h
  · have := NA_fwd hc ha ha0 (hT T le_rfl) (sub_nonneg.2 h)
    rwa [← Flow.map_add, sub_add_cancel] at this

omit ha in
/-- A fixed point `A` with `T = 0`, `π̄ = a`, `τ = 1` lies in `Σ_I(A)`. -/
theorem mem_SIA_of_fixed {e : OmG} (he : ∀ t, ϕG c t e = e) (h1 : gy1 e = 0)
    (h2 : gy2 e = a * gy3 e) (h3 : 0 < gy3 e) (hw : gw1 e = 1) : e ∈ SIA c a := fun t => by
  rw [he]; exact interior_subset (subset_interior_NA hc ha0 h1 h2 h3 hw)

end Hyp

end ConleyCheck.Gubser
