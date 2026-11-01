import ConleyCheck.Gubser.Infinity
import ConleyCheck.ODE.Fence

/-!
# Lemma `lem:TC`: the invariant set of the blocks `N^±`

`inv_TC`: a solution `(u, v, τ)` of `eq:flowTp`, with `dτ/ds = v (1 - τ²)`, that stays for all
time in `{|u| ≤ δ, 0 ≤ v ≤ δ', |τ| ≤ 1}` has `u = v = 0`. This is the curve-level content of
`Inv(N^±) = TC^±`, and it applies equally to the doubled base `θ ∈ S¹` (with `τ = cos θ`) and to the
interval `τ ∈ [-1, 1]`.

The proof follows the paper. A positive `v` stays positive. Off the cone `P = {|u| ≤ v}` the
quantity `u²` decays at rate `1/c`, and `P` is forward invariant, so a full orbit lies in `P`. In
`P`, `dv/ds` has the sign of `τ` and `τ` is nondecreasing. In the fibers `τ = ±1` the quantity
`1/v` moves at rate at least `1/3`. Otherwise `Ψ = v⁶ (1 - τ²)` is monotone with derivative
`2 v⁶ (1 - τ²) τ (v - u)`, which bounds `dτ/ds = Ψ / v⁵` below by a positive constant. This replaces
the integration of `d ln v/dτ` in the paper. Finally on `v = 0`, `u²` decays at a fixed rate.
-/

open Set Filter Topology Real

namespace ConleyCheck.Gubser

open ConleyCheck.ODE

variable {c δ δ' : ℝ} {u v τ : ℝ → ℝ}

theorem hasDerivAt_sq_fun {f : ℝ → ℝ} {f' s : ℝ} (h : HasDerivAt f f' s) :
    HasDerivAt (fun r => f r ^ 2) (2 * f s * f') s := by
  have := h.mul h
  simp only [← sq] at this
  exact this.congr_deriv (by ring)

section Inv

variable (H : TCHyp c δ δ')
  (hu : ∀ s, HasDerivAt u (Fu c (u s) (v s) (τ s)) s)
  (hv : ∀ s, HasDerivAt v (Fv (u s) (v s) (τ s)) s)
  (hτ : ∀ s, HasDerivAt τ (v s * (1 - τ s ^ 2)) s)
  (hτ1 : ∀ s, -1 ≤ τ s) (hτ2 : ∀ s, τ s ≤ 1)
  (hub : ∀ s, |u s| ≤ δ) (hv0 : ∀ s, 0 ≤ v s) (hvb : ∀ s, v s ≤ δ')

include hu hv hτ in
theorem continuous_uvτ : Continuous u ∧ Continuous v ∧ Continuous τ :=
  ⟨continuous_iff_continuousAt.2 fun s => (hu s).continuousAt,
    continuous_iff_continuousAt.2 fun s => (hv s).continuousAt,
    continuous_iff_continuousAt.2 fun s => (hτ s).continuousAt⟩

include H hu hτ1 hτ2 hub in
/-- On `v = 0` the only full orbit in `|u| ≤ δ` is `u = 0`. -/
theorem u_zero_of_v_zero (hvz : ∀ s, v s = 0) (s₀ : ℝ) : u s₀ = 0 := by
  by_contra hne
  have hc := H.hc
  have hδc : 5 / 3 * δ < 1 / c := by
    have := H.delta_lt
    have e : 3 / (5 * c) = 3 / 5 * (1 / c) := by field_simp
    rw [e] at this; linarith
  refine exp_growth_bwd (g := fun s => u s ^ 2) (g' := fun s => 2 * u s * Fu c (u s) (v s) (τ s))
    (s₀ := s₀) (κ := 2 * (1 / c - 5 / 3 * δ)) (M := δ ^ 2)
    (fun s _ => hasDerivAt_sq_fun (hu s)) (by linarith)
    (fun s _ => ?_) (by positivity) (fun s _ => ?_)
  · simp only [hvz s, (circle_at_infinity c (u s) (τ s)).1]
    have h1 : |u s * τ s| ≤ δ := by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (abs_le.2 ⟨hτ1 s, hτ2 s⟩)).trans (hub s)
    have h2 : -δ ≤ u s * τ s := (abs_le.1 h1).1
    nlinarith [mul_nonneg (sq_nonneg (u s)) (by linarith : 0 ≤ u s * τ s + δ)]
  · have := sq_abs (u s) ▸ pow_le_pow_left₀ (abs_nonneg _) (hub s) 2
    linarith

include hv hu hτ in
/-- A positive `v` stays positive, since `dv/ds = (τ (2v - u)/3) v`. -/
theorem v_pos_of_pos {s₀ : ℝ} (h0 : 0 < v s₀) (s : ℝ) : 0 < v s := by
  obtain ⟨cu, cv, cτ⟩ := continuous_uvτ hu hv hτ
  exact pos_of_linear_all (k := fun r => τ r * (2 * v r - u r) / 3)
    (fun r => (hv r).congr_deriv (by simp only [Fv]; ring)) (by fun_prop) h0 s

include H hu hv hτ1 hτ2 hub hv0 hvb in
/-- A full orbit with `v > 0` lies in the cone `P = {|u| ≤ v}`. -/
theorem mem_cone (hvp : ∀ s, 0 < v s) (s₀ : ℝ) : |u s₀| ≤ v s₀ := by
  have hc := H.hc
  -- the two half-cones are forward invariant
  have hP : ∀ s, |u s| ≤ v s → ∀ s', s ≤ s' → |u s'| ≤ v s' := by
    intro s hs s' hss'
    have h1 := nonpos_forward (g := fun r => u r - v r)
      (g' := fun r => Fu c (u r) (v r) (τ r) - Fv (u r) (v r) (τ r)) (fun r => (hu r).sub (hv r))
      hss' (by linarith [(abs_le.1 hs).2]) fun r _ hr => by
        rw [show u r = v r by linarith]
        exact (cone_faces_sign hc (hvp r) (hvb r) H.h2 (hτ1 r) (hτ2 r)).1
    have h2 := nonpos_forward (g := fun r => -u r - v r)
      (g' := fun r => -Fu c (u r) (v r) (τ r) - Fv (u r) (v r) (τ r))
      (fun r => (hu r).neg.sub (hv r)) hss' (by linarith [(abs_le.1 hs).1]) fun r _ hr => by
        rw [show u r = -v r by linarith]
        linarith [(cone_faces_sign hc (hvp r) (hvb r) H.h2 (hτ1 r) (hτ2 r)).2]
    exact abs_le.2 ⟨by linarith, by linarith⟩
  by_contra hout
  push Not at hout
  have hoff : ∀ s ≤ s₀, v s < |u s| := fun s hs => by
    by_contra h; push Not at h
    exact absurd (hP s h s₀ hs) (not_le.2 hout)
  have hu0 : 0 < u s₀ ^ 2 := by
    have : 0 < |u s₀| := (hvp s₀).trans hout
    exact sq_abs (u s₀) ▸ pow_pos this 2
  refine exp_growth_bwd (g := fun s => u s ^ 2) (g' := fun s => 2 * u s * Fu c (u s) (v s) (τ s))
    (s₀ := s₀) (κ := 1 / c) (M := δ ^ 2)
    (fun s _ => hasDerivAt_sq_fun (hu s)) (by positivity)
    (fun s hs => ?_) hu0 (fun s _ => ?_)
  · have := off_cone H (hv0 s) (hoff s hs) (hub s) (hvb s) (hτ1 s) (hτ2 s)
    have e : u s ^ 2 / (2 * c) = 1 / c * u s ^ 2 / 2 := by field_simp
    rw [e] at this
    linarith
  · have := sq_abs (u s) ▸ pow_le_pow_left₀ (abs_nonneg _) (hub s) 2
    linarith

include hτ hv0 hτ1 hτ2 in
theorem monotone_τ : Monotone τ :=
  monotone_of_deriv_nonneg (fun s => (hτ s).differentiableAt) fun s => by
    rw [(hτ s).deriv]
    exact mul_nonneg (hv0 s) (by nlinarith [hτ1 s, hτ2 s])

/-- `Ψ = v⁶ (1 - τ²)` has derivative `2 v⁶ (1 - τ²) τ (v - u)`. -/
theorem hasDerivAt_Ψ (hv : ∀ s, HasDerivAt v (Fv (u s) (v s) (τ s)) s)
    (hτ : ∀ s, HasDerivAt τ (v s * (1 - τ s ^ 2)) s) (s : ℝ) :
    HasDerivAt (fun r => v r ^ 6 * (1 - τ r ^ 2))
      (2 * v s ^ 6 * (1 - τ s ^ 2) * τ s * (v s - u s)) s := by
  have h := ((hv s).pow 6).mul (((hτ s).pow 2).const_sub 1)
  convert h using 1
  simp only [Fv, Pi.pow_apply]; push_cast; ring

include H hu hv hτ hτ1 hτ2 hub hv0 hvb in
/-- Lemma `lem:TC`, `Inv(N^±) = TC^±` at the level of solutions: a full orbit in
`{|u| ≤ δ, 0 ≤ v ≤ δ', |τ| ≤ 1}` has `u = v = 0`. -/
theorem inv_TC (s : ℝ) : u s = 0 ∧ v s = 0 := by
  have hc := H.hc
  by_cases hvz : ∀ s, v s = 0
  · exact ⟨u_zero_of_v_zero H hu hτ1 hτ2 hub hvz s, hvz s⟩
  exfalso
  push Not at hvz
  obtain ⟨s₀, hs₀⟩ := hvz
  have hvp : ∀ s, 0 < v s := v_pos_of_pos hu hv hτ (lt_of_le_of_ne (hv0 s₀) (Ne.symm hs₀))
  have hP := mem_cone H hu hv hτ1 hτ2 hub hv0 hvb hvp
  have hmono := monotone_τ hτ hτ1 hτ2 hv0
  -- `g = -1/v` has derivative `Fv / v²`
  have hg : ∀ s, HasDerivAt (fun r => -(1 / v r)) (Fv (u s) (v s) (τ s) / v s ^ 2) s := fun s => by
    have := ((hasDerivAt_const s (1 : ℝ)).div (hv s) (hvp s).ne').neg
    convert this using 1; ring
  have hgM : ∀ s, -(1 / v s) ≤ 0 := fun s => by
    have := one_div_pos.2 (hvp s); linarith
  by_cases h1 : ∃ s₁, τ s₁ = 1
  · -- the fiber `τ = 1`: `1/v` decreases at rate `1/3`
    obtain ⟨s₁, hs₁⟩ := h1
    refine no_growth_fwd hg (t₀ := s₁) (c := 1 / 3) (M := 0) (by norm_num) (fun s hs _ => ?_) hgM
    have hτs : τ s = 1 := le_antisymm (hτ2 s) (hs₁ ▸ hmono hs)
    have := (in_cone (hvp s) (hP s)).2.2.1
    rw [hτs]
    rw [neg_div] at this
    linarith
  by_cases h2 : ∃ s₁, τ s₁ = -1
  · obtain ⟨s₁, hs₁⟩ := h2
    refine no_growth_bwd hg (t₀ := s₁) (c := 1 / 3) (M := 0) (by norm_num) (fun s hs _ => ?_) hgM
    have hτs : τ s = -1 := le_antisymm (hs₁ ▸ hmono hs) (hτ1 s)
    have := (in_cone (hvp s) (hP s)).2.2.2
    rw [hτs]
    rw [neg_div] at this
    linarith
  push Not at h1 h2
  have hτs : ∀ s, τ s ^ 2 < 1 := fun s => by
    have a1 := lt_of_le_of_ne (hτ1 s) (Ne.symm (h2 s))
    have a2 := lt_of_le_of_ne (hτ2 s) (h1 s)
    nlinarith
  have hΨ := hasDerivAt_Ψ (u := u) hv hτ
  -- `τ' = Ψ / v⁵ ≥ C / δ'⁵` wherever `Ψ ≥ C`
  have hδ' := H.hδ'
  have hrate : ∀ C, 0 < C → ∀ s, C ≤ v s ^ 6 * (1 - τ s ^ 2) →
      C / δ' ^ 5 ≤ v s * (1 - τ s ^ 2) := fun C hC s hs => by
    have hv5 : v s ^ 5 ≤ δ' ^ 5 := pow_le_pow_left₀ (hv0 s) (hvb s) 5
    have hv5p : 0 < v s ^ 5 := pow_pos (hvp s) 5
    rw [div_le_iff₀ (by positivity)]
    calc C ≤ v s ^ 6 * (1 - τ s ^ 2) := hs
      _ = v s * (1 - τ s ^ 2) * v s ^ 5 := by ring
      _ ≤ v s * (1 - τ s ^ 2) * δ' ^ 5 :=
          mul_le_mul_of_nonneg_left hv5 (mul_nonneg (hv0 s) (by linarith [hτs s]))
  have hCpos : ∀ s, 0 < v s ^ 6 * (1 - τ s ^ 2) := fun s =>
    mul_pos (pow_pos (hvp s) 6) (by linarith [hτs s])
  by_cases h3 : ∃ s₁, 0 ≤ τ s₁
  · obtain ⟨s₁, hs₁⟩ := h3
    have hmonoΨ : MonotoneOn (fun r => v r ^ 6 * (1 - τ r ^ 2)) (Ici s₁) :=
      monotoneOn_of_deriv_nonneg (convex_Ici s₁)
        (fun r _ => (hΨ r).continuousAt.continuousWithinAt)
        (fun r _ => (hΨ r).differentiableAt.differentiableWithinAt) fun r hr => by
          rw [interior_Ici] at hr
          rw [(hΨ r).deriv]
          have hτr : 0 ≤ τ r := hs₁.trans (hmono (le_of_lt hr))
          have := (abs_le.1 (hP r)).2
          exact mul_nonneg (mul_nonneg (le_of_lt (mul_pos (mul_pos two_pos (pow_pos (hvp r) 6))
            (by linarith [hτs r]))) hτr) (by linarith)
    set C := v s₁ ^ 6 * (1 - τ s₁ ^ 2)
    refine no_growth_fwd hτ (t₀ := s₁) (c := C / δ' ^ 5) (M := 1) (by positivity [hCpos s₁])
      (fun s hs _ => hrate C (hCpos s₁) s (hmonoΨ (mem_Ici.2 le_rfl) (mem_Ici.2 hs) hs)) hτ2
  · push Not at h3
    have hantiΨ : Antitone (fun r => v r ^ 6 * (1 - τ r ^ 2)) :=
      antitone_of_deriv_nonpos (fun r => (hΨ r).differentiableAt) fun r => by
        rw [(hΨ r).deriv]
        have := (abs_le.1 (hP r)).2
        have hpos : 0 < 2 * v r ^ 6 * (1 - τ r ^ 2) :=
          mul_pos (mul_pos two_pos (pow_pos (hvp r) 6)) (by linarith [hτs r])
        nlinarith [mul_neg_of_pos_of_neg hpos (h3 r)]
    set C := v 0 ^ 6 * (1 - τ 0 ^ 2)
    refine no_growth_bwd (g := fun s => -τ s) (g' := fun s => -(v s * (1 - τ s ^ 2)))
      (fun s => (hτ s).neg) (t₀ := 0) (c := C / δ' ^ 5) (M := 1) (by positivity [hCpos 0])
      (fun s hs _ => ?_) fun s => by linarith [hτ1 s]
    have := hrate C (hCpos 0) s (hantiΨ hs)
    linarith

end Inv

end ConleyCheck.Gubser
