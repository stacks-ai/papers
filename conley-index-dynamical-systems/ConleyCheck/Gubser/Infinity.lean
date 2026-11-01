import ConleyCheck.Gubser.Basic

/-!
# The compactified Gubser flow (section `sec:full3d`)

* The charts `eq:flowTp`, `eq:flowTm` near `T = ±∞` and the chart near `π̄ = +∞`, as
  derivative identities along solutions (`d/dρ = |T| d/ds`, resp. `π̄ d/ds`).
* The equilibria at infinity, their linearizations and the center manifold of the `T`-axis
  curves.
* The polar form `eq:polar` and the barrier planes, Lemma `lem:barrier`.
* All inequalities in the proof of Lemma `lem:TC`, and the existence of `δ`.
* The face, tangency, membership and no-return inequalities in the proof of Theorem `thm:M`.
-/

namespace ConleyCheck.Gubser

/-! ## Charts at infinity -/

/-- `du/ds` in the chart `u = π̄/T`, `v = 1/T`, eq. `eq:flowTp`. -/
noncomputable def Fu (c u v τ : ℝ) : ℝ :=
  -(u / c) - 5 / 3 * u ^ 2 * τ + 4 / 15 * v ^ 2 * τ + 2 / 3 * u * v * τ
/-- `dv/ds` in the chart `eq:flowTp`. -/
noncomputable def Fv (u v τ : ℝ) : ℝ := v * τ / 3 * (2 * v - u)

/-- `du/ds` in the chart `u = π̄/T`, `v̂ = 1/|T|` near `T = -∞`, eq. `eq:flowTm`. -/
noncomputable def Gu (c u v τ : ℝ) : ℝ :=
  u / c + 5 / 3 * u ^ 2 * τ - 4 / 15 * v ^ 2 * τ + 2 / 3 * u * v * τ
/-- `dv̂/ds` in the chart `eq:flowTm`. -/
noncomputable def Gv (u v τ : ℝ) : ℝ := v * τ / 3 * (u + 2 * v)

section Charts
variable {c : ℝ} {T π τ : ℝ → ℝ} {ρ : ℝ}

/-- The chart `eq:flowTp`, for `T > 0`, with `ds = T dρ`. -/
theorem chart_Tplus (hc : c ≠ 0) (hT : HasDerivAt T (βT (T ρ) (π ρ) (τ ρ)) ρ)
    (hπ : HasDerivAt π (βπ c (T ρ) (π ρ) (τ ρ)) ρ) (hτ : HasDerivAt τ (βτ (τ ρ)) ρ)
    (hT0 : T ρ ≠ 0) :
    HasDerivAt (fun r => π r / T r) (T ρ * Fu c (π ρ / T ρ) (1 / T ρ) (τ ρ)) ρ ∧
    HasDerivAt (fun r => 1 / T r) (T ρ * Fv (π ρ / T ρ) (1 / T ρ) (τ ρ)) ρ ∧
    HasDerivAt τ (T ρ * ((1 / T ρ) * (1 - τ ρ ^ 2))) ρ := by
  refine ⟨?_, ?_, ?_⟩
  · convert hπ.div hT hT0 using 1
    simp only [Fu, βT, βπ]; field_simp; ring
  · convert (hasDerivAt_const ρ (1 : ℝ)).div hT hT0 using 1
    simp only [Fv, βT]; field_simp; ring
  · convert hτ using 1
    simp only [βτ]; field_simp

/-- The chart `eq:flowTm`, for `T < 0`, with `ds = -T dρ` and `v̂ = -1/T`. -/
theorem chart_Tminus (hc : c ≠ 0) (hT : HasDerivAt T (βT (T ρ) (π ρ) (τ ρ)) ρ)
    (hπ : HasDerivAt π (βπ c (T ρ) (π ρ) (τ ρ)) ρ) (hτ : HasDerivAt τ (βτ (τ ρ)) ρ)
    (hT0 : T ρ ≠ 0) :
    HasDerivAt (fun r => π r / T r) (-T ρ * Gu c (π ρ / T ρ) (-1 / T ρ) (τ ρ)) ρ ∧
    HasDerivAt (fun r => -1 / T r) (-T ρ * Gv (π ρ / T ρ) (-1 / T ρ) (τ ρ)) ρ ∧
    HasDerivAt τ (-T ρ * ((-1 / T ρ) * (1 - τ ρ ^ 2))) ρ := by
  refine ⟨?_, ?_, ?_⟩
  · convert hπ.div hT hT0 using 1
    simp only [Gu, βT, βπ]; field_simp; ring
  · convert (hasDerivAt_const ρ (-1 : ℝ)).div hT hT0 using 1
    simp only [Gv, βT]; field_simp; ring
  · convert hτ using 1
    simp only [βτ]; field_simp

/-- The chart near `P⁺`: `w = T/π̄`, `z = 1/π̄`, `ds = π̄ dρ`. -/
noncomputable def Fw (a c w z τ : ℝ) : ℝ :=
  w * (5 / 3 * τ - 2 / 3 * z * τ - 4 / 3 * a ^ 2 * z ^ 2 * τ + w / c)
noncomputable def Fz (a c w z τ : ℝ) : ℝ := z * (4 / 3 * (1 - a ^ 2 * z ^ 2) * τ + w / c)

theorem chart_Pplus {a : ℝ} (ha : a ^ 2 = 1 / 5) (hc : c ≠ 0)
    (hT : HasDerivAt T (βT (T ρ) (π ρ) (τ ρ)) ρ)
    (hπ : HasDerivAt π (βπ c (T ρ) (π ρ) (τ ρ)) ρ) (hπ0 : π ρ ≠ 0) :
    HasDerivAt (fun r => T r / π r) (π ρ * Fw a c (T ρ / π ρ) (1 / π ρ) (τ ρ)) ρ ∧
    HasDerivAt (fun r => 1 / π r) (π ρ * Fz a c (T ρ / π ρ) (1 / π ρ) (τ ρ)) ρ := by
  constructor
  · convert hT.div hπ hπ0 using 1
    simp only [Fw, βT, βπ]; rw [ha]; field_simp; ring
  · convert (hasDerivAt_const ρ (1 : ℝ)).div hπ hπ0 using 1
    simp only [Fz, βπ]; rw [ha]; field_simp; ring

end Charts

/-! ## Equilibria at infinity (Lemma `lem:barrier`(i)) -/

/-- On the circle at infinity `v = 0`, `du/ds = -u (1/c + 5/3 u τ)`; the frozen base. -/
theorem circle_at_infinity (c u τ : ℝ) :
    Fu c u 0 τ = -u * (1 / c + 5 / 3 * u * τ) ∧ Fv u 0 τ = 0 := by
  constructor <;> simp only [Fu, Fv] <;> ring

/-- The diagonal point `u_* = -3/(5cτ)`. -/
noncomputable def ustar (c τ : ℝ) : ℝ := -3 / (5 * c * τ)

theorem Fu_ustar {c τ : ℝ} (hc : c ≠ 0) (hτ : τ ≠ 0) : Fu c (ustar c τ) 0 τ = 0 := by
  simp only [Fu, ustar]; field_simp; ring

/-- `TC^±`: the linearization in `(u, v)` at `u = v = 0` has eigenvalues `-1/c` and `0`. -/
theorem lin_TC (c τ : ℝ) :
    HasDerivAt (fun u => Fu c u 0 τ) (-(1 / c)) 0 ∧ HasDerivAt (fun v => Fu c 0 v τ) 0 0 ∧
    HasDerivAt (fun u => Fv u 0 τ) 0 0 ∧ HasDerivAt (fun v => Fv 0 v τ) 0 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hasDerivAt_of_cubic 0 (-(5 / 3 * τ)) (-(1 / c)) 0 0 _
      (fun y => by simp only [Fu]; ring) (by ring)
  · exact hasDerivAt_of_cubic 0 (4 / 15 * τ) 0 0 0 _ (fun y => by simp only [Fu]; ring) (by ring)
  · exact hasDerivAt_of_cubic 0 0 0 0 0 _ (fun y => by simp only [Fv]; ring) (by ring)
  · exact hasDerivAt_of_cubic 0 (2 * τ / 3) 0 0 0 _ (fun y => by simp only [Fv]; ring) (by ring)

/-- `D⁺`: at `(u_*, 0)` the derivatives are `1/c` and `1/(5c)` (and `∂Fv/∂u = 0`), a source. -/
theorem lin_Dplus {c τ : ℝ} (hc : c ≠ 0) (hτ : τ ≠ 0) :
    HasDerivAt (fun u => Fu c u 0 τ) (1 / c) (ustar c τ) ∧
    HasDerivAt (fun v => Fv (ustar c τ) v τ) (1 / (5 * c)) 0 ∧
    HasDerivAt (fun u => Fv u 0 τ) 0 (ustar c τ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hasDerivAt_of_cubic 0 (-(5 / 3 * τ)) (-(1 / c)) 0 _ _
      (fun y => by simp only [Fu]; ring) (by simp only [ustar]; field_simp; ring)
  · exact hasDerivAt_of_cubic 0 (2 * τ / 3) (-(ustar c τ * τ / 3)) 0 0 _
      (fun y => by simp only [Fv]; ring) (by simp only [ustar]; field_simp; ring)
  · exact hasDerivAt_of_cubic 0 0 0 0 _ _ (fun y => by simp only [Fv]; ring) (by ring)

/-- `P⁺` has eigenvalues `5τ/3` and `4τ/3`, with vanishing off-diagonal entries. -/
theorem lin_Pplus (a c τ : ℝ) :
    HasDerivAt (fun w => Fw a c w 0 τ) (5 / 3 * τ) 0 ∧
    HasDerivAt (fun z => Fz a c 0 z τ) (4 / 3 * τ) 0 ∧
    HasDerivAt (fun z => Fw a c 0 z τ) 0 0 ∧ HasDerivAt (fun w => Fz a c w 0 τ) 0 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hasDerivAt_of_cubic 0 (1 / c) (5 / 3 * τ) 0 0 _ (fun y => by simp only [Fw]; ring)
      (by ring)
  · exact hasDerivAt_of_cubic (-(4 / 3 * a ^ 2 * τ)) 0 (4 / 3 * τ) 0 0 _
      (fun y => by simp only [Fz]; ring) (by ring)
  · exact hasDerivAt_of_cubic 0 0 0 0 0 _ (fun y => by simp only [Fw]; ring) (by ring)
  · exact hasDerivAt_of_cubic 0 0 0 0 0 _ (fun y => by simp only [Fz]; ring) (by ring)

/-- Center manifold of the `T`-axis curves: `u = (4cτ/15) v²` is invariant up to `O(v³)`, and the
reduced radial flow is `dv/ds = (2τ/3) v² + O(v³)`. -/
theorem center_manifold {c : ℝ} (hc : c ≠ 0) (τ v : ℝ) :
    Fu c (4 * c * τ / 15 * v ^ 2) v τ - 2 * (4 * c * τ / 15) * v * Fv (4 * c * τ / 15 * v ^ 2) v τ
      = v ^ 3 * (-(16 * c ^ 2 * τ ^ 3 * v / 225) - 8 * c * τ ^ 2 / 45) ∧
    Fv (4 * c * τ / 15 * v ^ 2) v τ = 2 * τ / 3 * v ^ 2 + v ^ 3 * (-(4 * c * τ ^ 2 / 45)) := by
  constructor
  · simp only [Fu, Fv]; field_simp; ring
  · simp only [Fv]; ring

/-! ## Lemma `lem:barrier`(ii), (iii) -/

/-- `r² φ̇ = T π̇ - π Ṫ` for the quadratic part equals `-r³ sin φ cos φ (cos φ/c + 5/3 τ sin φ)`. -/
theorem polar (c r φ τ : ℝ) :
    (r * Real.cos φ) * (-(4 / 3) * τ * (r * Real.sin φ) ^ 2 - r * Real.cos φ * (r * Real.sin φ) / c)
      - (r * Real.sin φ) * ((r * Real.cos φ) * (r * Real.sin φ) * τ / 3) =
    -(r ^ 3 * Real.sin φ * Real.cos φ * (1 / c * Real.cos φ + 5 / 3 * τ * Real.sin φ)) := by
  ring

/-- The diagonal directions are the zeros of `cos φ/c + 5/3 τ sin φ`, i.e. `tan φ = u_*`. -/
theorem polar_diagonal {c τ φ : ℝ} (hc : c ≠ 0) (hτ : τ ≠ 0) (hφ : Real.cos φ ≠ 0) :
    1 / c * Real.cos φ + 5 / 3 * τ * Real.sin φ = 0 ↔ Real.sin φ / Real.cos φ = ustar c τ := by
  have h5 : 5 * c * τ ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hc) hτ
  have h3c : 3 * c ≠ 0 := mul_ne_zero (by norm_num) hc
  have e : 3 * c * (1 / c * Real.cos φ + 5 / 3 * τ * Real.sin φ) =
      3 * Real.cos φ + 5 * c * τ * Real.sin φ := by field_simp
  simp only [ustar]
  rw [div_eq_div_iff hφ h5]
  constructor
  · intro h; rw [h, mul_zero] at e; linarith
  · intro h
    have : 3 * c * (1 / c * Real.cos φ + 5 / 3 * τ * Real.sin φ) = 0 := by rw [e]; linarith
    exact (mul_eq_zero.1 this).resolve_left h3c

/-- Lemma `lem:barrier`(iii): on `π̄ = ∓a`, `dπ̄/dρ = ±aT/c`. -/
theorem barrier_planes {a : ℝ} (ha : a ^ 2 = 1 / 5) (c T τ : ℝ) :
    βπ c T (-a) τ = a * T / c ∧ βπ c T a τ = -(a * T / c) := by
  constructor
  · simp only [βπ]; rw [show (-a) ^ 2 = a ^ 2 by ring, ha]; ring
  · simp only [βπ]; rw [ha]; ring

/-! ## Lemma `lem:TC` -/

/-- The smallness conditions on `δ` in the proof of Lemma `lem:TC`. -/
structure TCHyp (c δ δ' : ℝ) : Prop where
  hc : 0 < c
  hδ : 0 < δ
  hδ' : 0 < δ'
  hsq : δ' ^ 2 = δ / (4 * c)
  h1 : δ < δ'
  h2 : δ' < 15 / (16 * c)
  h3 : 5 / 3 * δ + 14 / 15 * δ' < 1 / (2 * c)

namespace TCHyp
variable {c δ δ' : ℝ} (H : TCHyp c δ δ')
include H

theorem inv_pos' : 0 < c⁻¹ := inv_pos.2 H.hc

theorem delta_lt : δ < 3 / (5 * c) := by
  have h3 := H.h3
  have hc := H.hc
  have hX : 0 < 1 / (2 * c) := by positivity
  have e : 3 / (5 * c) = 6 / 5 * (1 / (2 * c)) := by field_simp; ring
  rw [e]; nlinarith [H.hδ']

/-- Strict entrance on the faces `u = ±δ`. -/
theorem face_entrance {v τ : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ δ') (hτ1 : -1 ≤ τ) (hτ2 : τ ≤ 1) :
    Fu c δ v τ < 0 ∧ 0 < Fu c (-δ) v τ := by
  have hk := H.inv_pos'
  have hsq := H.hsq
  have hδ := H.hδ
  have hc := H.hc
  have e : δ / (4 * c) = δ * c⁻¹ / 4 := by field_simp
  rw [e] at hsq
  have hv2 : v ^ 2 ≤ δ' ^ 2 := by nlinarith
  have hb1 : 5 / 3 * δ + 2 / 3 * δ' < 14 / 15 * c⁻¹ := by
    have := H.h3
    have e2 : 1 / (2 * c) = c⁻¹ / 2 := by field_simp
    rw [e2] at this; nlinarith [H.hδ']
  simp only [Fu]
  have e3 : ∀ x : ℝ, x / c = x * c⁻¹ := fun x => by ring
  rw [e3, e3]
  have hm := mul_lt_mul_of_pos_left hb1 hδ
  have hdv := mul_nonneg hδ.le (by linarith : 0 ≤ δ' - v)
  constructor
  · nlinarith [mul_nonneg (sq_nonneg v) (by linarith : (0 : ℝ) ≤ 1 - τ),
      mul_nonneg (sq_nonneg δ) (by linarith : (0 : ℝ) ≤ 1 + τ),
      mul_nonneg hδ.le (mul_nonneg hv0 (by linarith : (0 : ℝ) ≤ 1 - τ))]
  · nlinarith [mul_nonneg (sq_nonneg v) (by linarith : (0 : ℝ) ≤ 1 + τ),
      mul_nonneg (sq_nonneg δ) (by linarith : (0 : ℝ) ≤ 1 - τ),
      mul_nonneg hδ.le (mul_nonneg hv0 (by linarith : (0 : ℝ) ≤ 1 + τ))]

/-- On the top face `v = δ'`, `2δ' - u > 0`, so `dv/ds` has the sign of `τ`. -/
theorem top_face {u τ : ℝ} (hu : |u| ≤ δ) :
    0 < 2 * δ' - u ∧ Fv u δ' τ = δ' * τ / 3 * (2 * δ' - u) := by
  refine ⟨?_, rfl⟩
  have := (abs_le.1 hu).2
  linarith [H.h1, H.hδ]

end TCHyp

/-- At `τ = 0` on the top face: `d²v/ds² = (δ'/3)(2δ' - u) dτ/ds` with `dτ/ds = δ'`. -/
theorem top_face_tangency {c : ℝ} {u v τ : ℝ → ℝ} {s : ℝ}
    (hu : HasDerivAt u (Fu c (u s) (v s) (τ s)) s) (hv : HasDerivAt v (Fv (u s) (v s) (τ s)) s)
    (hτ : HasDerivAt τ (v s * (1 - τ s ^ 2)) s) (h0 : τ s = 0) :
    HasDerivAt (fun r => Fv (u r) (v r) (τ r)) (v s / 3 * (2 * v s - u s) * v s) s := by
  have h := ((hv.mul hτ).div_const 3).mul ((hv.const_mul 2).sub hu)
  convert h using 1
  · funext r; simp only [Fv, Pi.mul_apply, Pi.sub_apply]
  · simp only [Fv, Pi.mul_apply, Pi.sub_apply, h0]; ring

/-- The cone `P = {|u| ≤ v}` is forward invariant: the two boundary derivatives. -/
theorem cone_faces (c v τ : ℝ) :
    Fu c v v τ - Fv v v τ = -(v / c) - 16 / 15 * v ^ 2 * τ ∧
    Fu c (-v) v τ + Fv (-v) v τ = v / c - 16 / 15 * v ^ 2 * τ := by
  constructor <;> simp only [Fu, Fv] <;> ring

theorem cone_faces_sign {c v δ' τ : ℝ} (hc : 0 < c) (hv : 0 < v) (hvδ : v ≤ δ')
    (h2 : δ' < 15 / (16 * c)) (hτ1 : -1 ≤ τ) (hτ2 : τ ≤ 1) :
    Fu c v v τ - Fv v v τ < 0 ∧ 0 < Fu c (-v) v τ + Fv (-v) v τ := by
  obtain ⟨e1, e2⟩ := cone_faces c v τ
  rw [e1, e2]
  have hk : 0 < c⁻¹ := inv_pos.2 hc
  have hb : 16 / 15 * v < c⁻¹ := by
    have : 16 / 15 * δ' < c⁻¹ := by
      have e : 15 / (16 * c) = 15 / 16 * c⁻¹ := by field_simp
      rw [e] at h2; linarith
    linarith
  have e3 : v / c = v * c⁻¹ := by ring
  rw [e3]
  constructor
  · nlinarith [mul_nonneg (mul_nonneg hv.le hv.le) (by linarith : (0 : ℝ) ≤ 1 + τ)]
  · nlinarith [mul_nonneg (mul_nonneg hv.le hv.le) (by linarith : (0 : ℝ) ≤ 1 - τ)]

/-- Off the cone, `d ln|u|/ds = Fu/u < -1/(2c)`. -/
theorem off_cone {c δ δ' u v τ : ℝ} (H : TCHyp c δ δ') (hv0 : 0 ≤ v) (hvu : v < |u|)
    (hu : |u| ≤ δ) (hvδ : v ≤ δ') (hτ1 : -1 ≤ τ) (hτ2 : τ ≤ 1) :
    u * Fu c u v τ < -(u ^ 2 / (2 * c)) := by
  have hc := H.hc
  have hk : 0 < c⁻¹ := inv_pos.2 hc
  have h3 : 5 / 3 * δ + 14 / 15 * δ' < c⁻¹ / 2 := by
    have := H.h3; have e : 1 / (2 * c) = c⁻¹ / 2 := by field_simp
    rwa [e] at this
  have hu0 : u ≠ 0 := by intro h; rw [h, abs_zero] at hvu; linarith
  have hu2 : 0 < u ^ 2 := by positivity
  simp only [Fu]
  have e1 : u * (-(u / c) - 5 / 3 * u ^ 2 * τ + 4 / 15 * v ^ 2 * τ + 2 / 3 * u * v * τ) =
      -(u ^ 2 * c⁻¹) - 5 / 3 * (u ^ 3 * τ) + 4 / 15 * (u * τ * v ^ 2) + 2 / 3 * (u ^ 2 * v * τ) := by
    ring
  have e2 : u ^ 2 / (2 * c) = u ^ 2 * (c⁻¹ / 2) := by field_simp
  rw [e1, e2]
  -- bounds on the three cubic terms
  have b1 : -(u ^ 3 * τ) ≤ δ * u ^ 2 := by
    have : |u ^ 3 * τ| ≤ δ * u ^ 2 := by
      rw [abs_mul, abs_pow]
      have hτ : |τ| ≤ 1 := abs_le.2 ⟨hτ1, hτ2⟩
      calc |u| ^ 3 * |τ| ≤ |u| ^ 3 * 1 := mul_le_mul_of_nonneg_left hτ (by positivity)
        _ = |u| * u ^ 2 := by rw [mul_one, pow_succ, sq_abs, mul_comm]
        _ ≤ δ * u ^ 2 := mul_le_mul_of_nonneg_right hu (by positivity)
    linarith [neg_abs_le (u ^ 3 * τ)]
  have b2 : u * τ * v ^ 2 ≤ δ' * u ^ 2 := by
    have : |u * τ * v ^ 2| ≤ δ' * u ^ 2 := by
      rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hv0]
      have hτ : |τ| ≤ 1 := abs_le.2 ⟨hτ1, hτ2⟩
      calc |u| * |τ| * v ^ 2 ≤ |u| * 1 * v ^ 2 := by gcongr
        _ = |u| * v * v := by ring
        _ ≤ |u| * |u| * δ' := by
          have := mul_le_mul hvu.le hvδ hv0 (abs_nonneg u)
          nlinarith [abs_nonneg u]
        _ = δ' * u ^ 2 := by rw [← sq, sq_abs]; ring
    linarith [le_abs_self (u * τ * v ^ 2)]
  have b3 : u ^ 2 * v * τ ≤ δ' * u ^ 2 := by
    have : u ^ 2 * v * τ ≤ u ^ 2 * v := by
      have := mul_le_mul_of_nonneg_left hτ2 (mul_nonneg hu2.le hv0); linarith
    nlinarith
  nlinarith

/-- In the cone `P`, `2v - u ∈ [v, 3v]`, and `d(1/v)/ds = -(2v - u)/(3v)` in the fiber `τ = 1`. -/
theorem in_cone {u v : ℝ} (hv : 0 < v) (hu : |u| ≤ v) :
    v ≤ 2 * v - u ∧ 2 * v - u ≤ 3 * v ∧ -Fv u v 1 / v ^ 2 ≤ -(1 / 3) ∧
      1 / 3 ≤ -Fv u v (-1) / v ^ 2 := by
  obtain ⟨h1, h2⟩ := abs_le.1 hu
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · simp only [Fv]
    rw [div_le_iff₀ (by positivity)]; nlinarith
  · simp only [Fv]
    rw [le_div_iff₀ (by positivity)]; nlinarith

/-- Outside the cone, in the fiber `τ = 1`, `d ln v/ds ≥ -|u|/3`. -/
theorem lnv_lower {u v : ℝ} (hv : 0 < v) : -|u| / 3 ≤ Fv u v 1 / v := by
  simp only [Fv]
  rw [le_div_iff₀ hv]
  nlinarith [mul_nonneg hv.le (by linarith [le_abs_self u, hv] : 0 ≤ 2 * v - u + |u|)]

/-- `d ln v/dτ = τ (2v - u) / (3v (1 - τ²))` and its bounds in `P`. -/
theorem dlnv_dtau {u v τ : ℝ} (hv : 0 < v) (hτ : τ ^ 2 < 1) (hu : |u| ≤ v) :
    Fv u v τ / v / (v * (1 - τ ^ 2)) = τ * (2 * v - u) / (3 * v * (1 - τ ^ 2)) ∧
    |τ * (2 * v - u) / (3 * v * (1 - τ ^ 2))| ≤ |τ| / (1 - τ ^ 2) ∧
    (0 ≤ τ → τ / (3 * (1 - τ ^ 2)) ≤ τ * (2 * v - u) / (3 * v * (1 - τ ^ 2))) := by
  have h1τ : 0 < 1 - τ ^ 2 := by linarith
  obtain ⟨hu1, hu2⟩ := abs_le.1 hu
  refine ⟨?_, ?_, ?_⟩
  · simp only [Fv]; field_simp
  · rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < 3 * v * (1 - τ ^ 2)),
      abs_of_nonneg (by linarith : 0 ≤ 2 * v - u), div_le_div_iff₀ (by positivity) h1τ]
    have : (2 * v - u) ≤ 3 * v := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg (abs_nonneg τ) h1τ.le)]
  · intro hτ0
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : v ≤ 2 * v - u := by linarith
    nlinarith [mul_nonneg hτ0 h1τ.le]

/-- An antiderivative of the lower bound: `d/dτ (-(1/6) ln(1-τ²)) = τ/(3(1-τ²))`. -/
theorem lnv_antiderivative {τ : ℝ} (hτ : τ ^ 2 < 1) :
    HasDerivAt (fun t => -(1 / 6) * Real.log (1 - t ^ 2)) (τ / (3 * (1 - τ ^ 2))) τ := by
  have h1τ : 1 - τ ^ 2 ≠ 0 := by linarith
  have h := (((hasDerivAt_pow 2 τ).const_sub 1).log h1τ).const_mul (-(1 / 6) : ℝ)
  convert h using 1
  field_simp; ring

/-- On `v = 0`, `|u|` strictly decreases when `0 < |u| ≤ δ < 3/(5c)`. -/
theorem v_zero_decay {c δ u τ : ℝ} (hc : 0 < c) (hu : |u| ≤ δ) (hδ : δ < 3 / (5 * c))
    (hτ1 : -1 ≤ τ) (hτ2 : τ ≤ 1) (hu0 : u ≠ 0) : u * Fu c u 0 τ < 0 := by
  rw [(circle_at_infinity c u τ).1]
  have hk : 0 < c⁻¹ := inv_pos.2 hc
  have hδ' : 5 / 3 * δ < c⁻¹ := by
    have e : 3 / (5 * c) = 3 / 5 * c⁻¹ := by field_simp
    rw [e] at hδ; linarith
  have hpos : 0 < 1 / c + 5 / 3 * u * τ := by
    have : |u * τ| ≤ δ := by
      rw [abs_mul]
      calc |u| * |τ| ≤ δ * 1 :=
            mul_le_mul hu (abs_le.2 ⟨hτ1, hτ2⟩) (abs_nonneg _) (le_trans (abs_nonneg u) hu)
        _ = δ := mul_one δ
    have := neg_abs_le (u * τ)
    rw [one_div]; nlinarith
  have hu2 : 0 < u ^ 2 := by positivity
  nlinarith [mul_pos hu2 hpos]

/-- For every `c > 0` there is `δ₀ > 0` such that every `δ ∈ (0, δ₀)` satisfies the conditions of
Lemma `lem:TC` with `δ' = √(δ/(4c))`. -/
theorem exists_delta {c : ℝ} (hc : 0 < c) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ → TCHyp c δ (Real.sqrt (δ / (4 * c))) := by
  refine ⟨3 / (20 * c), by positivity, fun δ hδ hδ0 => ?_⟩
  have h4c : 0 < 4 * c := by positivity
  have hq : 0 < δ / (4 * c) := by positivity
  have hsq : Real.sqrt (δ / (4 * c)) ^ 2 = δ / (4 * c) := Real.sq_sqrt hq.le
  have hk : δ * c < 3 / 20 := by
    have := (lt_div_iff₀ (by positivity : 0 < 20 * c)).1 hδ0; nlinarith
  refine ⟨hc, hδ, Real.sqrt_pos.2 hq, hsq, ?_, ?_, ?_⟩
  · rw [Real.lt_sqrt hδ.le, lt_div_iff₀ h4c]; nlinarith
  · rw [Real.sqrt_lt' (by positivity), div_pow, div_lt_div_iff₀ h4c (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hk hc]
  · -- `14/15 δ' < 1/(4c)` and `5/3 δ < 1/(4c)`
    have h1 : Real.sqrt (δ / (4 * c)) < 15 / (56 * c) := by
      rw [Real.sqrt_lt' (by positivity), div_pow, div_lt_div_iff₀ h4c (by positivity)]
      nlinarith [mul_lt_mul_of_pos_left hk hc]
    have h2 : 5 / 3 * δ < 1 / (4 * c) := by
      rw [lt_div_iff₀ h4c]; nlinarith
    have e1 : 14 / 15 * (15 / (56 * c)) = 1 / (4 * c) := by field_simp; ring
    have e2 : 1 / (4 * c) + 1 / (4 * c) = 1 / (2 * c) := by field_simp; ring
    linarith

/-! ## Theorem `thm:M` -/

section ThmM
variable {a c η : ℝ}

/-- `k_∓ = 4cη(2a ∓ η)/(3(a ∓ η))`. -/
noncomputable def kminus (a c η : ℝ) : ℝ := 4 * c * η * (2 * a - η) / (3 * (a - η))
noncomputable def kplus (a c η : ℝ) : ℝ := 4 * c * η * (2 * a + η) / (3 * (a + η))

/-- eq. `eq:Piminus`: on `Π⁻ ⊂ {π̄ = -a + η}`. -/
theorem Piminus (ha : a ^ 2 = 1 / 5) (T τ : ℝ) :
    βπ c T (-a + η) τ = 4 / 3 * η * (2 * a - η) * τ + (a - η) / c * T := by
  simp only [βπ]; rw [show (-a + η) ^ 2 = a ^ 2 - 2 * a * η + η ^ 2 by ring, ha]; ring

theorem Piplus (ha : a ^ 2 = 1 / 5) (T τ : ℝ) :
    βπ c T (a + η) τ = -(4 / 3) * η * (2 * a + η) * τ - (a + η) / c * T := by
  simp only [βπ]; rw [show (a + η) ^ 2 = a ^ 2 + 2 * a * η + η ^ 2 by ring, ha]; ring

theorem Piminus_zero (ha : a ^ 2 = 1 / 5) (hc : c ≠ 0) (haη : a - η ≠ 0) (τ : ℝ) :
    βπ c (-(kminus a c η * τ)) (-a + η) τ = 0 := by
  rw [Piminus ha]; simp only [kminus]; field_simp; ring

theorem Piplus_zero (ha : a ^ 2 = 1 / 5) (hc : c ≠ 0) (haη : a + η ≠ 0) (τ : ℝ) :
    βπ c (-(kplus a c η * τ)) (a + η) τ = 0 := by
  rw [Piplus ha]; simp only [kplus]; field_simp; ring

/-- The derivative of `βπ` along the flow (chain rule), used for the tangency computations. -/
theorem hasDerivAt_βπ_along {T π τ : ℝ → ℝ} {ρ : ℝ}
    (hT : HasDerivAt T (βT (T ρ) (π ρ) (τ ρ)) ρ)
    (hπ : HasDerivAt π (βπ c (T ρ) (π ρ) (τ ρ)) ρ) (hτ : HasDerivAt τ (βτ (τ ρ)) ρ) :
    HasDerivAt (fun r => βπ c (T r) (π r) (τ r))
      (J c (T ρ) (π ρ) (τ ρ) 1 0 * βT (T ρ) (π ρ) (τ ρ) +
        J c (T ρ) (π ρ) (τ ρ) 1 1 * βπ c (T ρ) (π ρ) (τ ρ) +
        J c (T ρ) (π ρ) (τ ρ) 1 2 * βτ (τ ρ)) ρ := by
  have h := ((((hπ.pow 2).sub_const (1 / 5 : ℝ)).const_mul (-(4 / 3) : ℝ)).mul hτ).sub
    ((hT.mul hπ).div_const c)
  convert h using 1
  · funext r; simp only [βπ, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply]
  · rw [show J c (T ρ) (π ρ) (τ ρ) 1 0 = -(π ρ / c) from rfl,
      show J c (T ρ) (π ρ) (τ ρ) 1 1 = -(8 * π ρ * τ ρ / 3) - T ρ / c from rfl,
      show J c (T ρ) (π ρ) (τ ρ) 1 2 = -(4 / 3) * (π ρ ^ 2 - 1 / 5) from rfl]
    simp only [βπ, βT, βτ, Pi.pow_apply]; push_cast; ring

/-- At a tangency point of `Π⁻` (`π̄ = -a+η`, `T = -k₋ τ`, so `dπ̄/dρ = 0`),
`d²π̄/dρ² = 4/3 η(2a-η)(1-τ²) + (a-η)(2+a-η) k₋ τ²/(3c)`. -/
theorem Piminus_second (ha : a ^ 2 = 1 / 5) (hc : c ≠ 0) (haη : a - η ≠ 0) (τ : ℝ) :
    let T := -(kminus a c η * τ)
    J c T (-a + η) τ 1 0 * βT T (-a + η) τ + J c T (-a + η) τ 1 1 * βπ c T (-a + η) τ +
      J c T (-a + η) τ 1 2 * βτ τ =
    4 / 3 * η * (2 * a - η) * (1 - τ ^ 2) + (a - η) * (2 + a - η) * kminus a c η / (3 * c) * τ ^ 2 := by
  intro T
  rw [Piminus_zero ha hc haη τ]
  rw [show J c T (-a + η) τ 1 0 = -((-a + η) / c) from rfl,
    show J c T (-a + η) τ 1 2 = -(4 / 3) * ((-a + η) ^ 2 - 1 / 5) from rfl]
  simp only [βT, βτ, T]
  rw [show (-a + η) ^ 2 = a ^ 2 - 2 * a * η + η ^ 2 by ring, ha]
  field_simp; ring

theorem Piplus_second (ha : a ^ 2 = 1 / 5) (hc : c ≠ 0) (haη : a + η ≠ 0) (τ : ℝ) :
    let T := -(kplus a c η * τ)
    J c T (a + η) τ 1 0 * βT T (a + η) τ + J c T (a + η) τ 1 1 * βπ c T (a + η) τ +
      J c T (a + η) τ 1 2 * βτ τ =
    -(4 / 3) * η * (2 * a + η) * (1 - τ ^ 2) - (a + η) * (2 - a - η) * kplus a c η / (3 * c) * τ ^ 2 := by
  intro T
  rw [Piplus_zero ha hc haη τ]
  rw [show J c T (a + η) τ 1 0 = -((a + η) / c) from rfl,
    show J c T (a + η) τ 1 2 = -(4 / 3) * ((a + η) ^ 2 - 1 / 5) from rfl]
  simp only [βT, βτ, T]
  rw [show (a + η) ^ 2 = a ^ 2 + 2 * a * η + η ^ 2 by ring, ha]
  field_simp; ring

/-- The tangencies are external: the second derivatives have strict signs on `τ ∈ [-1, 1]`. -/
theorem second_signs (ha0 : 0 < a) (ha2 : a < 1) (hc : 0 < c) (hη : 0 < η) (hηa : η < a / 2)
    {τ : ℝ} (hτ1 : -1 ≤ τ) (hτ2 : τ ≤ 1) :
    0 < 4 / 3 * η * (2 * a - η) * (1 - τ ^ 2) +
        (a - η) * (2 + a - η) * kminus a c η / (3 * c) * τ ^ 2 ∧
    -(4 / 3) * η * (2 * a + η) * (1 - τ ^ 2) -
        (a + η) * (2 - a - η) * kplus a c η / (3 * c) * τ ^ 2 < 0 := by
  have hkm : 0 < kminus a c η := by
    simp only [kminus]
    exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hc) hη) (by linarith)) (by linarith)
  have hkp : 0 < kplus a c η := by
    simp only [kplus]
    exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hc) hη) (by linarith)) (by linarith)
  have h1τ : 0 ≤ 1 - τ ^ 2 := by nlinarith
  have A : 0 < 4 / 3 * η * (2 * a - η) := by nlinarith
  have B : 0 < (a - η) * (2 + a - η) * kminus a c η / (3 * c) := by
    apply div_pos _ (by linarith); apply mul_pos (mul_pos (by linarith) (by linarith)) hkm
  have A' : 0 < 4 / 3 * η * (2 * a + η) := by nlinarith
  have B' : 0 < (a + η) * (2 - a - η) * kplus a c η / (3 * c) := by
    apply div_pos _ (by linarith); apply mul_pos (mul_pos (by linarith) (by linarith)) hkp
  -- `1 - τ²` and `τ²` cannot vanish simultaneously
  constructor
  · rcases lt_or_eq_of_le h1τ with h | h
    · nlinarith [sq_nonneg τ]
    · have : τ ^ 2 = 1 := by linarith
      rw [← h, this]; nlinarith
  · rcases lt_or_eq_of_le h1τ with h | h
    · nlinarith [sq_nonneg τ]
    · have : τ ^ 2 = 1 := by linarith
      rw [← h, this]; nlinarith

/-- For `T > 0` and `π̄ ≤ -a + η`, `|u| ≤ δ` gives `v ≤ δ/(a-η)`. -/
theorem v_bound {u v δ π : ℝ} (hv : 0 < v) (huv : u = π * v) (hπ : π ≤ -a + η)
    (haη : 0 < a - η) (hu : |u| ≤ δ) : v ≤ δ / (a - η) := by
  rw [le_div_iff₀ haη]
  have : u ≤ -(a - η) * v := by rw [huv]; nlinarith
  have := neg_abs_le u
  nlinarith

/-- `δ/(a-η) < δ'` follows from `2√(cδ) < a - η`. -/
theorem v_bound_lt {δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (haη : 0 < a - η)
    (h : 2 * Real.sqrt (c * δ) < a - η) : δ / (a - η) < Real.sqrt (δ / (4 * c)) := by
  rw [Real.lt_sqrt (by positivity)]
  have hs : (2 * Real.sqrt (c * δ)) ^ 2 = 4 * c * δ := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  have h2 : 4 * c * δ < (a - η) ^ 2 := by
    rw [← hs]; exact pow_lt_pow_left₀ h (by positivity) (by norm_num)
  rw [div_pow, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- On the top face `|π̄| = |u|/δ' ≤ δ/δ' = 2√(cδ)`. -/
theorem top_face_pi {δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    δ / Real.sqrt (δ / (4 * c)) = 2 * Real.sqrt (c * δ) := by
  have h1 : Real.sqrt (δ / (4 * c)) * (2 * Real.sqrt (c * δ)) = δ := by
    rw [mul_left_comm, ← Real.sqrt_mul (by positivity)]
    rw [show δ / (4 * c) * (c * δ) = (δ / 2) ^ 2 by field_simp; ring,
      Real.sqrt_sq (by positivity)]
    ring
  have hpos : 0 < Real.sqrt (δ / (4 * c)) := Real.sqrt_pos.2 (by positivity)
  rw [div_eq_iff hpos.ne']; linarith [h1]

/-- For every `c > 0` and `0 < a - η` there is `δ₀` so that all smallness conditions of
Lemma `lem:TC` and Theorem `thm:M` hold for `δ ∈ (0, δ₀)`. -/
theorem exists_delta_M (hc : 0 < c) (haη : 0 < a - η) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ →
      TCHyp c δ (Real.sqrt (δ / (4 * c))) ∧ 2 * Real.sqrt (c * δ) < a - η ∧ δ < 3 / (5 * c) := by
  obtain ⟨δ₁, hδ₁, H⟩ := exists_delta hc
  refine ⟨min δ₁ ((a - η) ^ 2 / (4 * c)), lt_min hδ₁ (by positivity), fun δ hδ hlt => ?_⟩
  have HT := H δ hδ (lt_of_lt_of_le hlt (min_le_left _ _))
  refine ⟨HT, ?_, HT.delta_lt⟩
  have h2 : δ < (a - η) ^ 2 / (4 * c) := lt_of_lt_of_le hlt (min_le_right _ _)
  rw [lt_div_iff₀ (by positivity)] at h2
  have hs : (2 * Real.sqrt (c * δ)) ^ 2 < (a - η) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 haη.le hs

/-- Membership of the `C`-points and of the diagonal points in `K^+`: `|u| = 15/(19c) > 3/(5c)`. -/
theorem membership {τ : ℝ} (hc : 0 < c) (hτ0 : τ ≠ 0) (hτ1 : |τ| ≤ 1) :
    2 / (38 * c / 15) = 15 / (19 * c) ∧ 3 / (5 * c) < 15 / (19 * c) ∧
      3 / (5 * c) ≤ |ustar c τ| := by
  refine ⟨by field_simp; ring, ?_, ?_⟩
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  · simp only [ustar]
    rw [abs_div, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 5 * c)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < |τ| := abs_pos.2 hτ0
    norm_num; nlinarith

/-- No return through `Π⁻` for `T ≥ 0` (the inequality argument in the proof). -/
theorem no_return {K b τ₁ τ₂ T₁ T₂ : ℝ} (hb : 0 < b) (hK : 0 < K) (h12 : τ₁ < τ₂) (h2 : τ₂ < 0)
    (hT : T₁ ≤ T₂) (hre : K * |τ₂| > b * T₂) (hex : 0 ≤ τ₁ ∨ K * |τ₁| ≤ b * T₁) : False := by
  rcases hex with h | h
  · linarith
  · rw [abs_of_neg h2] at hre
    rw [abs_of_neg (by linarith)] at h
    nlinarith

/-- `T` does not decrease while `τ < 0` and `π̄ < 2` (for `T ≥ 0`), and `|T|` decreases while
`τ > 0` and `π̄ < 2` (for `T < 0`). -/
theorem T_monotone {T π τ : ℝ} (hπ : π < 2) :
    (0 ≤ T → τ < 0 → 0 ≤ βT T π τ) ∧ (T < 0 → 0 < τ → 0 < βT T π τ) := by
  constructor
  · intro hT hτ; simp only [βT]; nlinarith [mul_nonneg hT (by linarith : (0 : ℝ) ≤ 2 - π)]
  · intro hT hτ; simp only [βT]
    have : 0 < (-T) * (2 - π) := mul_pos (by linarith) (by linarith)
    nlinarith

/-- In `D_π ∩ Z ∩ {T < 0}`: `dπ̄/dρ < 0`. -/
theorem Z_region {T π : ℝ} (ha : a ^ 2 = 1 / 5) (ha0 : 0 < a) (hc : 0 < c) (hηa : η < a)
    (hT : T < 0) (h1 : -a ≤ π) (h2 : π ≤ -a + η) : βπ c T π (-1) < 0 := by
  simp only [βπ]
  have hπ0 : π < 0 := by linarith
  have hsq : π ^ 2 ≤ a ^ 2 := by nlinarith
  have hTπ : 0 < T * π := mul_pos_of_neg_of_neg hT hπ0
  have : 0 < T * π / c := div_pos hTπ hc
  rw [ha] at hsq
  nlinarith

/-- The asymptotic coefficient in `π̄ + a = 3a/(c(2+9a)) T + O(T)`. -/
theorem asymptotic_coeff (hc : c ≠ 0) (h : 2 + 9 * a ≠ 0) :
    a / (c * ((2 + a) / 3 + 8 * a / 3)) = 3 * a / (c * (2 + 9 * a)) := by
  field_simp; ring

end ThmM

/-- Lemma `lem:fiber`(i): `Σ_I(C)` is a saddle of the fiber flow (negative determinant). -/
theorem IC_saddle : (-((21 + Real.sqrt 821) / 15)) * (-((21 - Real.sqrt 821) / 15)) < 0 := by
  have hs : Real.sqrt 821 ^ 2 = 821 := Real.sq_sqrt (by norm_num)
  nlinarith

end ConleyCheck.Gubser
