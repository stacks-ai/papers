import ConleyCheck.Conley.Sphere
import ConleyCheck.Conley.Block
import ConleyCheck.Conley.Conjugacy

/-!
# Radial rescaling of ellipsoid blocks

A continuous positively homogeneous gauge `ρ` with `ρ ≥ k₀ ‖·‖` defines a homeomorphism
`a ↦ (ρ a / ‖a‖) a` taking `{ρ ≤ 1}` onto the unit ball and `{ρ = 1}` onto the unit sphere. Applied
to `ρ = √q / δ` on both factors, it identifies `blockN / blockL` with the box
`(D^k × D^m) / (S^{k-1} × D^m)`, hence with `S^k` (`blockEquiv`).
-/

namespace ConleyCheck.Conley

open Set Filter Topology Metric
open scoped RealInnerProductSpace

section Radial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {ρ : V → ℝ}

/-- The radial map `a ↦ (ρ a / ‖a‖) a`. -/
noncomputable def radialFun (ρ : V → ℝ) (a : V) : V := (ρ a / ‖a‖) • a

/-- Its inverse `b ↦ (‖b‖ / ρ b) b`. -/
noncomputable def radialInv (ρ : V → ℝ) (b : V) : V := (‖b‖ / ρ b) • b

variable (hρc : Continuous ρ) (hρh : ∀ t : ℝ, 0 ≤ t → ∀ a, ρ (t • a) = t * ρ a)
  {k₀ : ℝ} (hk₀ : 0 < k₀) (hρlb : ∀ a, k₀ * ‖a‖ ≤ ρ a)
include hρh

theorem gauge_zero : ρ 0 = 0 := by
  have := hρh 0 le_rfl 0
  rwa [zero_smul, zero_mul] at this

include hk₀ hρlb in
theorem gauge_pos {a : V} (ha : a ≠ 0) : 0 < ρ a :=
  lt_of_lt_of_le (mul_pos hk₀ (norm_pos_iff.2 ha)) (hρlb a)

theorem norm_radialFun (a : V) : ‖radialFun ρ a‖ = |ρ a| := by
  by_cases ha : a = 0
  · simp [radialFun, ha, gauge_zero hρh]
  · have hn : 0 < ‖a‖ := norm_pos_iff.2 ha
    rw [radialFun, norm_smul, Real.norm_eq_abs, abs_div, abs_norm, div_mul_cancel₀ _ hn.ne']

include hk₀ hρlb

theorem norm_radialFun' (a : V) : ‖radialFun ρ a‖ = ρ a := by
  rw [norm_radialFun hρh, abs_of_nonneg ((mul_nonneg hk₀.le (norm_nonneg a)).trans (hρlb a))]

theorem radialInv_radialFun (a : V) : radialInv ρ (radialFun ρ a) = a := by
  by_cases ha : a = 0
  · simp [radialFun, radialInv, ha]
  · have hn : 0 < ‖a‖ := norm_pos_iff.2 ha
    have hp := gauge_pos hρh hk₀ hρlb ha
    have hc : 0 ≤ ρ a / ‖a‖ := (div_pos hp hn).le
    rw [radialInv, norm_radialFun' hρh hk₀ hρlb, radialFun, hρh _ hc, smul_smul]
    convert one_smul ℝ a
    field_simp

theorem radialFun_radialInv (b : V) : radialFun ρ (radialInv ρ b) = b := by
  by_cases hb : b = 0
  · simp [radialFun, radialInv, hb]
  · have hn : 0 < ‖b‖ := norm_pos_iff.2 hb
    have hp := gauge_pos hρh hk₀ hρlb hb
    have hc : 0 ≤ ‖b‖ / ρ b := (div_pos hn hp).le
    rw [radialFun, radialInv, hρh _ hc, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, smul_smul]
    convert one_smul ℝ b
    field_simp

include hρc

theorem continuous_radialFun : Continuous (radialFun ρ) := by
  refine continuous_iff_continuousAt.2 fun a => ?_
  by_cases ha : a = 0
  · subst ha
    have h0 : radialFun ρ 0 = 0 := by simp [radialFun]
    rw [ContinuousAt, h0, tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_radialFun' hρh hk₀ hρlb]
    simpa [gauge_zero hρh] using hρc.tendsto (0 : V)
  · exact ((hρc.continuousAt.div continuous_norm.continuousAt (norm_ne_zero_iff.2 ha)).smul
      continuousAt_id)

theorem continuous_radialInv : Continuous (radialInv ρ) := by
  refine continuous_iff_continuousAt.2 fun b => ?_
  by_cases hb : b = 0
  · subst hb
    have h0 : radialInv ρ 0 = 0 := by simp [radialInv]
    rw [ContinuousAt, h0]
    refine squeeze_zero_norm (a := fun b => ‖b‖ / k₀) (fun b => ?_) ?_
    · by_cases hb : b = 0
      · simp [radialInv, hb]
      · have hn : 0 < ‖b‖ := norm_pos_iff.2 hb
        have hp := gauge_pos hρh hk₀ hρlb hb
        rw [radialInv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_pos hn hp).le,
          div_mul_eq_mul_div, div_le_div_iff₀ hp hk₀]
        nlinarith [hρlb b]
    · simpa using (continuous_norm.div_const k₀).tendsto (0 : V)
  · exact ((continuous_norm.continuousAt.div hρc.continuousAt
      (gauge_pos hρh hk₀ hρlb hb).ne').smul continuousAt_id)

/-- The radial homeomorphism of a gauge. -/
noncomputable def radialHomeo : V ≃ₜ V where
  toFun := radialFun ρ
  invFun := radialInv ρ
  left_inv := radialInv_radialFun hρh hk₀ hρlb
  right_inv := radialFun_radialInv hρh hk₀ hρlb
  continuous_toFun := continuous_radialFun hρc hρh hk₀ hρlb
  continuous_invFun := continuous_radialInv hρc hρh hk₀ hρlb

theorem radialHomeo_apply (a : V) : radialHomeo hρc hρh hk₀ hρlb a = radialFun ρ a := rfl

end Radial

section Ellipsoid

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem qf_smul (P : V →L[ℝ] V) (t : ℝ) (a : V) : qf P (t • a) = t ^ 2 * qf P a := by
  simp only [qf, map_smul, real_inner_smul_left, real_inner_smul_right]; ring

variable {P : V →L[ℝ] V} {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (hP : ∀ a, τ * ‖a‖ ^ 2 ≤ qf P a)
include hτ hδ hP

theorem qf_nonneg (a : V) : 0 ≤ qf P a := le_trans (by positivity) (hP a)

/-- The gauge `√q / δ`. -/
theorem ellipsoid_gauge :
    Continuous (fun a => Real.sqrt (qf P a) / δ) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ a, Real.sqrt (qf P (t • a)) / δ = t * (Real.sqrt (qf P a) / δ)) ∧
    0 < Real.sqrt τ / δ ∧ ∀ a, Real.sqrt τ / δ * ‖a‖ ≤ Real.sqrt (qf P a) / δ := by
  refine ⟨(Real.continuous_sqrt.comp (continuous_qf P)).div_const δ, fun t ht a => ?_,
    by positivity, fun a => ?_⟩
  · rw [qf_smul, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht, mul_div_assoc]
  · rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hδ, ← Real.sqrt_sq (norm_nonneg a),
      ← Real.sqrt_mul hτ.le]
    exact Real.sqrt_le_sqrt (hP a)

theorem gauge_le_one_iff (a : V) : Real.sqrt (qf P a) / δ ≤ 1 ↔ qf P a ≤ δ ^ 2 := by
  rw [div_le_one hδ, Real.sqrt_le_left hδ.le]

theorem gauge_eq_one_iff (a : V) : Real.sqrt (qf P a) / δ = 1 ↔ qf P a = δ ^ 2 := by
  rw [div_eq_one_iff_eq hδ.ne', Real.sqrt_eq_iff_eq_sq (qf_nonneg hτ hδ hP a) hδ.le]

/-- The radial homeomorphism of the ellipsoid `{q ≤ δ²}` onto the unit ball. -/
noncomputable def ellipsoidHomeo : V ≃ₜ V :=
  radialHomeo (ellipsoid_gauge hτ hδ hP).1 (ellipsoid_gauge hτ hδ hP).2.1
    (ellipsoid_gauge hτ hδ hP).2.2.1 (ellipsoid_gauge hτ hδ hP).2.2.2

theorem ellipsoidHomeo_mem_closedBall (a : V) :
    ellipsoidHomeo hτ hδ hP a ∈ closedBall 0 1 ↔ qf P a ≤ δ ^ 2 := by
  rw [mem_closedBall_zero_iff, ellipsoidHomeo, radialHomeo_apply,
    norm_radialFun' (ellipsoid_gauge hτ hδ hP).2.1 (ellipsoid_gauge hτ hδ hP).2.2.1
      (ellipsoid_gauge hτ hδ hP).2.2.2, gauge_le_one_iff hτ hδ hP]

theorem ellipsoidHomeo_mem_sphere (a : V) :
    ellipsoidHomeo hτ hδ hP a ∈ sphere 0 1 ↔ qf P a = δ ^ 2 := by
  rw [mem_sphere_zero_iff_norm, ellipsoidHomeo, radialHomeo_apply,
    norm_radialFun' (ellipsoid_gauge hτ hδ hP).2.1 (ellipsoid_gauge hτ hδ hP).2.2.1
      (ellipsoid_gauge hτ hδ hP).2.2.2, gauge_eq_one_iff hτ hδ hP]

end Ellipsoid

/-- A pointed homotopy equivalence `N'/L' ≃ N/L` from a homeomorphism `h` with `h⁻¹ N = N'` and
`h⁻¹ L = L'`. -/
noncomputable def IndexSpace.equivOfPreimage {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (h : α ≃ₜ β) {N L : Set β} {N' L' : Set α} (hN : h ⁻¹' N = N')
    (hL : h ⁻¹' L = L') :
    PointedHomotopyEquiv (IndexSpace N' L') (IndexSpace N L) (IndexSpace.pt _ _)
      (IndexSpace.pt _ _) := by
  subst hN hL
  exact IndexSpace.preimageEquiv h N L

variable {k m : ℕ} {P₁ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)}
  {P₂ : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)} {τ₁ τ₂ δ : ℝ}

/-- `blockN / blockL ≃ S^k`. -/
noncomputable def blockEquiv (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hδ : 0 < δ)
    (hP₁ : ∀ a, τ₁ * ‖a‖ ^ 2 ≤ qf P₁ a) (hP₂ : ∀ b, τ₂ * ‖b‖ ^ 2 ≤ qf P₂ b) :
    PointedHomotopyEquiv (IndexSpace (blockN P₁ P₂ δ) (blockL P₁ P₂ δ)) (Sphere k)
      (IndexSpace.pt _ _) (Sphere.pt k) :=
  (IndexSpace.equivOfPreimage
    ((ellipsoidHomeo hτ₁ hδ hP₁).prodCongr (ellipsoidHomeo hτ₂ hδ hP₂))
    (N := boxN k m) (L := boxL k m)
    (by
      ext z
      show ellipsoidHomeo hτ₁ hδ hP₁ z.1 ∈ closedBall 0 1 ∧
          ellipsoidHomeo hτ₂ hδ hP₂ z.2 ∈ closedBall 0 1 ↔ qf P₁ z.1 ≤ δ ^ 2 ∧ qf P₂ z.2 ≤ δ ^ 2
      rw [ellipsoidHomeo_mem_closedBall, ellipsoidHomeo_mem_closedBall])
    (by
      ext z
      show ellipsoidHomeo hτ₁ hδ hP₁ z.1 ∈ sphere 0 1 ∧
          ellipsoidHomeo hτ₂ hδ hP₂ z.2 ∈ closedBall 0 1 ↔ qf P₁ z.1 = δ ^ 2 ∧ qf P₂ z.2 ≤ δ ^ 2
      rw [ellipsoidHomeo_mem_sphere, ellipsoidHomeo_mem_closedBall])).trans (boxEquiv k m)

end ConleyCheck.Conley
