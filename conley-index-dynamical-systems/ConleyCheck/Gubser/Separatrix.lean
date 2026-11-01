import ConleyCheck.ODE.SkewODE
import ConleyCheck.ODE.Triangular
import ConleyCheck.Conley.MovingSaddle
import ConleyCheck.Conley.FaceUniform
import ConleyCheck.Conley.SphereHomology
import ConleyCheck.Conley.Saddle
import ConleyCheck.Gubser.Basic

/-!
# The separatrix `S_B` of the Gubser flow as a moving saddle

The Gubser system `(βT, βπ, βτ)` has the invariant line `S_B = {(0, -1/√5, τ)}`. In the
coordinates `x = T/c`, `y = π + a` with `a = 1/√5` it reads
`x' = x τ (y - a - 2)/3`, `y' = κ y + a x` with `κ = (8a/3) τ - (4/3) τ y - x`, `τ' = 1 - τ²`,
independently of `c`. The moving frame `u = (1 - τ, a)`, `s = (-(1 + τ), a)` has constant
determinant `2a`, and in the coordinates `ξ = (a x + (1 + τ) y)/ε`, `η = ((1 - τ) y - a x)/ε` with
`ε = 1/20` the square `[-1, 1]²` is a common block whose exit set is `{|ξ| = 1}`, for every `c ≠ 0`.

* `P c hc`: the Gubser field, cut off away from `S_B`, as a skew-product ODE. It agrees with the
  Gubser field on the block (`P_F`).
* `eC hc`: the `τ`-dependent change of coordinates.
* `Dxi`, `Deta`: exact formulas for the derivatives of `ξ`, `η` along the flow on the block
  (`DQξ_P`, `DQη_P`), and the face inequalities. Lemma `lem:gubser-block` in the form stated in
  the paper is `Gubser/SepBlock.lean`.
* `isUniformBlock_sep`: the common block.
* `inv_sep`: the invariant set of the block is `S_B`.
-/

namespace ConleyCheck.Gubser.Sep

open Set Function ConleyCheck.ODE ConleyCheck.Conley
open scoped NNReal

/-! ### Constants -/

/-- `a = 1/√5`, so that `π = -a` on `S_B`. -/
noncomputable def a : ℝ := Real.sqrt 5 / 5

theorem a_pos : 0 < a := by unfold a; positivity

theorem a_sq : a ^ 2 = 1 / 5 := by
  unfold a
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem a_lt : a < 4473 / 10000 := by nlinarith [a_sq, a_pos]

theorem a_gt : 447 / 1000 < a := by nlinarith [a_sq, a_pos]

/-- The size of the block. -/
noncomputable def ε : ℝ := 1 / 20

theorem abs_tau (τ : Tau) : |(τ : ℝ)| ≤ 1 := abs_le.2 ⟨τ.2.1, τ.2.2⟩

/-! ### The cut-off field -/

variable (c : ℝ)

/-- The normalized coordinates `(T/c, π + a)`. -/
noncomputable def nrm (p : ℝ × ℝ) : ℝ × ℝ := (p.1 / c, p.2 + a)

noncomputable def bumpG : ContDiffBump (0 : ℝ × ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

noncomputable def bumpS : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The Gubser fiber field `(βT, βπ)` at `τ = s`. -/
noncomputable def fG (p : ℝ × ℝ) (s : ℝ) : ℝ × ℝ := (βT p.1 p.2 s, βπ c p.1 p.2 s)

/-- The Gubser fiber field, cut off outside `‖(T/c, π + a)‖ ≤ 2`, `|s| ≤ 2`. -/
noncomputable def A (q : (ℝ × ℝ) × ℝ) : ℝ × ℝ := (bumpG (nrm c q.1) * bumpS q.2) • fG c q.1 q.2

theorem contDiff_A : ContDiff ℝ 1 (A c) := by
  have h1 : ContDiff ℝ 1 fun q : (ℝ × ℝ) × ℝ => bumpG (nrm c q.1) :=
    bumpG.contDiff.comp (by unfold nrm; fun_prop)
  have h2 : ContDiff ℝ 1 fun q : (ℝ × ℝ) × ℝ => bumpS q.2 := bumpS.contDiff.comp contDiff_snd
  have h3 : ContDiff ℝ 1 fun q : (ℝ × ℝ) × ℝ => fG c q.1 q.2 := by
    unfold fG βT βπ; fun_prop
  exact (h1.mul h2).smul h3

variable {c}

theorem hasCompactSupport_A (hc : c ≠ 0) : HasCompactSupport (A c) := by
  have hK : IsCompact ((fun u : (ℝ × ℝ) × ℝ => ((c * u.1.1, u.1.2 - a), u.2)) ''
      (Metric.closedBall (0 : ℝ × ℝ) 2 ×ˢ Metric.closedBall (0 : ℝ) 2)) :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image (by fun_prop)
  refine HasCompactSupport.intro hK fun q hq => ?_
  by_contra hA
  apply hq
  have hG : bumpG (nrm c q.1) ≠ 0 := fun h => hA (by simp [A, h])
  have hS : bumpS q.2 ≠ 0 := fun h => hA (by simp [A, h])
  rw [← mem_support, bumpG.support_eq] at hG
  rw [← mem_support, bumpS.support_eq] at hS
  refine ⟨(nrm c q.1, q.2), ⟨Metric.ball_subset_closedBall hG, Metric.ball_subset_closedBall hS⟩,
    ?_⟩
  (ext <;> simp [nrm]); field_simp

/-- The base field `1 - τ²`. -/
def g0 (τ : ℝ) : ℝ := 1 - τ ^ 2

theorem lip_g0 : LipschitzOnWith 2 g0 (Icc (-1) 1) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [Real.dist_eq, Real.dist_eq]
  have e : g0 x - g0 y = (y - x) * (x + y) := by unfold g0; ring
  have hxy : |x + y| ≤ 2 := abs_le.2 ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
  rw [e, abs_mul, abs_sub_comm]
  push_cast
  calc |x - y| * |x + y| ≤ |x - y| * 2 := mul_le_mul_of_nonneg_left hxy (abs_nonneg _)
    _ = 2 * |x - y| := mul_comm _ _

/-- The cut-off Gubser system as a skew-product ODE. -/
noncomputable def P (hc : c ≠ 0) : SkewODE (ℝ × ℝ) :=
  SkewODE.ofSmooth (A c) (contDiff_A c) (hasCompactSupport_A hc) g0 2 lip_g0 (by simp [g0])
    (by simp [g0]) (fun τ hτ => by simp only [g0]; nlinarith [hτ.1, hτ.2])

variable (hc : c ≠ 0)

theorem P_g (τ : Tau) : (P hc).g τ = 1 - (τ : ℝ) ^ 2 := by
  show g0 (clamp τ) = _
  rw [clamp_of_mem τ.2]
  rfl

/-- Near `S_B` the cut-off field is the Gubser field. -/
theorem P_F {p : ℝ × ℝ} (hp1 : |p.1 / c| ≤ 1) (hp2 : |p.2 + a| ≤ 1) (τ : Tau) :
    (P hc).F (p, τ) = fG c p τ := by
  show A c (p, clamp τ) = _
  rw [clamp_of_mem τ.2]
  simp only [A]
  rw [bumpG.one_of_mem_closedBall, bumpS.one_of_mem_closedBall, one_mul, one_smul]
  · show dist (τ : ℝ) 0 ≤ 1
    rw [dist_zero_right, Real.norm_eq_abs]
    exact abs_tau τ
  · show dist (nrm c p) 0 ≤ 1
    rw [dist_zero_right, Prod.norm_def]
    simp only [nrm, Real.norm_eq_abs]
    exact max_le hp1 hp2

/-! ### The moving coordinates -/

variable (c) in
/-- `ξ = (a x + (1 + τ) y)/ε` with `x = T/c`, `y = π + a`. -/
noncomputable def cξ (p : ℝ × ℝ) (τ : ℝ) : ℝ := (a * (p.1 / c) + (1 + τ) * (p.2 + a)) / ε

variable (c) in
/-- `η = ((1 - τ) y - a x)/ε`. -/
noncomputable def cη (p : ℝ × ℝ) (τ : ℝ) : ℝ := ((1 - τ) * (p.2 + a) - a * (p.1 / c)) / ε

/-- `x/ε` in terms of `(ξ, η)`. -/
noncomputable def xt (ξ η τ : ℝ) : ℝ := (ξ * (1 - τ) - η * (1 + τ)) * (5 * a / 2)

/-- `y/ε` in terms of `(ξ, η)`. -/
noncomputable def yt (ξ η : ℝ) : ℝ := (ξ + η) / 2

noncomputable def iX (q : ℝ × ℝ) (τ : ℝ) : ℝ := ε * xt q.1 q.2 τ

noncomputable def iY (q : ℝ × ℝ) : ℝ := ε * yt q.1 q.2

omit hc in
theorem iX_c (p : ℝ × ℝ) (τ : ℝ) : iX (cξ c p τ, cη c p τ) τ = p.1 / c := by
  have : iX (cξ c p τ, cη c p τ) τ = 5 * a ^ 2 * (p.1 / c) := by
    simp only [iX, xt, cξ, cη, ε]; ring
  rw [this, a_sq]; ring

omit hc in
theorem iY_c (p : ℝ × ℝ) (τ : ℝ) : iY (cξ c p τ, cη c p τ) = p.2 + a := by
  simp only [iY, yt, cξ, cη, ε]; ring

include hc in
theorem cξ_i (q : ℝ × ℝ) (τ : ℝ) : cξ c (c * iX q τ, iY q - a) τ = q.1 := by
  have : cξ c (c * iX q τ, iY q - a) τ =
      (5 * a ^ 2 * (q.1 * (1 - τ) - q.2 * (1 + τ)) + (1 + τ) * (q.1 + q.2)) / 2 := by
    simp only [cξ, iX, iY, xt, yt, ε]; field_simp; ring
  rw [this, a_sq]; ring

include hc in
theorem cη_i (q : ℝ × ℝ) (τ : ℝ) : cη c (c * iX q τ, iY q - a) τ = q.2 := by
  have : cη c (c * iX q τ, iY q - a) τ =
      ((1 - τ) * (q.1 + q.2) - 5 * a ^ 2 * (q.1 * (1 - τ) - q.2 * (1 + τ))) / 2 := by
    simp only [cη, iX, iY, xt, yt, ε]; field_simp; ring
  rw [this, a_sq]; ring

/-- The change of coordinates `((T, π), τ) ↦ ((ξ, η), τ)`. -/
noncomputable def eC : (ℝ × ℝ) × Tau ≃ₜ (ℝ × ℝ) × Tau where
  toFun p := ((cξ c p.1 p.2, cη c p.1 p.2), p.2)
  invFun q := ((c * iX q.1 q.2, iY q.1 - a), q.2)
  left_inv p := Prod.ext (Prod.ext
    (by show c * iX _ _ = _; rw [iX_c]; field_simp)
    (by show iY _ - a = _; rw [iY_c]; ring)) rfl
  right_inv q := Prod.ext (Prod.ext (cξ_i hc _ _) (cη_i hc _ _)) rfl
  continuous_toFun := by unfold cξ cη; fun_prop
  continuous_invFun := by unfold iX iY xt yt; fun_prop

theorem eC_snd (p : (ℝ × ℝ) × Tau) : (eC hc p).2 = p.2 := rfl

/-! ### Derivatives along the flow -/

variable (c) in
theorem hasDerivAt_cξ (Q : SkewODE (ℝ × ℝ)) (p : (ℝ × ℝ) × Tau) (t : ℝ) :
    HasDerivAt (fun s => cξ c (Q.Φ s p).1 (Q.θ s p.2))
      ((a * ((Q.F ((Q.Φ t p).1, Q.θ t p.2)).1 / c) + Q.g (Q.θ t p.2) * ((Q.Φ t p).1.2 + a)
        + (1 + (Q.θ t p.2 : ℝ)) * (Q.F ((Q.Φ t p).1, Q.θ t p.2)).2) / ε) t := by
  have h := Q.hasDerivAt_Φ_fst p t
  have h1 : HasDerivAt (fun s => (Q.Φ s p).1.1) (Q.F ((Q.Φ t p).1, Q.θ t p.2)).1 t := by
    have := hasFDerivAt_fst.comp_hasDerivAt t h
    exact this
  have h2 : HasDerivAt (fun s => (Q.Φ s p).1.2) (Q.F ((Q.Φ t p).1, Q.θ t p.2)).2 t := by
    have := hasFDerivAt_snd.comp_hasDerivAt t h
    exact this
  have hτ := Q.hasDerivAt_θ p.2 t
  have := (((h1.div_const c).const_mul a).add ((hτ.const_add 1).mul (h2.add_const a))).div_const ε
  unfold cξ
  exact this.congr_deriv (by ring)

variable (c) in
theorem hasDerivAt_cη (Q : SkewODE (ℝ × ℝ)) (p : (ℝ × ℝ) × Tau) (t : ℝ) :
    HasDerivAt (fun s => cη c (Q.Φ s p).1 (Q.θ s p.2))
      ((-Q.g (Q.θ t p.2) * ((Q.Φ t p).1.2 + a)
        + (1 - (Q.θ t p.2 : ℝ)) * (Q.F ((Q.Φ t p).1, Q.θ t p.2)).2
        - a * ((Q.F ((Q.Φ t p).1, Q.θ t p.2)).1 / c)) / ε) t := by
  have h := Q.hasDerivAt_Φ_fst p t
  have h1 : HasDerivAt (fun s => (Q.Φ s p).1.1) (Q.F ((Q.Φ t p).1, Q.θ t p.2)).1 t := by
    have := hasFDerivAt_fst.comp_hasDerivAt t h
    exact this
  have h2 : HasDerivAt (fun s => (Q.Φ s p).1.2) (Q.F ((Q.Φ t p).1, Q.θ t p.2)).2 t := by
    have := hasFDerivAt_snd.comp_hasDerivAt t h
    exact this
  have hτ := Q.hasDerivAt_θ p.2 t
  have := (((hτ.const_sub 1).mul (h2.add_const a)).sub ((h1.div_const c).const_mul a)).div_const ε
  unfold cη
  exact this.congr_deriv (by ring)

omit hc in
theorem βT_c (x π τ : ℝ) (hc : c ≠ 0) : βT (c * x) π τ / c = x / 3 * (π - 2) * τ := by
  unfold βT; field_simp

omit hc in
theorem βπ_c (x π τ : ℝ) (hc : c ≠ 0) :
    βπ c (c * x) π τ = -(4 / 3) * (π ^ 2 - 1 / 5) * τ - x * π := by
  unfold βπ; field_simp

/-! ### The linearization in the moving frame -/

noncomputable def β₁ : ℝ := (7 * a - 2) / 3

noncomputable def δ₁ : ℝ := 3 * a - 4 / 3

noncomputable def B11 (τ : ℝ) : ℝ := (2 + β₁ * τ + δ₁ * τ ^ 2) / 2

noncomputable def B12 (τ : ℝ) : ℝ := δ₁ * τ * (1 + τ) / 2

noncomputable def B21 (τ : ℝ) : ℝ := δ₁ * τ * (1 - τ) / 2

noncomputable def B22 (τ : ℝ) : ℝ := (-2 + β₁ * τ - δ₁ * τ ^ 2) / 2

noncomputable def Q1 (ξ η τ : ℝ) : ℝ :=
  xt ξ η τ * yt ξ η * (a * τ / 3 - (1 + τ)) - 4 / 3 * τ * (1 + τ) * yt ξ η ^ 2

noncomputable def Q2 (ξ η τ : ℝ) : ℝ :=
  -(xt ξ η τ * yt ξ η * ((1 - τ) + a * τ / 3)) - 4 / 3 * τ * (1 - τ) * yt ξ η ^ 2

/-- `ξ'` on the block. -/
noncomputable def Dxi (ξ η τ : ℝ) : ℝ := B11 τ * ξ + B12 τ * η + ε * Q1 ξ η τ

/-- `η'` on the block. -/
noncomputable def Deta (ξ η τ : ℝ) : ℝ := B21 τ * ξ + B22 τ * η + ε * Q2 ξ η τ

theorem abs_xt_le {ξ η τ : ℝ} (hξ : |ξ| ≤ 1) (hη : |η| ≤ 1) (hτ : |τ| ≤ 1) :
    |xt ξ η τ| ≤ 5 * a := by
  rw [abs_le] at hξ hη hτ
  have hw : |ξ * (1 - τ) - η * (1 + τ)| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hξ.2) (sub_nonneg.2 hτ.2),
      mul_nonneg (neg_le_iff_add_nonneg.1 hξ.1) (sub_nonneg.2 hτ.2),
      mul_nonneg (sub_nonneg.2 hη.2) (neg_le_iff_add_nonneg.1 hτ.1),
      mul_nonneg (neg_le_iff_add_nonneg.1 hη.1) (neg_le_iff_add_nonneg.1 hτ.1)]
  have ha := a_pos
  rw [xt, abs_mul, abs_of_pos (by positivity : 0 < 5 * a / 2)]
  nlinarith

theorem abs_yt_le {ξ η : ℝ} (hξ : |ξ| ≤ 1) (hη : |η| ≤ 1) : |yt ξ η| ≤ 1 := by
  rw [abs_le] at *
  unfold yt
  constructor <;> linarith

theorem abs_Q_le {w v ξ η τ : ℝ} (hξ : |ξ| ≤ 1) (hη : |η| ≤ 1) (hτ : |τ| ≤ 1)
    (hw : |w| ≤ a / 3 + 2) (hv : |v| ≤ 8 / 3) :
    |xt ξ η τ * yt ξ η * w| + |v * yt ξ η ^ 2| ≤ 8 := by
  have hx := abs_xt_le hξ hη hτ
  have hy := abs_yt_le hξ hη
  have ha := a_pos
  have hy2 : |yt ξ η ^ 2| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hy
  rw [abs_mul, abs_mul, abs_mul]
  have h1 : |xt ξ η τ| * |yt ξ η| ≤ 5 * a :=
    (mul_le_mul hx hy (abs_nonneg _) (by linarith)).trans_eq (mul_one _)
  have h2 : |xt ξ η τ| * |yt ξ η| * |w| ≤ 5 * a * (a / 3 + 2) :=
    mul_le_mul h1 hw (abs_nonneg _) (by linarith)
  have h3 : |v| * |yt ξ η ^ 2| ≤ 8 / 3 :=
    (mul_le_mul hv hy2 (abs_nonneg _) (by norm_num)).trans_eq (mul_one _)
  nlinarith [a_sq, a_lt]

theorem abs_Q1_le {ξ η τ : ℝ} (hξ : |ξ| ≤ 1) (hη : |η| ≤ 1) (hτ : |τ| ≤ 1) :
    |Q1 ξ η τ| ≤ 8 := by
  have ha := a_pos
  have hw : |a * τ / 3 - (1 + τ)| ≤ a / 3 + 2 := by
    rw [abs_le] at hτ ⊢; constructor <;> nlinarith
  have hv : |4 / 3 * τ * (1 + τ)| ≤ 8 / 3 := by
    rw [abs_le] at hτ ⊢; constructor <;> nlinarith
  exact (abs_sub _ _).trans (abs_Q_le hξ hη hτ hw hv)

theorem abs_Q2_le {ξ η τ : ℝ} (hξ : |ξ| ≤ 1) (hη : |η| ≤ 1) (hτ : |τ| ≤ 1) :
    |Q2 ξ η τ| ≤ 8 := by
  have ha := a_pos
  have hw : |(1 - τ) + a * τ / 3| ≤ a / 3 + 2 := by
    rw [abs_le] at hτ ⊢; constructor <;> nlinarith
  have hv : |4 / 3 * τ * (1 - τ)| ≤ 8 / 3 := by
    rw [abs_le] at hτ ⊢; constructor <;> nlinarith
  unfold Q2
  refine (abs_sub _ _).trans ?_
  rw [abs_neg]
  exact abs_Q_le hξ hη hτ hw hv

theorem B11_ge {τ : ℝ} (hτ : |τ| ≤ 1) : 4 / 5 ≤ B11 τ := by
  rw [abs_le] at hτ
  have := a_gt; have := a_lt
  unfold B11 β₁ δ₁
  nlinarith [mul_nonneg (neg_le_iff_add_nonneg.1 hτ.1) (by linarith : (0 : ℝ) ≤ (7 * a - 2) / 3),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * a - 4 / 3) (sq_nonneg τ)]

theorem B22_le {τ : ℝ} (hτ : |τ| ≤ 1) : B22 τ ≤ -(4 / 5) := by
  rw [abs_le] at hτ
  have := a_gt; have := a_lt
  unfold B22 β₁ δ₁
  nlinarith [mul_nonneg (sub_nonneg.2 hτ.2) (by linarith : (0 : ℝ) ≤ (7 * a - 2) / 3),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * a - 4 / 3) (sq_nonneg τ)]

theorem abs_B12_le {τ : ℝ} (hτ : |τ| ≤ 1) : |B12 τ| ≤ 1 / 50 := by
  rw [abs_le] at hτ
  have := a_gt; have := a_lt
  have h0 : 0 ≤ 3 * a - 4 / 3 := by linarith
  have h1 : |τ * (1 + τ)| ≤ 2 := by rw [abs_le]; constructor <;> nlinarith
  have : B12 τ = (3 * a - 4 / 3) * (τ * (1 + τ)) / 2 := by unfold B12 δ₁; ring
  rw [this, abs_div, abs_mul, abs_of_nonneg h0, abs_two]
  have := mul_le_mul_of_nonneg_left h1 h0
  linarith

theorem abs_B21_le {τ : ℝ} (hτ : |τ| ≤ 1) : |B21 τ| ≤ 1 / 50 := by
  rw [abs_le] at hτ
  have := a_gt; have := a_lt
  have h0 : 0 ≤ 3 * a - 4 / 3 := by linarith
  have h1 : |τ * (1 - τ)| ≤ 2 := by rw [abs_le]; constructor <;> nlinarith
  have : B21 τ = (3 * a - 4 / 3) * (τ * (1 - τ)) / 2 := by unfold B21 δ₁; ring
  rw [this, abs_div, abs_mul, abs_of_nonneg h0, abs_two]
  have := mul_le_mul_of_nonneg_left h1 h0
  linarith

theorem small_of_abs {b u : ℝ} (hb : |b| ≤ 1 / 50) (hu : |u| ≤ 1) : |b * u| ≤ 1 / 50 := by
  rw [abs_mul]
  exact (mul_le_mul hb hu (abs_nonneg _) (by norm_num)).trans_eq (mul_one _)

theorem dxi_face_pos {η τ : ℝ} (hη : |η| ≤ 1) (hτ : |τ| ≤ 1) : 3 / 8 ≤ Dxi 1 η τ := by
  have h1 := B11_ge hτ
  have h2 := abs_le.1 (small_of_abs (abs_B12_le hτ) hη)
  have h3 := abs_le.1 (abs_Q1_le (ξ := 1) (by norm_num) hη hτ)
  unfold Dxi ε
  nlinarith

theorem dxi_face_neg {η τ : ℝ} (hη : |η| ≤ 1) (hτ : |τ| ≤ 1) : Dxi (-1) η τ ≤ -(3 / 8) := by
  have h1 := B11_ge hτ
  have h2 := abs_le.1 (small_of_abs (abs_B12_le hτ) hη)
  have h3 := abs_le.1 (abs_Q1_le (ξ := -1) (by norm_num) hη hτ)
  unfold Dxi ε
  nlinarith

theorem deta_face_neg {ξ τ : ℝ} (hξ : |ξ| ≤ 1) (hτ : |τ| ≤ 1) : Deta ξ 1 τ ≤ -(3 / 8) := by
  have h1 := B22_le hτ
  have h2 := abs_le.1 (small_of_abs (abs_B21_le hτ) hξ)
  have h3 := abs_le.1 (abs_Q2_le (η := 1) hξ (by norm_num) hτ)
  unfold Deta ε
  nlinarith

theorem deta_face_pos {ξ τ : ℝ} (hξ : |ξ| ≤ 1) (hτ : |τ| ≤ 1) : 3 / 8 ≤ Deta ξ (-1) τ := by
  have h1 := B22_le hτ
  have h2 := abs_le.1 (small_of_abs (abs_B21_le hτ) hξ)
  have h3 := abs_le.1 (abs_Q2_le (η := -1) hξ (by norm_num) hτ)
  unfold Deta ε
  nlinarith

/-! ### The block -/

theorem abs_iX_le {q : ℝ × ℝ} (h1 : |q.1| ≤ 1) (h2 : |q.2| ≤ 1) {τ : ℝ} (hτ : |τ| ≤ 1) :
    |iX q τ| ≤ 5 * a * ε := by
  rw [iX, abs_mul, abs_of_pos (by norm_num [ε] : (0 : ℝ) < ε), mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_xt_le h1 h2 hτ) (by norm_num [ε])

theorem abs_iY_le {q : ℝ × ℝ} (h1 : |q.1| ≤ 1) (h2 : |q.2| ≤ 1) : |iY q| ≤ ε := by
  rw [iY, abs_mul, abs_of_pos (by norm_num [ε] : (0 : ℝ) < ε)]
  exact (mul_le_mul_of_nonneg_left (abs_yt_le h1 h2) (by norm_num [ε])).trans_eq (mul_one _)

variable (c) in
/-- The point `(T, π)` with block coordinates `q` at height `τ`. -/
noncomputable def ptB (q : ℝ × ℝ) (τ : ℝ) : ℝ × ℝ := (c * iX q τ, iY q - a)

variable (c) in
/-- `ξ'` at `(q, τ)` for a skew-product ODE `Q`. -/
noncomputable def DQξ (Q : SkewODE (ℝ × ℝ)) (q : ℝ × ℝ) (τ : Tau) : ℝ :=
  (a * ((Q.F (ptB c q τ, τ)).1 / c) + Q.g τ * ((ptB c q τ).2 + a)
    + (1 + (τ : ℝ)) * (Q.F (ptB c q τ, τ)).2) / ε

variable (c) in
/-- `η'` at `(q, τ)` for a skew-product ODE `Q`. -/
noncomputable def DQη (Q : SkewODE (ℝ × ℝ)) (q : ℝ × ℝ) (τ : Tau) : ℝ :=
  (-Q.g τ * ((ptB c q τ).2 + a) + (1 - (τ : ℝ)) * (Q.F (ptB c q τ, τ)).2
    - a * ((Q.F (ptB c q τ, τ)).1 / c)) / ε

theorem hasDerivAt_Q_ξ (Q : SkewODE (ℝ × ℝ)) (q : ℝ × ℝ) (τ : Tau) :
    HasDerivAt (fun t => (conjFlow Q.Φ (eC hc) t (q, τ)).1.1) (DQξ c Q q τ) 0 := by
  have h := hasDerivAt_cξ c Q (ptB c q τ, τ) 0
  simp only [Flow.map_zero_apply] at h
  exact h

theorem hasDerivAt_Q_η (Q : SkewODE (ℝ × ℝ)) (q : ℝ × ℝ) (τ : Tau) :
    HasDerivAt (fun t => (conjFlow Q.Φ (eC hc) t (q, τ)).1.2) (DQη c Q q τ) 0 := by
  have h := hasDerivAt_cη c Q (ptB c q τ, τ) 0
  simp only [Flow.map_zero_apply] at h
  exact h

theorem P_F_blk {q : ℝ × ℝ} (h1 : |q.1| ≤ 1) (h2 : |q.2| ≤ 1) (τ : Tau) :
    (P hc).F (ptB c q τ, τ) = fG c (ptB c q τ) τ := by
  have hX := abs_iX_le h1 h2 (abs_tau τ)
  have hY := abs_iY_le h1 h2
  have := a_lt
  exact P_F hc (by simp only [ptB]; rw [mul_div_cancel_left₀ _ hc]; norm_num [ε] at hX ⊢; linarith)
    (by simp only [ptB]; rw [sub_add_cancel]; norm_num [ε] at hY ⊢; linarith) τ

/-- On the block, `ξ'` for the Gubser system is `Dxi`. -/
theorem DQξ_P {q : ℝ × ℝ} (h1 : |q.1| ≤ 1) (h2 : |q.2| ≤ 1) (τ : Tau) :
    DQξ c (P hc) q τ = Dxi q.1 q.2 τ := by
  unfold DQξ
  rw [P_F_blk hc h1 h2, P_g]
  simp only [fG, ptB]
  rw [βT_c _ _ _ hc, βπ_c _ _ _ hc]
  simp only [Dxi, B11, B12, Q1, β₁, δ₁, iX, iY, xt, yt, ε]
  linear_combination 5 * (a * q.2 * τ ^ 2 + a * q.2 * τ + a * τ ^ 2 * q.1 - a * τ * q.1
    - q.2 * τ ^ 2 - 4 * q.2 * τ - 3 * q.2 - τ ^ 2 * q.1 - 32 * τ ^ 2 - 2 * τ * q.1 - 32 * τ
    + 3 * q.1) / 6 * a_sq

/-- On the block, `η'` for the Gubser system is `Deta`. -/
theorem DQη_P {q : ℝ × ℝ} (h1 : |q.1| ≤ 1) (h2 : |q.2| ≤ 1) (τ : Tau) :
    DQη c (P hc) q τ = Deta q.1 q.2 τ := by
  unfold DQη
  rw [P_F_blk hc h1 h2, P_g]
  simp only [fG, ptB]
  rw [βT_c _ _ _ hc, βπ_c _ _ _ hc]
  simp only [Deta, B21, B22, Q2, β₁, δ₁, iX, iY, xt, yt, ε]
  linear_combination -5 * (a * q.2 * τ ^ 2 + a * q.2 * τ + a * τ ^ 2 * q.1 - a * τ * q.1
    - q.2 * τ ^ 2 + 2 * q.2 * τ + 3 * q.2 - τ ^ 2 * q.1 - 32 * τ ^ 2 + 4 * τ * q.1 + 32 * τ
    - 3 * q.1) / 6 * a_sq

/-! ### Perturbations -/

variable (c) in
/-- `Q` is `η`-close to the Gubser system on the block, in the sup norm, with the
`T`-component measured in units of `c`. -/
structure IsClose (Q : SkewODE (ℝ × ℝ)) (η : ℝ) : Prop where
  F1 : ∀ q : ℝ × ℝ, |q.1| ≤ 1 → |q.2| ≤ 1 → ∀ τ : Tau,
    |(Q.F (ptB c q τ, τ)).1 / c - (fG c (ptB c q τ) τ).1 / c| ≤ η
  F2 : ∀ q : ℝ × ℝ, |q.1| ≤ 1 → |q.2| ≤ 1 → ∀ τ : Tau,
    |(Q.F (ptB c q τ, τ)).2 - (fG c (ptB c q τ) τ).2| ≤ η
  g : ∀ τ : Tau, |Q.g τ - (1 - (τ : ℝ) ^ 2)| ≤ η

theorem isClose_P : IsClose c (P hc) 0 where
  F1 q h1 h2 τ := by rw [P_F_blk hc h1 h2]; simp
  F2 q h1 h2 τ := by rw [P_F_blk hc h1 h2]; simp
  g τ := by rw [P_g]; simp

omit hc in
theorem abs_three_le {A B C α β γ : ℝ} (hA : |A| ≤ α) (hB : |B| ≤ β) (hC : |C| ≤ γ) :
    |(A + B + C) / ε| ≤ (α + β + γ) * 20 := by
  rw [abs_div, abs_of_pos (by norm_num [ε] : (0 : ℝ) < ε), div_eq_mul_inv]
  have : ε⁻¹ = 20 := by norm_num [ε]
  rw [this]
  exact mul_le_mul_of_nonneg_right ((abs_add_three _ _ _).trans (by linarith)) (by norm_num)

omit hc in
theorem DQ_close_aux {Q : SkewODE (ℝ × ℝ)} {η : ℝ} (hQ : IsClose c Q η) {q : ℝ × ℝ}
    (h1 : |q.1| ≤ 1) (h2 : |q.2| ≤ 1) (τ : Tau) :
    |a * ((Q.F (ptB c q τ, τ)).1 / c - (fG c (ptB c q τ) τ).1 / c)| ≤ a * η ∧
      |(Q.g τ - (1 - (τ : ℝ) ^ 2)) * iY q| ≤ η * ε ∧
      |(1 + (τ : ℝ)) * ((Q.F (ptB c q τ, τ)).2 - (fG c (ptB c q τ) τ).2)| ≤ 2 * η ∧
      |(1 - (τ : ℝ)) * ((Q.F (ptB c q τ, τ)).2 - (fG c (ptB c q τ) τ).2)| ≤ 2 * η ∧ 0 ≤ η := by
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hQ.g τ)
  have hτ := abs_le.1 (abs_tau τ)
  refine ⟨?_, ?_, ?_, ?_, hη0⟩
  · rw [abs_mul, abs_of_pos a_pos]
    exact mul_le_mul_of_nonneg_left (hQ.F1 q h1 h2 τ) a_pos.le
  · rw [abs_mul]
    exact mul_le_mul (hQ.g τ) (abs_iY_le h1 h2) (abs_nonneg _) hη0
  · rw [abs_mul, mul_comm 2]
    exact mul_le_mul (abs_le.2 ⟨by linarith, by linarith⟩) (hQ.F2 q h1 h2 τ) (abs_nonneg _)
      (by norm_num)
    |>.trans_eq (mul_comm _ _)
  · rw [abs_mul, mul_comm 2]
    exact mul_le_mul (abs_le.2 ⟨by linarith, by linarith⟩) (hQ.F2 q h1 h2 τ) (abs_nonneg _)
      (by norm_num)
    |>.trans_eq (mul_comm _ _)

include hc in
theorem DQξ_close {Q : SkewODE (ℝ × ℝ)} {η : ℝ} (hQ : IsClose c Q η) {q : ℝ × ℝ}
    (h1 : |q.1| ≤ 1) (h2 : |q.2| ≤ 1) (τ : Tau) : |DQξ c Q q τ - Dxi q.1 q.2 τ| ≤ 50 * η := by
  obtain ⟨hA, hB, hC, -, hη0⟩ := DQ_close_aux hQ h1 h2 τ
  rw [← DQξ_P hc h1 h2 τ]
  have e : DQξ c Q q τ - DQξ c (P hc) q τ =
      (a * ((Q.F (ptB c q τ, τ)).1 / c - (fG c (ptB c q τ) τ).1 / c)
        + (Q.g τ - (1 - (τ : ℝ) ^ 2)) * iY q
        + (1 + (τ : ℝ)) * ((Q.F (ptB c q τ, τ)).2 - (fG c (ptB c q τ) τ).2)) / ε := by
    unfold DQξ
    rw [P_F_blk hc h1 h2, P_g]
    simp only [ptB, sub_add_cancel]
    ring
  rw [e]
  have := abs_three_le hA hB hC
  have := a_lt
  nlinarith [this, show ε = 1 / 20 from rfl]

include hc in
theorem DQη_close {Q : SkewODE (ℝ × ℝ)} {η : ℝ} (hQ : IsClose c Q η) {q : ℝ × ℝ}
    (h1 : |q.1| ≤ 1) (h2 : |q.2| ≤ 1) (τ : Tau) : |DQη c Q q τ - Deta q.1 q.2 τ| ≤ 50 * η := by
  obtain ⟨hA, hB, -, hC, hη0⟩ := DQ_close_aux hQ h1 h2 τ
  rw [← DQη_P hc h1 h2 τ]
  have e : DQη c Q q τ - DQη c (P hc) q τ =
      (-((Q.g τ - (1 - (τ : ℝ) ^ 2)) * iY q)
        + (1 - (τ : ℝ)) * ((Q.F (ptB c q τ, τ)).2 - (fG c (ptB c q τ) τ).2)
        + -(a * ((Q.F (ptB c q τ, τ)).1 / c - (fG c (ptB c q τ) τ).1 / c))) / ε := by
    unfold DQη
    rw [P_F_blk hc h1 h2, P_g]
    simp only [ptB, sub_add_cancel]
    ring
  rw [e]
  have hB' : |-((Q.g τ - (1 - (τ : ℝ) ^ 2)) * iY q)| ≤ η * ε := by rw [abs_neg]; exact hB
  have hA' : |-(a * ((Q.F (ptB c q τ, τ)).1 / c - (fG c (ptB c q τ) τ).1 / c))| ≤ a * η := by
    rw [abs_neg]; exact hA
  have := abs_three_le hB' hC hA'
  have := a_lt
  nlinarith [this, show ε = 1 / 20 from rfl]

/-- The faces of the block `[-1, 1]²`. -/
def gB : Fin 4 → ℝ × ℝ → ℝ :=
  ![fun q => q.1 - 1, fun q => -q.1 - 1, fun q => q.2 - 1, fun q => -q.2 - 1]

theorem blk_iff {q : ℝ × ℝ} : (∀ j, gB j q ≤ 0) ↔ |q.1| ≤ 1 ∧ |q.2| ≤ 1 := by
  constructor
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    simp [gB] at h0 h1 h2 h3
    exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩
  · rintro ⟨h1, h2⟩ j
    rw [abs_le] at h1 h2
    fin_cases j <;> simp [gB] <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem continuous_gB (k : Fin 4) : Continuous (gB k) := by
  fin_cases k <;> simp [gB] <;> fun_prop

/-- The block `N = [-1, 1]²`. -/
def NB : Set (ℝ × ℝ) := {q | ∀ k, gB k q ≤ 0}

/-- Its exit set `{|ξ| = 1}`. -/
def LB : Set (ℝ × ℝ) := {q | (∀ k, gB k q ≤ 0) ∧ ∃ k ∈ ({0, 1} : Set (Fin 4)), gB k q = 0}

theorem NB_eq : NB = Icc (-1) 1 ×ˢ Icc (-1) 1 := by
  ext q
  simp only [NB, mem_ofPred_eq, blk_iff, abs_le, mem_prod, mem_Icc]

theorem LB_eq : LB = {q | |q.1| = 1 ∧ |q.2| ≤ 1} := by
  ext q
  simp only [LB, mem_ofPred_eq, blk_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, k, hk, h0⟩
    simp only [mem_insert_iff, mem_singleton_iff] at hk
    rcases hk with rfl | rfl <;> simp [gB] at h0
    · exact ⟨by rw [show q.1 = 1 by linarith]; norm_num, h2⟩
    · exact ⟨by rw [show q.1 = -1 by linarith]; norm_num, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1.le, h2⟩, ?_⟩
    rcases abs_eq (zero_le_one' ℝ) |>.1 h1 with h | h
    · exact ⟨0, by simp, by simp [gB, h]⟩
    · exact ⟨1, by simp, by simp [gB, h]⟩

variable (c) in
/-- The derivatives across the faces. -/
noncomputable def DBQ (Q : SkewODE (ℝ × ℝ)) : Fin 4 → ℝ × ℝ → Tau → ℝ :=
  ![fun q τ => DQξ c Q q τ, fun q τ => -DQξ c Q q τ, fun q τ => DQη c Q q τ,
    fun q τ => -DQη c Q q τ]

/-- The block `[-1, 1]²` in the moving coordinates is a common block, with exit set `{|ξ| = 1}`,
for every skew-product ODE that is `1/200`-close to the Gubser system on the block. -/
theorem isUniformBlock_pert (Q : SkewODE (ℝ × ℝ)) {η : ℝ} (hη : η ≤ 1 / 200)
    (hQ : IsClose c Q η) : IsUniformBlock (conjFlow Q.Φ (eC hc)) NB LB := by
  refine isUniformBlock_of_faces (D := DBQ c Q) continuous_gB
    (by rw [← NB, NB_eq]; exact isCompact_Icc.prod isCompact_Icc) ?_ ?_ ?_
  · intro k q τ _
    have hξ := hasDerivAt_Q_ξ hc Q q τ
    have hη := hasDerivAt_Q_η hc Q q τ
    fin_cases k
    · exact hξ.sub_const 1
    · exact hξ.neg.sub_const 1
    · exact hη.sub_const 1
    · exact hη.neg.sub_const 1
  · intro k hk q τ hq h0
    rw [blk_iff] at hq
    have hd := abs_le.1 (DQξ_close hc hQ hq.1 hq.2 τ)
    simp only [mem_insert_iff, mem_singleton_iff] at hk
    rcases hk with rfl | rfl
    · have h1 : q.1 = 1 := by simp [gB] at h0; linarith
      show 0 < DQξ c Q q τ
      have := dxi_face_pos hq.2 (abs_tau τ)
      rw [h1] at hd
      linarith [hd.1]
    · have h1 : q.1 = -1 := by simp [gB] at h0; linarith
      show 0 < -DQξ c Q q τ
      have := dxi_face_neg hq.2 (abs_tau τ)
      rw [h1] at hd
      linarith [hd.2]
  · intro k hk q τ hq h0
    rw [blk_iff] at hq
    have hd := abs_le.1 (DQη_close hc hQ hq.1 hq.2 τ)
    fin_cases k
    · simp at hk
    · simp at hk
    · have h1 : q.2 = 1 := by simp [gB] at h0; linarith
      show DQη c Q q τ < 0
      have := deta_face_neg hq.1 (abs_tau τ)
      rw [h1] at hd
      linarith [hd.2]
    · have h1 : q.2 = -1 := by simp [gB] at h0; linarith
      show -DQη c Q q τ < 0
      have := deta_face_pos hq.1 (abs_tau τ)
      rw [h1] at hd
      linarith [hd.1]

theorem isUniformBlock_sep : IsUniformBlock (conjFlow (P hc).Φ (eC hc)) NB LB :=
  isUniformBlock_pert hc (P hc) (by norm_num) (isClose_P hc)

/-! ### The invariant set of the block -/

/-- The separatrix `S_B = {T = 0, π = -a}`. -/
def SB : Set ((ℝ × ℝ) × Tau) := {p | p.1 = (0, -a)}

theorem F_SB (r : ℝ) : (P hc).F ((0, -a), r) = 0 := by
  show A c ((0, -a), clamp r) = 0
  simp [A, fG, βT, βπ, a_sq]

/-- `S_B` is invariant, with `T = 0`, `π = -a` along the flow. -/
theorem Φ_SB (τ₀ : Tau) (t : ℝ) : ((P hc).Φ t (((0 : ℝ), -a), τ₀)).1 = (0, -a) := by
  have hγ : IsSol (P hc).V fun s => (((0 : ℝ), -a), (P hc).β s τ₀) := fun s => by
    have := (hasDerivAt_const s (((0 : ℝ), -a) : ℝ × ℝ)).prodMk ((P hc).hasDerivAt_β τ₀ s)
    convert this using 1
    simp only [SkewODE.V, F_SB]
  have h := flowOf_eq_of_isSol (P hc).exists_lipschitz_V.choose_spec
    (P hc).exists_bound_V.choose_spec hγ 0 t
  simp only [Flow.map_zero_apply] at h
  exact congrArg Prod.fst h

/-- `x = T/c` along the orbit of `p`. -/
noncomputable def xs (p : (ℝ × ℝ) × Tau) (s : ℝ) : ℝ := ((P hc).Φ s p).1.1 / c

/-- `y = π + a` along the orbit of `p`. -/
noncomputable def ys (p : (ℝ × ℝ) × Tau) (s : ℝ) : ℝ := ((P hc).Φ s p).1.2 + a

/-- `τ` along the orbit of `p`. -/
noncomputable def τs (p : (ℝ × ℝ) × Tau) (s : ℝ) : ℝ := ((P hc).θ s p.2 : ℝ)

omit hc in
theorem βT_div (T π τ : ℝ) : βT T π τ / c = T / c / 3 * (π - 2) * τ := by unfold βT; ring

omit hc in
theorem βπ_div (T π τ : ℝ) : βπ c T π τ = -(4 / 3) * (π ^ 2 - 1 / 5) * τ - T / c * π := by
  unfold βπ; ring

/-- Near `S_B` the system is `x' = τ (y - a - 2)/3 · x`, `y' = κ y + a x` with
`κ = (8a/3) τ - (4/3) τ y - x`. -/
theorem hasDerivAt_xs_ys (p : (ℝ × ℝ) × Tau) (s : ℝ) (hx : |xs hc p s| ≤ 1)
    (hy : |ys hc p s| ≤ 1) :
    HasDerivAt (xs hc p) (τs hc p s * (ys hc p s - a - 2) / 3 * xs hc p s) s ∧
      HasDerivAt (ys hc p) ((8 * a / 3 * τs hc p s - 4 / 3 * τs hc p s * ys hc p s - xs hc p s) *
        ys hc p s + a * xs hc p s) s := by
  have h := (P hc).hasDerivAt_Φ_fst p s
  have h1 : HasDerivAt (fun s => ((P hc).Φ s p).1.1)
      ((P hc).F (((P hc).Φ s p).1, (P hc).θ s p.2)).1 s := by
    have := hasFDerivAt_fst.comp_hasDerivAt s h
    exact this
  have h2 : HasDerivAt (fun s => ((P hc).Φ s p).1.2)
      ((P hc).F (((P hc).Φ s p).1, (P hc).θ s p.2)).2 s := by
    have := hasFDerivAt_snd.comp_hasDerivAt s h
    exact this
  rw [P_F hc (p := ((P hc).Φ s p).1) hx hy] at h1 h2
  refine ⟨(h1.div_const c).congr_deriv ?_, (h2.add_const a).congr_deriv ?_⟩
  · simp only [fG, xs, ys, τs]
    rw [βT_div]
    ring
  · simp only [fG, xs, ys, τs]
    rw [βπ_div]
    linear_combination (-(4 / 3) * ((P hc).θ s p.2 : ℝ)) * a_sq

theorem continuous_xs (p : (ℝ × ℝ) × Tau) : Continuous (xs hc p) :=
  ((P hc).continuous_Φ_fst p).fst.div_const c

theorem continuous_ys (p : (ℝ × ℝ) × Tau) : Continuous (ys hc p) :=
  ((P hc).continuous_Φ_fst p).snd.add continuous_const

theorem continuous_τs (p : (ℝ × ℝ) × Tau) : Continuous (τs hc p) := (P hc).continuous_θ p.2

/-- The invariant set of the block is `S_B`. -/
theorem sep_of_inv {p : (ℝ × ℝ) × Tau} (hp : p ∈ Inv (P hc).Φ ((eC hc) ⁻¹' (NB ×ˢ univ))) :
    p ∈ SB := by
  have hN : ∀ s, |cξ c ((P hc).Φ s p).1 (τs hc p s)| ≤ 1 ∧
      |cη c ((P hc).Φ s p).1 (τs hc p s)| ≤ 1 := fun s => by
    have h : ∀ j, gB j (cξ c ((P hc).Φ s p).1 (τs hc p s), cη c ((P hc).Φ s p).1 (τs hc p s)) ≤ 0 :=
      (hp s).1
    exact blk_iff.1 h
  have hτ : ∀ s, |τs hc p s| ≤ 1 := fun s => abs_tau _
  have hx : ∀ s, |xs hc p s| ≤ 5 * a * ε := fun s => by
    have := abs_iX_le (q := (cξ c ((P hc).Φ s p).1 (τs hc p s), cη c ((P hc).Φ s p).1 (τs hc p s)))
      (hN s).1 (hN s).2 (hτ s)
    rwa [iX_c] at this
  have hy : ∀ s, |ys hc p s| ≤ ε := fun s => by
    have := abs_iY_le (q := (cξ c ((P hc).Φ s p).1 (τs hc p s), cη c ((P hc).Φ s p).1 (τs hc p s)))
      (hN s).1 (hN s).2
    rwa [iY_c] at this
  have ha1 := a_lt
  have ha2 := a_gt
  have hx' : ∀ s, -(5 * a / 20) ≤ xs hc p s ∧ xs hc p s ≤ 5 * a / 20 := fun s => by
    have := abs_le.1 (hx s); simp only [ε] at this; constructor <;> linarith [this.1, this.2]
  have hy' : ∀ s, -(1 / 20) ≤ ys hc p s ∧ ys hc p s ≤ 1 / 20 := fun s => by
    have := abs_le.1 (hy s); simp only [ε] at this; exact this
  have hx1 : ∀ s, |xs hc p s| ≤ 1 := fun s =>
    abs_le.2 ⟨by linarith [(hx' s).1], by linarith [(hx' s).2]⟩
  have hy1 : ∀ s, |ys hc p s| ≤ 1 := fun s =>
    abs_le.2 ⟨by linarith [(hy' s).1], by linarith [(hy' s).2]⟩
  have hd := fun s => hasDerivAt_xs_ys hc p s (hx1 s) (hy1 s)
  have hcx := continuous_xs hc p
  have hcy := continuous_ys hc p
  have hcτ := continuous_τs hc p
  have hch : Continuous fun s => τs hc p s * (ys hc p s - a - 2) / 3 := by fun_prop
  have hcκ : Continuous fun s => 8 * a / 3 * τs hc p s - 4 / 3 * τs hc p s * ys hc p s - xs hc p s := by
    fun_prop
  have hfix : ∀ b : ℝ, (p.2 : ℝ) = b → (b = 1 ∨ b = -1) → ∀ s, τs hc p s = b := fun b hb hb' s => by
    unfold τs
    rw [(P hc).isHeight_θ.fix p.2 (hb ▸ hb') s, hb]
  have key : xs hc p 0 = 0 ∧ ys hc p 0 = 0 := by
    by_cases h1 : (p.2 : ℝ) = 1
    · have hτ1 := hfix 1 h1 (Or.inl rfl)
      have hx0 := lin_zero_of_le (c := 1 / 2) (B := 1)
        (h := fun s => τs hc p s * (ys hc p s - a - 2) / 3) (by norm_num) (fun s => (hd s).1) hch hx1
        (fun s => by simp only [hτ1]; linarith [(hy' s).2]) 0
      refine ⟨hx0, lin_zero_of_ge (c := 1 / 2) (B := 1)
        (h := fun s => 8 * a / 3 * τs hc p s - 4 / 3 * τs hc p s * ys hc p s - xs hc p s)
        (by norm_num) (fun s => (hd s).2.congr_deriv ?_) hcκ hy1
        (fun s => by simp only [hτ1]; linarith [(hy' s).2, (hx' s).2]) 0⟩
      have := lin_zero_of_le (c := 1 / 2) (B := 1)
        (h := fun s => τs hc p s * (ys hc p s - a - 2) / 3) (by norm_num) (fun s => (hd s).1) hch hx1
        (fun s => by simp only [hτ1]; linarith [(hy' s).2]) s
      rw [this]; ring
    by_cases h2 : (p.2 : ℝ) = -1
    · have hτ1 := hfix (-1) h2 (Or.inr rfl)
      have hxz : ∀ s, xs hc p s = 0 := lin_zero_of_ge (c := 1 / 2) (B := 1)
        (h := fun s => τs hc p s * (ys hc p s - a - 2) / 3) (by norm_num) (fun s => (hd s).1) hch hx1
        (fun s => by simp only [hτ1]; linarith [(hy' s).2])
      refine ⟨hxz 0, lin_zero_of_le (c := 1 / 2) (B := 1)
        (h := fun s => 8 * a / 3 * τs hc p s - 4 / 3 * τs hc p s * ys hc p s - xs hc p s)
        (by norm_num) (fun s => (hd s).2.congr_deriv (by rw [hxz s]; ring)) hcκ hy1
        (fun s => by simp only [hτ1]; linarith [(hy' s).2, (hx' s).1]) 0⟩
    have hlow : -1 < (p.2 : ℝ) := lt_of_le_of_ne p.2.2.1 (Ne.symm h2)
    have hhigh : (p.2 : ℝ) < 1 := lt_of_le_of_ne p.2.2.2 h1
    obtain ⟨T₁, hT₁⟩ := base_tendsto_top (P hc).isHeight_θ hlow (by norm_num : (0 : ℝ) < 1 / 2)
    obtain ⟨T₂, hT₂⟩ := base_tendsto_bot (P hc).isHeight_θ hhigh (by norm_num : (0 : ℝ) < 1 / 2)
    refine tri_zero (a := a) (c := 1 / 4) (B := 1) (T := max T₁ (-T₂)) a_pos (by norm_num)
      (h := fun s => τs hc p s * (ys hc p s - a - 2) / 3)
      (κ := fun s => 8 * a / 3 * τs hc p s - 4 / 3 * τs hc p s * ys hc p s - xs hc p s)
      (fun s => (hd s).1) hch (fun s => (hd s).2) hcκ hy1 ?_ ?_ 0
    · intro t ht
      have hτt : 1 / 2 < τs hc p t := by
        have := hT₁ t ((le_max_left _ _).trans ht); unfold τs; linarith
      have hτt' : τs hc p t ≤ 1 := (abs_le.1 (hτ t)).2
      have := hy' t; have := hx' t
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ τs hc p t) (by linarith : (0 : ℝ) ≤ ys hc p t + 1 / 20),
        mul_nonneg (by linarith : (0 : ℝ) ≤ τs hc p t - 1 / 2) a_pos.le]
    · intro t ht
      have hτt : τs hc p t < -(1 / 2) := by
        have := hT₂ t (by linarith [le_max_right T₁ (-T₂)]); unfold τs; linarith
      have hτt' : -1 ≤ τs hc p t := (abs_le.1 (hτ t)).1
      have := hy' t; have := hx' t
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -τs hc p t) (by linarith : (0 : ℝ) ≤ 1 / 20 - ys hc p t),
        mul_nonneg (by linarith : (0 : ℝ) ≤ -(1 / 2) - τs hc p t) a_pos.le]
  obtain ⟨k1, k2⟩ := key
  simp only [xs, ys, Flow.map_zero_apply, div_eq_zero_iff, hc, or_false] at k1 k2
  exact Prod.ext k1 (eq_neg_of_add_eq_zero_left k2)

theorem inv_sep : Inv (P hc).Φ ((eC hc) ⁻¹' (NB ×ˢ univ)) = SB := by
  ext p
  refine ⟨sep_of_inv hc, fun hp t => ⟨?_, mem_univ _⟩⟩
  obtain ⟨q, τ₀⟩ := p
  simp only [SB, mem_ofPred_eq] at hp
  subst hp
  show (cξ c ((P hc).Φ t (((0 : ℝ), -a), τ₀)).1 _, cη c ((P hc).Φ t (((0 : ℝ), -a), τ₀)).1 _) ∈ NB
  rw [Φ_SB hc τ₀ t]
  simp [NB, blk_iff, cξ, cη]

/-! ### The index -/

noncomputable def e1 : ℝ ≃ₜ EuclideanSpace ℝ (Fin 1) :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).toHomeomorph.symm

theorem norm_e1 (r : ℝ) : ‖e1 r‖ = |r| := by
  simp [e1, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]

/-- The block coordinates as the saddle coordinates `ℝ¹ × ℝ¹`. -/
noncomputable def σB : ℝ × ℝ ≃ₜ SaddleSpace 1 1 := e1.prodCongr e1

theorem σB_N : σB ⁻¹' boxN 1 1 = NB := by
  ext q
  simp [σB, boxN, norm_e1, NB, blk_iff]

theorem σB_L : σB ⁻¹' boxL 1 1 = LB := by
  rw [LB_eq]
  ext q
  simp [σB, boxL, norm_e1]

/-- The index space of the block is the circle. -/
noncomputable def idxB :
    PointedHomotopyEquiv (IndexSpace NB LB) (Sphere 1) (IndexSpace.pt NB LB) (Sphere.pt 1) := by
  rw [← σB_N, ← σB_L]
  exact (IndexSpace.preimageEquiv σB _ _).trans (boxEquiv 1 1)

theorem hasIndex_sphere_of_block {α : Type*} [TopologicalSpace α] {ϕ : Flow ℝ α} {S : Set α}
    (h : HasIndex ϕ S (IndexSpace NB LB) (IndexSpace.pt NB LB)) :
    HasIndex ϕ S (Sphere 1) (Sphere.pt 1) := by
  obtain ⟨N', L', hP, ⟨f⟩⟩ := h
  exact ⟨N', L', hP, ⟨f.trans idxB⟩⟩

theorem fiber_SB (b : Tau) : {x | (x, b) ∈ SB} = {((0 : ℝ), -a)} := by
  ext x; simp [SB]

/-- An additive bijection of `ℤ` is `±1`. -/
theorem int_bij_pm (g : ℤ →ₗ[ℤ] ℤ) (hg : Bijective g) : (∀ n, g n = n) ∨ ∀ n, g n = -n := by
  have hn : ∀ n : ℤ, g n = n * g 1 := fun n => by
    conv_lhs => rw [← mul_one n, ← smul_eq_mul, map_smul]
    rfl
  obtain ⟨m, hm⟩ := hg.2 1
  rw [hn, mul_comm] at hm
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hm with h | h
  · exact Or.inl fun n => by rw [hn, h, mul_one]
  · exact Or.inr fun n => by rw [hn, h, mul_neg_one]

/-- Corollary `cor:gubserB`(i). For every `c ≠ 0` the block `e⁻¹(N × [-1, 1])` isolates
`S_B = {T = 0, π = -1/√5}`, whose ends `K_± = {(0, -1/√5)}` have homology index `Λ[1]`. The
double `S_B♮` has trivial index, and the transport `Ψ : CH_*(K_-) → CH_*(K_+)` is an
isomorphism. -/
theorem cor_gubserB_i (K : Type) [Ring K] :
    IsIsolatingNbhd (P hc).Φ ((eC hc) ⁻¹' (NB ×ˢ univ)) ∧
      Inv (P hc).Φ ((eC hc) ⁻¹' (NB ×ˢ univ)) = SB ∧
      (∀ b : Tau, {x | (x, b) ∈ SB} = {((0 : ℝ), -a)}) ∧
      ∃ (hSn : IsIsolatedInvariantSet (dblΦ (P hc).isSkew_Φ (P hc).isHeight_θ) (snat SB))
        (hKp : IsIsolatedInvariantSet (fiberFlow (P hc).isSkew_Φ Tau.top
          (base_top (P hc).isHeight_θ)) {x | (x, Tau.top) ∈ SB})
        (hKm : IsIsolatedInvariantSet (fiberFlow (P hc).isSkew_Φ Tau.bot
          (base_bot (P hc).isHeight_θ)) {x | (x, Tau.bot) ∈ SB})
        (Ψ : ∀ k, homologyIndex K _ hKm k →ₗ[K] homologyIndex K _ hKp k)
        (i : ∀ k, homologyIndex K _ hKp k →ₗ[K] homologyIndex K _ hSn k)
        (p : ∀ k, homologyIndex K _ hSn (k + 1) →ₗ[K] homologyIndex K _ hKm k),
        (∀ k, Exact (Ψ k) (i k)) ∧ (∀ k, Exact (i (k + 1)) (p k)) ∧
        (∀ k, Exact (p k) (Ψ k)) ∧ (∀ k, Subsingleton (homologyIndex K _ hSn k)) ∧
        (∀ k, Bijective (Ψ k)) ∧
        Nonempty (homologyIndex K _ hKp 1 ≃ₗ[K] K) ∧
        (∀ n, n ≠ 1 → Subsingleton (homologyIndex K _ hKp n)) ∧
        Nonempty (homologyIndex K _ hKm 1 ≃ₗ[K] K) ∧
        (∀ n, n ≠ 1 → Subsingleton (homologyIndex K _ hKm n)) := by
  have hB := isUniformBlock_sep hc
  have hci := conj_index (P hc).isSkew_Φ (eC hc) (eC_snd hc) (P hc).isHeight_θ hB
  have hp := (hasIndex_sphere_of_block hci.2.1).homologyIndex_sphere' K
  have hm := (hasIndex_sphere_of_block hci.2.2).homologyIndex_sphere' K
  refine ⟨hci.1, inv_sep hc, fiber_SB, ?_⟩
  rw [← inv_sep hc]
  obtain ⟨hSn, hKp, hKm, Ψ, i, p, h1, h2, h3, h4, h5⟩ :=
    rate_transport_conj (P hc).isSkew_Φ (eC hc) (eC_snd hc) (P hc).isHeight_θ K hB
  exact ⟨hSn, hKp, hKm, Ψ, i, p, h1, h2, h3, h4, h5, hp.1, hp.2, hm.1, hm.2⟩

/-- Corollary `cor:gubserB`(i) over `ℤ`: in the generators `CH_1(K_±) ≅ ℤ`, `Ψ_1 = ±1`. -/
theorem cor_gubserB_i_int :
    ∃ (hKp : IsIsolatedInvariantSet (fiberFlow (P hc).isSkew_Φ Tau.top
          (base_top (P hc).isHeight_θ)) {x | (x, Tau.top) ∈ SB})
      (hKm : IsIsolatedInvariantSet (fiberFlow (P hc).isSkew_Φ Tau.bot
          (base_bot (P hc).isHeight_θ)) {x | (x, Tau.bot) ∈ SB})
      (Ψ : ∀ k, homologyIndex ℤ _ hKm k →ₗ[ℤ] homologyIndex ℤ _ hKp k)
      (eP : homologyIndex ℤ _ hKp 1 ≃ₗ[ℤ] ℤ) (eM : homologyIndex ℤ _ hKm 1 ≃ₗ[ℤ] ℤ),
      (∀ k, Bijective (Ψ k)) ∧
        ((∀ n, eP (Ψ 1 (eM.symm n)) = n) ∨ ∀ n, eP (Ψ 1 (eM.symm n)) = -n) := by
  obtain ⟨-, -, -, -, hKp, hKm, Ψ, -, -, -, -, -, -, h5, ⟨eP⟩, -, ⟨eM⟩, -⟩ := cor_gubserB_i hc ℤ
  refine ⟨hKp, hKm, Ψ, eP, eM, h5, int_bij_pm (eP.toLinearMap ∘ₗ Ψ 1 ∘ₗ eM.symm.toLinearMap) ?_⟩
  exact eP.bijective.comp ((h5 1).comp eM.symm.bijective)

/-- Corollary `cor:gubserB`(ii). `CH_*(S_B) ≅ Λ[1]`, and the Morse sets `K_+ × {0}` and
`K_- × {1}` of `S_B♮` have homology index `Λ[1]` and `Λ[2]`. -/
theorem cor_gubserB_ii (K : Type) [Ring K] :
    ∃ hS : IsIsolatedInvariantSet (P hc).Φ SB,
      (Nonempty (homologyIndex K _ hS 1 ≃ₗ[K] K) ∧
        ∀ n, n ≠ 1 → Subsingleton (homologyIndex K _ hS n)) ∧
      IsAttractorRepellerPair (dblΦ (P hc).isSkew_Φ (P hc).isHeight_θ) (snat SB)
        ({x | (x, Tau.top) ∈ SB} ×ˢ {Dbl.zero}) ({x | (x, Tau.bot) ∈ SB} ×ˢ {Dbl.one}) ∧
      ∃ (hA : IsIsolatedInvariantSet (dblΦ (P hc).isSkew_Φ (P hc).isHeight_θ)
          ({x | (x, Tau.top) ∈ SB} ×ˢ {Dbl.zero}))
        (hR : IsIsolatedInvariantSet (dblΦ (P hc).isSkew_Φ (P hc).isHeight_θ)
          ({x | (x, Tau.bot) ∈ SB} ×ˢ {Dbl.one})),
        (Nonempty (homologyIndex K _ hA 1 ≃ₗ[K] K) ∧
          ∀ n, n ≠ 1 → Subsingleton (homologyIndex K _ hA n)) ∧
        (Nonempty (homologyIndex K _ hR 2 ≃ₗ[K] K) ∧
          ∀ n, n ≠ 2 → Subsingleton (homologyIndex K _ hR n)) := by
  obtain ⟨hN, hInv, -, -, hKp, hKm, -, -, -, -, -, -, -, -, hp1, hp2, hm1, hm2⟩ :=
    cor_gubserB_i hc K
  have hS : IsIsolatedInvariantSet (P hc).Φ SB := ⟨_, hN, hInv⟩
  obtain ⟨-, hK, hSK⟩ := slab_index (P hc).isSkew_Φ (P hc).isHeight_θ K hS
  obtain ⟨-, hAR⟩ := snat_attractorRepeller (P hc).isSkew_Φ (P hc).isHeight_θ hS
  have eA := fun k => (snat_attractor_index (P hc).isSkew_Φ (P hc).isHeight_θ K hS hAR.isolated_A
    hKp k).some
  have eR := fun k => (snat_repeller_index (P hc).isSkew_Φ (P hc).isHeight_θ K hS hAR.isolated_R
    hKm k).some
  have hR0 := snat_repeller_zero (P hc).isSkew_Φ (P hc).isHeight_θ K hS hAR.isolated_R
  refine ⟨hS, ⟨⟨(hSK 1).some.symm.trans hp1.some⟩, fun n hn => ?_⟩, hAR, hAR.isolated_A,
    hAR.isolated_R, ⟨⟨(eA 1).trans hp1.some⟩, fun n hn => ?_⟩, ⟨⟨(eR 1).trans hm1.some⟩,
      fun n hn => ?_⟩⟩
  · have := hp2 n hn
    exact (hSK n).some.symm.toEquiv.subsingleton
  · have := hp2 n hn
    exact (eA n).toEquiv.subsingleton
  · rcases n with _ | k
    · exact hR0
    · have := hm2 k (by omega)
      exact (eR k).toEquiv.subsingleton

/-! ### Persistence -/

/-- Corollary `cor:gubserB`(iii). For every skew-product ODE `Q` that is `1/200`-close to the
Gubser system on the block, in the sense of `IsClose`, the conclusions of part (i) persist for
`S_Q = Inv(e⁻¹(N × [-1, 1]))`, which lies in the block around `S_B`, and over a nontrivial ring some
orbit of `S_Q` with `-1 < τ < 1` runs from `K_-` to `K_+`. -/
theorem cor_gubserB_iii (K : Type) [Ring K] (Q : SkewODE (ℝ × ℝ)) {η : ℝ} (hη : η ≤ 1 / 200)
    (hQ : IsClose c Q η) :
    IsIsolatingNbhd Q.Φ ((eC hc) ⁻¹' (NB ×ˢ univ)) ∧
      ∃ (hSn : IsIsolatedInvariantSet (dblΦ Q.isSkew_Φ Q.isHeight_θ)
          (snat (Inv Q.Φ ((eC hc) ⁻¹' (NB ×ˢ univ)))))
        (hKp : IsIsolatedInvariantSet (fiberFlow Q.isSkew_Φ Tau.top (base_top Q.isHeight_θ))
          {x | (x, Tau.top) ∈ Inv Q.Φ ((eC hc) ⁻¹' (NB ×ˢ univ))})
        (hKm : IsIsolatedInvariantSet (fiberFlow Q.isSkew_Φ Tau.bot (base_bot Q.isHeight_θ))
          {x | (x, Tau.bot) ∈ Inv Q.Φ ((eC hc) ⁻¹' (NB ×ˢ univ))})
        (Ψ : ∀ k, homologyIndex K _ hKm k →ₗ[K] homologyIndex K _ hKp k)
        (i : ∀ k, homologyIndex K _ hKp k →ₗ[K] homologyIndex K _ hSn k)
        (p : ∀ k, homologyIndex K _ hSn (k + 1) →ₗ[K] homologyIndex K _ hKm k),
        (∀ k, Exact (Ψ k) (i k)) ∧ (∀ k, Exact (i (k + 1)) (p k)) ∧
        (∀ k, Exact (p k) (Ψ k)) ∧ (∀ k, Subsingleton (homologyIndex K _ hSn k)) ∧
        (∀ k, Bijective (Ψ k)) ∧
        Nonempty (homologyIndex K _ hKp 1 ≃ₗ[K] K) ∧
        (∀ n, n ≠ 1 → Subsingleton (homologyIndex K _ hKp n)) ∧
        Nonempty (homologyIndex K _ hKm 1 ≃ₗ[K] K) ∧
        (∀ n, n ≠ 1 → Subsingleton (homologyIndex K _ hKm n)) ∧
        (Nontrivial K → ∃ q ∈ Inv Q.Φ ((eC hc) ⁻¹' (NB ×ˢ univ)), (q.2 : ℝ) ∈ Ioo (-1) 1 ∧
          omegaLim Q.Φ q ⊆ Inv Q.Φ ((eC hc) ⁻¹' (NB ×ˢ univ)) ∩ (fun q => (q.2 : ℝ)) ⁻¹' {1} ∧
          alphaLim Q.Φ q ⊆ Inv Q.Φ ((eC hc) ⁻¹' (NB ×ˢ univ)) ∩ (fun q => (q.2 : ℝ)) ⁻¹' {-1}) :=
  moving_saddle Q.isSkew_Φ (eC hc) (eC_snd hc) Q.isHeight_θ K (isUniformBlock_pert hc Q hη hQ) idxB

/-! ### Transversality -/

omit hc in
/-- Proposition `prop:transversal`, `ker L = 0`. Along any base orbit with `τ ≥ 1/2` for large
`t` and `τ ≤ -1/2` for large `-t`, every solution of the linearization
`δT' = -k τ δT`, `δπ' = (8a/3) τ δπ + (a/c) δT`, `k = (2 + a)/3`, with `δπ` bounded is zero. -/
theorem prop_transversal_ker (hc : c ≠ 0) {τ δT δπ : ℝ → ℝ} (hτc : Continuous τ) {T₀ : ℝ}
    (hτ1 : ∀ t ≥ T₀, 1 / 2 ≤ τ t) (hτ2 : ∀ t ≤ -T₀, τ t ≤ -(1 / 2))
    (hT : ∀ t, HasDerivAt δT (-((2 + a) / 3) * τ t * δT t) t)
    (hπ : ∀ t, HasDerivAt δπ (8 * a / 3 * τ t * δπ t + a / c * δT t) t)
    {B : ℝ} (hb : ∀ t, |δπ t| ≤ B) (t : ℝ) : δT t = 0 ∧ δπ t = 0 := by
  have ha := a_pos
  have h := tri_zero (x := fun s => δT s / c) (y := δπ) (h := fun s => -((2 + a) / 3) * τ s)
    (κ := fun s => 8 * a / 3 * τ s) (a := a) (c := 4 * a / 3) (B := B) (T := T₀) a_pos
    (by positivity) (fun s => ((hT s).div_const c).congr_deriv (by ring)) (by fun_prop)
    (fun s => (hπ s).congr_deriv (by ring)) (by fun_prop) hb
    (fun s hs => by have := hτ1 s hs; nlinarith) (fun s hs => by have := hτ2 s hs; nlinarith) t
  exact ⟨by simpa [hc] using h.1, h.2⟩

omit hc in
/-- `ker L = 0` along the separatrix `((0, -a), θ_t b)`, `-1 < b < 1`, for any height flow `θ`. -/
theorem prop_transversal (hc : c ≠ 0) {θ : Flow ℝ Tau} (hθ : IsHeight θ (fun b => (b : ℝ)))
    {b : Tau} (hb1 : -1 < (b : ℝ)) (hb2 : (b : ℝ) < 1) {δT δπ : ℝ → ℝ}
    (hT : ∀ t, HasDerivAt δT (-((2 + a) / 3) * (θ t b : ℝ) * δT t) t)
    (hπ : ∀ t, HasDerivAt δπ (8 * a / 3 * (θ t b : ℝ) * δπ t + a / c * δT t) t)
    {B : ℝ} (hb : ∀ t, |δπ t| ≤ B) (t : ℝ) : δT t = 0 ∧ δπ t = 0 := by
  obtain ⟨T₁, hT₁⟩ := base_tendsto_top hθ hb1 (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨T₂, hT₂⟩ := base_tendsto_bot hθ hb2 (by norm_num : (0 : ℝ) < 1 / 2)
  refine prop_transversal_ker hc (τ := fun t => (θ t b : ℝ)) (T₀ := max T₁ (-T₂))
    (continuous_subtype_val.comp (θ.continuous continuous_id continuous_const))
    (fun s hs => ?_) (fun s hs => ?_) hT hπ hb t
  · have := hT₁ s ((le_max_left _ _).trans hs); linarith
  · have := hT₂ s (by linarith [le_max_right T₁ (-T₂)]); linarith

/-! ### The limit `c = ∞` -/

/-- The Gubser fiber field at `c = ∞`, where the coupling `-T π / c` drops out. -/
noncomputable def f0 (p : ℝ × ℝ) (s : ℝ) : ℝ × ℝ :=
  (βT p.1 p.2 s, -(4 / 3) * (p.2 ^ 2 - 1 / 5) * s)

/-- The field at `c = ∞`, cut off outside `‖(T, π + a)‖ ≤ 2`, `|s| ≤ 2`. -/
noncomputable def A0 (q : (ℝ × ℝ) × ℝ) : ℝ × ℝ :=
  (bumpG (q.1.1, q.1.2 + a) * bumpS q.2) • f0 q.1 q.2

theorem contDiff_A0 : ContDiff ℝ 1 A0 := by
  have h1 : ContDiff ℝ 1 fun q : (ℝ × ℝ) × ℝ => bumpG (q.1.1, q.1.2 + a) :=
    bumpG.contDiff.comp (by fun_prop)
  have h2 : ContDiff ℝ 1 fun q : (ℝ × ℝ) × ℝ => bumpS q.2 := bumpS.contDiff.comp contDiff_snd
  have h3 : ContDiff ℝ 1 fun q : (ℝ × ℝ) × ℝ => f0 q.1 q.2 := by unfold f0 βT; fun_prop
  exact (h1.mul h2).smul h3

theorem hasCompactSupport_A0 : HasCompactSupport A0 := by
  have hK : IsCompact ((fun u : (ℝ × ℝ) × ℝ => ((u.1.1, u.1.2 - a), u.2)) ''
      (Metric.closedBall (0 : ℝ × ℝ) 2 ×ˢ Metric.closedBall (0 : ℝ) 2)) :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image (by fun_prop)
  refine HasCompactSupport.intro hK fun q hq => ?_
  by_contra hA
  apply hq
  have hG : bumpG (q.1.1, q.1.2 + a) ≠ 0 := fun h => hA (by simp [A0, h])
  have hS : bumpS q.2 ≠ 0 := fun h => hA (by simp [A0, h])
  rw [← mem_support, bumpG.support_eq] at hG
  rw [← mem_support, bumpS.support_eq] at hS
  exact ⟨((q.1.1, q.1.2 + a), q.2),
    ⟨Metric.ball_subset_closedBall hG, Metric.ball_subset_closedBall hS⟩, by simp⟩

/-- The cut-off Gubser system at `c = ∞`. -/
noncomputable def P0 : SkewODE (ℝ × ℝ) :=
  SkewODE.ofSmooth A0 contDiff_A0 hasCompactSupport_A0 g0 2 lip_g0 (by simp [g0]) (by simp [g0])
    (fun τ hτ => by simp only [g0]; nlinarith [hτ.1, hτ.2])

theorem P0_F {T : ℝ} (hT : |T| ≤ 1) {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    P0.F ((T, -a), r) = (T / 3 * (-a - 2) * r, 0) := by
  show A0 ((T, -a), clamp r) = _
  rw [clamp_of_mem hr]
  simp only [A0]
  rw [bumpG.one_of_mem_closedBall, bumpS.one_of_mem_closedBall, one_mul, one_smul]
  · simp [f0, βT, a_sq]
  · show dist r 0 ≤ 1
    rw [dist_zero_right, Real.norm_eq_abs]
    exact abs_le.2 hr
  · show dist ((T, -a + a) : ℝ × ℝ) 0 ≤ 1
    rw [dist_zero_right, Prod.norm_def]
    simp [hT]

theorem P0_g {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) : P0.g r = 1 - r ^ 2 := by
  show g0 (clamp r) = _
  rw [clamp_of_mem hr]
  rfl

theorem hasDerivAt_tanh (s : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh s ^ 2) s := by
  have h := (Real.hasDerivAt_sinh s).div (Real.hasDerivAt_cosh s) (Real.cosh_pos s).ne'
  have e : Real.tanh = fun x => Real.sinh x / Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
  rw [e]
  refine h.congr_deriv ?_
  have := (Real.cosh_pos s).ne'
  field_simp

theorem hasDerivAt_Tmode (A s : ℝ) :
    HasDerivAt (fun s => A * Real.cosh s ^ (-((2 + a) / 3)))
      (A * Real.cosh s ^ (-((2 + a) / 3)) / 3 * (-a - 2) * Real.tanh s) s := by
  have h := ((Real.hasDerivAt_cosh s).rpow_const (p := -((2 + a) / 3))
    (Or.inl (Real.cosh_pos s).ne')).const_mul A
  refine h.congr_deriv ?_
  rw [Real.rpow_sub_one (Real.cosh_pos s).ne', Real.tanh_eq_sinh_div_cosh]
  have := (Real.cosh_pos s).ne'
  field_simp
  ring

theorem abs_Tmode_le (A s : ℝ) : |A * Real.cosh s ^ (-((2 + a) / 3))| ≤ |A| := by
  have ha := a_pos
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Real.cosh_pos s).le _)]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (Real.rpow_le_one_of_one_le_of_nonpos (Real.one_le_cosh s) (by linarith))

/-- At `c = ∞` the `T`-mode `(A cosh^{-k} t, -a, tanh t)` is an orbit. -/
theorem P0_Tmode {A : ℝ} (hA : |A| ≤ 1) (t : ℝ) :
    P0.Ψ t ((A, -a), 0) = ((A * Real.cosh t ^ (-((2 + a) / 3)), -a), Real.tanh t) := by
  have hγ : IsSol P0.V fun s => ((A * Real.cosh s ^ (-((2 + a) / 3)), -a), Real.tanh s) :=
    fun s => by
      have h2 := ((hasDerivAt_Tmode A s).prodMk (hasDerivAt_const s (-a))).prodMk
        (hasDerivAt_tanh s)
      convert h2 using 1
      have hr : Real.tanh s ∈ Icc (-1 : ℝ) 1 :=
        ⟨(Real.neg_one_lt_tanh s).le, (Real.tanh_lt_one s).le⟩
      simp only [SkewODE.V, P0_F ((abs_Tmode_le A s).trans hA) hr, P0_g hr]
  have := flowOf_eq_of_isSol P0.exists_lipschitz_V.choose_spec P0.exists_bound_V.choose_spec hγ 0 t
  simp only [Real.cosh_zero, Real.one_rpow, mul_one, Real.tanh_zero, add_zero] at this
  exact this

/-- Corollary `cor:gubserB`(iv). At `c = ∞` the separatrix `S_B` is not isolated, since every
neighborhood of it contains the orbits `(A cosh^{-k} t, -a, tanh t)` with small `A ≠ 0`. -/
theorem cor_gubserB_iv : ¬ IsIsolatedInvariantSet P0.Φ SB := by
  rintro ⟨N, ⟨-, hNi⟩, hInv⟩
  have hSBc : IsCompact SB := by
    have : SB = {((0 : ℝ), -a)} ×ˢ (univ : Set Tau) := by ext p; simp [SB]
    rw [this]
    exact isCompact_singleton.prod isCompact_univ
  obtain ⟨δ, hδ, hth⟩ :=
    hSBc.exists_thickening_subset_open isOpen_interior (by rw [← hInv]; exact hNi)
  set A := min (δ / 2) 1 with hAdef
  have hA0 : 0 < A := lt_min (half_pos hδ) one_pos
  have hA1 : |A| ≤ 1 := by rw [abs_of_pos hA0]; exact min_le_right _ _
  have hAδ : A < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  set p0 : (ℝ × ℝ) × Tau := ((A, -a), ⟨0, by norm_num, by norm_num⟩) with hp0def
  have hp0 : p0 ∈ Inv P0.Φ N := fun t => by
    apply interior_subset
    apply hth
    rw [Metric.mem_thickening_iff]
    refine ⟨(((0 : ℝ), -a), P0.θ t p0.2), rfl, ?_⟩
    have h1 : (P0.Φ t p0).1 = (A * Real.cosh t ^ (-((2 + a) / 3)), -a) := by
      show (P0.Ψ t ((A, -a), (0 : ℝ))).1 = _
      rw [P0_Tmode hA1 t]
    rw [Prod.dist_eq, h1]
    refine max_lt ?_ (by rw [show (P0.Φ t p0).2 = P0.θ t p0.2 from rfl, dist_self]; exact hδ)
    rw [Prod.dist_eq]
    refine max_lt ?_ (by rw [dist_self]; exact hδ)
    rw [Real.dist_eq, sub_zero]
    exact (abs_Tmode_le A t).trans_lt (by rw [abs_of_pos hA0]; exact hAδ)
  rw [hInv] at hp0
  have : A = 0 := congrArg Prod.fst (hp0 : p0.1 = (0, -a))
  linarith

end ConleyCheck.Gubser.Sep
