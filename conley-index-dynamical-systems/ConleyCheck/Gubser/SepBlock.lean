import ConleyCheck.Gubser.Separatrix

/-!
# The moving block of the separatrix

Lemma `lem:gubser-block`. In the coordinates `(ξ, η)` of `Gubser/Separatrix.lean`, the derivatives
of `ξ` and `η` along the Gubser system are `Dxi`, `Deta` (`DQξ_P`, `DQη_P`), and they have the form
`eq:xieta-dot`,
`ξ' = (1 + c₁ τ + c₂ τ²) ξ + c₂ τ (1 + τ) η + R_ξ`,
`η' = -(1 - c₁ τ + c₂ τ²) η + c₂ τ (1 - τ) ξ + R_η`, with `c₁ = 7√5/30 - 1/3`,
`c₂ = 3√5/10 - 2/3` and the quadratic remainders `Rξ`, `Rη`
(`Dxi_eq`, `Deta_eq`, `lem_gubser_block_deriv`). On `N_B = [-1, 1]²` and for `|τ| ≤ 1`:

* `|R_ξ|, |R_η| ≤ 29/120` (`abs_Rξ_le`, `abs_Rη_le`);
* (a) `±ξ' > 1/2` on the faces `ξ = ±1` and `±η' < -1/2` on the faces `η = ±1`
  (`lem_gubser_block_a`);
* (b) the cone estimate `ξ ξ' - η η' ≥ (3/5)(ξ² + η²)` (`lem_gubser_block_b`).

The last assertion of the lemma, that only `S_B = {ξ = η = 0}` stays in `N_B`, is `inv_sep`, and
its fibers over `τ = ±1`, which are the invariant sets of the frozen flows `f_±`, are
`{(0, -a)}` (`lem_gubser_block_inv`). Lean proves it from the triangular structure of the system in
the coordinates `(T/c, π + a)`, not from the cone estimate (b).
-/

namespace ConleyCheck.Gubser.Sep

open Set Function ConleyCheck.ODE ConleyCheck.Conley

/-! ### Constants -/

theorem sqrt5_eq : Real.sqrt 5 = 5 * a := by unfold a; ring

theorem sqrt5_gt : 2235 / 1000 < Real.sqrt 5 := by rw [sqrt5_eq]; linarith [a_gt]

theorem sqrt5_lt : Real.sqrt 5 < 22365 / 10000 := by rw [sqrt5_eq]; linarith [a_lt]

/-- `c₁ = 7√5/30 - 1/3`. -/
noncomputable def c₁ : ℝ := 7 * Real.sqrt 5 / 30 - 1 / 3

/-- `c₂ = 3√5/10 - 2/3`. -/
noncomputable def c₂ : ℝ := 3 * Real.sqrt 5 / 10 - 2 / 3

theorem c₁_pos : 0 < c₁ := by unfold c₁; linarith [sqrt5_gt]

theorem c₁_lt : c₁ < 1 / 5 := by unfold c₁; linarith [sqrt5_lt]

theorem c₂_pos : 0 < c₂ := by unfold c₂; linarith [sqrt5_gt]

theorem c₂_lt : c₂ < 1 / 200 := by unfold c₂; linarith [sqrt5_lt]

/-! ### The identities `eq:xieta-dot` -/

/-- The quadratic remainder `R_ξ`. -/
noncomputable def Rξ (ξ η τ : ℝ) : ℝ :=
  (ξ + η) / 240 * (((3 * Real.sqrt 5 - 5) * τ ^ 2 + (6 * Real.sqrt 5 - 5) * τ + 3 * Real.sqrt 5) * η
    + ((3 * Real.sqrt 5 - 5) * τ ^ 2 - 3 * τ - 3 * Real.sqrt 5) * ξ)

/-- The quadratic remainder `R_η`. -/
noncomputable def Rη (ξ η τ : ℝ) : ℝ :=
  -((ξ + η) / 240 * (((3 * Real.sqrt 5 - 5) * τ ^ 2 + 3 * τ - 3 * Real.sqrt 5) * η
    + ((3 * Real.sqrt 5 - 5) * τ ^ 2 - (6 * Real.sqrt 5 - 5) * τ + 3 * Real.sqrt 5) * ξ))

theorem Dxi_eq (ξ η τ : ℝ) :
    Dxi ξ η τ = (1 + c₁ * τ + c₂ * τ ^ 2) * ξ + c₂ * (τ * (1 + τ)) * η + Rξ ξ η τ := by
  simp only [Dxi, B11, B12, Q1, β₁, δ₁, xt, yt, ε, c₁, c₂, Rξ, sqrt5_eq]
  linear_combination -(τ * (η + ξ) * (η * τ + η + τ * ξ - ξ)) / 48 * a_sq

theorem Deta_eq (ξ η τ : ℝ) :
    Deta ξ η τ = -(1 - c₁ * τ + c₂ * τ ^ 2) * η + c₂ * (τ * (1 - τ)) * ξ + Rη ξ η τ := by
  simp only [Deta, B21, B22, Q2, β₁, δ₁, xt, yt, ε, c₁, c₂, Rη, sqrt5_eq]
  linear_combination (τ * (η + ξ) * (η * τ + η + τ * ξ - ξ)) / 48 * a_sq

variable {c : ℝ} (hc : c ≠ 0)

/-- Lemma `lem:gubser-block`, `eq:xieta-dot`: on the block, the derivatives of `ξ` and `η` along
the compactified Gubser flow. -/
theorem lem_gubser_block_deriv {q : ℝ × ℝ} (h1 : |q.1| ≤ 1) (h2 : |q.2| ≤ 1) (τ : Tau) :
    HasDerivAt (fun t => (conjFlow (P hc).Φ (eC hc) t (q, τ)).1.1)
        ((1 + c₁ * τ + c₂ * (τ : ℝ) ^ 2) * q.1 + c₂ * (τ * (1 + τ)) * q.2 + Rξ q.1 q.2 τ) 0 ∧
      HasDerivAt (fun t => (conjFlow (P hc).Φ (eC hc) t (q, τ)).1.2)
        (-(1 - c₁ * τ + c₂ * (τ : ℝ) ^ 2) * q.2 + c₂ * (τ * (1 - τ)) * q.1 + Rη q.1 q.2 τ) 0 := by
  rw [← Dxi_eq, ← Deta_eq, ← DQξ_P hc h1 h2, ← DQη_P hc h1 h2]
  exact ⟨hasDerivAt_Q_ξ hc _ q τ, hasDerivAt_Q_η hc _ q τ⟩

/-! ### Bounds on the remainders -/

theorem abs_quad_le {p q r τ : ℝ} (hτ : |τ| ≤ 1) : |p * τ ^ 2 + q * τ + r| ≤ |p| + |q| + |r| := by
  have h2 : |τ ^ 2| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hτ
  have e1 : |p * τ ^ 2| ≤ |p| := by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h2
  have e2 : |q * τ| ≤ |q| := by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hτ
  exact (abs_add_three _ _ _).trans (by linarith)

theorem abs_R_le {ξ η u v : ℝ} (hξ : |ξ| ≤ 1) (hη : |η| ≤ 1) (huv : |u| + |v| ≤ 29) :
    |(ξ + η) / 240 * (u * η + v * ξ)| ≤ 29 / 120 := by
  have h1 : |ξ + η| ≤ 2 := (abs_add_le _ _).trans (by linarith)
  have h2 : |u * η + v * ξ| ≤ 29 := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have := mul_le_of_le_one_right (abs_nonneg u) hη
    have := mul_le_of_le_one_right (abs_nonneg v) hξ
    linarith
  rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 240)]
  have := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
  have e : |ξ + η| / 240 * |u * η + v * ξ| = |ξ + η| * |u * η + v * ξ| / 240 := by ring
  rw [e]
  linarith

theorem abs_Rξ_le {ξ η τ : ℝ} (hξ : |ξ| ≤ 1) (hη : |η| ≤ 1) (hτ : |τ| ≤ 1) :
    |Rξ ξ η τ| ≤ 29 / 120 := by
  have hs := sqrt5_gt
  have hu := abs_quad_le (p := 3 * Real.sqrt 5 - 5) (q := 6 * Real.sqrt 5 - 5)
    (r := 3 * Real.sqrt 5) hτ
  have hv := abs_quad_le (p := 3 * Real.sqrt 5 - 5) (q := -3) (r := -(3 * Real.sqrt 5)) hτ
  have hp : |3 * Real.sqrt 5 - 5| = 3 * Real.sqrt 5 - 5 := abs_of_pos (by linarith)
  have hq : |6 * Real.sqrt 5 - 5| = 6 * Real.sqrt 5 - 5 := abs_of_pos (by linarith)
  have hr : |-(3 * Real.sqrt 5)| = 3 * Real.sqrt 5 := by
    rw [abs_neg]; exact abs_of_pos (by linarith)
  have hr' : |3 * Real.sqrt 5| = 3 * Real.sqrt 5 := abs_of_pos (by linarith)
  have h3 : |(-3 : ℝ)| = 3 := by norm_num
  have e : Rξ ξ η τ = (ξ + η) / 240 *
      (((3 * Real.sqrt 5 - 5) * τ ^ 2 + (6 * Real.sqrt 5 - 5) * τ + 3 * Real.sqrt 5) * η
        + ((3 * Real.sqrt 5 - 5) * τ ^ 2 + -3 * τ + -(3 * Real.sqrt 5)) * ξ) := by
    unfold Rξ; ring
  rw [e]
  exact abs_R_le hξ hη (by linarith [sqrt5_lt])

theorem abs_Rη_le {ξ η τ : ℝ} (hξ : |ξ| ≤ 1) (hη : |η| ≤ 1) (hτ : |τ| ≤ 1) :
    |Rη ξ η τ| ≤ 29 / 120 := by
  have hs := sqrt5_gt
  have hu := abs_quad_le (p := 3 * Real.sqrt 5 - 5) (q := 3) (r := -(3 * Real.sqrt 5)) hτ
  have hv := abs_quad_le (p := 3 * Real.sqrt 5 - 5) (q := -(6 * Real.sqrt 5 - 5))
    (r := 3 * Real.sqrt 5) hτ
  have hp : |3 * Real.sqrt 5 - 5| = 3 * Real.sqrt 5 - 5 := abs_of_pos (by linarith)
  have hq : |-(6 * Real.sqrt 5 - 5)| = 6 * Real.sqrt 5 - 5 := by
    rw [abs_neg]; exact abs_of_pos (by linarith)
  have hr : |-(3 * Real.sqrt 5)| = 3 * Real.sqrt 5 := by
    rw [abs_neg]; exact abs_of_pos (by linarith)
  have hr' : |3 * Real.sqrt 5| = 3 * Real.sqrt 5 := abs_of_pos (by linarith)
  have h3 : |(3 : ℝ)| = 3 := by norm_num
  have e : Rη ξ η τ = -((ξ + η) / 240 *
      (((3 * Real.sqrt 5 - 5) * τ ^ 2 + 3 * τ + -(3 * Real.sqrt 5)) * η
        + ((3 * Real.sqrt 5 - 5) * τ ^ 2 + -(6 * Real.sqrt 5 - 5) * τ + 3 * Real.sqrt 5) * ξ)) := by
    unfold Rη; ring
  rw [e, abs_neg]
  exact abs_R_le hξ hη (by linarith [sqrt5_lt])

/-! ### (a) The face inequalities -/

theorem abs_c₁_mul_le {τ : ℝ} (hτ : |τ| ≤ 1) : |c₁ * τ| ≤ c₁ := by
  rw [abs_mul, abs_of_pos c₁_pos]
  exact mul_le_of_le_one_right c₁_pos.le hτ

theorem abs_c₂_mul_le {w u : ℝ} (hw : |w| ≤ 2) (hu : |u| ≤ 1) : |c₂ * w * u| ≤ 2 * c₂ := by
  rw [abs_mul, abs_mul, abs_of_pos c₂_pos]
  calc c₂ * |w| * |u| = c₂ * (|w| * |u|) := by ring
    _ ≤ c₂ * (2 * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hw hu (abs_nonneg _) (by norm_num)) c₂_pos.le
    _ = 2 * c₂ := by ring

theorem abs_tp_le {τ : ℝ} (hτ : |τ| ≤ 1) : |τ * (1 + τ)| ≤ 2 := by
  rw [abs_le] at hτ ⊢; constructor <;> nlinarith

theorem abs_tm_le {τ : ℝ} (hτ : |τ| ≤ 1) : |τ * (1 - τ)| ≤ 2 := by
  rw [abs_le] at hτ ⊢; constructor <;> nlinarith

/-- Lemma `lem:gubser-block`(a). -/
theorem lem_gubser_block_a {ξ η τ : ℝ} (hξ : |ξ| ≤ 1) (hη : |η| ≤ 1) (hτ : |τ| ≤ 1) :
    1 / 2 < Dxi 1 η τ ∧ Dxi (-1) η τ < -(1 / 2) ∧ Deta ξ 1 τ < -(1 / 2) ∧
      1 / 2 < Deta ξ (-1) τ := by
  have h1 := abs_le.1 (abs_c₁_mul_le hτ)
  have h2 : 0 ≤ c₂ * τ ^ 2 := mul_nonneg c₂_pos.le (sq_nonneg τ)
  have hp := abs_le.1 (abs_c₂_mul_le (abs_tp_le hτ) hη)
  have hm := abs_le.1 (abs_c₂_mul_le (abs_tm_le hτ) hξ)
  have r1 := abs_le.1 (abs_Rξ_le (ξ := 1) (by norm_num) hη hτ)
  have r2 := abs_le.1 (abs_Rξ_le (ξ := -1) (by norm_num) hη hτ)
  have r3 := abs_le.1 (abs_Rη_le (η := 1) hξ (by norm_num) hτ)
  have r4 := abs_le.1 (abs_Rη_le (η := -1) hξ (by norm_num) hτ)
  have := c₁_lt
  have := c₂_lt
  rw [Dxi_eq, Dxi_eq, Deta_eq, Deta_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-! ### (b) The cone estimate -/

theorem cone_eq (ξ η τ : ℝ) :
    ξ * Dxi ξ η τ - η * Deta ξ η τ =
      (ξ ^ 2 + η ^ 2) + c₁ * (τ * (ξ ^ 2 - η ^ 2)) + c₂ * τ ^ 2 * (ξ + η) ^ 2 +
        (ξ + η) / 240 * ((3 * Real.sqrt 5 - 5) * τ ^ 2 * (ξ + η) ^ 2
          - 3 * τ * (ξ + η) * (ξ - η) - 3 * Real.sqrt 5 * (ξ - η) ^ 2) := by
  rw [Dxi_eq, Deta_eq]
  unfold Rξ Rη
  ring

theorem abs_cubic_le {ξ η τ : ℝ} (hξ : |ξ| ≤ 1) (hη : |η| ≤ 1) (hτ : |τ| ≤ 1) :
    |(ξ + η) / 240 * ((3 * Real.sqrt 5 - 5) * τ ^ 2 * (ξ + η) ^ 2
      - 3 * τ * (ξ + η) * (ξ - η) - 3 * Real.sqrt 5 * (ξ - η) ^ 2)| ≤ 1 / 7 * (ξ ^ 2 + η ^ 2) := by
  have hs := sqrt5_gt
  have hs' := sqrt5_lt
  have hA : |ξ + η| ≤ 2 := (abs_add_le _ _).trans (by linarith)
  have hp : 0 ≤ 3 * Real.sqrt 5 - 5 := by linarith
  have hτ2 : τ ^ 2 ≤ 1 := by
    rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) hτ
  set A := ξ + η
  set B := ξ - η
  have t1 : |(3 * Real.sqrt 5 - 5) * τ ^ 2 * A ^ 2| ≤ (3 * Real.sqrt 5 - 5) * A ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_left hτ2 hp).trans_eq (mul_one _)) (sq_nonneg A)
  have t2 : |3 * τ * A * B| ≤ 3 / 2 * (A ^ 2 + B ^ 2) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have hAB := two_mul_le_add_sq |A| |B|
    rw [sq_abs, sq_abs] at hAB
    have := mul_le_of_le_one_left (mul_nonneg (abs_nonneg A) (abs_nonneg B)) hτ
    nlinarith [abs_nonneg τ, abs_nonneg A, abs_nonneg B]
  have t3 : |3 * Real.sqrt 5 * B ^ 2| = 3 * Real.sqrt 5 * B ^ 2 :=
    abs_of_nonneg (mul_nonneg (by linarith) (sq_nonneg B))
  have hbr : |(3 * Real.sqrt 5 - 5) * τ ^ 2 * A ^ 2 - 3 * τ * A * B - 3 * Real.sqrt 5 * B ^ 2| ≤
      2 * (3 * Real.sqrt 5 + 3 / 2) * (ξ ^ 2 + η ^ 2) := by
    have hAB : A ^ 2 + B ^ 2 = 2 * (ξ ^ 2 + η ^ 2) := by simp only [A, B]; ring
    have := sq_nonneg A
    have := sq_nonneg B
    have hb : |(3 * Real.sqrt 5 - 5) * τ ^ 2 * A ^ 2 - 3 * τ * A * B - 3 * Real.sqrt 5 * B ^ 2| ≤
        |(3 * Real.sqrt 5 - 5) * τ ^ 2 * A ^ 2| + |3 * τ * A * B| + |3 * Real.sqrt 5 * B ^ 2| :=
      have h := abs_sub ((3 * Real.sqrt 5 - 5) * τ ^ 2 * A ^ 2) (3 * τ * A * B)
      (abs_sub _ _).trans (by linarith)
    have : (3 * Real.sqrt 5 - 5) * A ^ 2 ≤ 3 * Real.sqrt 5 * A ^ 2 := by nlinarith
    nlinarith
  have hS : 0 ≤ ξ ^ 2 + η ^ 2 := by positivity
  rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 240)]
  have hm := mul_le_mul hA hbr (abs_nonneg _) (by norm_num)
  have hK : 2 * (2 * (3 * Real.sqrt 5 + 3 / 2)) ≤ 240 / 7 := by linarith
  have := mul_le_mul_of_nonneg_right hK hS
  have e : |A| / 240 * |(3 * Real.sqrt 5 - 5) * τ ^ 2 * A ^ 2 - 3 * τ * A * B
      - 3 * Real.sqrt 5 * B ^ 2| = |A| * |(3 * Real.sqrt 5 - 5) * τ ^ 2 * A ^ 2 - 3 * τ * A * B
      - 3 * Real.sqrt 5 * B ^ 2| / 240 := by ring
  rw [e]
  nlinarith

/-- Lemma `lem:gubser-block`(b), the cone estimate. -/
theorem lem_gubser_block_b {ξ η τ : ℝ} (hξ : |ξ| ≤ 1) (hη : |η| ≤ 1) (hτ : |τ| ≤ 1) :
    3 / 5 * (ξ ^ 2 + η ^ 2) ≤ ξ * Dxi ξ η τ - η * Deta ξ η τ := by
  rw [cone_eq]
  have hS : 0 ≤ ξ ^ 2 + η ^ 2 := by positivity
  have hτ' := abs_le.1 hτ
  have h1 : -(ξ ^ 2 + η ^ 2) ≤ τ * (ξ ^ 2 - η ^ 2) := by
    have : |τ * (ξ ^ 2 - η ^ 2)| ≤ ξ ^ 2 + η ^ 2 := by
      rw [abs_mul]
      have hd : |ξ ^ 2 - η ^ 2| ≤ ξ ^ 2 + η ^ 2 :=
        abs_le.2 ⟨by nlinarith [sq_nonneg ξ, sq_nonneg η], by nlinarith [sq_nonneg ξ, sq_nonneg η]⟩
      exact (mul_le_mul hτ hd (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    exact (abs_le.1 this).1
  have h2 : c₁ * -(ξ ^ 2 + η ^ 2) ≤ c₁ * (τ * (ξ ^ 2 - η ^ 2)) :=
    mul_le_mul_of_nonneg_left h1 c₁_pos.le
  have h3 : c₁ * (ξ ^ 2 + η ^ 2) ≤ 1 / 5 * (ξ ^ 2 + η ^ 2) :=
    mul_le_mul_of_nonneg_right c₁_lt.le hS
  have h4 : 0 ≤ c₂ * τ ^ 2 * (ξ + η) ^ 2 := by
    have := c₂_pos
    positivity
  have h5 := (abs_le.1 (abs_cubic_le hξ hη hτ)).1
  nlinarith

/-! ### The invariant set -/

/-- Lemma `lem:gubser-block`, last assertion: only `S_B = {ξ = η = 0}` stays in `N_B`, and the
fibers over `τ = ±1` (the invariant sets of `N_B` for the frozen flows `f_±`) are `{(0, -a)}`. -/
theorem lem_gubser_block_inv :
    Inv (P hc).Φ ((eC hc) ⁻¹' (NB ×ˢ univ)) = SB ∧
      ∀ b : Tau, {x | (x, b) ∈ Inv (P hc).Φ ((eC hc) ⁻¹' (NB ×ˢ univ))} = {((0 : ℝ), -a)} := by
  refine ⟨inv_sep hc, fun b => ?_⟩
  rw [inv_sep hc]
  exact fiber_SB b

end ConleyCheck.Gubser.Sep
