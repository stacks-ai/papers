import ConleyCheck.Calculus

/-!
# The one-loop `O(N)`-type model (section `sec:ON`)

The rescaled flow `eq:ONy` is
`y₁' = -(y₁ + 9 y₁² + (N-1) y₂²)`, `y₂' = -(y₂ + 6 y₁ y₂ + (N+2) y₂²)`.

We verify the fixed points and their completeness, the Jacobians, eigenvalues and Morse indices,
the gradient structure of Lemma `lem:ONstructure`(i), the invariant lines of (ii), the boundary
behaviour behind (iii) and (iv), the face inequalities of the isolating block of Proposition
`prop:ON`, the reduced flows of Corollary `cor:ON`(i) and the change of variables to the cubic
anisotropy model.
-/

namespace ConleyCheck.ON

/-- First component of the rescaled vector field `eq:ONy`. -/
def f₁ (N y₁ y₂ : ℝ) : ℝ := -(y₁ + 9 * y₁ ^ 2 + (N - 1) * y₂ ^ 2)

/-- Second component of the rescaled vector field `eq:ONy`. -/
def f₂ (N y₁ y₂ : ℝ) : ℝ := -(y₂ + 6 * y₁ * y₂ + (N + 2) * y₂ ^ 2)

/-! ## Fixed points -/

noncomputable def ptG : ℝ × ℝ := (0, 0)
noncomputable def ptI : ℝ × ℝ := (-1 / 9, 0)
noncomputable def ptC (N : ℝ) : ℝ × ℝ := (-(N - 1) / (9 * N), -1 / (3 * N))
noncomputable def ptH (N : ℝ) : ℝ × ℝ := (-1 / (N + 8), -1 / (N + 8))

/-- `p` is a zero of the vector field. -/
def IsZero (N : ℝ) (p : ℝ × ℝ) : Prop := f₁ N p.1 p.2 = 0 ∧ f₂ N p.1 p.2 = 0

theorem isZero_G (N : ℝ) : IsZero N ptG := by
  simp [IsZero, ptG, f₁, f₂]

theorem isZero_I (N : ℝ) : IsZero N ptI := by
  constructor <;> simp only [ptI, f₁, f₂] <;> ring

theorem isZero_C {N : ℝ} (hN : N ≠ 0) : IsZero N (ptC N) := by
  constructor <;> simp only [ptC, f₁, f₂] <;> field_simp <;> ring

theorem isZero_H {N : ℝ} (hN : N + 8 ≠ 0) : IsZero N (ptH N) := by
  constructor <;> simp only [ptH, f₁, f₂] <;> field_simp <;> ring

/-- "A direct computation shows that these are all the zeros of the vector field." -/
theorem zeros_complete {N y₁ y₂ : ℝ} (hN : 0 < N) (h : IsZero N (y₁, y₂)) :
    (y₁, y₂) = ptG ∨ (y₁, y₂) = ptI ∨ (y₁, y₂) = ptC N ∨ (y₁, y₂) = ptH N := by
  obtain ⟨h1, h2⟩ := h
  simp only [f₁, f₂] at h1 h2
  have h2' : y₂ * (1 + 6 * y₁ + (N + 2) * y₂) = 0 := by linear_combination (-1) * h2
  rcases mul_eq_zero.1 h2' with hy | hL
  · subst hy
    have : y₁ * (1 + 9 * y₁) = 0 := by linear_combination (-1) * h1
    rcases mul_eq_zero.1 this with h0 | h9
    · left; simp [ptG, h0]
    · right; left
      simp only [ptI, Prod.mk.injEq, and_true]
      linarith
  · have hprod : (3 * N * y₂ + 1) * ((N + 8) * y₂ + 1) = 0 := by
      linear_combination (-12) * h1 + (3 * N * y₂ - 18 * y₁ + 6 * y₂ + 1) * hL
    rcases mul_eq_zero.1 hprod with he | he
    · right; right; left
      have hy1 : 9 * N * y₁ + (N - 1) = 0 := by
        linear_combination (3 * N / 2) * hL - ((N + 2) / 2) * he
      simp only [ptC, Prod.mk.injEq]
      constructor
      · rw [eq_div_iff (by positivity)]; linarith
      · rw [eq_div_iff (by positivity)]; linarith
    · right; right; right
      have hy1 : (N + 8) * y₁ + 1 = 0 := by
        linear_combination ((N + 8) / 6) * hL - ((N + 2) / 6) * he
      have h8 : N + 8 ≠ 0 := by positivity
      simp only [ptH, Prod.mk.injEq]
      constructor
      · rw [eq_div_iff h8]; linarith
      · rw [eq_div_iff h8]; linarith

/-- At `N = 4` the points `Σ_C` and `Σ_H` collide, and only there (for `N > 0`). -/
theorem ptC_eq_ptH_iff {N : ℝ} (hN : 0 < N) : ptC N = ptH N ↔ N = 4 := by
  constructor
  · intro h
    have h2 := congrArg Prod.snd h
    simp only [ptC, ptH] at h2
    have h8 : N + 8 ≠ 0 := by positivity
    have h3 : 3 * N ≠ 0 := by positivity
    field_simp at h2
    linarith
  · rintro rfl
    simp only [ptC, ptH]; norm_num

/-! ## Jacobian and eigenvalues -/

/-- The Jacobian `Df` of `eq:ONy`. -/
def J (N y₁ y₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-(1 + 18 * y₁), -(2 * (N - 1) * y₂); -(6 * y₂), -(1 + 6 * y₁ + 2 * (N + 2) * y₂)]

theorem hasDerivAt_f₁_y₁ (N y₁ y₂ : ℝ) :
    HasDerivAt (fun y => f₁ N y y₂) (J N y₁ y₂ 0 0) y₁ :=
  hasDerivAt_of_cubic 0 (-9) (-1) (-((N - 1) * y₂ ^ 2)) y₁ _
    (fun y => by simp only [f₁]; ring) (by rw [show J N y₁ y₂ 0 0 = -(1 + 18 * y₁) from rfl]; ring)

theorem hasDerivAt_f₁_y₂ (N y₁ y₂ : ℝ) :
    HasDerivAt (fun y => f₁ N y₁ y) (J N y₁ y₂ 0 1) y₂ :=
  hasDerivAt_of_cubic 0 (-(N - 1)) 0 (-(y₁ + 9 * y₁ ^ 2)) y₂ _
    (fun y => by simp only [f₁]; ring)
    (by rw [show J N y₁ y₂ 0 1 = -(2 * (N - 1) * y₂) from rfl]; ring)

theorem hasDerivAt_f₂_y₁ (N y₁ y₂ : ℝ) :
    HasDerivAt (fun y => f₂ N y y₂) (J N y₁ y₂ 1 0) y₁ :=
  hasDerivAt_of_cubic 0 0 (-(6 * y₂)) (-(y₂ + (N + 2) * y₂ ^ 2)) y₁ _
    (fun y => by simp only [f₂]; ring) (by rw [show J N y₁ y₂ 1 0 = -(6 * y₂) from rfl]; ring)

theorem hasDerivAt_f₂_y₂ (N y₁ y₂ : ℝ) :
    HasDerivAt (fun y => f₂ N y₁ y) (J N y₁ y₂ 1 1) y₂ :=
  hasDerivAt_of_cubic 0 (-(N + 2)) (-(1 + 6 * y₁)) 0 y₂ _
    (fun y => by simp only [f₂]; ring)
    (by rw [show J N y₁ y₂ 1 1 = -(1 + 6 * y₁ + 2 * (N + 2) * y₂) from rfl]; ring)

theorem eig_G (N : ℝ) : HasEigenvalues (J N ptG.1 ptG.2) (-1) (-1) := by
  intro x; simp [J, ptG, Matrix.det_fin_two]

theorem eig_I (N : ℝ) : HasEigenvalues (J N ptI.1 ptI.2) 1 (-1 / 3) := by
  intro x; simp [J, ptI, Matrix.det_fin_two]; ring

theorem eig_C {N : ℝ} (hN : N ≠ 0) :
    HasEigenvalues (J N (ptC N).1 (ptC N).2) 1 ((N - 4) / (3 * N)) := by
  intro x; simp [J, ptC, Matrix.det_fin_two]; field_simp; ring

theorem eig_H {N : ℝ} (hN : N + 8 ≠ 0) :
    HasEigenvalues (J N (ptH N).1 (ptH N).2) 1 ((4 - N) / (N + 8)) := by
  intro x; simp [J, ptH, Matrix.det_fin_two]; field_simp; ring

/-- The linearizations at `Σ_G` and `Σ_I` do not depend on `N` (proof of `prop:ONramp`(ii)). -/
theorem J_G (N : ℝ) : J N ptG.1 ptG.2 = !![-1, 0; 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J, ptG]

theorem J_I (N : ℝ) : J N ptI.1 ptI.2 = !![1, 0; 0, -1 / 3] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J, ptI] <;> norm_num

/-- For `N > 4`: `(Σ_G, Σ_I, Σ_H, Σ_C) = (0, 1, 1, 2)`. -/
theorem morse_indices_gt4 {N : ℝ} (hN : 4 < N) :
    morseIndex (-1) (-1) = 0 ∧ morseIndex 1 (-1 / 3) = 1 ∧
      morseIndex 1 ((4 - N) / (N + 8)) = 1 ∧ morseIndex 1 ((N - 4) / (3 * N)) = 2 := by
  have hH : ¬ 0 < (4 - N) / (N + 8) := not_lt.2 (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (by linarith))
  have hC : 0 < (N - 4) / (3 * N) := div_pos (by linarith) (by linarith)
  refine ⟨by norm_num [morseIndex], by norm_num [morseIndex], ?_, ?_⟩ <;>
    simp [morseIndex, hH, hC]

/-- For `1 < N < 4`: `(Σ_G, Σ_I, Σ_H, Σ_C) = (0, 1, 2, 1)`. -/
theorem morse_indices_lt4 {N : ℝ} (h1 : 1 < N) (hN : N < 4) :
    morseIndex (-1) (-1) = 0 ∧ morseIndex 1 (-1 / 3) = 1 ∧
      morseIndex 1 ((4 - N) / (N + 8)) = 2 ∧ morseIndex 1 ((N - 4) / (3 * N)) = 1 := by
  have hH : 0 < (4 - N) / (N + 8) := div_pos (by linarith) (by linarith)
  have hC : ¬ 0 < (N - 4) / (3 * N) := not_lt.2 (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (by linarith))
  refine ⟨by norm_num [morseIndex], by norm_num [morseIndex], ?_, ?_⟩ <;>
    simp [morseIndex, hH, hC]

/-- At the exchange of stability, the unlabeled Morse indices of `(Σ_G, Σ_I, Σ_H, Σ_C)` agree for
`N₋ > 4` and `1 < N₊ < 4`, while the indices of the labeled points `Σ_H` and `Σ_C` change. -/
theorem morse_exchange {Nm Np : ℝ} (hm : 4 < Nm) (h1 : 1 < Np) (hp : Np < 4) :
    ({morseIndex (-1) (-1), morseIndex 1 (-1 / 3), morseIndex 1 ((4 - Nm) / (Nm + 8)),
        morseIndex 1 ((Nm - 4) / (3 * Nm))} : Multiset ℕ) =
      {morseIndex (-1) (-1), morseIndex 1 (-1 / 3), morseIndex 1 ((4 - Np) / (Np + 8)),
        morseIndex 1 ((Np - 4) / (3 * Np))} ∧
    morseIndex 1 ((4 - Nm) / (Nm + 8)) ≠ morseIndex 1 ((4 - Np) / (Np + 8)) ∧
    morseIndex 1 ((Nm - 4) / (3 * Nm)) ≠ morseIndex 1 ((Np - 4) / (3 * Np)) := by
  obtain ⟨g1, i1, h1', c1⟩ := morse_indices_gt4 hm
  obtain ⟨-, -, h2', c2⟩ := morse_indices_lt4 h1 hp
  rw [g1, i1, h1', c1, h2', c2]
  decide

/-! ## Lemma `lem:ONstructure`(i): gradient structure -/

/-- The potential `eq:ONV`. -/
noncomputable def V (N y₁ y₂ : ℝ) : ℝ :=
  1 / 2 * y₁ ^ 2 + (N - 1) / 6 * y₂ ^ 2 + 3 * y₁ ^ 3 + (N - 1) * y₁ * y₂ ^ 2 +
    (N - 1) * (N + 2) / 9 * y₂ ^ 3

theorem hasDerivAt_V_y₁ (N y₁ y₂ : ℝ) :
    HasDerivAt (fun y => V N y y₂) (-f₁ N y₁ y₂) y₁ :=
  hasDerivAt_of_cubic 3 (1 / 2) ((N - 1) * y₂ ^ 2)
    ((N - 1) / 6 * y₂ ^ 2 + (N - 1) * (N + 2) / 9 * y₂ ^ 3) y₁ _
    (fun y => by simp only [V]; ring) (by simp only [f₁]; ring)

/-- `∂V/∂y₂ = (N-1)/3 · (y₂ + 6 y₁ y₂ + (N+2) y₂²)`, so with `g = diag(1, (N-1)/3)` the flow
is `y' = -g⁻¹ ∇V`. -/
theorem hasDerivAt_V_y₂ (N y₁ y₂ : ℝ) :
    HasDerivAt (fun y => V N y₁ y) (-((N - 1) / 3) * f₂ N y₁ y₂) y₂ :=
  hasDerivAt_of_cubic ((N - 1) * (N + 2) / 9) ((N - 1) / 6 + (N - 1) * y₁) 0
    (1 / 2 * y₁ ^ 2 + 3 * y₁ ^ 3) y₂ _
    (fun y => by simp only [V]; ring) (by simp only [f₂]; ring)

/-- Along a solution of `eq:ONy`, `dV/ds = -(f₁² + (N-1)/3 f₂²)`. -/
theorem hasDerivAt_V_along {N : ℝ} {y₁ y₂ : ℝ → ℝ} {s : ℝ}
    (h1 : HasDerivAt y₁ (f₁ N (y₁ s) (y₂ s)) s) (h2 : HasDerivAt y₂ (f₂ N (y₁ s) (y₂ s)) s) :
    HasDerivAt (fun t => V N (y₁ t) (y₂ t))
      (-(f₁ N (y₁ s) (y₂ s) ^ 2 + (N - 1) / 3 * f₂ N (y₁ s) (y₂ s) ^ 2)) s := by
  have h := (((((h1.pow 2).const_mul (1 / 2 : ℝ)).add ((h2.pow 2).const_mul ((N - 1) / 6))).add
    ((h1.pow 3).const_mul (3 : ℝ))).add ((h1.mul (h2.pow 2)).const_mul (N - 1))).add
    ((h2.pow 3).const_mul ((N - 1) * (N + 2) / 9))
  convert h using 1
  · funext t; simp only [V, Pi.add_apply, Pi.pow_apply, Pi.mul_apply]; ring
  · simp only [f₁, f₂, Pi.pow_apply]; push_cast; ring

/-- `V` strictly decreases away from the zeros of the vector field (`N > 1`). -/
theorem dV_neg {N a b : ℝ} (hN : 1 < N) :
    -(a ^ 2 + (N - 1) / 3 * b ^ 2) ≤ 0 ∧ (-(a ^ 2 + (N - 1) / 3 * b ^ 2) = 0 ↔ a = 0 ∧ b = 0) := by
  have hN' : 0 < (N - 1) / 3 := by linarith
  refine ⟨by nlinarith [sq_nonneg a, sq_nonneg b], ⟨fun h => ?_, fun ⟨ha, hb⟩ => by simp [ha, hb]⟩⟩
  have ha : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
  have hb : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
  exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ha, pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hb⟩

/-! ## Lemma `lem:ONstructure`(ii): invariant lines

The paper states `y₂' - k y₁' = -k(k-1)((N-1)k-3) y₁²` on the line `y₂ = k y₁`. The correct sign
is `+`, as the following identity shows. The conclusion (the set of `k`) is unaffected. -/

theorem line_identity (N k y : ℝ) :
    f₂ N y (k * y) - k * f₁ N y (k * y) = k * (k - 1) * ((N - 1) * k - 3) * y ^ 2 := by
  simp only [f₁, f₂]; ring

theorem line_invariant_iff {N k : ℝ} (hN : 1 < N) :
    (∀ y, f₂ N y (k * y) - k * f₁ N y (k * y) = 0) ↔ k = 0 ∨ k = 1 ∨ k = 3 / (N - 1) := by
  have hN1 : N - 1 ≠ 0 := by linarith
  constructor
  · intro h
    have h1 := h 1
    rw [line_identity] at h1
    simp only [one_pow, mul_one] at h1
    rcases mul_eq_zero.1 h1 with h' | h'
    · rcases mul_eq_zero.1 h' with h'' | h''
      · exact Or.inl h''
      · exact Or.inr (Or.inl (by linarith))
    · right; right
      rw [eq_div_iff hN1]; linarith
  · rintro (rfl | rfl | rfl) y <;> rw [line_identity]
    · ring
    · ring
    · field_simp; ring

theorem ptI_on_axis : ptI.2 = 0 * ptI.1 := by simp [ptI]
theorem ptH_on_diagonal (N : ℝ) : (ptH N).2 = 1 * (ptH N).1 := by simp [ptH]
theorem ptC_on_third_line {N : ℝ} (hN : 1 < N) : (ptC N).2 = 3 / (N - 1) * (ptC N).1 := by
  have : N - 1 ≠ 0 := by linarith
  have : N ≠ 0 := by linarith
  simp only [ptC]; field_simp; ring

/-- At `N = 4` the third line is the diagonal. -/
theorem third_line_at_4 : (3 : ℝ) / (4 - 1) = 1 := by norm_num

/-- Corollary `cor:ON`(i): on the line `y = ς (1, k)` the flow is `ς' = -ς (1 + α ς)` with
`α = 9 + (N-1) k²`. -/
theorem reduced_line_flow (N k ς : ℝ) :
    f₁ N ς (k * ς) = -ς * (1 + (9 + (N - 1) * k ^ 2) * ς) := by
  simp only [f₁]; ring

theorem alpha_axis (N : ℝ) : 9 + (N - 1) * (0 : ℝ) ^ 2 = 9 := by ring
theorem alpha_diagonal (N : ℝ) : 9 + (N - 1) * (1 : ℝ) ^ 2 = N + 8 := by ring
theorem alpha_third {N : ℝ} (hN : 1 < N) :
    9 + (N - 1) * (3 / (N - 1)) ^ 2 = 9 * N / (N - 1) := by
  have : N - 1 ≠ 0 := by linarith
  field_simp; ring

/-- Points strictly between `-1/α` and `0` move toward the origin. -/
theorem reduced_moves_to_origin {α ς : ℝ} (hα : 0 < α) (h1 : -1 / α < ς) (h2 : ς < 0) :
    0 < -ς * (1 + α * ς) := by
  have : 0 < 1 + α * ς := by
    have := (div_lt_iff₀ hα).1 h1
    nlinarith
  nlinarith

/-- On the axis, `Σ_I` is repelling: the derivative of `-ς(1 + 9ς)` at `ς = -1/9` is `1`. -/
theorem axis_repelling_at_I :
    HasDerivAt (fun ς : ℝ => -ς * (1 + 9 * ς)) 1 (-1 / 9) :=
  hasDerivAt_of_cubic 0 (-9) (-1) 0 _ _ (fun y => by ring) (by norm_num)

/-! ## Lemma `lem:ONstructure`(iii), (iv) -/

/-- The axis `y₂ = 0` is invariant. -/
theorem axis_invariant (N y₁ : ℝ) : f₂ N y₁ 0 = 0 := by simp [f₂]

/-- On `{y₁ = 0, y₂ < 0}` one has `y₁' = -(N-1) y₂² < 0`, so the flow enters `Q`. -/
theorem quadrant_entry {N y₂ : ℝ} (hN : 1 < N) (hy : y₂ < 0) : f₁ N 0 y₂ < 0 := by
  simp only [f₁]
  have : 0 < y₂ ^ 2 := by nlinarith
  nlinarith

/-- With `x = -y₁`: `x' ≥ x (9x - 1)`. -/
theorem blowup_x {N y₁ y₂ : ℝ} (hN : 1 ≤ N) : -f₁ N y₁ y₂ ≥ (-y₁) * (9 * (-y₁) - 1) := by
  simp only [f₁]; nlinarith [sq_nonneg y₂]

/-- On `Q`, with `w = -y₂`: `w' = w((N+2)w - 1 - 6y₁) ≥ w((N+2)w - 1)`. -/
theorem blowup_w (N y₁ y₂ : ℝ) :
    -f₂ N y₁ y₂ = (-y₂) * ((N + 2) * (-y₂) - 1 - 6 * y₁) := by
  simp only [f₂]; ring

theorem blowup_w_ge {N y₁ y₂ : ℝ} (h1 : y₁ ≤ 0) (h2 : y₂ ≤ 0) :
    -f₂ N y₁ y₂ ≥ (-y₂) * ((N + 2) * (-y₂) - 1) := by
  rw [blowup_w]; nlinarith

/-! ## Proposition `prop:ON`: the face inequalities of `R = [-1/8, δ] × [-1/2, δ]`, `δ = 1/100` -/

noncomputable def δ : ℝ := 1 / 100

theorem face_right {N y₂ : ℝ} (hN : 1 < N) : f₁ N δ y₂ < 0 := by
  simp only [f₁, δ]; nlinarith [sq_nonneg y₂]

theorem face_left {N y₂ : ℝ} (hN : 1 < N) : f₁ N (-1 / 8) y₂ < 0 := by
  simp only [f₁]; nlinarith [sq_nonneg y₂]

theorem face_left_value (N y₂ : ℝ) : f₁ N (-1 / 8) y₂ = -(1 / 64 + (N - 1) * y₂ ^ 2) := by
  simp only [f₁]; ring

theorem face_top {N y₁ : ℝ} (hN : 1 < N) (h1 : -1 / 8 ≤ y₁) : f₂ N y₁ δ ≤ -δ / 4 := by
  simp only [f₂, δ]; nlinarith

theorem face_bottom {N y₁ : ℝ} (hN : 1 < N) (h1 : y₁ ≤ δ) : f₂ N y₁ (-1 / 2) < 0 := by
  simp only [f₂, δ] at *; nlinarith

theorem face_bottom_value (N y₁ : ℝ) :
    f₂ N y₁ (-1 / 2) = 1 / 2 * (1 + 6 * y₁ - (N + 2) / 2) := by
  simp only [f₂]; ring

/-- The rectangle `[-1/9, 0] × [-1/(N+2), 0]` lies in the interior of `R`. -/
theorem inner_rect_in_interior {N : ℝ} (hN : 1 < N) :
    (-1 / 8 : ℝ) < -1 / 9 ∧ (0 : ℝ) < δ ∧ (-1 / 2 : ℝ) < -1 / (N + 2) := by
  refine ⟨by norm_num, by norm_num [δ], ?_⟩
  rw [div_lt_div_iff₀ (by norm_num) (by linarith)]; linarith

/-- `Σ_C` and `Σ_H` have strictly negative coordinates, and all four fixed points lie in
`[-1/9, 0] × [-1/(N+2), 0]`. -/
theorem fixed_points_in_rect {N : ℝ} (hN : 1 < N) :
    (ptC N).1 < 0 ∧ (ptC N).2 < 0 ∧ (ptH N).1 < 0 ∧
    -1 / 9 ≤ (ptC N).1 ∧ -1 / (N + 2) ≤ (ptC N).2 ∧
    -1 / 9 ≤ (ptH N).1 ∧ -1 / (N + 2) ≤ (ptH N).2 := by
  have h0 : 0 < N := by linarith
  simp only [ptC, ptH]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply div_neg_of_neg_of_pos <;> linarith
  · apply div_neg_of_neg_of_pos <;> linarith
  · apply div_neg_of_neg_of_pos <;> linarith
  · rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
  · rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith

/-! ## Original couplings and the cubic anisotropy model -/

/-- The beta functions `eq:ONbeta`, with `K = 8π²` kept as a parameter. -/
noncomputable def β₁ (K ε N l₁ l₂ : ℝ) : ℝ := ε * l₁ + (9 * l₁ ^ 2 + (N - 1) * l₂ ^ 2) / K
noncomputable def β₂ (K ε N l₁ l₂ : ℝ) : ℝ := ε * l₂ + (6 * l₁ * l₂ + (N + 2) * l₂ ^ 2) / K

/-- The rescaling `λ = K ε y`, `s = ε t` turns `dλ/dt = -β(λ)` into `eq:ONy`. -/
theorem rescaling {K ε : ℝ} (hK : K ≠ 0) (N y₁ y₂ : ℝ) :
    -β₁ K ε N (K * ε * y₁) (K * ε * y₂) = K * ε ^ 2 * f₁ N y₁ y₂ ∧
    -β₂ K ε N (K * ε * y₁) (K * ε * y₂) = K * ε ^ 2 * f₂ N y₁ y₂ := by
  constructor <;> simp only [β₁, β₂, f₁, f₂] <;> field_simp <;> ring

/-- In `u = λ₂`, `v = λ₁ - λ₂` the beta functions are those of the cubic anisotropy model. -/
theorem cubic_anisotropy {K : ℝ} (hK : K ≠ 0) (ε N u v : ℝ) :
    β₂ K ε N (u + v) u = ε * u + ((N + 8) * u ^ 2 + 6 * u * v) / K ∧
    β₁ K ε N (u + v) u - β₂ K ε N (u + v) u = ε * v + (12 * u * v + 9 * v ^ 2) / K := by
  constructor <;> simp only [β₁, β₂] <;> field_simp <;> ring

end ConleyCheck.ON
