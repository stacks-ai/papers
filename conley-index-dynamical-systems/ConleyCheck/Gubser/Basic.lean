import ConleyCheck.Calculus

/-!
# Gubser flow of Israel–Stewart theory (section `sec:gubser`)

`dT/dρ = T(π̄-2)τ/3`, `dπ̄/dρ = -4/3 (π̄² - 1/5) τ - T π̄/c`, `dτ/dρ = 1 - τ²`.

We verify the Jacobian `eq:gubserJ`, the equilibria of table `tab:gubser` and that there are no
others, the fiber eigenvalues and Morse indices, the reversor `eq:reversor`, the reduced solutions
`eq:gpi-sol`, `eq:gT-sol`, the torus chart and the separatrix block of Proposition `prop:torus`,
and the linearization along the separatrix used in Proposition `prop:transversal`.
-/

namespace ConleyCheck.Gubser

variable (c : ℝ)

noncomputable def βT (T π τ : ℝ) : ℝ := T / 3 * (π - 2) * τ
noncomputable def βπ (T π τ : ℝ) : ℝ := -(4 / 3) * (π ^ 2 - 1 / 5) * τ - T * π / c
def βτ (τ : ℝ) : ℝ := 1 - τ ^ 2

/-! ## The Jacobian `eq:gubserJ` -/

noncomputable def J (T π τ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(π - 2) * τ / 3, T * τ / 3, T * (π - 2) / 3;
     -(π / c), -(8 * π * τ / 3) - T / c, -(4 / 3) * (π ^ 2 - 1 / 5);
     0, 0, -(2 * τ)]

section Jacobian
variable (T π τ : ℝ)

theorem J00 : HasDerivAt (fun x => βT x π τ) (J c T π τ 0 0) T :=
  hasDerivAt_of_cubic 0 0 ((π - 2) * τ / 3) 0 T _ (fun y => by simp only [βT]; ring)
    (by rw [show J c T π τ 0 0 = (π - 2) * τ / 3 from rfl]; ring)
theorem J01 : HasDerivAt (fun x => βT T x τ) (J c T π τ 0 1) π :=
  hasDerivAt_of_cubic 0 0 (T * τ / 3) (-(2 * T * τ / 3)) π _ (fun y => by simp only [βT]; ring)
    (by rw [show J c T π τ 0 1 = T * τ / 3 from rfl]; ring)
theorem J02 : HasDerivAt (fun x => βT T π x) (J c T π τ 0 2) τ :=
  hasDerivAt_of_cubic 0 0 (T * (π - 2) / 3) 0 τ _ (fun y => by simp only [βT]; ring)
    (by rw [show J c T π τ 0 2 = T * (π - 2) / 3 from rfl]; ring)
theorem J10 : HasDerivAt (fun x => βπ c x π τ) (J c T π τ 1 0) T :=
  hasDerivAt_of_cubic 0 0 (-(π / c)) (-(4 / 3) * (π ^ 2 - 1 / 5) * τ) T _
    (fun y => by simp only [βπ]; ring) (by rw [show J c T π τ 1 0 = -(π / c) from rfl]; ring)
theorem J11 : HasDerivAt (fun x => βπ c T x τ) (J c T π τ 1 1) π :=
  hasDerivAt_of_cubic 0 (-(4 / 3) * τ) (-(T / c)) (4 / 15 * τ) π _
    (fun y => by simp only [βπ]; ring)
    (by rw [show J c T π τ 1 1 = -(8 * π * τ / 3) - T / c from rfl]; ring)
theorem J12 : HasDerivAt (fun x => βπ c T π x) (J c T π τ 1 2) τ :=
  hasDerivAt_of_cubic 0 0 (-(4 / 3) * (π ^ 2 - 1 / 5)) (-(T * π / c)) τ _
    (fun y => by simp only [βπ]; ring)
    (by rw [show J c T π τ 1 2 = -(4 / 3) * (π ^ 2 - 1 / 5) from rfl]; ring)
theorem J22 : HasDerivAt (fun x => βτ x) (J c T π τ 2 2) τ :=
  hasDerivAt_of_cubic 0 (-1) 0 1 τ _ (fun y => by simp only [βτ]; ring)
    (by rw [show J c T π τ 2 2 = -(2 * τ) from rfl]; ring)

end Jacobian

/-! ## Equilibria -/

/-- The zeros of the vector field are the six points of table `tab:gubser`. -/
theorem equilibria_iff {c : ℝ} (hc : c ≠ 0) (T π τ : ℝ) :
    (βT T π τ = 0 ∧ βπ c T π τ = 0 ∧ βτ τ = 0) ↔
      (τ = 1 ∨ τ = -1) ∧ ((T = 0 ∧ π ^ 2 = 1 / 5) ∨ (π = 2 ∧ T = -(38 * c * τ / 15))) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    simp only [βT, βπ, βτ] at h1 h2 h3
    have hτ : τ = 1 ∨ τ = -1 := by
      have : (τ - 1) * (τ + 1) = 0 := by linear_combination -h3
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · right; linarith
    have hτ0 : τ ≠ 0 := by rcases hτ with h | h <;> simp [h]
    refine ⟨hτ, ?_⟩
    have : T * (π - 2) * τ = 0 := by linear_combination 3 * h1
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with hT | hπ
      · left
        subst hT
        refine ⟨rfl, ?_⟩
        have : (π ^ 2 - 1 / 5) * τ = 0 := by linear_combination (-3 / 4) * h2
        rcases mul_eq_zero.1 this with h' | h'
        · linarith
        · exact absurd h' hτ0
      · right
        have hπ2 : π = 2 := by linarith
        subst hπ2
        refine ⟨rfl, ?_⟩
        field_simp at h2
        linarith
    · exact absurd h hτ0
  · rintro ⟨hτ, h | h⟩
    · obtain ⟨rfl, hπ⟩ := h
      refine ⟨by simp [βT], ?_, ?_⟩
      · simp only [βπ]; rw [hπ]; ring
      · rcases hτ with rfl | rfl <;> simp [βτ]
    · obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp [βT], ?_, ?_⟩
      · simp only [βπ]; field_simp; ring
      · rcases hτ with rfl | rfl <;> simp [βτ]

/-- `a = 1/√5` satisfies `a² = 1/5`. -/
theorem a_sq : (1 / Real.sqrt 5) ^ 2 = 1 / 5 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]; norm_num

theorem a_bounds : 0 < 1 / Real.sqrt 5 ∧ 1 / Real.sqrt 5 < 1 / 2 := by
  have h5 : (2 : ℝ) < Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  exact ⟨by positivity, by rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith⟩

/-! ## Fiber eigenvalues (table `tab:gubser`) -/

/-- The fiber block `∂(βT, βπ)/∂(T, π)` of the Jacobian. -/
noncomputable def Jf (T π τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(π - 2) * τ / 3, T * τ / 3; -(π / c), -(8 * π * τ / 3) - T / c]

section Eigen
variable {a : ℝ}

theorem eig_UA : HasEigenvalues (Jf c 0 a (-1)) ((2 - a) / 3) (8 * a / 3) := by
  intro x; rw [Jf, det_smul_one_sub_fin_two]; ring
theorem eig_IA : HasEigenvalues (Jf c 0 a 1) (-((2 - a) / 3)) (-(8 * a / 3)) := by
  intro x; rw [Jf, det_smul_one_sub_fin_two]; ring
theorem eig_UB : HasEigenvalues (Jf c 0 (-a) (-1)) ((2 + a) / 3) (-(8 * a / 3)) := by
  intro x; rw [Jf, det_smul_one_sub_fin_two]; ring
theorem eig_IB : HasEigenvalues (Jf c 0 (-a) 1) (-((2 + a) / 3)) (8 * a / 3) := by
  intro x; rw [Jf, det_smul_one_sub_fin_two]; ring

theorem eig_UC {c : ℝ} (hc : c ≠ 0) :
    HasEigenvalues (Jf c (38 * c / 15) 2 (-1)) ((21 + Real.sqrt 821) / 15)
      ((21 - Real.sqrt 821) / 15) := by
  intro x
  have hs : Real.sqrt 821 ^ 2 = 821 := Real.sq_sqrt (by norm_num)
  have hdet : (x • (1 : Matrix (Fin 2) (Fin 2) ℝ) - Jf c (38 * c / 15) 2 (-1)).det =
      x ^ 2 - 42 / 15 * x - 76 / 45 := by
    rw [Jf, det_smul_one_sub_fin_two]; field_simp; ring
  rw [hdet]; linear_combination (1 / 225) * hs

theorem eig_IC {c : ℝ} (hc : c ≠ 0) :
    HasEigenvalues (Jf c (-(38 * c / 15)) 2 1) (-((21 + Real.sqrt 821) / 15))
      (-((21 - Real.sqrt 821) / 15)) := by
  intro x
  have hs : Real.sqrt 821 ^ 2 = 821 := Real.sq_sqrt (by norm_num)
  have hdet : (x • (1 : Matrix (Fin 2) (Fin 2) ℝ) - Jf c (-(38 * c / 15)) 2 1).det =
      x ^ 2 + 42 / 15 * x - 76 / 45 := by
    rw [Jf, det_smul_one_sub_fin_two]; field_simp; ring
  rw [hdet]; linear_combination (1 / 225) * hs

theorem sqrt821_gt : (21 : ℝ) < Real.sqrt 821 := by
  rw [show (21 : ℝ) = Real.sqrt (21 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- Fiber indices `μ = 2, 0, 1, 1, 1, 1` for `U(A), I(A), U(B), I(B), U(C), I(C)`. -/
theorem fiber_indices (ha : 0 < a) (ha2 : a < 2) :
    morseIndex ((2 - a) / 3) (8 * a / 3) = 2 ∧
    morseIndex (-((2 - a) / 3)) (-(8 * a / 3)) = 0 ∧
    morseIndex ((2 + a) / 3) (-(8 * a / 3)) = 1 ∧
    morseIndex (-((2 + a) / 3)) (8 * a / 3) = 1 ∧
    morseIndex ((21 + Real.sqrt 821) / 15) ((21 - Real.sqrt 821) / 15) = 1 ∧
    morseIndex (-((21 + Real.sqrt 821) / 15)) (-((21 - Real.sqrt 821) / 15)) = 1 := by
  have h1 : 0 < (2 - a) / 3 := by linarith
  have h2 : 0 < 8 * a / 3 := by linarith
  have h3 : 0 < (2 + a) / 3 := by linarith
  have hs := sqrt821_gt
  have h4 : 0 < (21 + Real.sqrt 821) / 15 := by linarith
  have h5 : ¬ 0 < (21 - Real.sqrt 821) / 15 := by linarith
  have h6 : 0 < -((21 - Real.sqrt 821) / 15) := by linarith
  simp only [morseIndex]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> split_ifs <;> first | rfl | linarith

end Eigen

/-- The normal eigenvalue `∂βτ/∂τ = -2τ` is `±2` at `τ = ∓1`. -/
theorem normal_eigen : J c 0 0 (-1) 2 2 = 2 ∧ J c 0 0 1 2 2 = -2 := by
  constructor <;> rw [show ∀ T π τ, J c T π τ 2 2 = -(2 * τ) from fun _ _ _ => rfl] <;> ring

/-! ## The reversor `eq:reversor` -/

/-- `𝒮(T, π̄, τ) = (-T, π̄, -τ)` reverses the flow: `β(𝒮x) = -D𝒮 β(x)`. -/
theorem reversor (T π τ : ℝ) :
    βT (-T) π (-τ) = βT T π τ ∧ βπ c (-T) π (-τ) = -βπ c T π τ ∧ βτ (-τ) = βτ τ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [βT, βπ, βτ] <;> ring

/-- The plane `T = 0` is invariant. -/
theorem T_plane_invariant (π τ : ℝ) : βT 0 π τ = 0 := by simp [βT]

/-! ## The reduced system (`T = 0`, or `c = ∞`) -/

/-- `π̄(ρ) = a (cosh^κ ρ + K)/(cosh^κ ρ - K)` solves `dπ̄/dρ = -4/3(π̄² - a²) tanh ρ` when
`κ = 8a/3`, eq. `eq:gpi-sol`. -/
theorem gpi_sol {a K ρ : ℝ} (hK : Real.cosh ρ ^ (8 * a / 3) ≠ K) :
    HasDerivAt (fun r => a * (Real.cosh r ^ (8 * a / 3) + K) / (Real.cosh r ^ (8 * a / 3) - K))
      (-(4 / 3) * ((a * (Real.cosh ρ ^ (8 * a / 3) + K) / (Real.cosh ρ ^ (8 * a / 3) - K)) ^ 2
        - a ^ 2) * Real.tanh ρ) ρ := by
  have hc : 0 < Real.cosh ρ := Real.cosh_pos ρ
  have hX : HasDerivAt (fun r => Real.cosh r ^ (8 * a / 3))
      (Real.sinh ρ * (8 * a / 3) * Real.cosh ρ ^ (8 * a / 3 - 1)) ρ :=
    (Real.hasDerivAt_cosh ρ).rpow_const (Or.inl hc.ne')
  have hne : Real.cosh ρ ^ (8 * a / 3) - K ≠ 0 := sub_ne_zero.2 hK
  have h := ((hX.add_const K).const_mul a).div (hX.sub_const K) hne
  convert h using 1
  rw [Real.rpow_sub hc, Real.rpow_one, Real.tanh_eq_sinh_div_cosh]
  have hc0 := hc.ne'
  generalize Real.cosh ρ ^ (8 * a / 3) = X at hne ⊢
  field_simp
  ring

/-- The `T`-equation `eq:gT-sol` holds in logarithmic form: with `X = cosh^κ ρ`, `X' = κ X tanh ρ`
and `π̄ = a (X+K)/(X-K)`, one has `d ln T/dρ = (π̄ - 2) tanh ρ / 3` exactly when `3κ/4 = 2a`. -/
theorem gT_log_derivative {a K X t : ℝ} (hXK : X - K ≠ 0) :
    -((2 + a) / 3) * t + (1 / 4) * (8 * a / 3 * X * t) / (X - K) =
      (a * (X + K) / (X - K) - 2) * t / 3 := by
  field_simp; ring

/-! ## Proposition `prop:torus`: the chart `w = 1/π̄` and the separatrix block -/

/-- In `w = 1/π̄`, `dw/dt = 4/3 (1 - a² w²) cos θ`. -/
theorem torus_chart {a π θ : ℝ} (hπ : π ≠ 0) :
    -(-(4 / 3) * (π ^ 2 - a ^ 2) * Real.cos θ) / π ^ 2 =
      4 / 3 * (1 - a ^ 2 * (1 / π) ^ 2) * Real.cos θ := by
  field_simp

/-- On `π̄ = -a ± δ`, `dπ̄/dt = -4/3(π̄² - a²) cos θ` equals `±(4/3) δ (2a ∓ δ) cos θ`. -/
theorem separatrix_faces (a δ θ : ℝ) :
    -(4 / 3) * ((-a + δ) ^ 2 - a ^ 2) * Real.cos θ = 4 / 3 * δ * (2 * a - δ) * Real.cos θ ∧
    -(4 / 3) * ((-a - δ) ^ 2 - a ^ 2) * Real.cos θ = -(4 / 3 * δ * (2 * a + δ) * Real.cos θ) := by
  constructor <;> ring

/-- Second derivative along the reduced doubled flow: `π̈ = -4/3 (π̄² - a²) sin²θ` where
`cos θ = 0`. -/
theorem separatrix_tangency {a : ℝ} {π θ : ℝ → ℝ} {t : ℝ}
    (hπ : HasDerivAt π (-(4 / 3) * (π t ^ 2 - a ^ 2) * Real.cos (θ t)) t)
    (hθ : HasDerivAt θ (-Real.sin (θ t)) t) (h0 : Real.cos (θ t) = 0) :
    HasDerivAt (fun s => -(4 / 3) * (π s ^ 2 - a ^ 2) * Real.cos (θ s))
      (-(4 / 3) * (π t ^ 2 - a ^ 2) * Real.sin (θ t) ^ 2) t := by
  have h := (((hπ.pow 2).sub_const (a ^ 2)).const_mul (-(4 / 3) : ℝ)).mul hθ.cos
  convert h using 1
  rw [h0]; simp only [Pi.pow_apply]; push_cast; ring

/-! ## Proposition `prop:transversal`: the linearization along `γ_B` -/

/-- Along `(T, π̄) ≡ (0, -a)`, the fiber linearization is `δT' = -kτ δT`,
`δπ̄' = (8a/3) τ δπ̄ + (a/c) δT`, with `k = (2+a)/3`. -/
theorem separatrix_linearization (a τ : ℝ) :
    Jf c 0 (-a) τ = !![-((2 + a) / 3) * τ, 0; a / c, 8 * a / 3 * τ] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Jf] <;> ring

/-- `δT = cosh^{-k} ρ` solves `δT' = -k tanh ρ · δT`. -/
theorem deltaT_sol (k ρ : ℝ) :
    HasDerivAt (fun r => Real.cosh r ^ (-k)) (-k * Real.tanh ρ * Real.cosh ρ ^ (-k)) ρ := by
  have hc : 0 < Real.cosh ρ := Real.cosh_pos ρ
  have h := (Real.hasDerivAt_cosh ρ).rpow_const (p := -k) (Or.inl hc.ne')
  convert h using 1
  rw [Real.rpow_sub hc, Real.rpow_one, Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem nu_eq (a : ℝ) : 8 * a / 3 + (2 + a) / 3 = 2 / 3 + 3 * a := by ring

/-! ## Lemma `lem:G` and Lemma `lem:double` for `g(τ) = 1 - τ²` -/

/-- `G(θ) = -g(cos θ)/sin θ = -sin θ` for `g = 1 - τ²`. -/
theorem G_gubser {θ : ℝ} (h : Real.sin θ ≠ 0) :
    -(1 - Real.cos θ ^ 2) / Real.sin θ = -Real.sin θ := by
  rw [← Real.sin_sq]; field_simp

/-- The normal eigenvalues are halved in the double: `G'(0) = -1 = g'(1)/2`, `G'(π) = 1`. -/
theorem G_gubser_deriv : HasDerivAt (fun θ => -Real.sin θ) (-1) 0 ∧
    HasDerivAt (fun θ => -Real.sin θ) 1 Real.pi := by
  constructor
  · have h := (Real.hasDerivAt_sin 0).neg
    rw [Real.cos_zero] at h
    exact h
  · have h := (Real.hasDerivAt_sin Real.pi).neg
    rw [Real.cos_pi, neg_neg] at h
    exact h

/-- Lemma `lem:double`(a): along `θ' = G(θ)`, `d/dt cos θ = g(cos θ)`. -/
theorem cos_semiconj {g G : ℝ → ℝ} {θ : ℝ → ℝ} {t : ℝ} (hθ : HasDerivAt θ (G (θ t)) t)
    (hG : -Real.sin (θ t) * G (θ t) = g (Real.cos (θ t))) :
    HasDerivAt (fun s => Real.cos (θ s)) (g (Real.cos (θ t))) t := by
  have := hθ.cos
  convert this using 1
  rw [← hG]

end ConleyCheck.Gubser
