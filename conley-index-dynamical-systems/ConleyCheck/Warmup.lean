import ConleyCheck.Calculus
import ConleyCheck.Gubser.Basic

/-!
# Sections `subsec:warmup`, `subsec:phase` and Proposition `prop:Hcrit`(i)

The explicit warm-up solution `x = a (cosh^κ t + K)/(cosh^κ t - K)` is `ConleyCheck.Gubser.gpi_sol`.
Checked here: the restriction to `T = 0`, the Morse indices of `A, B, C, D`, the constant of motion
`K = (x-a)/(x+a) (1-p^2)^(-κ/2)`, the three classes of solutions, the solutions of the phase
transition model, the quadrature for a time-dependent `α`, and the clock `σ = tanh(κ t)`.
-/

namespace ConleyCheck.Warmup

/-- The warm-up system is the Gubser flow on its invariant plane `T = 0`. -/
theorem restriction (c x p : ℝ) : Gubser.βπ c 0 x p = -(4 / 3) * p * (x ^ 2 - 1 / 5) := by
  simp only [Gubser.βπ]; ring

/-- Morse indices in `X × ℝ`: the fiber eigenvalue is `∂ₓF = -8px/3` and the normal eigenvalue is
`g'(p) = -2p`. At `A = (a,-1)` both are positive, at `B = (a,1)` both negative, and at `C = (-a,-1)`,
`D = (-a,1)` they have opposite signs. -/
theorem morse_indices {a : ℝ} (ha : 0 < a) :
    (0 < -(8 / 3) * (-1) * a ∧ 0 < -2 * (-1 : ℝ)) ∧ (-(8 / 3) * 1 * a < 0 ∧ -2 * (1 : ℝ) < 0) ∧
      (-(8 / 3) * (-1) * (-a) < 0 ∧ 0 < -2 * (-1 : ℝ)) ∧
      (0 < -(8 / 3) * 1 * (-a) ∧ -2 * (1 : ℝ) < 0) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

theorem fiber_derivative (a p x : ℝ) :
    HasDerivAt (fun y => -(4 / 3) * p * (y ^ 2 - a ^ 2)) (-(8 / 3) * p * x) x :=
  hasDerivAt_of_cubic 0 (-(4 / 3) * p) 0 (4 / 3 * p * a ^ 2) x _ (fun y => by ring) (by ring)

/-- `K = (x-a)/(x+a) (1-p^2)^(-κ/2)` is a constant of motion on `{|p| < 1}` exactly for
`κ = 8a/3`. -/
theorem constant_of_motion {a κ : ℝ} (hκ : κ = 8 * a / 3) {x p : ℝ → ℝ} {t : ℝ}
    (hx : HasDerivAt x (-(4 / 3) * p t * (x t ^ 2 - a ^ 2)) t)
    (hp : HasDerivAt p (1 - p t ^ 2) t) (hxa : x t + a ≠ 0) (hp1 : p t ^ 2 < 1) :
    HasDerivAt (fun s => (x s - a) / (x s + a) * (1 - p s ^ 2) ^ (-κ / 2)) 0 t := by
  have hq : 0 < 1 - p t ^ 2 := by linarith
  have hQ : HasDerivAt (fun s => 1 - p s ^ 2) (-(2 * p t * (1 - p t ^ 2))) t := by
    have h2 := (hp.mul hp).const_sub 1
    convert h2 using 1
    · funext s; simp only [Pi.mul_apply]; ring
    · ring
  have hR := hQ.rpow_const (p := -κ / 2) (Or.inl hq.ne')
  have hF := ((hx.sub_const a).div (hx.add_const a) hxa).mul hR
  convert hF using 1
  simp only [Pi.div_apply]
  rw [Real.rpow_sub_one hq.ne']
  have hq0 := hq.ne'
  generalize (1 - p t ^ 2) ^ (-κ / 2) = Y
  subst hκ
  field_simp
  ring

/-- `K < 1` iff `x(0) > -a` (bounded solutions `A → B`), and `K > 1` iff `x(0) < -a` (blow-up). -/
theorem K_classes {a x : ℝ} (ha : 0 < a) :
    (-a < x → (x - a) / (x + a) < 1) ∧ (x < -a → 1 < (x - a) / (x + a)) := by
  constructor
  · intro h; rw [div_lt_one (by linarith)]; linarith
  · intro h; rw [one_lt_div_of_neg (by linarith)]; linarith

/-! ## The phase transition `dX/dz = -α (X^2 - 1)/(2z)` -/

/-- `X = (z^α - C₁)/(z^α + C₁)` solves `eq:phase`. -/
theorem phase_sol {α C z : ℝ} (hz : 0 < z) (hC : 0 < C) :
    HasDerivAt (fun y => (y ^ α - C) / (y ^ α + C))
      (-α * (((z ^ α - C) / (z ^ α + C)) ^ 2 - 1) / (2 * z)) z := by
  have hY := Real.hasDerivAt_rpow_const (p := α) (Or.inl hz.ne')
  have hpos : 0 < z ^ α := Real.rpow_pos_of_pos hz α
  have hne : z ^ α + C ≠ 0 := by positivity
  have h := (hY.sub_const C).div (hY.add_const C) hne
  convert h using 1
  rw [Real.rpow_sub_one hz.ne']
  have hz0 := hz.ne'
  generalize z ^ α = Y at hne ⊢
  field_simp
  ring

/-- The Morse indices of `X_c^±` are exchanged at `α_c = 0`: the linearization of
`-α(X^2-1)/2` is `-α` at `X = 1` and `α` at `X = -1`. -/
theorem phase_linearization (α : ℝ) :
    HasDerivAt (fun X => -α * (X ^ 2 - 1) / 2) (-α) 1 ∧
      HasDerivAt (fun X => -α * (X ^ 2 - 1) / 2) α (-1) :=
  ⟨hasDerivAt_of_cubic 0 (-α / 2) 0 (α / 2) 1 _ (fun y => by ring) (by ring),
    hasDerivAt_of_cubic 0 (-α / 2) 0 (α / 2) (-1) _ (fun y => by ring) (by ring)⟩

/-- Time-dependent `α`: `(X-1)/(X+1) e^{A(t)}` is constant, i.e. `(X-1)/(X+1) = K e^{-A(t)}`. -/
theorem quadrature {α A X : ℝ → ℝ} {t : ℝ} (hX : HasDerivAt X (-α t / 2 * (X t ^ 2 - 1)) t)
    (hA : HasDerivAt A (α t) t) (h1 : X t + 1 ≠ 0) :
    HasDerivAt (fun s => (X s - 1) / (X s + 1) * Real.exp (A s)) 0 t := by
  have h := ((hX.sub_const 1).div (hX.add_const 1) h1).mul hA.exp
  convert h using 1
  simp only [Pi.div_apply]
  field_simp
  ring

/-- `X ≡ ±1` solve the equation for every `α(·)`. -/
theorem constant_solutions (α : ℝ) : -α / 2 * ((1 : ℝ) ^ 2 - 1) = 0 ∧
    -α / 2 * ((-1 : ℝ) ^ 2 - 1) = 0 := by
  constructor <;> ring

/-! ## Proposition `prop:Hcrit`(i) -/

/-- `σ(t) = tanh(κ t)` solves `σ' = κ (1 - σ^2)`. -/
theorem tanh_sol (κ t : ℝ) :
    HasDerivAt (fun s => Real.tanh (κ * s)) (κ * (1 - Real.tanh (κ * t) ^ 2)) t := by
  have e : (fun s => Real.tanh (κ * s)) = fun s => Real.sinh (κ * s) / Real.cosh (κ * s) :=
    funext fun s => Real.tanh_eq_sinh_div_cosh _
  rw [e]
  have hf : HasDerivAt (fun s => κ * s) κ t := by
    simpa using (hasDerivAt_id' t).const_mul κ
  have hc := Real.cosh_pos (κ * t)
  have h := hf.sinh.div hf.cosh hc.ne'
  convert h using 1
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- `1/(κ(1-τ^2)) = cosh^2(κ t)/κ` for `τ = tanh(κ t)`. -/
theorem dtau_factor {κ t : ℝ} (hκ : κ ≠ 0) :
    1 / (κ * (1 - Real.tanh (κ * t) ^ 2)) = Real.cosh (κ * t) ^ 2 / κ := by
  have hc := (Real.cosh_pos (κ * t)).ne'
  have h1 : 1 - Real.tanh (κ * t) ^ 2 = 1 / Real.cosh (κ * t) ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    linear_combination Real.cosh_sq_sub_sinh_sq (κ * t)
  rw [h1]
  field_simp

end ConleyCheck.Warmup
