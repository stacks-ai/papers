import Mathlib

/-!
# Small calculus helpers

Partial derivatives of the polynomial vector fields in the paper are checked by writing the
function of one variable in the normal form `A y^3 + B y^2 + C y + D` and differentiating that.
-/

namespace ConleyCheck

theorem hasDerivAt_cubic (A B C D x : ℝ) :
    HasDerivAt (fun y => A * y ^ 3 + B * y ^ 2 + C * y + D) (3 * A * x ^ 2 + 2 * B * x + C) x := by
  have h1 := (hasDerivAt_pow 3 x).const_mul A
  have h2 := (hasDerivAt_pow 2 x).const_mul B
  have h3 := (hasDerivAt_id x).const_mul C
  convert ((h1.add h2).add h3).add_const D using 1
  simp
  ring

/-- A function of one variable that agrees with a cubic polynomial has the expected derivative. -/
theorem hasDerivAt_of_cubic {f : ℝ → ℝ} (A B C D x d : ℝ)
    (hf : ∀ y, f y = A * y ^ 3 + B * y ^ 2 + C * y + D)
    (hd : d = 3 * A * x ^ 2 + 2 * B * x + C) : HasDerivAt f d x := by
  have : f = fun y => A * y ^ 3 + B * y ^ 2 + C * y + D := funext hf
  rw [this, hd]
  exact hasDerivAt_cubic A B C D x

/-- `e₁, e₂` are the eigenvalues of the `2 × 2` matrix `A`, i.e. the roots of its characteristic
polynomial `det (x • 1 - A)`. -/
def HasEigenvalues (A : Matrix (Fin 2) (Fin 2) ℝ) (e₁ e₂ : ℝ) : Prop :=
  ∀ x : ℝ, (x • (1 : Matrix (Fin 2) (Fin 2) ℝ) - A).det = (x - e₁) * (x - e₂)

theorem det_smul_one_sub_fin_two (x a b c d : ℝ) :
    (x • (1 : Matrix (Fin 2) (Fin 2) ℝ) - !![a, b; c, d]).det = (x - a) * (x - d) - b * c := by
  have : x • (1 : Matrix (Fin 2) (Fin 2) ℝ) - !![a, b; c, d] = !![x - a, -b; -c, x - d] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [this, Matrix.det_fin_two_of]; ring

/-- Number of positive eigenvalues (the Morse index of a hyperbolic planar equilibrium). -/
noncomputable def morseIndex (e₁ e₂ : ℝ) : ℕ :=
  (if 0 < e₁ then 1 else 0) + (if 0 < e₂ then 1 else 0)

end ConleyCheck
