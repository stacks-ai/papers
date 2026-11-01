import Mathlib

/-!
# Connection matrices

A connection matrix is encoded by the matrix `D` with `D i j` the coefficient of generator `i` in
`Δ (generator j)`. The input from Conley theory (existence of a connection matrix, `Δ² = 0`,
degree `-1`, vanishing of entries between non-ordered Morse sets, and `H(Δ) ≅ CH_*` of the total
set) enters as hypotheses, and we verify the resulting linear algebra.

* `DON`: Remark `rem:ONconn` (the connection matrices of Corollary `cor:ON`(ii), (iii)).
* `Dshift`: Remark `rem:ONrampconn` and the discussion after it. Every connection matrix of the
  shift is `Δ₋ ⊕ Δ₊ + T_λ` (`Dshift_eq_Dlam`), and these are conjugate by a filtered change of basis
  (`Dlam_conj`). The blocks `T_λ` are not: `T_0` has rank `2` and `T_1` rank `4` (`Tblk_rank_zero`,
  `Tblk_rank_of_ne`, `Tblk_not_equiv`). The data shared by all `T_λ` are `Dlam_common`.
* `Dtorus`: Proposition `prop:torus`(iii).
* `DM`: the connection matrix of Theorem `thm:M`.
-/

namespace ConleyCheck

open Matrix

theorem zmod2_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl h
  · rfl

/-- `H(D) = 0`: every cycle is a boundary. -/
def Acyclic {n R : Type*} [Fintype n] [CommRing R] (D : Matrix n n R) : Prop :=
  ∀ v : n → R, D *ᵥ v = 0 → ∃ w, D *ᵥ w = v

/-! ## Remark `rem:ONconn`

Generators `(Σ_G, Σ_I, Σ_H, Σ_C)` of degrees `(0, 1, 1, 2)` (for `N > 4`), with
`Δ Σ_I = Δ Σ_H = Σ_G` after orientation and `Δ Σ_C = a Σ_I + b Σ_H`. For `1 < N < 4` the same
matrix applies with `Σ_H` and `Σ_C` exchanged. -/

def DON {R : Type*} [CommRing R] (a b : R) : Matrix (Fin 4) (Fin 4) R :=
  !![0, 1, 1, 0; 0, 0, 0, a; 0, 0, 0, b; 0, 0, 0, 0]

theorem DON_sq {R : Type*} [CommRing R] (a b : R) : DON a b * DON a b = 0 ↔ a + b = 0 := by
  constructor
  · intro h
    have := congrFun (congrFun h 0) 3
    simpa [DON, Matrix.mul_apply, Fin.sum_univ_four] using this
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [DON, Matrix.mul_apply, Fin.sum_univ_four, h]

/-- The degree-two generator does not survive in homology iff `(a, b) ≠ 0`. -/
theorem DON_H2_iff {K : Type*} [Field K] (a b : K) :
    (∀ x : K, DON a b *ᵥ Pi.single 3 x = 0 → x = 0) ↔ (a ≠ 0 ∨ b ≠ 0) := by
  have hcol : ∀ x : K, DON a b *ᵥ Pi.single 3 x = ![0, a * x, b * x, 0] := by
    intro x; ext i; fin_cases i <;> simp [DON, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  simp only [hcol]
  constructor
  · intro h
    by_contra hab
    push Not at hab
    have := h 1 (by ext i; fin_cases i <;> simp [hab.1, hab.2])
    exact one_ne_zero this
  · rintro hab x hx
    have h1 := congrFun hx 1
    have h2 := congrFun hx 2
    simp at h1 h2
    rcases hab with ha | hb
    · exact (h1.resolve_left ha)
    · exact (h2.resolve_left hb)

/-- Remark `rem:ONconn`: `Δ² = 0` and `H(Δ) = 0` force `a ≠ 0` and `b = -a`. -/
theorem DON_forced {K : Type*} [Field K] (a b : K) (hsq : DON a b * DON a b = 0)
    (hH : ∀ x : K, DON a b *ᵥ Pi.single 3 x = 0 → x = 0) : a ≠ 0 ∧ b = -a := by
  have h1 := (DON_sq a b).1 hsq
  have h2 := (DON_H2_iff a b).1 hH
  have hb : b = -a := by linear_combination h1
  refine ⟨?_, hb⟩
  rintro rfl
  rcases h2 with h | h
  · exact h rfl
  · exact h (by simp [hb])

/-- Over `𝔽₂` the connection matrix is unique, `a = b = 1`. -/
theorem DON_F2 (a b : ZMod 2) (hsq : DON a b * DON a b = 0)
    (hH : ∀ x : ZMod 2, DON a b *ᵥ Pi.single 3 x = 0 → x = 0) : a = 1 ∧ b = 1 := by
  obtain ⟨ha, hb⟩ := DON_forced a b hsq hH
  have ha1 : a = 1 := zmod2_eq_one_of_ne_zero ha
  subst ha1
  exact ⟨rfl, by rw [hb]; decide⟩

/-- With `a = 1`, `b = -1` the complex is acyclic, in agreement with `h(B_N) = 0̄`. -/
theorem DON_acyclic {R : Type*} [CommRing R] : Acyclic (DON (1 : R) (-1)) := by
  intro v hv
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp [DON, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at h0 h1
  refine ⟨![0, v 0, 0, v 1], ?_⟩
  ext i
  fin_cases i <;> simp [DON, Matrix.mulVec, dotProduct, Fin.sum_univ_four, h1]
  linear_combination -h0

/-! ## Proposition `prop:ONramp`(iii): the parameter shift through `N = 4`

Generators, in this order, `Σ_G⁻, Σ_I⁻, Σ_H⁻, Σ_C⁻, Σ_G⁺, Σ_I⁺, Σ_H⁺, Σ_C⁺` with degrees in the
double `1, 2, 2, 3, 0, 1, 2, 1`. The UV block is `Δ₋` of `rem:ONconn` (for `N₋ > 4`), the IR block is
`Δ₊` (for `N₊ < 4`), and the transition block is the general degree-`(-1)` block allowed by the
order: `T Σ_G⁻ = t Σ_G⁺`, `T Σ_I⁻ = h Σ_I⁺`, `T Σ_H⁻ = a Σ_I⁺ + b Σ_C⁺`, `T Σ_C⁻ = l Σ_H⁺`. -/

def Dshift {R : Type*} [CommRing R] (t h a b l : R) : Matrix (Fin 8) (Fin 8) R :=
  !![0, 1, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, -1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0;
     t, 0, 0, 0, 0, 1, 0, 1;
     0, h, a, 0, 0, 0, 1, 0;
     0, 0, 0, l, 0, 0, 0, 0;
     0, 0, b, 0, 0, 0, -1, 0]

/-- Degrees of the generators in the double. -/
def degShift : Fin 8 → ℕ := ![1, 2, 2, 3, 0, 1, 2, 1]

/-- Every entry has degree `-1`. -/
theorem Dshift_degree {R : Type*} [CommRing R] (t h a b l : R) (i j : Fin 8)
    (hij : Dshift t h a b l i j ≠ 0) : degShift j = degShift i + 1 := by
  fin_cases i <;> fin_cases j <;> simp_all [Dshift, degShift]

/-- `Δ² = 0` holds iff `h = -t`, `a = l - t` and `b = -l`. -/
theorem Dshift_sq {R : Type*} [CommRing R] (t h a b l : R) :
    Dshift t h a b l * Dshift t h a b l = 0 ↔ h = -t ∧ a = l - t ∧ b = -l := by
  constructor
  · intro hsq
    have e1 := congrFun (congrFun hsq 4) 1
    have e3 := congrFun (congrFun hsq 5) 3
    have e4 := congrFun (congrFun hsq 7) 3
    simp [Dshift, Matrix.mul_apply, Fin.sum_univ_eight] at e1 e3 e4
    refine ⟨by linear_combination e1, by linear_combination e1 - e3, by linear_combination -e4⟩
  · rintro ⟨rfl, rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Dshift, Matrix.mul_apply, Fin.sum_univ_eight] <;> ring

/-- The normalized transition block `T_λ` of `eq:ONT` (`t = 1`). -/
def Dlam {R : Type*} [CommRing R] (l : R) : Matrix (Fin 8) (Fin 8) R :=
  Dshift 1 (-1) (l - 1) (-l) l

theorem Dlam_sq {R : Type*} [CommRing R] (l : R) : Dlam l * Dlam l = 0 :=
  (Dshift_sq _ _ _ _ _).2 ⟨rfl, rfl, rfl⟩

/-- The filtered change of basis `Σ_H⁻ ↦ Σ_H⁻ + λ Σ_H⁺`. -/
def Pshift {R : Type*} [CommRing R] (l : R) : Matrix (Fin 8) (Fin 8) R :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, l, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

theorem Pshift_mul_inv {R : Type*} [CommRing R] (l : R) : Pshift l * Pshift (-l) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pshift, Matrix.mul_apply, Fin.sum_univ_eight]

/-- The full connection matrices for different `λ` are conjugate: `P_λ D_λ = D_0 P_λ`. -/
theorem Dlam_conj {R : Type*} [CommRing R] (l : R) : Pshift l * Dlam l = Dlam 0 * Pshift l := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pshift, Dlam, Dshift, Matrix.mul_apply, Fin.sum_univ_eight] <;> ring

/-- With `t = 1`, every admissible matrix is `Dlam λ`: the connection matrices of the shift are
`Δ₋ ⊕ Δ₊ + T_λ`. -/
theorem Dshift_eq_Dlam {R : Type*} [CommRing R] (h a b l : R)
    (hsq : Dshift 1 h a b l * Dshift 1 h a b l = 0) : Dshift 1 h a b l = Dlam l := by
  obtain ⟨rfl, rfl, rfl⟩ := (Dshift_sq _ _ _ _ _).1 hsq
  rfl

/-- The data shared by all `T_λ`: `T Σ_G⁻ = Σ_G⁺`, `T Σ_I⁻ = -Σ_I⁺`, and `a + b = -1` for
`T Σ_H⁻ = a Σ_I⁺ + b Σ_C⁺`. -/
theorem Dlam_common {R : Type*} [CommRing R] (l : R) :
    Dlam l 4 0 = 1 ∧ Dlam l 5 1 = -1 ∧ Dlam l 5 2 + Dlam l 7 2 = -1 := by
  refine ⟨by simp [Dlam, Dshift], by simp [Dlam, Dshift], ?_⟩
  simp [Dlam, Dshift]
  ring

/-- The representative `T_1`: `T_1 Σ_H⁻ = -Σ_C⁺` and `T_1 Σ_C⁻ = Σ_H⁺`. -/
theorem Dlam_one {R : Type*} [CommRing R] :
    Dlam (1 : R) 5 2 = 0 ∧ Dlam (1 : R) 7 2 = -1 ∧ Dlam (1 : R) 6 3 = 1 := by
  simp [Dlam, Dshift]

/-- The transition block `T_λ` alone, from `(Σ_G⁻, Σ_I⁻, Σ_H⁻, Σ_C⁻)` to
`(Σ_G⁺, Σ_I⁺, Σ_H⁺, Σ_C⁺)`. -/
def Tblk {R : Type*} [CommRing R] (l : R) : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0; 0, -1, l - 1, 0; 0, 0, 0, l; 0, 0, -l, 0]

theorem Tblk_eq {R : Type*} [CommRing R] (l : R) (i j : Fin 4) :
    Tblk l i j = Dlam l ⟨i + 4, by omega⟩ ⟨j, by omega⟩ := by
  fin_cases i <;> fin_cases j <;> simp [Tblk, Dlam, Dshift]

theorem Tblk_det {R : Type*} [CommRing R] (l : R) : (Tblk l).det = -l ^ 2 := by
  simp [Tblk, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  ring

/-- `T_0` has no entry from `Σ_C⁻` and no entry into `Σ_C⁺`. -/
theorem Tblk_zero_C {R : Type*} [CommRing R] :
    (∀ i, Tblk (0 : R) i 3 = 0) ∧ ∀ j, Tblk (0 : R) 3 j = 0 := by
  constructor <;> intro k <;> fin_cases k <;> simp [Tblk]

/-- The blocks `T_λ` are not conjugate: no change of bases of the UV and IR generators takes `T_0`
to `T_1`. -/
theorem Tblk_not_equiv {R : Type*} [CommRing R] [Nontrivial R] (A B : Matrix (Fin 4) (Fin 4) R) :
    A * Tblk 0 * B ≠ Tblk 1 := by
  intro h
  have := congrArg Matrix.det h
  simp [Matrix.det_mul, Tblk_det] at this

/-- `T_λ` has rank `4` for `λ ≠ 0`, in particular `T_1`. -/
theorem Tblk_rank_of_ne {K : Type*} [Field K] {l : K} (hl : l ≠ 0) : (Tblk l).rank = 4 := by
  have h : IsUnit (Tblk l).det := by
    rw [Tblk_det]; exact (neg_ne_zero.2 (pow_ne_zero 2 hl)).isUnit
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h), Fintype.card_fin]

/-- The column operation `Σ_H⁻ ↦ Σ_H⁻ - Σ_I⁻`, which brings `T_0` to diagonal form. -/
def Qblk {R : Type*} [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0; 0, 1, -1, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- `T_0` has rank `2`. -/
theorem Tblk_rank_zero {K : Type*} [Field K] : (Tblk (0 : K)).rank = 2 := by
  classical
  have hQ : IsUnit (Qblk : Matrix (Fin 4) (Fin 4) K).det := by
    have : (Qblk : Matrix (Fin 4) (Fin 4) K).det = 1 := by
      simp [Qblk, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    rw [this]; exact isUnit_one
  have hD : Tblk (0 : K) * Qblk = Matrix.diagonal ![1, -1, 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Tblk, Qblk, Matrix.mul_apply, Fin.sum_univ_four]
  rw [← Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQ, hD, Matrix.rank_diagonal]
  rw [Fintype.card_subtype]
  have : Finset.univ.filter (fun i : Fin 4 => (![1, -1, 0, 0] : Fin 4 → K) i ≠ 0) = {0, 1} := by
    ext i; fin_cases i <;> simp
  rw [this]
  rfl

/-- `T_λ Σ_H⁻ ≠ 0` for every `λ`: its coefficients sum to `-1`. -/
theorem Dlam_H_ne_zero {R : Type*} [CommRing R] [Nontrivial R] (l : R) :
    Dlam l 5 2 ≠ 0 ∨ Dlam l 7 2 ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  simp [Dlam, Dshift] at h1 h2
  have : (1 : R) = 0 := by linear_combination h2 - h1
  exact one_ne_zero this

/-- A transition block preserving all labels is excluded for degree reasons. -/
theorem label_preserving_excluded : degShift 3 ≠ degShift 7 + 1 ∧ degShift 2 ≠ degShift 6 + 1 := by
  decide

/-- Over `𝔽₂` (`t = h = 1`), every admissible matrix is `Dlam λ`. -/
theorem Dshift_F2 (a b l : ZMod 2) (hsq : Dshift 1 1 a b l * Dshift 1 1 a b l = 0) :
    Dshift 1 1 a b l = Dlam l := by
  obtain ⟨-, ha, hb⟩ := (Dshift_sq _ _ _ _ _).1 hsq
  subst ha hb
  have : (-1 : ZMod 2) = 1 := by decide
  simp [Dlam, this]

/-! ## Proposition `prop:torus`(iii)

Generators `Σ_U(A), Σ_U(B), Σ_I(B), Σ_I(A)` of degrees `2, 1, 1, 0`. The UV and IR blocks
vanish, and the only entries allowed by degree and order are `x` from `Σ_U(A)` to `Σ_I(B)` and
`y` from `Σ_U(B)` to `Σ_I(A)`. -/

def Dtorus {R : Type*} [CommRing R] (x y : R) : Matrix (Fin 4) (Fin 4) R :=
  !![0, 0, 0, 0; 0, 0, 0, 0; x, 0, 0, 0; 0, y, 0, 0]

theorem Dtorus_sq {R : Type*} [CommRing R] (x y : R) : Dtorus x y * Dtorus x y = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dtorus, Matrix.mul_apply, Fin.sum_univ_four]

theorem Dtorus_acyclic_iff {K : Type*} [Field K] (x y : K) :
    Acyclic (Dtorus x y) ↔ x ≠ 0 ∧ y ≠ 0 := by
  have hmv : ∀ v : Fin 4 → K, Dtorus x y *ᵥ v = ![0, 0, x * v 0, y * v 1] := by
    intro v; ext i; fin_cases i <;> simp [Dtorus, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  constructor
  · intro h
    constructor
    · rintro rfl
      obtain ⟨w, hw⟩ := h (Pi.single 0 1) (by
        rw [hmv]; ext i; fin_cases i <;> simp)
      have := congrFun hw 0
      rw [hmv] at this
      simp at this
    · rintro rfl
      obtain ⟨w, hw⟩ := h (Pi.single 1 1) (by
        rw [hmv]; ext i; fin_cases i <;> simp)
      have := congrFun hw 1
      rw [hmv] at this
      simp at this
  · rintro ⟨hx, hy⟩ v hv
    rw [hmv] at hv
    have h2 := congrFun hv 2
    have h3 := congrFun hv 3
    simp [hx, hy] at h2 h3
    refine ⟨![v 2 / x, v 3 / y, 0, 0], ?_⟩
    rw [hmv]
    ext i
    fin_cases i <;> simp [h2, h3, mul_div_cancel₀, hx, hy]

/-- Over `𝔽₂` the one-sided connection matrix is forced: `x = y = 1`. -/
theorem Dtorus_F2 (x y : ZMod 2) (h : Acyclic (Dtorus x y)) : x = 1 ∧ y = 1 := by
  obtain ⟨hx, hy⟩ := (Dtorus_acyclic_iff x y).1 h
  exact ⟨zmod2_eq_one_of_ne_zero hx, zmod2_eq_one_of_ne_zero hy⟩

/-! ## Theorem `thm:M`: the connection matrix of the doubled compactified Gubser flow

Generators `Σ_U(A), TC⁻, TC⁺, Σ_I(A)` of degrees `3, 2, 1, 0`. The possible entries are `p`
(`Σ_U(A) → TC⁻`), `q` (`TC⁻ → TC⁺`) and `r` (`TC⁺ → Σ_I(A)`). -/

def DM {R : Type*} [CommRing R] (p q r : R) : Matrix (Fin 4) (Fin 4) R :=
  !![0, 0, 0, 0; p, 0, 0, 0; 0, q, 0, 0; 0, 0, r, 0]

theorem DM_mulVec {R : Type*} [CommRing R] (p q r : R) (v : Fin 4 → R) :
    DM p q r *ᵥ v = ![0, p * v 0, q * v 1, r * v 2] := by
  ext i; fin_cases i <;> simp [DM, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- `H_3 = 0` (`Σ_U(A)` is not a cycle), `H_0 ≠ 0` (nothing hits degree `0`) and `Δ² = 0` force
`p ≠ 0` and `q = r = 0`. -/
theorem DM_forced {K : Type*} [Field K] (p q r : K) (hsq : DM p q r * DM p q r = 0)
    (h3 : ∀ x : K, DM p q r *ᵥ Pi.single 0 x = 0 → x = 0)
    (h0 : ∀ w : Fin 4 → K, (DM p q r *ᵥ w) 3 = 0) : p ≠ 0 ∧ q = 0 ∧ r = 0 := by
  have hp : p ≠ 0 := by
    rintro rfl
    have := h3 1 (by rw [DM_mulVec]; ext i; fin_cases i <;> simp)
    exact one_ne_zero this
  have hr : r = 0 := by
    have := h0 (Pi.single 2 1)
    rw [DM_mulVec] at this
    simpa using this
  have hqp : q * p = 0 := by
    have := congrFun (congrFun hsq 2) 0
    simpa [DM, Matrix.mul_apply, Fin.sum_univ_four] using this
  exact ⟨hp, (mul_eq_zero.1 hqp).resolve_right hp, hr⟩

/-- For `Δ Σ_U(A) = TC⁻` and all other entries zero, the cycles are `v₀ = 0` and the boundaries
are `v₀ = v₂ = v₃ = 0`, so `H(Δ)` is spanned by `TC⁺` and `Σ_I(A)`, i.e. `F[1] ⊕ F[0]`. -/
theorem DM_homology {K : Type*} [Field K] (v : Fin 4 → K) :
    (DM (1 : K) 0 0 *ᵥ v = 0 ↔ v 0 = 0) ∧
    ((∃ w, DM (1 : K) 0 0 *ᵥ w = v) ↔ v 0 = 0 ∧ v 2 = 0 ∧ v 3 = 0) := by
  constructor
  · rw [DM_mulVec]
    constructor
    · intro h; simpa using congrFun h 1
    · intro h; ext i; fin_cases i <;> simp [h]
  · constructor
    · rintro ⟨w, rfl⟩
      simp [DM_mulVec]
    · rintro ⟨h0, h2, h3⟩
      refine ⟨![v 1, 0, 0, 0], ?_⟩
      rw [DM_mulVec]; ext i; fin_cases i <;> simp [h0, h2, h3]

theorem DM_F2 (p q r : ZMod 2) (hsq : DM p q r * DM p q r = 0)
    (h3 : ∀ x : ZMod 2, DM p q r *ᵥ Pi.single 0 x = 0 → x = 0)
    (h0 : ∀ w : Fin 4 → ZMod 2, (DM p q r *ᵥ w) 3 = 0) : p = 1 ∧ q = 0 ∧ r = 0 := by
  obtain ⟨hp, hq, hr⟩ := DM_forced p q r hsq h3 h0
  exact ⟨zmod2_eq_one_of_ne_zero hp, hq, hr⟩

/-! ## Index bookkeeping -/

/-- Proposition `prop:boundary`: a hyperbolic UV point of fiber index `μ` has index `μ + 1` in
the double, an IR point has index `μ`. The table `tab:gubser` and the `O(N)` shift. -/
theorem double_indices :
    -- Gubser: Σ_U(A), Σ_U(B), Σ_U(C) have μ = 2, 1, 1; Σ_I(A), Σ_I(B), Σ_I(C) have μ = 0, 1, 1.
    (2 + 1, 1 + 1, 1 + 1, 0, 1, 1) = (3, 2, 2, 0, 1, 1) ∧
    -- `O(N)`: UV (`N₋ > 4`) μ = 0, 1, 1, 2 for G, I, H, C; IR (`N₊ < 4`) μ = 0, 1, 2, 1.
    (0 + 1, 1 + 1, 1 + 1, 2 + 1) = (degShift 0, degShift 1, degShift 2, degShift 3) ∧
    (0, 1, 2, 1) = (degShift 4, degShift 5, degShift 6, degShift 7) := by
  decide

/-- Fredholm indices `μ₋ - μ₊` quoted in the paper. -/
theorem fredholm_counts :
    -- Gubser pairs: U(A)→I(A), U(B)→I(A), U(A)→I(B), U(B)→I(B)
    ((2 : ℤ) - 0, (1 : ℤ) - 0, (2 : ℤ) - 1, (1 : ℤ) - 1) = (2, 1, 1, 0) ∧
    -- the reduced (planar) separatrix, the `O(N)` diagonal solution, Bjorken
    ((0 : ℤ) - 1, (1 : ℤ) - 2, (0 : ℤ) - 0) = (-1, -1, 0) := by
  decide

end ConleyCheck
