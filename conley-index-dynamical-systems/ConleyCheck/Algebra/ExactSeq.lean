import Mathlib

/-!
# The homological algebra of section `sec:theory`

The topological input of each statement (existence of the attractor–repeller sequence, the
boundary indices of Proposition `prop:boundary`, McCord duality) is taken as a hypothesis, and we
verify the algebra that the paper derives from it. Palmer's theorem itself is proved in
`ConleyCheck.Palmer.palmer`, which uses `fredholm_index_eq` and `sup_eq_top_iff_inf_eq_bot`.

* `bijective_of_exact_of_subsingleton`: the step in Theorem `thm:slab` (repeller index zero), in
  Theorem `thm:rate`(ii) (`CH_*(S^♮) = 0` forces `Ψ` to be an isomorphism) and in Corollary
  `cor:attractors` (`CH_*(M^±) = 0`). The full corollary is `ConleyCheck.Gubser.cor_attractors`.
* `finrank_middle`: Theorem `thm:transport`(i), `CH_k(S^♮) ≅ coker Ψ_k ⊕ ker Ψ_{k-1}`.
* `two_smul_eq_zero_of_equivariant` and its corollaries: Theorem `thm:equivariant`(ii).
* `euler_shift`, `euler_reflect`: Theorems `thm:equivariant`(iii) and `thm:duality`.
* `fredholm_index_eq`, `sup_eq_top_iff_inf_eq_bot`, `tangent_span_iff`:
  Proposition `prop:palmer`(ii), (iii).
-/

namespace ConleyCheck

open Function Module

section Exact

variable {R : Type*} [Ring R] {M₁ M₂ M₃ M₄ : Type*}
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄]
  [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄]

/-- In an exact segment `M₁ → M₂ → M₃ → M₄` with `M₁ = 0` and `M₄ = 0`, the middle map is an
isomorphism. -/
theorem bijective_of_exact_of_subsingleton {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃}
    {k : M₃ →ₗ[R] M₄} (hfg : Exact f g) (hgk : Exact g k) [Subsingleton M₁] [Subsingleton M₄] :
    Bijective g := by
  constructor
  · intro x y hxy
    have : g (x - y) = 0 := by simp [hxy]
    obtain ⟨z, hz⟩ := (hfg (x - y)).1 this
    rw [Subsingleton.elim z 0, map_zero] at hz
    exact sub_eq_zero.1 hz.symm
  · intro z
    obtain ⟨x, hx⟩ := (hgk z).1 (Subsingleton.elim _ _)
    exact ⟨x, hx⟩

/-- If the incoming connecting map vanishes, the next map is injective. -/
theorem injective_of_exact_of_zero {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃} (hfg : Exact f g)
    (hf : f = 0) : Injective g := by
  intro x y hxy
  have : g (x - y) = 0 := by simp [hxy]
  obtain ⟨z, hz⟩ := (hfg (x - y)).1 this
  rw [hf, LinearMap.zero_apply] at hz
  exact sub_eq_zero.1 hz.symm

/-- If the outgoing connecting map vanishes, the previous map is surjective. -/
theorem surjective_of_exact_of_zero {g : M₂ →ₗ[R] M₃} {k : M₃ →ₗ[R] M₄} (hgk : Exact g k)
    (hk : k = 0) : Surjective g := by
  intro z
  obtain ⟨x, hx⟩ := (hgk z).1 (by rw [hk, LinearMap.zero_apply])
  exact ⟨x, hx⟩

end Exact

section Transport

variable {K : Type*} [Field K] {P Q S P' Q' : Type*}
  [AddCommGroup P] [AddCommGroup Q] [AddCommGroup S] [AddCommGroup P'] [AddCommGroup Q']
  [Module K P] [Module K Q] [Module K S] [Module K P'] [Module K Q']
  [FiniteDimensional K Q] [FiniteDimensional K S]

/-- Theorem `thm:transport`(i): in the exact sequence
`CH_k(K₋) →Ψ_k CH_k(K₊) → CH_k(S^♮) → CH_{k-1}(K₋) →Ψ_{k-1} CH_{k-1}(K₊)`,
`dim CH_k(S^♮) = dim coker Ψ_k + dim ker Ψ_{k-1}`. -/
theorem finrank_middle (Ψ : P →ₗ[K] Q) (j : Q →ₗ[K] S) (d : S →ₗ[K] P') (Ψ' : P' →ₗ[K] Q')
    (h1 : Exact Ψ j) (h2 : Exact j d) (h3 : Exact d Ψ') :
    finrank K S = finrank K (Q ⧸ LinearMap.range Ψ) + finrank K (LinearMap.ker Ψ') := by
  have e1 := LinearMap.exact_iff.1 h1
  have e2 := LinearMap.exact_iff.1 h2
  have e3 := LinearMap.exact_iff.1 h3
  have r1 := LinearMap.finrank_range_add_finrank_ker d
  have r2 := LinearMap.finrank_range_add_finrank_ker j
  have r3 := Submodule.finrank_quotient_add_finrank (LinearMap.range Ψ)
  rw [e2] at r1
  rw [e1] at r2
  rw [e3]
  omega

end Transport

section Equivariant

variable {R : Type*} [CommRing R] {A P : Type*} [AddCommGroup A] [AddCommGroup P]
  [Module R A] [Module R P]

/-- Theorem `thm:equivariant`(ii): if the sheet exchange acts by `+1` on the attractor index, by
`-1` on the repeller index, and commutes with the connecting map `∂`, then `2∂ = 0`. -/
theorem two_smul_eq_zero_of_equivariant (d : P →ₗ[R] A) (rA : A →ₗ[R] A) (rP : P →ₗ[R] P)
    (hA : ∀ a, rA a = a) (hP : ∀ v, rP v = -v) (hcomm : ∀ v, d (rP v) = rA (d v)) :
    (2 : R) • d = 0 := by
  ext v
  have h1 := hcomm v
  rw [hP, hA, map_neg] at h1
  simp only [LinearMap.smul_apply, LinearMap.zero_apply]
  calc (2 : R) • d v = d v + d v := two_smul _ _
    _ = -d v + d v := by rw [h1]
    _ = 0 := neg_add_cancel _

/-- If `2` is invertible, `∂ = 0`. -/
theorem eq_zero_of_two_smul_eq_zero {d : P →ₗ[R] A} (h : (2 : R) • d = 0) (h2 : IsUnit (2 : R)) :
    d = 0 := by
  obtain ⟨u, hu⟩ := h2
  have : (↑u⁻¹ : R) • ((2 : R) • d) = d := by rw [← hu, smul_smul, Units.inv_mul, one_smul]
  rw [← this, h, smul_zero]

/-- If the target has no `2`-torsion, `∂ = 0` (the torsion-free case over `ℤ`). -/
theorem eq_zero_of_two_smul_eq_zero_of_noTorsion {d : P →ₗ[R] A} (h : (2 : R) • d = 0)
    (htf : ∀ a : A, (2 : R) • a = 0 → a = 0) : d = 0 := by
  ext v
  exact htf _ (by simpa using congrArg (fun φ => φ v) h)

/-- Over `𝔽₂` the identity `2∂ = 0` holds for every map, so it carries no information. -/
theorem two_smul_eq_zero_F2 {A P : Type*} [AddCommGroup A] [AddCommGroup P] [Module (ZMod 2) A]
    [Module (ZMod 2) P] (d : P →ₗ[ZMod 2] A) : (2 : ZMod 2) • d = 0 := by
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

end Equivariant

section Euler

open Finset

/-- Theorem `thm:equivariant`(iii): with `CH_k(S̃) ≅ CH_k(K₊) ⊕ CH_{k-1}(K₋)`, the reduced Euler
characteristic is `χ(K₊) - χ(K₋)`. Here `a k`, `b k` are the dimensions in degree `k`. -/
theorem euler_shift (a b : ℕ → ℤ) (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1) ^ k * (a k + if k = 0 then 0 else b (k - 1)) =
      ∑ k ∈ range (n + 1), (-1) ^ k * a k - ∑ k ∈ range n, (-1) ^ k * b k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun k => (-1 : ℤ) ^ k * a k) (n + 1),
      sum_range_succ (fun k => (-1 : ℤ) ^ k * b k) n]
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    ring

/-- The Euler characteristic identity for an involution, `χ(Y) = 2χ(Y/R) - χ(Y^R)`, combined
with Theorem `thm:slab` (`χ(Y/R) = χ(K₊)`) and `Y^R = h(K₊) ∨ h(K₋)`. -/
theorem euler_involution (χY χYR χquot χp χm : ℤ) (hY : χY = 2 * χquot - χYR)
    (hslab : χquot = χp) (hfix : χYR = χp + χm) : χY = χp - χm := by
  subst hslab hfix; linarith

/-- Theorem `thm:duality`: if `dim CH_k(K) = dim CH_{n-k}(K)` for `0 ≤ k ≤ n`, then
`χ = (-1)^n χ`. -/
theorem euler_reflect (d : ℕ → ℤ) (n : ℕ) (hd : ∀ k ≤ n, d (n - k) = d k) :
    ∑ k ∈ range (n + 1), (-1) ^ k * d k = (-1) ^ n * ∑ k ∈ range (n + 1), (-1) ^ k * d k := by
  have hsign : ∀ k ≤ n, ((-1 : ℤ) ^ (n - k)) = (-1) ^ n * (-1) ^ k := by
    intro k hk
    have h1 : ((-1 : ℤ) ^ (n - k)) * (-1) ^ k = (-1) ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    have h2 : ((-1 : ℤ) ^ k) * (-1) ^ k = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    calc ((-1 : ℤ) ^ (n - k)) = (-1) ^ (n - k) * ((-1) ^ k * (-1) ^ k) := by rw [h2, mul_one]
      _ = (-1) ^ n * (-1) ^ k := by rw [← mul_assoc, h1]
  conv_lhs => rw [← sum_range_reflect (fun k => (-1) ^ k * d k) (n + 1)]
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
  simp only [Nat.add_sub_cancel]
  rw [hsign k hk', hd k hk']
  ring

theorem euler_eq_zero_of_odd (d : ℕ → ℤ) {n : ℕ} (hn : Odd n) (hd : ∀ k ≤ n, d (n - k) = d k) :
    ∑ k ∈ range (n + 1), (-1) ^ k * d k = 0 := by
  have h := euler_reflect d n hd
  rw [hn.neg_one_pow] at h
  linarith

end Euler

section Fredholm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Proposition `prop:palmer`(ii), (iii): with `ker L ≅ E^u ∩ E^s` and
`coker L ≅ V/(E^u + E^s)`, `dim E^u = μ₋` and `dim E^s = n - μ₊`, the index is `μ₋ - μ₊`. -/
theorem fredholm_index_eq (Eu Es : Submodule K V) :
    (finrank K ↥(Eu ⊓ Es) : ℤ) - (finrank K V - finrank K ↥(Eu ⊔ Es)) =
      finrank K ↥Eu - (finrank K V - finrank K ↥Es) := by
  have := Submodule.finrank_sup_add_finrank_inf_eq Eu Es
  omega

/-- If the index is zero, `E^u + E^s = V` if and only if `E^u ∩ E^s = 0`. -/
theorem sup_eq_top_iff_inf_eq_bot {Eu Es : Submodule K V}
    (hdim : finrank K ↥Eu + finrank K ↥Es = finrank K V) : Eu ⊔ Es = ⊤ ↔ Eu ⊓ Es = ⊥ := by
  have hs := Submodule.finrank_sup_add_finrank_inf_eq Eu Es
  have hle := Submodule.finrank_le (Eu ⊔ Es)
  constructor
  · intro h
    rw [h, finrank_top] at hs
    exact Submodule.finrank_eq_zero.1 (by omega)
  · intro h
    rw [h, finrank_bot] at hs
    exact Submodule.eq_top_of_finrank_eq (by omega)

omit [FiniteDimensional K V] in
/-- The tangent spaces `⟨γ̇(0)⟩ ⊕ (E^u × 0)` and `⟨γ̇(0)⟩ ⊕ (E^s × 0)` span `V × K` if and only
if `E^u + E^s = V`, as soon as `γ̇(0)` has a nonzero `θ`-component. -/
theorem tangent_span_iff (Eu Es : Submodule K V) (ξ : V) {θ : K} (hθ : θ ≠ 0) :
    ((K ∙ (ξ, θ)) ⊔ Eu.map (LinearMap.inl K V K)) ⊔ ((K ∙ (ξ, θ)) ⊔ Es.map (LinearMap.inl K V K))
      = ⊤ ↔ Eu ⊔ Es = ⊤ := by
  have hrw : ((K ∙ (ξ, θ)) ⊔ Eu.map (LinearMap.inl K V K)) ⊔
      ((K ∙ (ξ, θ)) ⊔ Es.map (LinearMap.inl K V K)) =
      (K ∙ (ξ, θ)) ⊔ (Eu ⊔ Es).map (LinearMap.inl K V K) := by
    rw [Submodule.map_sup]
    rw [sup_sup_sup_comm, sup_idem]
  rw [hrw]
  constructor
  · intro h
    rw [eq_top_iff]
    intro x _
    have hx : ((x, 0) : V × K) ∈ (K ∙ (ξ, θ)) ⊔ (Eu ⊔ Es).map (LinearMap.inl K V K) := by
      rw [h]; trivial
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
    have h2 := congrArg Prod.snd huw
    have h1 := congrArg Prod.fst huw
    simp only [Prod.smul_mk, Prod.snd_add, LinearMap.inl_apply, add_zero, smul_eq_mul] at h2
    have hc : c = 0 := by
      rcases mul_eq_zero.1 h2 with hc | hc
      · exact hc
      · exact absurd hc hθ
    subst hc
    simp only [zero_smul, zero_add] at h1
    simp only [Prod.fst_add, Prod.fst_zero, LinearMap.inl_apply, zero_add] at h1
    rw [← h1]; exact hy
  · intro h
    rw [eq_top_iff]
    rintro ⟨x, t⟩ _
    refine Submodule.mem_sup.2 ⟨(t / θ) • (ξ, θ), Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self _), (x - (t / θ) • ξ, 0), ?_, ?_⟩
    · rw [h, Submodule.map_top]
      exact ⟨x - (t / θ) • ξ, rfl⟩
    · ext
      · simp
      · simp [div_mul_cancel₀ t hθ]

end Fredholm

end ConleyCheck
