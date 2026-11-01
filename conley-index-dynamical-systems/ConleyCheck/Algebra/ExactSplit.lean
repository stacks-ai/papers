import Mathlib

/-!
# Exactness under isomorphisms, and splitting over division rings

Exactness of `f, g` is preserved by composing with linear equivalences at the ends or in the
middle. Over a division ring, an exact sequence `A → B → C → D → E` gives
`C ≅ coker(A → B) × ker(D → E)` (`exact_split`).
-/

namespace ConleyCheck

open Function

variable {R : Type*} [Ring R] {M₁ M₂ M₃ N : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
  [AddCommGroup M₃] [AddCommGroup N] [Module R M₁] [Module R M₂] [Module R M₃] [Module R N]
  {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃}

theorem exact_comp_equiv_left (e : N ≃ₗ[R] M₁) (h : Exact f g) :
    Exact (f ∘ₗ e.toLinearMap) g := by
  intro y
  rw [h y]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e.symm x, by simp⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e x, rfl⟩

theorem exact_equiv_comp_right (e : M₃ ≃ₗ[R] N) (h : Exact f g) :
    Exact f (e.toLinearMap ∘ₗ g) := by
  intro y
  rw [← h y]
  simp

theorem exact_equiv_middle (e : M₂ ≃ₗ[R] N) (h : Exact f g) :
    Exact (e.toLinearMap ∘ₗ f) (g ∘ₗ e.symm.toLinearMap) := by
  intro y
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply, Set.mem_range]
  rw [h (e.symm y)]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [hx, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [← hx, LinearEquiv.symm_apply_apply]⟩

theorem subsingleton_of_exact {P : Type*} [AddCommGroup P] [Module R P] [Subsingleton P]
    {q : P →ₗ[R] M₁} {e : M₁ →ₗ[R] M₂} (he : Exact q e) [Subsingleton M₂] : Subsingleton M₁ := by
  refine ⟨fun x y => ?_⟩
  have hxy : e (x - y) = 0 := by rw [map_sub, Subsingleton.elim (e x) (e y), sub_self]
  obtain ⟨z, hz⟩ := (he _).1 hxy
  rw [Subsingleton.elim z 0, map_zero] at hz
  exact sub_eq_zero.1 hz.symm

theorem subsingleton_of_surjective {P : Type*} [Subsingleton P] {q : P → M₁}
    (hq : Surjective q) : Subsingleton M₁ :=
  ⟨fun x y => by
    obtain ⟨a, rfl⟩ := hq x
    obtain ⟨b, rfl⟩ := hq y
    rw [Subsingleton.elim a b]⟩

/-- Two exact sequences `S_{k+1} → R_{k+1} → A_k` with `S_0 → R_0` onto, and
`S_{k+1} → A_{k+1} → R_k` with `S_0 → A_0` onto, with all `S_k = 0`, force `A_k = R_k = 0`. -/
theorem subsingleton_of_two_les {A Rr S : ℕ → Type*} [∀ k, AddCommGroup (A k)]
    [∀ k, AddCommGroup (Rr k)] [∀ k, AddCommGroup (S k)] [∀ k, Module R (A k)]
    [∀ k, Module R (Rr k)] [∀ k, Module R (S k)] (hS : ∀ k, Subsingleton (S k))
    (p : ∀ k, S k →ₗ[R] Rr k) (d : ∀ k, Rr (k + 1) →ₗ[R] A k) (h1 : ∀ k, Exact (p (k + 1)) (d k))
    (h0 : Surjective (p 0)) (p' : ∀ k, S k →ₗ[R] A k) (d' : ∀ k, A (k + 1) →ₗ[R] Rr k)
    (h1' : ∀ k, Exact (p' (k + 1)) (d' k)) (h0' : Surjective (p' 0)) :
    ∀ k, Subsingleton (A k) ∧ Subsingleton (Rr k) := by
  intro k
  induction k with
  | zero =>
    haveI := hS 0
    exact ⟨subsingleton_of_surjective h0', subsingleton_of_surjective h0⟩
  | succ k ih =>
    haveI := hS (k + 1)
    haveI := ih.1
    haveI := ih.2
    exact ⟨subsingleton_of_exact (h1' k), subsingleton_of_exact (h1 k)⟩

variable {K : Type*} [DivisionRing K] {A B C D E : Type*} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] [Module K A] [Module K B] [Module K C]
  [Module K D] [Module K E]

/-- Over a division ring, an exact sequence `A → B → C → D → E` gives
`C ≅ coker(A → B) × ker(D → E)`. -/
theorem exact_split {f : A →ₗ[K] B} {g : B →ₗ[K] C} {h : C →ₗ[K] D} {j : D →ₗ[K] E}
    (hfg : Exact f g) (hgh : Exact g h) (hhj : Exact h j) :
    Nonempty (C ≃ₗ[K] (B ⧸ LinearMap.range f) × LinearMap.ker j) := by
  have e1 : LinearMap.ker g = LinearMap.range f := (LinearMap.exact_iff.1 hfg)
  have e2 : LinearMap.ker h = LinearMap.range g := (LinearMap.exact_iff.1 hgh)
  have e3 : LinearMap.ker j = LinearMap.range h := (LinearMap.exact_iff.1 hhj)
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (LinearMap.ker h)
  have eA : LinearMap.ker h ≃ₗ[K] B ⧸ LinearMap.range f :=
    (LinearEquiv.ofEq _ _ e2).trans ((LinearMap.quotKerEquivRange g).symm.trans
      (Submodule.quotEquivOfEq _ _ e1))
  have eB : q ≃ₗ[K] LinearMap.ker j :=
    (Submodule.quotientEquivOfIsCompl _ _ hq).symm.trans ((LinearMap.quotKerEquivRange h).trans
      (LinearEquiv.ofEq _ _ e3.symm))
  exact ⟨(Submodule.prodEquivOfIsCompl _ _ hq).symm.trans (eA.prodCongr eB)⟩

/-- Over a division ring, an exact sequence `A → B → C → 0` gives `C ≅ coker(A → B)`. -/
theorem exact_coker {f : A →ₗ[K] B} {g : B →ₗ[K] C} (hfg : Exact f g) (hg : Surjective g) :
    Nonempty (C ≃ₗ[K] B ⧸ LinearMap.range f) :=
  ⟨(LinearMap.quotKerEquivOfSurjective g hg).symm.trans
    (Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.1 hfg))⟩

section Rank

variable {A B C A' B' C' : ℕ → Type*} [∀ k, AddCommGroup (A k)] [∀ k, Module K (A k)]
  [∀ k, AddCommGroup (B k)] [∀ k, Module K (B k)] [∀ k, AddCommGroup (C k)] [∀ k, Module K (C k)]
  [∀ k, FiniteDimensional K (A k)] [∀ k, FiniteDimensional K (B k)]
  [∀ k, AddCommGroup (A' k)] [∀ k, Module K (A' k)] [∀ k, AddCommGroup (B' k)]
  [∀ k, Module K (B' k)] [∀ k, AddCommGroup (C' k)] [∀ k, Module K (C' k)]
  [∀ k, FiniteDimensional K (A' k)] [∀ k, FiniteDimensional K (B' k)]

/-- In an exact sequence `⋯ → A_k → B_k → C_k → A_{k-1} → ⋯ → B_0 → C_0 → 0` of vector spaces,
with the first map `Ψ_k` and `A_k`, `B_k` finite-dimensional,
`dim C_0 + rk Ψ_0 = dim B_0` and `dim C_{k+1} + rk Ψ_{k+1} + rk Ψ_k = dim B_{k+1} + dim A_k`. -/
theorem les_finrank {Ψ : ∀ k, A k →ₗ[K] B k} {i : ∀ k, B k →ₗ[K] C k}
    {p : ∀ k, C (k + 1) →ₗ[K] A k} (h1 : ∀ k, Exact (Ψ k) (i k))
    (h2 : ∀ k, Exact (i (k + 1)) (p k)) (h3 : ∀ k, Exact (p k) (Ψ k)) (h0 : Surjective (i 0)) :
    Module.finrank K (C 0) + Module.finrank K (LinearMap.range (Ψ 0)) = Module.finrank K (B 0) ∧
    ∀ k, Module.finrank K (C (k + 1)) + Module.finrank K (LinearMap.range (Ψ (k + 1))) +
      Module.finrank K (LinearMap.range (Ψ k)) =
        Module.finrank K (B (k + 1)) + Module.finrank K (A k) := by
  refine ⟨?_, fun k => ?_⟩
  · obtain ⟨e⟩ := exact_coker (h1 0) h0
    rw [e.finrank_eq, Submodule.finrank_quotient_add_finrank]
  · obtain ⟨e⟩ := exact_split (h1 (k + 1)) (h2 k) (h3 k)
    have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range (Ψ (k + 1)))
    have hk := LinearMap.finrank_range_add_finrank_ker (Ψ k)
    rw [e.finrank_eq, Module.finrank_prod]
    omega

/-- The ranks of the first maps of two such exact sequences agree if the dimensions of the three
families of spaces agree. -/
theorem les_finrank_range_eq {Ψ : ∀ k, A k →ₗ[K] B k} {i : ∀ k, B k →ₗ[K] C k}
    {p : ∀ k, C (k + 1) →ₗ[K] A k} (h1 : ∀ k, Exact (Ψ k) (i k))
    (h2 : ∀ k, Exact (i (k + 1)) (p k)) (h3 : ∀ k, Exact (p k) (Ψ k)) (h0 : Surjective (i 0))
    {Ψ' : ∀ k, A' k →ₗ[K] B' k} {i' : ∀ k, B' k →ₗ[K] C' k}
    {p' : ∀ k, C' (k + 1) →ₗ[K] A' k} (h1' : ∀ k, Exact (Ψ' k) (i' k))
    (h2' : ∀ k, Exact (i' (k + 1)) (p' k)) (h3' : ∀ k, Exact (p' k) (Ψ' k))
    (h0' : Surjective (i' 0)) (hA : ∀ k, Module.finrank K (A k) = Module.finrank K (A' k))
    (hB : ∀ k, Module.finrank K (B k) = Module.finrank K (B' k))
    (hC : ∀ k, Module.finrank K (C k) = Module.finrank K (C' k)) (k : ℕ) :
    Module.finrank K (LinearMap.range (Ψ k)) = Module.finrank K (LinearMap.range (Ψ' k)) := by
  obtain ⟨e0, e⟩ := les_finrank h1 h2 h3 h0
  obtain ⟨e0', e'⟩ := les_finrank h1' h2' h3' h0'
  induction k with
  | zero =>
    have := hB 0
    have := hC 0
    omega
  | succ k ih =>
    have := e k
    have := e' k
    have := hA k
    have := hB (k + 1)
    have := hC (k + 1)
    omega

end Rank

end ConleyCheck
