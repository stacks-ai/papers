import ConleyCheck.Conley.CircleSign
import ConleyCheck.Algebra.ExactSplit

/-!
# Euler characteristics of the circle double

Theorem `thm:equivariant`(iii) over a field `F`, for truncated Euler characteristics
`χ_N(M) = ∑_{k ≤ N} (-1)^k dim M_k`:

* `les_euler`: in a long exact sequence `⋯ → A_k → B_k → C_k → A_{k-1} → ⋯ → C_0 → 0` of
  finite-dimensional spaces with `C_{N+1} = 0`, `χ_N(B) = χ_N(A) + χ_N(C)`;
* `equivariant_iii`: if `CH_N(K₋; f₋) = 0`, then
  `χ_N(S̃) = χ_N(K₊; f₊) - χ_{N-1}(K₋; f₋)`, and, with `χ_N(S) = χ_N(K₊; f₊)` (Theorem `thm:slab`),
  `χ_N(S̃) = 2 χ_N(S) - (χ_N(K₊; f₊) + χ_{N-1}(K₋; f₋))`.

Over a field this needs no hypothesis on the characteristic: it uses only the exact sequence of the
attractor–repeller pair, not the splitting of Theorem `thm:equivariant`(ii).
-/

namespace ConleyCheck.Conley

open Finset Function

universe u

/-- `∑_{k ≤ N} (-1)^k d_k`. -/
def eulerSum (d : ℕ → ℕ) (N : ℕ) : ℤ := ∑ k ∈ range (N + 1), (-1) ^ k * (d k : ℤ)

section LES

variable {K : Type*} [Field K]

/-- The middle term of an exact sequence of finite-dimensional spaces is finite-dimensional. -/
theorem finiteDimensional_of_exact {A B C : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B]
    [Module K B] [AddCommGroup C] [Module K C] [FiniteDimensional K A] [FiniteDimensional K C]
    {f : A →ₗ[K] B} {g : B →ₗ[K] C} (h : Exact f g) : FiniteDimensional K B := by
  refine Module.finite_def.2 (Submodule.fg_of_fg_map_of_fg_inf_ker g
    (IsNoetherian.noetherian _) ?_)
  rw [top_inf_eq, h.linearMap_ker_eq, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map f

variable {A B C : ℕ → Type*} [∀ k, AddCommGroup (A k)] [∀ k, Module K (A k)]
  [∀ k, AddCommGroup (B k)] [∀ k, Module K (B k)] [∀ k, AddCommGroup (C k)] [∀ k, Module K (C k)]
  [∀ k, FiniteDimensional K (A k)] [∀ k, FiniteDimensional K (B k)]
  {Ψ : ∀ k, A k →ₗ[K] B k} {i : ∀ k, B k →ₗ[K] C k} {p : ∀ k, C (k + 1) →ₗ[K] A k}

theorem les_euler_aux (h1 : ∀ k, Exact (Ψ k) (i k)) (h2 : ∀ k, Exact (i (k + 1)) (p k))
    (h3 : ∀ k, Exact (p k) (Ψ k)) (h0 : Surjective (i 0)) (N : ℕ) :
    eulerSum (fun k => Module.finrank K (B k)) N - eulerSum (fun k => Module.finrank K (A k)) N -
      eulerSum (fun k => Module.finrank K (C k)) N =
      (-1) ^ N * ((Module.finrank K (LinearMap.range (Ψ N)) : ℤ) - Module.finrank K (A N)) := by
  obtain ⟨e0, e⟩ := ConleyCheck.les_finrank h1 h2 h3 h0
  induction N with
  | zero =>
    simp only [eulerSum, zero_add, sum_range_one, pow_zero, one_mul]
    have := congrArg (Nat.cast : ℕ → ℤ) e0
    push_cast at this
    linarith
  | succ N ih =>
    simp only [eulerSum] at ih ⊢
    rw [sum_range_succ, sum_range_succ (fun k => (-1 : ℤ) ^ k * (Module.finrank K (A k) : ℤ)),
      sum_range_succ (fun k => (-1 : ℤ) ^ k * (Module.finrank K (C k) : ℤ))]
    have := congrArg (Nat.cast : ℕ → ℤ) (e N)
    push_cast at this
    linear_combination ih + (-1 : ℤ) ^ N * this

/-- The Euler characteristic of a long exact sequence. -/
theorem les_euler (h1 : ∀ k, Exact (Ψ k) (i k)) (h2 : ∀ k, Exact (i (k + 1)) (p k))
    (h3 : ∀ k, Exact (p k) (Ψ k)) (h0 : Surjective (i 0)) (N : ℕ) (hN : Subsingleton (C (N + 1))) :
    eulerSum (fun k => Module.finrank K (B k)) N =
      eulerSum (fun k => Module.finrank K (A k)) N + eulerSum (fun k => Module.finrank K (C k)) N := by
  have hinj : Injective (Ψ N) := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    obtain ⟨c, rfl⟩ := (h3 N a).1 ha
    rw [Subsingleton.elim c 0, map_zero]
  have h := les_euler_aux h1 h2 h3 h0 N
  rw [LinearMap.finrank_range_of_inj hinj, sub_self, mul_zero] at h
  linarith

end LES

/-! ### Theorem `thm:equivariant`(iii) -/

section Double

variable {X : Type u} [TopologicalSpace X] [T2Space X] [TopologicalSpace.MetrizableSpace X]
  {Φ : Flow ℝ (X × Tau)} {θ : Flow ℝ Tau} (hΦ : IsSkew Φ θ) (hθ : IsHeight θ (fun b => (b : ℝ)))

include hΦ hθ in
/-- Theorem `thm:equivariant`(iii) over a field `F`. If `CH_*(K_±; f_±)` are finite-dimensional
and `CH_N(K₋; f₋) = 0`, then
`χ_N(S̃) = χ_N(K₊; f₊) - χ_{N-1}(K₋; f₋) = 2 χ_N(S) - (χ_N(K₊; f₊) + χ_{N-1}(K₋; f₋))`,
where `χ_N(M) = ∑_{k ≤ N} (-1)^k dim CH_k(M)`. When the indices vanish above degree `N`
these are the full reduced Euler characteristics of the Conley indices. -/
theorem equivariant_iii (F : Type u) [Field F] {S : Set (X × Tau)}
    (hS : IsIsolatedInvariantSet Φ S)
    (h : IsAttractorRepellerPair (circΦ hΦ hθ) (cq ⁻¹' S) ({x | (x, Tau.top) ∈ S} ×ˢ {Circ.zero})
      ({x | (x, Tau.bot) ∈ S} ×ˢ {Circ.pi}))
    (hKp : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ)) {x | (x, Tau.top) ∈ S})
    (hKm : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ)) {x | (x, Tau.bot) ∈ S})
    [hfp : ∀ k, FiniteDimensional F (homologyIndex F (fiberFlow hΦ Tau.top (base_top hθ)) hKp k)]
    [hfm : ∀ k, FiniteDimensional F (homologyIndex F (fiberFlow hΦ Tau.bot (base_bot hθ)) hKm k)]
    (N : ℕ) (hN : Subsingleton (homologyIndex F (fiberFlow hΦ Tau.bot (base_bot hθ)) hKm N)) :
    eulerSum (fun k => Module.finrank F (homologyIndex F (circΦ hΦ hθ) h.isolated k)) N =
        eulerSum (fun k => Module.finrank F
          (homologyIndex F (fiberFlow hΦ Tau.top (base_top hθ)) hKp k)) N -
        ∑ k ∈ range N, (-1) ^ k * (Module.finrank F
          (homologyIndex F (fiberFlow hΦ Tau.bot (base_bot hθ)) hKm k) : ℤ) ∧
      eulerSum (fun k => Module.finrank F (homologyIndex F (circΦ hΦ hθ) h.isolated k)) N =
        2 * eulerSum (fun k => Module.finrank F (homologyIndex F Φ hS k)) N -
          (eulerSum (fun k => Module.finrank F
            (homologyIndex F (fiberFlow hΦ Tau.top (base_top hθ)) hKp k)) N +
          ∑ k ∈ range N, (-1) ^ k * (Module.finrank F
            (homologyIndex F (fiberFlow hΦ Tau.bot (base_bot hθ)) hKm k) : ℤ)) := by
  obtain ⟨i, p, d, h1, h2, h3, h0, -, -⟩ := equivariant_ii hΦ hθ F hS h
  have hA := circ_index_attractor hΦ hθ F h.isolated_A hKp
  obtain ⟨hR, hR0⟩ := circ_index_repeller hΦ hθ F h.isolated_R hKm
  have dA : ∀ k, Module.finrank F (homologyIndex F (circΦ hΦ hθ) h.isolated_A k) =
      Module.finrank F (homologyIndex F (fiberFlow hΦ Tau.top (base_top hθ)) hKp k) :=
    fun k => (hA k).some.finrank_eq
  have dR : ∀ k, Module.finrank F (homologyIndex F (circΦ hΦ hθ) h.isolated_R (k + 1)) =
      Module.finrank F (homologyIndex F (fiberFlow hΦ Tau.bot (base_bot hθ)) hKm k) :=
    fun k => (hR k).some.finrank_eq
  have dR0 : Module.finrank F (homologyIndex F (circΦ hΦ hθ) h.isolated_R 0) = 0 :=
    Module.finrank_zero_of_subsingleton
  have fA : ∀ k, FiniteDimensional F (homologyIndex F (circΦ hΦ hθ) h.isolated_A k) :=
    fun k => LinearEquiv.finiteDimensional (hA k).some.symm
  have fR : ∀ k, FiniteDimensional F (homologyIndex F (circΦ hΦ hθ) h.isolated_R k) := by
    intro k
    cases k with
    | zero => infer_instance
    | succ k => exact LinearEquiv.finiteDimensional (hR k).some.symm
  have fS : ∀ k, FiniteDimensional F (homologyIndex F (circΦ hΦ hθ) h.isolated k) :=
    fun k => finiteDimensional_of_exact (h1 k)
  have hsub : Subsingleton (homologyIndex F (circΦ hΦ hθ) h.isolated_R (N + 1)) :=
    (hR N).some.toEquiv.subsingleton
  have he := les_euler h1 h2 h3 h0 N hsub
  have eR : eulerSum (fun k => Module.finrank F
      (homologyIndex F (circΦ hΦ hθ) h.isolated_R k)) N =
      -∑ k ∈ range N, (-1) ^ k * (Module.finrank F
        (homologyIndex F (fiberFlow hΦ Tau.bot (base_bot hθ)) hKm k) : ℤ) := by
    unfold eulerSum
    rw [sum_range_succ']
    simp only [dR, dR0, pow_succ, Nat.cast_zero, mul_zero, add_zero]
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun k _ => by ring
  have eA : eulerSum (fun k => Module.finrank F
      (homologyIndex F (circΦ hΦ hθ) h.isolated_A k)) N =
      eulerSum (fun k => Module.finrank F
        (homologyIndex F (fiberFlow hΦ Tau.top (base_top hθ)) hKp k)) N := by
    simp only [eulerSum, dA]
  obtain ⟨-, hK', hslab⟩ := slab_index hΦ hθ F hS
  have eS : eulerSum (fun k => Module.finrank F (homologyIndex F Φ hS k)) N =
      eulerSum (fun k => Module.finrank F
        (homologyIndex F (fiberFlow hΦ Tau.top (base_top hθ)) hKp k)) N := by
    simp only [eulerSum]
    refine sum_congr rfl fun k _ => ?_
    rw [← (hslab k).some.finrank_eq]
  refine ⟨by rw [he, eA, eR]; ring, by rw [he, eA, eR, eS]; ring⟩

end Double

end ConleyCheck.Conley
