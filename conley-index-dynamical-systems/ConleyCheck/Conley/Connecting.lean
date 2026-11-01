import ConleyCheck.Conley.Nested
import ConleyCheck.Conley.Regular
import ConleyCheck.Conley.MorseSets

/-!
# The connecting map detects connecting orbits, for every index triple

For an attractor–repeller pair `(A, R)` of `S` and an index triple `N₀ ⊆ N₁ ⊆ N₂`, the connecting
map of the triple is `δ : H_{k+1}(N₂, N₁) → H_k(N₁, N₀)`.

* `singδ_eq_zero_of_subset_union`: if `S = A ∪ R`, then `δ = 0` for every index triple with
  `(N₁, N₀)` collared. Swapping the roles of `A` and `R` gives an index triple `N₀ ⊆ M₁ ⊆ N₂` for
  the swapped pair, so `(N₂, M₁)` is an index pair for `A` containing `(N₁, N₀)`. After collaring,
  `H_*(N₁, N₀) → H_*(N₂, M₁')` is an isomorphism (`singIncl_bijective_of_nested`), so
  `H_*(N₁, N₀) → H_*(N₂, N₀)` is injective and `δ = 0` by exactness.
* `exists_connecting_of_singδ_ne_zero`: hence `δ ≠ 0` for one such triple gives a connecting orbit
  from `R` to `A`. No choice of triple is involved.
-/

namespace ConleyCheck.Conley

open CategoryTheory Set

universe u

variable (K : Type u) [Ring K] {α : Type u} [TopologicalSpace α] [T2Space α] {ϕ : Flow ℝ α}
  {S A R : Set α}

/-- If `S = A ∪ R`, the connecting map of every index triple with `(N₁, N₀)` collared vanishes. -/
theorem singδ_eq_zero_of_subset_union (h : IsAttractorRepellerPair ϕ S A R) (hS : S ⊆ A ∪ R)
    {N₀ N₁ N₂ : Set α} (hT : IsIndexTriple ϕ S A R N₀ N₁ N₂) (c₁ : IsCollared ϕ N₁ N₀) (k : ℤ) :
    singδ K k N₂ N₁ N₀ = 0 := by
  obtain ⟨M₁, hT'⟩ := exists_indexTriple_of_pair (h.swap hS) hT.pair_S
  obtain ⟨M₁', hM, hPM, hcM, -⟩ := exists_collared_of_indexPair hT'.pair_R
  have h0 : N₀ ⊆ M₁' := hT'.sub₀₁.trans hM
  have hbij := singIncl_bijective_of_nested K hT.pair_A hPM c₁ hcM hT.sub₁₂ h0 k
  have hfac := singIncl_comp K k hT.sub₁₂ (subset_refl N₀) (subset_refl N₂) h0
  have hinj : Function.Injective (singIncl K k hT.sub₁₂ (subset_refl N₀)).hom := by
    intro x y hxy
    apply hbij.1
    have := congrArg (singIncl K k (subset_refl N₂) h0).hom hxy
    exact (congrArg (fun φ => φ.hom x) hfac).symm.trans
      (this.trans (congrArg (fun φ => φ.hom y) hfac))
  have hex := sing_exact_δ' K k hT.sub₀₁ hT.sub₁₂
  ext x
  apply hinj
  rw [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
  exact (hex _).2 ⟨x, rfl⟩

/-- A nonzero connecting map, for any index triple with `(N₁, N₀)` collared, gives a connecting
orbit from `R` to `A`. -/
theorem exists_connecting_of_singδ_ne_zero (h : IsAttractorRepellerPair ϕ S A R)
    {N₀ N₁ N₂ : Set α} (hT : IsIndexTriple ϕ S A R N₀ N₁ N₂) (c₁ : IsCollared ϕ N₁ N₀) {k : ℤ}
    (hδ : singδ K k N₂ N₁ N₀ ≠ 0) :
    ∃ x ∈ S, x ∉ A ∧ x ∉ R ∧ omegaLim ϕ x ⊆ A ∧ alphaLim ϕ x ⊆ R := by
  rcases h.connecting_or_eq_union with hc | hS
  · exact hc
  · exact absurd (singδ_eq_zero_of_subset_union K h hS.subset hT c₁ k) hδ

/-- The attractor–repeller sequence of `homologyIndex_attractor_repeller_of_pair`, together with
the fact that a nonzero connecting map gives a connecting orbit. -/
theorem homologyIndex_attractor_repeller_connecting (h : IsAttractorRepellerPair ϕ S A R) :
    ∃ (i : ∀ n, homologyIndex K ϕ h.isolated_A n →ₗ[K] homologyIndex K ϕ h.isolated n)
      (p : ∀ n, homologyIndex K ϕ h.isolated n →ₗ[K] homologyIndex K ϕ h.isolated_R n)
      (d : ∀ n, homologyIndex K ϕ h.isolated_R (n + 1) →ₗ[K] homologyIndex K ϕ h.isolated_A n),
      (∀ n, Function.Exact (i n) (p n)) ∧ (∀ n, Function.Exact (p (n + 1)) (d n)) ∧
        (∀ n, Function.Exact (d n) (i n)) ∧ Function.Surjective (p 0) ∧
        ∀ n, d n ≠ 0 → ∃ x ∈ S, x ∉ A ∧ x ∉ R ∧ omegaLim ϕ x ⊆ A ∧ alphaLim ϕ x ⊆ R := by
  obtain ⟨N₀, N₁, N₂, hT, c₁, c₂, c₃⟩ := exists_collared_indexTriple h
  let eA := homologyIndexEquiv K h.isolated_A hT.pair_A c₁
  let eS := homologyIndexEquiv K h.isolated hT.pair_S c₂
  let eR := homologyIndexEquiv K h.isolated_R hT.pair_R c₃
  refine ⟨fun n => (eS n).symm.toLinearMap ∘ₗ
      (singIncl K (Int.ofNat n) hT.sub₁₂ (subset_refl N₀)).hom ∘ₗ (eA n).toLinearMap,
    fun n => (eR n).symm.toLinearMap ∘ₗ
      (singIncl K (Int.ofNat n) (subset_refl N₂) hT.sub₀₁).hom ∘ₗ (eS n).toLinearMap,
    fun n => (eA n).symm.toLinearMap ∘ₗ (singδ K (Int.ofNat n) N₂ N₁ N₀).hom ∘ₗ
      (eR (n + 1)).toLinearMap, fun n => ?_, fun n => ?_, fun n => ?_, ?_, fun n hd => ?_⟩
  · exact exact_conj K (eA n) (eS n) (eR n) (sing_exact_incl K (Int.ofNat n) hT.sub₀₁ hT.sub₁₂)
  · exact exact_conj K (eS (n + 1)) (eR (n + 1)) (eA n)
      (sing_exact_δ K (Int.ofNat n) hT.sub₀₁ hT.sub₁₂)
  · exact exact_conj K (eR (n + 1)) (eA n) (eS n)
      (sing_exact_δ' K (Int.ofNat n) hT.sub₀₁ hT.sub₁₂)
  · intro y
    obtain ⟨x, hx⟩ := (sing_exact_δ K (Int.negSucc 0) hT.sub₀₁ hT.sub₁₂ (eR 0 y)).1
      (Subsingleton.elim _ _)
    refine ⟨(eS 0).symm x, ?_⟩
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.apply_symm_apply]
    rw [LinearEquiv.symm_apply_eq]
    exact hx
  · refine exists_connecting_of_singδ_ne_zero K h hT c₁ (k := Int.ofNat n) fun h0 => hd ?_
    ext x
    have e := congrArg (fun φ => φ.hom ((eR (n + 1)) x)) h0
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply] at e
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.zero_apply]
    erw [e, map_zero]

end ConleyCheck.Conley
