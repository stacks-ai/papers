import ConleyCheck.Conley.Morse
import ConleyCheck.Algebra.ExactSeq

/-!
# Conley index theory, Stage 4: the homology index and the attractor–repeller sequence

Mathlib does not yet have relative singular homology with the long exact sequence of a triple.
`PairHomology` packages exactly that structure, namely groups `H_k(N, L)`, maps induced by
inclusions of pairs and boundary maps, with exactness of the sequence of every triple
`L ⊆ M ⊆ N`. Relative singular homology is an instance, namely `singularPairHomology` in
`ConleyCheck.Conley.SingularPair`. The paper's homology index is `CH_*(S) = H̃_*(N/L)`
(`ConleyCheck.Conley.HomologyIndex`). Excision is proved in `ConleyCheck.Conley.Excision`, but
identifying `H̃_*(N/L)` with `H_*(N, L)` also needs `L` to be a deformation retract of a
neighborhood in `N`, which fails for some index pairs. So the sequences below are stated for
`H_*(N, L)`. For index triples with collared pairs, the attractor–repeller sequence for `CH_*`
itself is `ConleyCheck.Conley.homologyIndex_attractor_repeller` in `ConleyCheck.Conley.Collar`.
Every attractor–repeller pair has such a triple, so the sequence holds unconditionally
(`ConleyCheck.Conley.homologyIndex_attractor_repeller_of_pair` in `ConleyCheck.Conley.Regular`).

Given any `PairHomology`, the attractor–repeller sequence
`⋯ → CH_k(A) → CH_k(S) → CH_k(R) → CH_{k-1}(A) → ⋯` follows from `exists_indexTriple`, and the
consequences used in the paper (Theorem `thm:slab`, Theorem `thm:rate`(ii), Corollary
`cor:attractors`) follow from `ConleyCheck.bijective_of_exact_of_subsingleton`. These are
proved.
-/

namespace ConleyCheck.Conley

open Set CategoryTheory Function

universe u v w

/-- A homology theory on pairs of subsets of `α`, with the exact sequence of triples. -/
structure PairHomology (K : Type u) [Ring K] (α : Type v) [TopologicalSpace α] where
  H : ℤ → Set α → Set α → ModuleCat.{w} K
  incl : ∀ (k : ℤ) {N L N' L' : Set α}, N ⊆ N' → L ⊆ L' → (H k N L ⟶ H k N' L')
  δ : ∀ (k : ℤ) (N M L : Set α), H (k + 1) N M ⟶ H k M L
  exact_incl : ∀ (k : ℤ) {N M L : Set α} (hLM : L ⊆ M) (hMN : M ⊆ N),
    Exact (incl k hMN (subset_refl L)).hom (incl k (subset_refl N) hLM).hom
  exact_δ : ∀ (k : ℤ) {N M L : Set α} (hLM : L ⊆ M) (_ : M ⊆ N),
    Exact (incl (k + 1) (subset_refl N) hLM).hom (δ k N M L).hom
  exact_δ' : ∀ (k : ℤ) {N M L : Set α} (_ : L ⊆ M) (hMN : M ⊆ N),
    Exact (δ k N M L).hom (incl k hMN (subset_refl L)).hom

variable {K : Type u} [Ring K] {α : Type v} [TopologicalSpace α] {ϕ : Flow ℝ α}

/-- The attractor–repeller sequence of an index triple. -/
theorem attractor_repeller_sequence [T2Space α]
    (h : PairHomology.{u, v, w} K α) {S A R : Set α} (hAR : IsAttractorRepellerPair ϕ S A R) :
    ∃ N₀ N₁ N₂, ∃ hT : IsIndexTriple ϕ S A R N₀ N₁ N₂, ∀ k : ℤ,
      Exact (h.incl k hT.sub₁₂ (subset_refl N₀)).hom (h.incl k (subset_refl N₂) hT.sub₀₁).hom ∧
      Exact (h.incl (k + 1) (subset_refl N₂) hT.sub₀₁).hom (h.δ k N₂ N₁ N₀).hom ∧
      Exact (h.δ k N₂ N₁ N₀).hom (h.incl k hT.sub₁₂ (subset_refl N₀)).hom := by
  obtain ⟨N₀, N₁, N₂, hT⟩ := exists_indexTriple hAR
  exact ⟨N₀, N₁, N₂, hT, fun k =>
    ⟨h.exact_incl k hT.sub₀₁ hT.sub₁₂, h.exact_δ k hT.sub₀₁ hT.sub₁₂, h.exact_δ' k hT.sub₀₁ hT.sub₁₂⟩⟩

/-- If the repeller has trivial homology index, `CH_*(A) → CH_*(S)` is an isomorphism. -/
theorem attractor_iso_of_repeller_trivial [T2Space α] (h : PairHomology.{u, v, w} K α) {S A R : Set α}
    (hAR : IsAttractorRepellerPair ϕ S A R)
    (hR : ∀ N L, IsIndexPair ϕ R N L → ∀ k, Subsingleton (h.H k N L)) :
    ∃ N₀ N₁ N₂, ∃ hT : IsIndexTriple ϕ S A R N₀ N₁ N₂, ∀ k : ℤ,
      Bijective (h.incl k hT.sub₁₂ (subset_refl N₀)).hom := by
  obtain ⟨N₀, N₁, N₂, hT⟩ := exists_indexTriple hAR
  refine ⟨N₀, N₁, N₂, hT, fun k => ?_⟩
  haveI := hR N₂ N₁ hT.pair_R (k + 1)
  haveI := hR N₂ N₁ hT.pair_R k
  exact bijective_of_exact_of_subsingleton (h.exact_δ' k hT.sub₀₁ hT.sub₁₂) (h.exact_incl k hT.sub₀₁ hT.sub₁₂)

/-- If the attractor has trivial homology index, `CH_*(S) → CH_*(R)` is an isomorphism. -/
theorem repeller_iso_of_attractor_trivial [T2Space α] (h : PairHomology.{u, v, w} K α) {S A R : Set α}
    (hAR : IsAttractorRepellerPair ϕ S A R)
    (hA : ∀ N L, IsIndexPair ϕ A N L → ∀ k, Subsingleton (h.H k N L)) :
    ∃ N₀ N₁ N₂, ∃ hT : IsIndexTriple ϕ S A R N₀ N₁ N₂, ∀ k : ℤ,
      Bijective (h.incl (k + 1) (subset_refl N₂) hT.sub₀₁).hom := by
  obtain ⟨N₀, N₁, N₂, hT⟩ := exists_indexTriple hAR
  refine ⟨N₀, N₁, N₂, hT, fun k => ?_⟩
  haveI := hA N₁ N₀ hT.pair_A (k + 1)
  haveI := hA N₁ N₀ hT.pair_A k
  exact bijective_of_exact_of_subsingleton (h.exact_incl (k + 1) hT.sub₀₁ hT.sub₁₂)
    (h.exact_δ k hT.sub₀₁ hT.sub₁₂)

end ConleyCheck.Conley
