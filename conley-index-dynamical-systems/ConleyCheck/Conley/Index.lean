import ConleyCheck.Conley.Uniqueness

/-!
# Conley index theory, Stage 2: the homotopy Conley index

* `exists_indexPair` (Conley 1978, Salamon 1985 Thm. 4.3): every isolated invariant set has an
  index pair inside any isolating neighborhood. Proved in `ConleyCheck.Conley.Existence`.
* `indexPair_unique` (Salamon 1985 Thm. 4.10): the pointed homotopy type of `N/L` does not depend
  on the index pair. Proved in `ConleyCheck.Conley.Uniqueness`.

Everything below is proved for flows on Hausdorff spaces, in particular Ważewski's principle
`nonempty_of_not_contractible`.
-/

namespace ConleyCheck.Conley

open Set

variable {α : Type*} [TopologicalSpace α] {ϕ : Flow ℝ α}

/-- Existence of index pairs. -/
theorem exists_indexPair [T2Space α] {N : Set α} (hN : IsIsolatingNbhd ϕ N) :
    ∃ N₁ L, IsIndexPair ϕ (Inv ϕ N) N₁ L ∧ N₁ ⊆ N :=
  exists_indexPair_of_t2 hN

/-- Independence of the index pair. -/
theorem indexPair_unique [T2Space α] {S N L N' L' : Set α}
    (h : IsIndexPair ϕ S N L) (h' : IsIndexPair ϕ S N' L') :
    Nonempty (PointedHomotopyEquiv (IndexSpace N L) (IndexSpace N' L')
      (IndexSpace.pt N L) (IndexSpace.pt N' L')) :=
  indexPair_unique_of_t2 h h'

variable (ϕ)

/-- `S` has Conley index `[X, x₀]`. -/
def HasIndex (S : Set α) (X : Type*) [TopologicalSpace X] (x₀ : X) : Prop :=
  ∃ N L, IsIndexPair ϕ S N L ∧
    Nonempty (PointedHomotopyEquiv (IndexSpace N L) X (IndexSpace.pt N L) x₀)

/-- `S` has trivial Conley index `0̄`. -/
def IndexTrivial (S : Set α) : Prop :=
  ∃ N L, IsIndexPair ϕ S N L ∧ PointedContractible (IndexSpace N L) (IndexSpace.pt N L)

variable {ϕ}

/-- Every isolated invariant set has an index. -/
theorem IsIsolatedInvariantSet.hasIndex [T2Space α] {S : Set α}
    (h : IsIsolatedInvariantSet ϕ S) : ∃ N L, IsIndexPair ϕ S N L := by
  obtain ⟨N, hN, rfl⟩ := h
  obtain ⟨N₁, L, hP, -⟩ := exists_indexPair hN
  exact ⟨N₁, L, hP⟩

/-- The index is computed by any index pair. -/
theorem HasIndex.of_indexPair [T2Space α] {S N L : Set α}
    {X : Type*} [TopologicalSpace X] {x₀ : X} (h : HasIndex ϕ S X x₀) (hP : IsIndexPair ϕ S N L) :
    Nonempty (PointedHomotopyEquiv (IndexSpace N L) X (IndexSpace.pt N L) x₀) := by
  obtain ⟨N', L', hP', ⟨e⟩⟩ := h
  obtain ⟨e'⟩ := indexPair_unique hP hP'
  exact ⟨e'.trans e⟩

/-- The index is well defined up to pointed homotopy equivalence. -/
theorem HasIndex.unique [T2Space α] {S : Set α}
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x₀ : X} {y₀ : Y}
    (hX : HasIndex ϕ S X x₀) (hY : HasIndex ϕ S Y y₀) :
    Nonempty (PointedHomotopyEquiv X Y x₀ y₀) := by
  obtain ⟨N, L, hP, ⟨e⟩⟩ := hX
  obtain ⟨e'⟩ := hY.of_indexPair hP
  exact ⟨e.symm.trans e'⟩

/-- A trivial index is trivial for every index pair. -/
theorem IndexTrivial.of_indexPair [T2Space α] {S N L : Set α}
    (h : IndexTrivial ϕ S) (hP : IsIndexPair ϕ S N L) :
    PointedContractible (IndexSpace N L) (IndexSpace.pt N L) := by
  obtain ⟨N', L', hP', hc⟩ := h
  obtain ⟨e⟩ := indexPair_unique hP hP'
  exact hc.of_equiv e

/-- The empty set has trivial index. -/
theorem indexTrivial_empty : IndexTrivial ϕ (∅ : Set α) :=
  ⟨∅, ∅, isIndexPair_empty isCompact_empty, pointedContractible_self _⟩

/-- Ważewski's principle: a nontrivial index forces a nonempty invariant set. -/
theorem nonempty_of_not_contractible [T2Space α] {S N L : Set α}
    (hP : IsIndexPair ϕ S N L)
    (h : ¬ PointedContractible (IndexSpace N L) (IndexSpace.pt N L)) : S.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  exact h (indexTrivial_empty.of_indexPair hP)

theorem nonempty_of_not_indexTrivial [T2Space α] {S : Set α}
    (h : ¬ IndexTrivial ϕ S) : S.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  exact h indexTrivial_empty

end ConleyCheck.Conley
