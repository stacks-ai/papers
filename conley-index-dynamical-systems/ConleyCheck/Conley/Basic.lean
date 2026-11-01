import Mathlib

/-!
# Conley index theory, Stage 1: invariant sets, isolating neighborhoods and index pairs

Everything is stated for a global flow `ϕ : Flow ℝ α` (Mathlib's `Flow`) on a topological space.
The definitions follow Conley (1978) and Salamon (1985), as recalled in section `sec:background`
of the paper. All results in this file are proved.
-/

namespace ConleyCheck.Conley

open Set

variable {α : Type*} [TopologicalSpace α] (ϕ : Flow ℝ α)

/-- The maximal invariant subset `Inv(N) = {x : ϕ(ℝ, x) ⊆ N}`. -/
def Inv (N : Set α) : Set α := {x | ∀ t, ϕ t x ∈ N}

/-- A set is invariant if it contains the full orbit of each of its points. -/
def IsInvariantSet (S : Set α) : Prop := ∀ t, ∀ x ∈ S, ϕ t x ∈ S

/-- `N` is an isolating neighborhood if it is compact and `Inv(N) ⊆ int N`. -/
def IsIsolatingNbhd (N : Set α) : Prop := IsCompact N ∧ Inv ϕ N ⊆ interior N

/-- `S` is an isolated invariant set if `S = Inv(N)` for an isolating neighborhood `N`. -/
def IsIsolatedInvariantSet (S : Set α) : Prop := ∃ N, IsIsolatingNbhd ϕ N ∧ Inv ϕ N = S

/-- `L` is positively invariant relative to `N`: an orbit segment from `L` that stays in `N`
stays in `L`. -/
def IsPosInvRel (L N : Set α) : Prop :=
  ∀ x ∈ L, ∀ t, 0 ≤ t → (∀ s ∈ Icc 0 t, ϕ s x ∈ N) → ϕ t x ∈ L

/-- `L` is an exit set for `N`: an orbit leaving `N` passes through `L` first. -/
def IsExitSet (L N : Set α) : Prop :=
  ∀ x ∈ N, ∀ t, 0 ≤ t → ϕ t x ∉ N → ∃ s ∈ Icc 0 t, (∀ r ∈ Icc 0 s, ϕ r x ∈ N) ∧ ϕ s x ∈ L

/-- An index pair `(N, L)` for `S`. -/
structure IsIndexPair (S N L : Set α) : Prop where
  isCompact_N : IsCompact N
  isCompact_L : IsCompact L
  subset : L ⊆ N
  isolating : IsIsolatingNbhd ϕ (closure (N \ L))
  inv_eq : Inv ϕ (closure (N \ L)) = S
  nhds : S ⊆ interior (N \ L)
  posInv : IsPosInvRel ϕ L N
  exit : IsExitSet ϕ L N

variable {ϕ}

theorem Inv_subset (N : Set α) : Inv ϕ N ⊆ N := fun x hx => by
  have := hx 0
  rwa [ϕ.map_zero_apply] at this

theorem Inv_mono {N M : Set α} (h : N ⊆ M) : Inv ϕ N ⊆ Inv ϕ M := fun _ hx t => h (hx t)

theorem flow_mem_Inv {N : Set α} {x : α} (hx : x ∈ Inv ϕ N) (s : ℝ) : ϕ s x ∈ Inv ϕ N := by
  intro t
  rw [← ϕ.map_add]
  exact hx (t + s)

theorem isInvariantSet_Inv (N : Set α) : IsInvariantSet ϕ (Inv ϕ N) :=
  fun t _ hx => flow_mem_Inv hx t

/-- `Inv(N)` is the largest invariant subset of `N`. -/
theorem subset_Inv {S N : Set α} (hS : IsInvariantSet ϕ S) (hSN : S ⊆ N) : S ⊆ Inv ϕ N :=
  fun x hx t => hSN (hS t x hx)

theorem Inv_Inv (N : Set α) : Inv ϕ (Inv ϕ N) = Inv ϕ N :=
  (Inv_subset _).antisymm (subset_Inv (isInvariantSet_Inv N) subset_rfl)

theorem Inv_eq_iInter (N : Set α) : Inv ϕ N = ⋂ t, ϕ t ⁻¹' N := by
  ext x; simp [Inv]

theorem isClosed_Inv {N : Set α} (hN : IsClosed N) : IsClosed (Inv ϕ N) := by
  rw [Inv_eq_iInter]
  exact isClosed_iInter fun t => hN.preimage (ϕ.continuous_toFun t)

theorem isCompact_Inv [T2Space α] {N : Set α} (hN : IsCompact N) : IsCompact (Inv ϕ N) :=
  hN.of_isClosed_subset (isClosed_Inv hN.isClosed) (Inv_subset N)

theorem Inv_empty : Inv ϕ (∅ : Set α) = ∅ := subset_empty_iff.1 (Inv_subset _)

theorem IsIsolatedInvariantSet.isInvariantSet {S : Set α} (h : IsIsolatedInvariantSet ϕ S) :
    IsInvariantSet ϕ S := by
  obtain ⟨N, -, rfl⟩ := h
  exact isInvariantSet_Inv N

theorem IsIsolatedInvariantSet.isCompact [T2Space α] {S : Set α}
    (h : IsIsolatedInvariantSet ϕ S) : IsCompact S := by
  obtain ⟨N, hN, rfl⟩ := h
  exact isCompact_Inv hN.1

/-- Isolation is robust: a compact `N'` with `Inv(N) ⊆ int N'` and `N' ⊆ N` isolates the same
set. -/
theorem Inv_eq_of_between {N N' : Set α} (hN' : Inv ϕ N ⊆ interior N') (hsub : N' ⊆ N) :
    Inv ϕ N' = Inv ϕ N :=
  (Inv_mono hsub).antisymm
    (subset_Inv (isInvariantSet_Inv N) (hN'.trans interior_subset))

theorem isIsolatingNbhd_of_between {N N' : Set α} (hc : IsCompact N')
    (hN' : Inv ϕ N ⊆ interior N') (hsub : N' ⊆ N) : IsIsolatingNbhd ϕ N' :=
  ⟨hc, by rw [Inv_eq_of_between hN' hsub]; exact hN'⟩

/-- A point of `N` whose full orbit stays in `N` lies in `Inv(N)`; hence if `Inv(N) = ∅` every
orbit through `N` leaves `N` in forward or backward time. -/
theorem exists_leave_of_Inv_empty {N : Set α} (h : Inv ϕ N = ∅) (x : α) : ∃ t, ϕ t x ∉ N := by
  by_contra hx
  push Not at hx
  have : x ∈ Inv ϕ N := hx
  rw [h] at this
  exact this

/-- `(N, N)` is an index pair for the empty set. -/
theorem isIndexPair_empty {N : Set α} (hN : IsCompact N) : IsIndexPair ϕ ∅ N N where
  isCompact_N := hN
  isCompact_L := hN
  subset := subset_rfl
  isolating := by
    simp only [sdiff_self, closure_empty]
    exact ⟨isCompact_empty, by rw [Inv_empty]; exact empty_subset _⟩
  inv_eq := by simp only [sdiff_self, closure_empty]; exact Inv_empty
  nhds := empty_subset _
  posInv := fun _ _ t ht hN => hN t ⟨ht, le_rfl⟩
  exit := fun x hx _ ht _ => ⟨0, ⟨le_rfl, ht⟩, fun r hr => by
      rw [show r = 0 from le_antisymm hr.2 hr.1, ϕ.map_zero_apply]; exact hx,
    by rw [ϕ.map_zero_apply]; exact hx⟩

theorem IsIndexPair.isIsolatedInvariantSet {S N L : Set α} (h : IsIndexPair ϕ S N L) :
    IsIsolatedInvariantSet ϕ S :=
  ⟨_, h.isolating, h.inv_eq⟩

theorem IsIndexPair.subset_N [T2Space α] {S N L : Set α} (h : IsIndexPair ϕ S N L) : S ⊆ N := by
  rw [← h.inv_eq]
  exact (Inv_subset _).trans
    (closure_minimal sdiff_subset h.isCompact_N.isClosed)

end ConleyCheck.Conley
