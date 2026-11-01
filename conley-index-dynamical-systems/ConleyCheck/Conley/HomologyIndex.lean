import ConleyCheck.Conley.Index
import ConleyCheck.Conley.SingularPair

/-!
# The homology Conley index

The paper defines the homology index as `CH_*(S) = H̃_*(N/L)` for an index pair `(N, L)` of `S`.
Here `H̃_n(X)` is the reduced singular homology of a pointed space, namely the cokernel of the map
`H_n(pt) → H_n(X)` induced by the base point.

* `redIso`: a pointed homotopy equivalence induces an isomorphism on reduced homology. This uses
  the homotopy invariance of singular homology from Mathlib.
* `homologyIndex_unique`: `H̃_*(N/L)` does not depend on the index pair. This follows from the
  uniqueness of the pointed homotopy type of `N/L` (`indexPair_unique`).
* `homologyIndex`, `homologyIndexIso`: the homology index of an isolated invariant set, and its
  identification with `H̃_*(N/L)` for every index pair.
* `nonempty_of_homologyIndex_nontrivial`: Ważewski's principle for the homology index.
-/

namespace ConleyCheck.Conley

open CategoryTheory Limits Set

universe u

section Reduced

variable (K : Type u) [Ring K] {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

/-- Singular homology `H_n(X; K)`. -/
noncomputable abbrev absH (X : Type u) [TopologicalSpace X] (n : ℕ) : ModuleCat.{u} K :=
  ((singFunctor K).obj (TopCat.of X)).homology n

/-- The map on singular homology induced by a continuous map. -/
noncomputable abbrev hMap (f : C(X, Y)) (n : ℕ) : absH K X n ⟶ absH K Y n :=
  HomologicalComplex.homologyMap ((singFunctor K).map (TopCat.ofHom f)) n

theorem hMap_id (n : ℕ) : hMap K (ContinuousMap.id X) n = 𝟙 _ := by
  change HomologicalComplex.homologyMap ((singFunctor K).map (𝟙 _)) n = _
  rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]

theorem hMap_comp (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    hMap K (g.comp f) n = hMap K f n ≫ hMap K g n := by
  rw [hMap, TopCat.ofHom_comp, CategoryTheory.Functor.map_comp,
    HomologicalComplex.homologyMap_comp]

theorem hMap_congr {f g : C(X, Y)} (h : f.Homotopic g) (n : ℕ) : hMap K f n = hMap K g n := by
  obtain ⟨H⟩ := h
  exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (f := TopCat.ofHom f) (g := TopCat.ofHom g) H _ n

/-- The inclusion of the base point. -/
def ptMap (x₀ : X) : C(PUnit.{u + 1}, X) := ContinuousMap.const _ x₀

/-- Reduced singular homology `H̃_n(X; K)` of the pointed space `(X, x₀)`. -/
noncomputable abbrev redH (X : Type u) [TopologicalSpace X] (x₀ : X) (n : ℕ) : ModuleCat.{u} K :=
  cokernel (hMap K (ptMap x₀) n)

theorem redH_hom_ext {x₀ : X} {n : ℕ} {W : ModuleCat.{u} K} {a b : redH K X x₀ n ⟶ W}
    (h : cokernel.π _ ≫ a = cokernel.π _ ≫ b) : a = b :=
  coequalizer.hom_ext h

theorem ptMap_comp (f : C(X, Y)) {x₀ : X} {y₀ : Y} (hf : f x₀ = y₀) :
    f.comp (ptMap x₀) = ptMap y₀ := by
  ext
  exact hf

/-- The map on reduced homology induced by a pointed map. -/
noncomputable def redMap (f : C(X, Y)) {x₀ : X} {y₀ : Y} (hf : f x₀ = y₀) (n : ℕ) :
    redH K X x₀ n ⟶ redH K Y y₀ n :=
  cokernel.map (hMap K (ptMap x₀) n) (hMap K (ptMap y₀) n) (𝟙 _) (hMap K f n) (by
    rw [← hMap_comp, ptMap_comp f hf, Category.id_comp])

@[reassoc]
theorem π_redMap (f : C(X, Y)) {x₀ : X} {y₀ : Y} (hf : f x₀ = y₀) (n : ℕ) :
    cokernel.π _ ≫ redMap K f hf n = hMap K f n ≫ cokernel.π _ :=
  cokernel.π_desc _ _ _

/-- A pointed homotopy equivalence induces an isomorphism on reduced homology. -/
noncomputable def redIso {x₀ : X} {y₀ : Y} (e : PointedHomotopyEquiv X Y x₀ y₀) (n : ℕ) :
    redH K X x₀ n ≅ redH K Y y₀ n where
  hom := redMap K e.toFun e.map_pt n
  inv := redMap K e.invFun e.inv_pt n
  hom_inv_id := by
    refine redH_hom_ext K ?_
    rw [π_redMap_assoc, π_redMap, ← Category.assoc, ← hMap_comp, hMap_congr K e.left.homotopic,
      hMap_id, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    refine redH_hom_ext K ?_
    rw [π_redMap_assoc, π_redMap, ← Category.assoc, ← hMap_comp, hMap_congr K e.right.homotopic,
      hMap_id, Category.id_comp, Category.comp_id]

/-- A pointed contractible space has zero reduced homology. -/
theorem redH_subsingleton {x₀ : X} (h : PointedContractible X x₀) (n : ℕ) :
    Subsingleton (redH K X x₀ n) := by
  have hc : ContinuousMap.const X x₀ = (ptMap x₀).comp (ContinuousMap.const X PUnit.unit) := rfl
  have hπ : cokernel.π (hMap K (ptMap x₀) n) = 0 :=
    calc cokernel.π (hMap K (ptMap x₀) n)
        = hMap K (ContinuousMap.id X) n ≫ cokernel.π _ := by rw [hMap_id, Category.id_comp]
      _ = 0 := by
        rw [hMap_congr K h.homotopic, hc, hMap_comp K (ContinuousMap.const X PUnit.unit),
          Category.assoc, cokernel.condition, comp_zero]
  have hz : IsZero (redH K X x₀ n) := IsZero.of_epi_eq_zero _ hπ
  exact (ModuleCat.isZero_iff_subsingleton).1 hz

end Reduced

section Index

variable (K : Type u) [Ring K] {α : Type u} [TopologicalSpace α] {ϕ : Flow ℝ α}

/-- `H̃_*(N/L)` does not depend on the index pair. -/
theorem homologyIndex_unique [T2Space α] {S N L N' L' : Set α}
    (hP : IsIndexPair ϕ S N L) (hP' : IsIndexPair ϕ S N' L') (n : ℕ) :
    Nonempty (redH K (IndexSpace N L) (IndexSpace.pt N L) n ≅
      redH K (IndexSpace N' L') (IndexSpace.pt N' L') n) := by
  obtain ⟨e⟩ := indexPair_unique hP hP'
  exact ⟨redIso K e n⟩

variable (ϕ)

/-- The homology Conley index `CH_n(S) = H̃_n(N/L)`, computed from a chosen index pair. -/
noncomputable def homologyIndex [T2Space α] {S : Set α} (hS : IsIsolatedInvariantSet ϕ S)
    (n : ℕ) : ModuleCat.{u} K :=
  redH K (IndexSpace hS.hasIndex.choose hS.hasIndex.choose_spec.choose)
    (IndexSpace.pt _ _) n

variable {ϕ}

/-- `CH_n(S) ≅ H̃_n(N/L)` for every index pair `(N, L)` of `S`. -/
theorem homologyIndexIso [T2Space α] {S N L : Set α} (hS : IsIsolatedInvariantSet ϕ S)
    (hP : IsIndexPair ϕ S N L) (n : ℕ) :
    Nonempty (homologyIndex K ϕ hS n ≅ redH K (IndexSpace N L) (IndexSpace.pt N L) n) :=
  homologyIndex_unique K hS.hasIndex.choose_spec.choose_spec hP n

/-- Ważewski's principle: a nonzero homology index forces a nonempty invariant set. -/
theorem nonempty_of_homologyIndex_nontrivial [T2Space α] {S : Set α}
    (hS : IsIsolatedInvariantSet ϕ S) {n : ℕ} (h : Nontrivial (homologyIndex K ϕ hS n)) :
    S.Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  subst hne
  have hc := indexTrivial_empty.of_indexPair (ϕ := ϕ) hS.hasIndex.choose_spec.choose_spec
  exact @not_subsingleton _ h (redH_subsingleton K hc n)

end Index

end ConleyCheck.Conley
