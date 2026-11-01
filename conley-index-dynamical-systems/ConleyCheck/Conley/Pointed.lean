import Mathlib

/-!
# The pointed space `N/L` and pointed homotopy equivalences

`IndexSpace N L` is `N ⊔ {*}` with `L ∪ {*}` collapsed to the base point. For `L ≠ ∅` this is the
usual `N/L`, and for `L = ∅` it is `N` with a disjoint base point, as in Conley's convention.
All results in this file are proved.
-/

namespace ConleyCheck.Conley

open ContinuousMap

section HomotopyRel

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Precomposition of a homotopy relative to a set. -/
theorem HomotopicRel.precomp {f₀ f₁ : C(Y, Z)} {S : Set Y} (h : f₀.HomotopicRel f₁ S)
    (g : C(X, Y)) {T : Set X} (hT : Set.MapsTo g T S) :
    (f₀.comp g).HomotopicRel (f₁.comp g) T := by
  obtain ⟨F⟩ := h
  exact ⟨{ toHomotopy := F.toHomotopy.comp (ContinuousMap.Homotopy.refl g)
           prop' := fun t x hx => by simpa using F.eq_fst t (hT hx) }⟩

end HomotopyRel

section Pointed

variable (X Y Z : Type*) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A homotopy equivalence of pointed spaces, with homotopies relative to the base points. -/
structure PointedHomotopyEquiv (x₀ : X) (y₀ : Y) where
  toFun : C(X, Y)
  invFun : C(Y, X)
  map_pt : toFun x₀ = y₀
  inv_pt : invFun y₀ = x₀
  left : (invFun.comp toFun).HomotopicRel (ContinuousMap.id X) {x₀}
  right : (toFun.comp invFun).HomotopicRel (ContinuousMap.id Y) {y₀}

/-- `(X, x₀)` is contractible relative to its base point. -/
def PointedContractible (x₀ : X) : Prop :=
  (ContinuousMap.id X).HomotopicRel (ContinuousMap.const X x₀) {x₀}

variable {X Y Z}

namespace PointedHomotopyEquiv

def refl (x₀ : X) : PointedHomotopyEquiv X X x₀ x₀ where
  toFun := ContinuousMap.id X
  invFun := ContinuousMap.id X
  map_pt := rfl
  inv_pt := rfl
  left := HomotopicRel.refl _
  right := HomotopicRel.refl _

def symm {x₀ : X} {y₀ : Y} (e : PointedHomotopyEquiv X Y x₀ y₀) :
    PointedHomotopyEquiv Y X y₀ x₀ where
  toFun := e.invFun
  invFun := e.toFun
  map_pt := e.inv_pt
  inv_pt := e.map_pt
  left := e.right
  right := e.left

theorem comp_homotopicRel {x₀ : X} {y₀ : Y} {f : C(X, Y)} {g : C(Y, Z)}
    {f' : C(Y, X)} {g' : C(Z, Y)} (hf : f x₀ = y₀)
    (hg : (g'.comp g).HomotopicRel (ContinuousMap.id Y) {y₀})
    (hf' : (f'.comp f).HomotopicRel (ContinuousMap.id X) {x₀}) :
    ((f'.comp g').comp (g.comp f)).HomotopicRel (ContinuousMap.id X) {x₀} := by
  have h1 := (HomotopicRel.precomp hg f (T := {x₀})
    (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact hf)).comp_continuousMap f'
  rw [ContinuousMap.comp_assoc, ContinuousMap.id_comp] at h1
  rw [ContinuousMap.comp_assoc]
  exact h1.trans hf'

def trans {x₀ : X} {y₀ : Y} {z₀ : Z} (e : PointedHomotopyEquiv X Y x₀ y₀)
    (e' : PointedHomotopyEquiv Y Z y₀ z₀) : PointedHomotopyEquiv X Z x₀ z₀ where
  toFun := e'.toFun.comp e.toFun
  invFun := e.invFun.comp e'.invFun
  map_pt := by simp [e.map_pt, e'.map_pt]
  inv_pt := by simp [e.inv_pt, e'.inv_pt]
  left := comp_homotopicRel e.map_pt e'.left e.left
  right := comp_homotopicRel e'.inv_pt e.right e'.right

end PointedHomotopyEquiv

/-- A space with a single point is contractible. -/
theorem pointedContractible_of_subsingleton [Subsingleton X] (x₀ : X) :
    PointedContractible X x₀ := by
  have : ContinuousMap.id X = ContinuousMap.const X x₀ := by
    ext x; exact Subsingleton.elim _ _
  rw [PointedContractible, this]
  exact HomotopicRel.refl _

/-- Contractibility is invariant under pointed homotopy equivalence. -/
theorem PointedContractible.of_equiv {x₀ : X} {y₀ : Y} (e : PointedHomotopyEquiv X Y x₀ y₀)
    (h : PointedContractible Y y₀) : PointedContractible X x₀ := by
  have h1 := (HomotopicRel.precomp h e.toFun (T := {x₀})
    (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact e.map_pt)).comp_continuousMap e.invFun
  rw [ContinuousMap.id_comp] at h1
  have h2 : (e.invFun.comp ((ContinuousMap.const Y y₀).comp e.toFun)) =
      ContinuousMap.const X x₀ := by
    ext x; simp [e.inv_pt]
  rw [h2] at h1
  exact e.left.symm.trans h1

end Pointed

/-- The equivalence relation collapsing `{b | P b}` to one point. -/
def collapseSetoid {β : Type*} (P : β → Prop) : Setoid β where
  r a b := a = b ∨ (P a ∧ P b)
  iseqv := by
    refine ⟨fun _ => Or.inl rfl, fun h => ?_, fun h₁ h₂ => ?_⟩
    · rcases h with rfl | ⟨ha, hb⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hb, ha⟩
    · rcases h₁ with rfl | ⟨ha, hb⟩
      · exact h₂
      · rcases h₂ with rfl | ⟨_, hc⟩
        · exact Or.inr ⟨ha, hb⟩
        · exact Or.inr ⟨ha, hc⟩

section Wedge

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The two base points of `X ⊔ Y`. -/
def wedgeBase (x₀ : X) (y₀ : Y) : X ⊕ Y → Prop
  | .inl x => x = x₀
  | .inr y => y = y₀

variable (X Y) in
/-- The wedge sum `X ∨ Y`. -/
def Wedge (x₀ : X) (y₀ : Y) : Type _ := Quotient (collapseSetoid (wedgeBase x₀ y₀))

instance (x₀ : X) (y₀ : Y) : TopologicalSpace (Wedge X Y x₀ y₀) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

def Wedge.pt (x₀ : X) (y₀ : Y) : Wedge X Y x₀ y₀ := Quotient.mk _ (.inl x₀)

end Wedge

section IndexSpace

variable {α : Type*} [TopologicalSpace α]

/-- The points of `N ⊔ {*}` that are collapsed, namely `L ∪ {*}`. -/
def collapsed (N L : Set α) : N ⊕ Unit → Prop
  | .inl x => (x : α) ∈ L
  | .inr _ => True

def indexSetoid (N L : Set α) : Setoid (N ⊕ Unit) := collapseSetoid (collapsed N L)

/-- The pointed space `N/L`. -/
def IndexSpace (N L : Set α) : Type _ := Quotient (indexSetoid N L)

instance (N L : Set α) : TopologicalSpace (IndexSpace N L) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

/-- The base point `[L]` of `N/L`. -/
def IndexSpace.pt (N L : Set α) : IndexSpace N L := Quotient.mk _ (.inr ())

/-- The projection `N → N/L`. -/
def IndexSpace.proj (N L : Set α) : C(N, IndexSpace N L) where
  toFun x := Quotient.mk _ (.inl x)
  continuous_toFun := continuous_quotient_mk'.comp continuous_inl

theorem IndexSpace.proj_eq_pt {N L : Set α} {x : N} (hx : (x : α) ∈ L) :
    IndexSpace.proj N L x = IndexSpace.pt N L :=
  Quotient.sound (Or.inr ⟨hx, trivial⟩)

/-- `N/N` is a point. -/
instance (N : Set α) : Subsingleton (IndexSpace N N) := by
  constructor
  intro a b
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  rename_i a b
  apply Quotient.sound
  refine Or.inr ⟨?_, ?_⟩
  · rcases a with x | _
    · exact x.2
    · trivial
  · rcases b with x | _
    · exact x.2
    · trivial

theorem pointedContractible_self (N : Set α) :
    PointedContractible (IndexSpace N N) (IndexSpace.pt N N) :=
  pointedContractible_of_subsingleton _

end IndexSpace

end ConleyCheck.Conley
