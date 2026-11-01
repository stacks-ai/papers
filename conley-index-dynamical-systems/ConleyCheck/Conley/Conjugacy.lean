import ConleyCheck.Conley.Uniqueness
import ConleyCheck.Conley.Index

/-!
# Invariance of the Conley index under topological conjugacy

A homeomorphism `h : α ≃ₜ β` induces a homeomorphism `(h⁻¹ N)/(h⁻¹ L) ≃ N/L`. If moreover `h`
conjugates a flow `ϕ` on `α` to a flow `ψ` on `β`, then `h⁻¹` maps index pairs of `ψ` to index
pairs of `ϕ`, so `HasIndex ψ S X x₀` implies `HasIndex ϕ (h⁻¹ S) X x₀`.
-/

namespace ConleyCheck.Conley

open Set

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

theorem IndexSpace.hom_ext {N L : Set α} {Y : Type*} [TopologicalSpace Y]
    {f g : C(IndexSpace N L, Y)} (h₁ : ∀ y, f (IndexSpace.proj N L y) = g (IndexSpace.proj N L y))
    (h₂ : f (IndexSpace.pt N L) = g (IndexSpace.pt N L)) : f = g := by
  ext q
  induction q using Quotient.inductionOn with
  | h a =>
    rcases a with y | u
    · exact h₁ y
    · exact h₂

/-- A pointed homotopy equivalence from a pair of mutually inverse pointed maps. -/
def PointedHomotopyEquiv.ofInverse {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ : X} {y₀ : Y} (f : C(X, Y)) (g : C(Y, X)) (hf : f x₀ = y₀) (hg : g y₀ = x₀)
    (h₁ : g.comp f = ContinuousMap.id X) (h₂ : f.comp g = ContinuousMap.id Y) :
    PointedHomotopyEquiv X Y x₀ y₀ where
  toFun := f
  invFun := g
  map_pt := hf
  inv_pt := hg
  left := h₁ ▸ ContinuousMap.HomotopicRel.refl _
  right := h₂ ▸ ContinuousMap.HomotopicRel.refl _

/-- The map `(h⁻¹ N)/(h⁻¹ L) → N/L` induced by `h`. -/
noncomputable def IndexSpace.preimageMap (h : α ≃ₜ β) (N L : Set β) :
    C(IndexSpace (h ⁻¹' N) (h ⁻¹' L), IndexSpace N L) :=
  descend (IndexSpace.pt N L)
    ((IndexSpace.proj N L).comp
      ⟨fun x => ⟨h x, x.2⟩, (h.continuous.comp continuous_subtype_val).subtype_mk _⟩)
    (fun _ hy => IndexSpace.proj_eq_pt hy)

/-- The map `N/L → (h⁻¹ N)/(h⁻¹ L)` induced by `h⁻¹`. -/
noncomputable def IndexSpace.preimageInv (h : α ≃ₜ β) (N L : Set β) :
    C(IndexSpace N L, IndexSpace (h ⁻¹' N) (h ⁻¹' L)) :=
  descend (IndexSpace.pt _ _)
    ((IndexSpace.proj (h ⁻¹' N) (h ⁻¹' L)).comp
      ⟨fun y => ⟨h.symm y, show h (h.symm y) ∈ N by rw [h.apply_symm_apply]; exact y.2⟩,
        (h.symm.continuous.comp continuous_subtype_val).subtype_mk _⟩)
    (fun y hy => IndexSpace.proj_eq_pt (show h (h.symm y) ∈ L by rw [h.apply_symm_apply]; exact hy))

/-- `(h⁻¹ N)/(h⁻¹ L) ≃ N/L` as pointed spaces. -/
noncomputable def IndexSpace.preimageEquiv (h : α ≃ₜ β) (N L : Set β) :
    PointedHomotopyEquiv (IndexSpace (h ⁻¹' N) (h ⁻¹' L)) (IndexSpace N L)
      (IndexSpace.pt _ _) (IndexSpace.pt _ _) :=
  PointedHomotopyEquiv.ofInverse (IndexSpace.preimageMap h N L) (IndexSpace.preimageInv h N L)
    rfl rfl
    (IndexSpace.hom_ext (fun y => congrArg (IndexSpace.proj _ _)
      (Subtype.ext (h.symm_apply_apply (y : α)))) rfl)
    (IndexSpace.hom_ext (fun y => congrArg (IndexSpace.proj _ _)
      (Subtype.ext (h.apply_symm_apply (y : β)))) rfl)

/-- The flow `h ∘ ϕ ∘ h⁻¹`. -/
noncomputable def conjFlow (ϕ : Flow ℝ α) (h : α ≃ₜ β) : Flow ℝ β where
  toFun t y := h (ϕ t (h.symm y))
  cont' := h.continuous.comp (ϕ.continuous continuous_fst (h.symm.continuous.comp continuous_snd))
  map_add' t₁ t₂ y := by simp [ϕ.map_add]
  map_zero' y := by simp

theorem conjFlow_apply (ϕ : Flow ℝ α) (h : α ≃ₜ β) (t : ℝ) (y : β) :
    conjFlow ϕ h t y = h (ϕ t (h.symm y)) := rfl

section Conj

variable {ϕ : Flow ℝ α} {ψ : Flow ℝ β} {h : α ≃ₜ β} (hc : ∀ t x, h (ϕ t x) = ψ t (h x))
include hc

theorem Inv_preimage (M : Set β) : Inv ϕ (h ⁻¹' M) = h ⁻¹' Inv ψ M := by
  ext x
  simp only [Inv, mem_ofPred_eq, mem_preimage, hc]

theorem IsIndexPair.preimage {S N L : Set β} (hP : IsIndexPair ψ S N L) :
    IsIndexPair ϕ (h ⁻¹' S) (h ⁻¹' N) (h ⁻¹' L) := by
  have hcl : closure (h ⁻¹' N \ h ⁻¹' L) = h ⁻¹' closure (N \ L) := by
    rw [← preimage_sdiff, h.preimage_closure]
  exact
    { isCompact_N := h.isCompact_preimage.2 hP.isCompact_N
      isCompact_L := h.isCompact_preimage.2 hP.isCompact_L
      subset := preimage_mono hP.subset
      isolating := by
        refine ⟨?_, ?_⟩
        · rw [hcl]; exact h.isCompact_preimage.2 hP.isolating.1
        · rw [hcl, Inv_preimage hc, ← h.preimage_interior]
          exact preimage_mono hP.isolating.2
      inv_eq := by rw [hcl, Inv_preimage hc, hP.inv_eq]
      nhds := by
        rw [← preimage_sdiff, ← h.preimage_interior]
        exact preimage_mono hP.nhds
      posInv := fun x hx t ht hseg => by
        show h (ϕ t x) ∈ L
        rw [hc]
        exact hP.posInv _ hx t ht fun s hs => by rw [← hc]; exact hseg s hs
      exit := fun x hx t ht hout => by
        obtain ⟨s, hs, hseg, hL⟩ := hP.exit _ hx t ht (by rw [← hc]; exact hout)
        exact ⟨s, hs, fun r hr => show h (ϕ r x) ∈ N by rw [hc]; exact hseg r hr,
          show h (ϕ s x) ∈ L by rw [hc]; exact hL⟩ }

theorem HasIndex.preimage {S : Set β} {X : Type*} [TopologicalSpace X] {x₀ : X}
    (hS : HasIndex ψ S X x₀) : HasIndex ϕ (h ⁻¹' S) X x₀ := by
  obtain ⟨N, L, hP, ⟨e⟩⟩ := hS
  exact ⟨_, _, hP.preimage hc, ⟨(IndexSpace.preimageEquiv h N L).trans e⟩⟩

end Conj

end ConleyCheck.Conley
