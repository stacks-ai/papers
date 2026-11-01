import ConleyCheck.Conley.Height
import ConleyCheck.Conley.Family

/-!
# Product flows, skew products and boundary indices

This file contains the general part of Proposition `prop:boundary`.

* Index pairs pull back along open embeddings that conjugate flows
  (`IsIndexPair.preimage_of_isOpenEmbedding`), with the same index space.
* For a product flow `f × θ`, products of index pairs are index pairs (`IsIndexPair.prod`). If
  the base pair is `(N₂, ∅)` and `N₂` contracts to the base point, the index is that of the fiber
  (`IndexSpace.prodEquiv`). If the base pair `(N₂, L₂)` deforms into `L₂`, the index is trivial
  (`IndexSpace.prod_pointedContractible`).
* A skew-product flow `Φ` on `X × B` over a base flow `θ` is deformed into the product flow
  `f₀ × θ`, where `f₀` is the fiber flow over a fixed point `b₀`, by translating the base point
  along `θ` towards `b₀` (`SkewContraction`). Continuation then identifies the index of
  `K × {b₀}` for `Φ` with its index for `f₀ × θ` (`skew_continuation`).
-/

namespace ConleyCheck.Conley

open Set Topology unitInterval

open scoped Classical

/-! ### Pulling back index pairs along open embeddings -/

section Embedding

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {ϕ : Flow ℝ α} {ψ : Flow ℝ β}
  {e : β → α} (he : IsOpenEmbedding e) (hc : ∀ t x, e (ψ t x) = ϕ t (e x))

include hc in
theorem Inv_preimage_of_conj (M : Set α) : Inv ψ (e ⁻¹' M) = e ⁻¹' Inv ϕ M := by
  ext x
  simp only [Inv, mem_ofPred_eq, mem_preimage, hc]

include he hc in
theorem IsIndexPair.preimage_of_isOpenEmbedding [T2Space α] {S N L : Set α}
    (hP : IsIndexPair ϕ S N L) (hN : N ⊆ range e) :
    IsIndexPair ψ (e ⁻¹' S) (e ⁻¹' N) (e ⁻¹' L) := by
  have hcpt : ∀ {A : Set α}, A ⊆ N → IsCompact A → IsCompact (e ⁻¹' A) := fun hA hAc => by
    rw [he.isEmbedding.isCompact_iff, image_preimage_eq_of_subset (hA.trans hN)]
    exact hAc
  have hNc := hP.isCompact_N.isClosed
  have hcl : closure (e ⁻¹' N \ e ⁻¹' L) = e ⁻¹' closure (N \ L) := by
    rw [← preimage_sdiff, he.isOpenMap.preimage_closure_eq_closure_preimage he.continuous]
  exact
    { isCompact_N := hcpt le_rfl hP.isCompact_N
      isCompact_L := hcpt hP.subset hP.isCompact_L
      subset := preimage_mono hP.subset
      isolating := by
        refine ⟨?_, ?_⟩
        · rw [hcl]
          exact hcpt (closure_minimal sdiff_subset hNc) hP.isolating.1
        · rw [hcl, Inv_preimage_of_conj hc,
            ← he.isOpenMap.preimage_interior_eq_interior_preimage he.continuous]
          exact preimage_mono hP.isolating.2
      inv_eq := by rw [hcl, Inv_preimage_of_conj hc, hP.inv_eq]
      nhds := by
        rw [← preimage_sdiff, ← he.isOpenMap.preimage_interior_eq_interior_preimage he.continuous]
        exact preimage_mono hP.nhds
      posInv := fun x hx t ht hseg => by
        show e (ψ t x) ∈ L
        rw [hc]
        exact hP.posInv _ hx t ht fun s hs => by rw [← hc]; exact hseg s hs
      exit := fun x hx t ht hout => by
        obtain ⟨s, hs, hseg, hL⟩ := hP.exit _ hx t ht (by rw [← hc]; exact hout)
        exact ⟨s, hs, fun r hr => show e (ψ r x) ∈ N by rw [hc]; exact hseg r hr,
          show e (ψ s x) ∈ L by rw [hc]; exact hL⟩ }

/-- `(e⁻¹ N)/(e⁻¹ L) ≃ N/L` for an embedding `e` whose range contains `N`. -/
noncomputable def IndexSpace.embeddingEquiv {e : β → α} (he : IsEmbedding e) {N L : Set α}
    (hN : N ⊆ range e) :
    PointedHomotopyEquiv (IndexSpace (e ⁻¹' N) (e ⁻¹' L)) (IndexSpace N L)
      (IndexSpace.pt _ _) (IndexSpace.pt _ _) :=
  have hinv : ∀ y : N, e (he.toHomeomorph.symm ⟨y, hN y.2⟩) = y := fun y => by
    have := congrArg Subtype.val (he.toHomeomorph.apply_symm_apply ⟨y, hN y.2⟩)
    rwa [IsEmbedding.toHomeomorph_apply_coe] at this
  PointedHomotopyEquiv.ofInverse
    (descend (IndexSpace.pt N L)
      ((IndexSpace.proj N L).comp
        ⟨fun x => ⟨e x, x.2⟩, (he.continuous.comp continuous_subtype_val).subtype_mk _⟩)
      (fun _ hy => IndexSpace.proj_eq_pt hy))
    (descend (IndexSpace.pt _ _)
      ((IndexSpace.proj (e ⁻¹' N) (e ⁻¹' L)).comp
        ⟨fun y => ⟨he.toHomeomorph.symm ⟨y, hN y.2⟩, show e _ ∈ N by rw [hinv]; exact y.2⟩,
          ((he.toHomeomorph.symm.continuous.comp
            (continuous_subtype_val.subtype_mk _))).subtype_mk _⟩)
      (fun y hy => IndexSpace.proj_eq_pt
        (show e (he.toHomeomorph.symm ⟨y, hN y.2⟩) ∈ L by rw [hinv]; exact hy)))
    rfl rfl
    (IndexSpace.hom_ext (fun x => congrArg (IndexSpace.proj _ _) (Subtype.ext
      (he.toHomeomorph_symm_apply (x : β)))) rfl)
    (IndexSpace.hom_ext (fun y => congrArg (IndexSpace.proj _ _) (Subtype.ext (hinv y))) rfl)

end Embedding

/-! ### Product flows -/

section Product

variable {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]

/-- The product flow `(x, b) ↦ (f_t x, θ_t b)`. -/
def prodFlow (f : Flow ℝ X) (θ : Flow ℝ B) : Flow ℝ (X × B) where
  toFun t p := (f t p.1, θ t p.2)
  cont' := (f.continuous continuous_fst (continuous_fst.comp continuous_snd)).prodMk
    (θ.continuous continuous_fst (continuous_snd.comp continuous_snd))
  map_add' t₁ t₂ p := by simp only [Flow.map_add]
  map_zero' p := by simp only [Flow.map_zero_apply]

theorem prodFlow_apply (f : Flow ℝ X) (θ : Flow ℝ B) (t : ℝ) (p : X × B) :
    prodFlow f θ t p = (f t p.1, θ t p.2) := rfl

variable {f : Flow ℝ X} {θ : Flow ℝ B}

theorem Inv_prod (A : Set X) (C : Set B) :
    Inv (prodFlow f θ) (A ×ˢ C) = Inv f A ×ˢ Inv θ C := by
  ext p
  simp only [Inv, mem_ofPred_eq, mem_prod, prodFlow_apply, forall_and]

/-- The product of two index pairs is an index pair for the product flow. -/
theorem IsIndexPair.prod {S₁ N₁ L₁ : Set X} {S₂ N₂ L₂ : Set B} (h₁ : IsIndexPair f S₁ N₁ L₁)
    (h₂ : IsIndexPair θ S₂ N₂ L₂) :
    IsIndexPair (prodFlow f θ) (S₁ ×ˢ S₂) (N₁ ×ˢ N₂) (L₁ ×ˢ N₂ ∪ N₁ ×ˢ L₂) := by
  have hsd : N₁ ×ˢ N₂ \ (L₁ ×ˢ N₂ ∪ N₁ ×ˢ L₂) = (N₁ \ L₁) ×ˢ (N₂ \ L₂) := by
    ext ⟨a, b⟩
    simp only [mem_sdiff, mem_prod, mem_union]
    tauto
  have hcl : closure (N₁ ×ˢ N₂ \ (L₁ ×ˢ N₂ ∪ N₁ ×ˢ L₂)) =
      closure (N₁ \ L₁) ×ˢ closure (N₂ \ L₂) := by
    rw [hsd, closure_prod_eq]
  exact
    { isCompact_N := h₁.isCompact_N.prod h₂.isCompact_N
      isCompact_L := (h₁.isCompact_L.prod h₂.isCompact_N).union
        (h₁.isCompact_N.prod h₂.isCompact_L)
      subset := union_subset (prod_mono h₁.subset le_rfl) (prod_mono le_rfl h₂.subset)
      isolating := by
        refine ⟨?_, ?_⟩
        · rw [hcl]; exact h₁.isolating.1.prod h₂.isolating.1
        · rw [hcl, Inv_prod, interior_prod_eq]
          exact prod_mono h₁.isolating.2 h₂.isolating.2
      inv_eq := by rw [hcl, Inv_prod, h₁.inv_eq, h₂.inv_eq]
      nhds := by
        rw [hsd, interior_prod_eq]
        exact prod_mono h₁.nhds h₂.nhds
      posInv := fun p hp t ht hseg => by
        have hN := hseg t ⟨ht, le_rfl⟩
        rcases hp with ⟨ha, -⟩ | ⟨-, hb⟩
        · exact Or.inl ⟨h₁.posInv _ ha t ht fun s hs => (hseg s hs).1, hN.2⟩
        · exact Or.inr ⟨hN.1, h₂.posInv _ hb t ht fun s hs => (hseg s hs).2⟩
      exit := fun p hp t ht hout => by
        have hout' : f t p.1 ∉ N₁ ∨ θ t p.2 ∉ N₂ := by
          by_contra h
          push Not at h
          exact hout ⟨h.1, h.2⟩
        rcases hout' with h | h
        · obtain ⟨s, hs, hseg, hL⟩ := h₁.exit _ hp.1 t ht h
          by_cases hθ : ∀ r ∈ Icc 0 s, θ r p.2 ∈ N₂
          · exact ⟨s, hs, fun r hr => ⟨hseg r hr, hθ r hr⟩,
              Or.inl ⟨hL, hθ s ⟨hs.1, le_rfl⟩⟩⟩
          · push Not at hθ
            obtain ⟨r, hr, hrN⟩ := hθ
            obtain ⟨s', hs', hseg', hL'⟩ := h₂.exit _ hp.2 r hr.1 hrN
            refine ⟨s', ⟨hs'.1, hs'.2.trans (hr.2.trans hs.2)⟩, fun q hq =>
              ⟨hseg q ⟨hq.1, hq.2.trans (hs'.2.trans hr.2)⟩, hseg' q hq⟩, Or.inr ⟨?_, hL'⟩⟩
            exact hseg s' ⟨hs'.1, hs'.2.trans hr.2⟩
        · obtain ⟨s, hs, hseg, hL⟩ := h₂.exit _ hp.2 t ht h
          by_cases hf : ∀ r ∈ Icc 0 s, f r p.1 ∈ N₁
          · exact ⟨s, hs, fun r hr => ⟨hf r hr, hseg r hr⟩,
              Or.inr ⟨hf s ⟨hs.1, le_rfl⟩, hL⟩⟩
          · push Not at hf
            obtain ⟨r, hr, hrN⟩ := hf
            obtain ⟨s', hs', hseg', hL'⟩ := h₁.exit _ hp.1 r hr.1 hrN
            refine ⟨s', ⟨hs'.1, hs'.2.trans (hr.2.trans hs.2)⟩, fun q hq =>
              ⟨hseg' q hq, hseg q ⟨hq.1, hq.2.trans (hs'.2.trans hr.2)⟩⟩, Or.inl ⟨hL', ?_⟩⟩
            exact hseg s' ⟨hs'.1, hs'.2.trans hr.2⟩ }

/-- The product of an index pair with an attracting pair `(N₂, ∅)`. -/
theorem IsIndexPair.prod_empty {S₁ N₁ L₁ : Set X} {S₂ N₂ : Set B} (h₁ : IsIndexPair f S₁ N₁ L₁)
    (h₂ : IsIndexPair θ S₂ N₂ ∅) :
    IsIndexPair (prodFlow f θ) (S₁ ×ˢ S₂) (N₁ ×ˢ N₂) (L₁ ×ˢ N₂) := by
  have := h₁.prod h₂
  rwa [Set.prod_empty, union_empty] at this

variable {N₁ L₁ : Set X} {N₂ L₂ : Set B}

/-- If `N₂` contracts to `b₀` inside `N₂`, then `(N₁ × N₂)/(L₁ × N₂) ≃ N₁/L₁`. -/
noncomputable def IndexSpace.prodEquiv {b₀ : B} (hb₀ : b₀ ∈ N₂) (H : C(I × N₂, N₂))
    (hH0 : ∀ b, H (0, b) = b) (hH1 : ∀ b, H (1, b) = ⟨b₀, hb₀⟩) :
    PointedHomotopyEquiv (IndexSpace (N₁ ×ˢ N₂) (L₁ ×ˢ N₂)) (IndexSpace N₁ L₁)
      (IndexSpace.pt _ _) (IndexSpace.pt _ _) where
  toFun := descend (IndexSpace.pt N₁ L₁)
    ((IndexSpace.proj N₁ L₁).comp ⟨fun z => ⟨(z : X × B).1, z.2.1⟩,
      (continuous_fst.comp continuous_subtype_val).subtype_mk _⟩)
    (fun _ hz => IndexSpace.proj_eq_pt hz.1)
  invFun := descend (IndexSpace.pt _ _)
    ((IndexSpace.proj (N₁ ×ˢ N₂) (L₁ ×ˢ N₂)).comp ⟨fun x => ⟨((x : X), b₀), x.2, hb₀⟩,
      (continuous_subtype_val.prodMk continuous_const).subtype_mk _⟩)
    (fun _ hx => IndexSpace.proj_eq_pt ⟨hx, hb₀⟩)
  map_pt := rfl
  inv_pt := rfl
  left := by
    let F : C(I × (N₁ ×ˢ N₂ : Set (X × B)), IndexSpace (N₁ ×ˢ N₂) (L₁ ×ˢ N₂)) :=
      (IndexSpace.proj _ _).comp
        ⟨fun p => ⟨((p.2 : X × B).1, (H (σ p.1, ⟨(p.2 : X × B).2, p.2.2.2⟩) : B)), p.2.2.1,
            (H _).2⟩,
          ((continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
            (continuous_subtype_val.comp (H.continuous.comp ((continuous_symm.comp
              continuous_fst).prodMk ((continuous_snd.comp (continuous_subtype_val.comp
                continuous_snd)).subtype_mk _))))).subtype_mk _⟩
    have hF : ∀ (s : I) (z : (N₁ ×ˢ N₂ : Set (X × B))), (z : X × B) ∈ L₁ ×ˢ N₂ →
        F (s, z) = IndexSpace.pt _ _ := fun s z hz =>
      IndexSpace.proj_eq_pt ⟨hz.1, (H _).2⟩
    refine ⟨
      { toFun := descendProd (IndexSpace.pt _ _) F hF
        continuous_toFun := (descendProd (IndexSpace.pt _ _) F hF).continuous
        map_zero_left := fun q => ?_
        map_one_left := fun q => ?_
        prop' := fun t q hq => ?_ }⟩
    · induction q using Quotient.inductionOn
      rename_i a
      rcases a with z | u
      · show IndexSpace.proj _ _ _ = IndexSpace.proj _ _ _
        congr 1
        exact Subtype.ext (Prod.ext rfl (by
          simpa using congrArg Subtype.val (hH1 ⟨(z : X × B).2, z.2.2⟩)))
      · rfl
    · induction q using Quotient.inductionOn
      rename_i a
      rcases a with z | u
      · show IndexSpace.proj _ _ _ = IndexSpace.proj _ _ _
        congr 1
        exact Subtype.ext (Prod.ext rfl (by
          simpa using congrArg Subtype.val (hH0 ⟨(z : X × B).2, z.2.2⟩)))
      · rfl
    · rw [mem_singleton_iff.1 hq]
      rfl
  right := by
    have : (descend (IndexSpace.pt N₁ L₁)
        ((IndexSpace.proj N₁ L₁).comp ⟨fun z => ⟨(z : X × B).1, z.2.1⟩,
          (continuous_fst.comp continuous_subtype_val).subtype_mk _⟩)
        (fun _ hz => IndexSpace.proj_eq_pt hz.1)).comp
        (descend (IndexSpace.pt _ _)
        ((IndexSpace.proj (N₁ ×ˢ N₂) (L₁ ×ˢ N₂)).comp ⟨fun x => ⟨((x : X), b₀), x.2, hb₀⟩,
          (continuous_subtype_val.prodMk continuous_const).subtype_mk _⟩)
        (fun _ hx => IndexSpace.proj_eq_pt ⟨hx, hb₀⟩)) = ContinuousMap.id _ :=
      IndexSpace.hom_ext (fun _ => rfl) rfl
    rw [this]
    exact ContinuousMap.HomotopicRel.refl _

/-- If `(N₂, L₂)` deforms into `L₂` through maps preserving `N₂` and `L₂`, then
`(N₁ × N₂)/(L₁ × N₂ ∪ N₁ × L₂)` is contractible. -/
theorem IndexSpace.prod_pointedContractible (H : C(I × N₂, N₂)) (hH0 : ∀ b, H (0, b) = b)
    (hH1 : ∀ b, (H (1, b) : B) ∈ L₂) (hHL : ∀ s (b : N₂), (b : B) ∈ L₂ → (H (s, b) : B) ∈ L₂) :
    PointedContractible (IndexSpace (N₁ ×ˢ N₂) (L₁ ×ˢ N₂ ∪ N₁ ×ˢ L₂)) (IndexSpace.pt _ _) := by
  let F : C(I × (N₁ ×ˢ N₂ : Set (X × B)), IndexSpace (N₁ ×ˢ N₂) (L₁ ×ˢ N₂ ∪ N₁ ×ˢ L₂)) :=
    (IndexSpace.proj _ _).comp
      ⟨fun p => ⟨((p.2 : X × B).1, (H (p.1, ⟨(p.2 : X × B).2, p.2.2.2⟩) : B)), p.2.2.1,
          (H _).2⟩,
        ((continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
          (continuous_subtype_val.comp (H.continuous.comp (continuous_fst.prodMk
            ((continuous_snd.comp (continuous_subtype_val.comp
              continuous_snd)).subtype_mk _))))).subtype_mk _⟩
  have hF : ∀ (s : I) (z : (N₁ ×ˢ N₂ : Set (X × B))),
      (z : X × B) ∈ L₁ ×ˢ N₂ ∪ N₁ ×ˢ L₂ → F (s, z) = IndexSpace.pt _ _ := by
    intro s z hz
    refine IndexSpace.proj_eq_pt ?_
    rcases hz with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl ⟨ha, (H _).2⟩
    · exact Or.inr ⟨ha, hHL _ _ hb⟩
  refine ⟨
    { toFun := descendProd (IndexSpace.pt _ _) F hF
      continuous_toFun := (descendProd (IndexSpace.pt _ _) F hF).continuous
      map_zero_left := fun q => ?_
      map_one_left := fun q => ?_
      prop' := fun t q hq => ?_ }⟩
  · induction q using Quotient.inductionOn
    rename_i a
    rcases a with z | u
    · show IndexSpace.proj _ _ _ = IndexSpace.proj _ _ _
      congr 1
      exact Subtype.ext (Prod.ext rfl (congrArg Subtype.val (hH0 ⟨(z : X × B).2, z.2.2⟩)))
    · rfl
  · induction q using Quotient.inductionOn
    rename_i a
    rcases a with z | u
    · exact IndexSpace.proj_eq_pt (Or.inr ⟨z.2.1, hH1 _⟩)
    · rfl
  · rw [mem_singleton_iff.1 hq]
    rfl

end Product

/-! ### Skew products -/

section Skew

variable {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]

/-- `Φ` is a skew product over the base flow `θ`. -/
def IsSkew (Φ : Flow ℝ (X × B)) (θ : Flow ℝ B) : Prop := ∀ t p, (Φ t p).2 = θ t p.2

variable {Φ : Flow ℝ (X × B)} {θ : Flow ℝ B}

theorem IsSkew.flow_eq (hΦ : IsSkew Φ θ) (t : ℝ) (p : X × B) :
    Φ t p = ((Φ t p).1, θ t p.2) := Prod.ext rfl (hΦ t p)

/-- The fiber flow over a fixed point `b₀` of the base. -/
def fiberFlow (hΦ : IsSkew Φ θ) (b₀ : B) (hb₀ : ∀ t, θ t b₀ = b₀) : Flow ℝ X where
  toFun t x := (Φ t (x, b₀)).1
  cont' := continuous_fst.comp
    (Φ.continuous continuous_fst (continuous_snd.prodMk continuous_const))
  map_add' t s x := by
    have e : Φ s (x, b₀) = ((Φ s (x, b₀)).1, b₀) := by
      rw [hΦ.flow_eq, hb₀]
    show (Φ (t + s) (x, b₀)).1 = (Φ t ((Φ s (x, b₀)).1, b₀)).1
    rw [Φ.map_add, e]
  map_zero' x := by
    show (Φ 0 (x, b₀)).1 = x
    rw [Φ.map_zero_apply]

theorem fiberFlow_apply (hΦ : IsSkew Φ θ) (b₀ : B) (hb₀ : ∀ t, θ t b₀ = b₀) (t : ℝ) (x : X) :
    fiberFlow hΦ b₀ hb₀ t x = (Φ t (x, b₀)).1 := rfl

/-- A deformation of the base onto a fixed point `b₀` through maps commuting with `θ`. -/
structure SkewContraction (θ : Flow ℝ B) (b₀ : B) where
  g : C(I × B, B)
  one : ∀ b, g (1, b) = b
  zero : ∀ b, g (0, b) = b₀
  fix : ∀ l, g (l, b₀) = b₀
  equivariant : ∀ l t b, g (l, θ t b) = θ t (g (l, b))

variable {b₀ : B}

theorem SkewContraction.fixed (c : SkewContraction θ b₀) (t : ℝ) : θ t b₀ = b₀ := by
  have := c.equivariant 0 t b₀
  rw [c.zero, c.zero] at this
  exact this.symm

/-- The family of flows `(x, b) ↦ (φ(t, g_λ b, x), θ_t b)`. -/
def SkewContraction.family (hΦ : IsSkew Φ θ) (c : SkewContraction θ b₀) : FlowFamily (X × B) where
  flow :=
    { toFun := fun t q => (q.1, ((Φ t (q.2.1, c.g (q.1, q.2.2))).1, θ t q.2.2))
      cont' := by
        refine (continuous_fst.comp continuous_snd).prodMk
          ((continuous_fst.comp (Φ.continuous continuous_fst
            ((continuous_fst.comp (continuous_snd.comp continuous_snd)).prodMk
              (c.g.continuous.comp ((continuous_fst.comp continuous_snd).prodMk
                (continuous_snd.comp (continuous_snd.comp continuous_snd))))))).prodMk
          (θ.continuous continuous_fst (continuous_snd.comp (continuous_snd.comp continuous_snd))))
      map_add' := fun t s q => by
        have e : ((Φ s (q.2.1, c.g (q.1, q.2.2))).1, c.g (q.1, θ s q.2.2)) =
            Φ s (q.2.1, c.g (q.1, q.2.2)) := by
          rw [c.equivariant, hΦ.flow_eq s]
        simp only [Prod.mk.injEq, true_and]
        rw [Flow.map_add, Flow.map_add, ← e]
        exact ⟨rfl, rfl⟩
      map_zero' := fun q => by
        simp only [Flow.map_zero_apply] }
  fst_eq _ _ := rfl

variable (hΦ : IsSkew Φ θ) (c : SkewContraction θ b₀)

theorem SkewContraction.slice_one : (c.family hΦ).slice 1 = Φ := by
  refine Flow.ext fun t p => ?_
  show ((Φ t (p.1, c.g (1, p.2))).1, θ t p.2) = Φ t p
  rw [c.one]
  exact (hΦ.flow_eq t p).symm

theorem SkewContraction.slice_zero :
    (c.family hΦ).slice 0 = prodFlow (fiberFlow hΦ b₀ c.fixed) θ := by
  refine Flow.ext fun t p => ?_
  show ((Φ t (p.1, c.g (0, p.2))).1, θ t p.2) = ((Φ t (p.1, b₀)).1, θ t p.2)
  rw [c.zero]

/-- A full orbit in `A × C` with `Inv θ C = {b₀}` lies in the fiber over `b₀`. -/
theorem IsSkew.Inv_prod {b₀ : B} (hfix : ∀ t, θ t b₀ = b₀) {A : Set X} {C : Set B}
    (hC : Inv θ C = {b₀}) : Inv Φ (A ×ˢ C) = Inv (fiberFlow hΦ b₀ hfix) A ×ˢ {b₀} := by
  ext ⟨x, b⟩
  constructor
  · intro hp
    have hb : b ∈ Inv θ C := fun t => by
      have := (hp t).2
      rwa [hΦ] at this
    rw [hC] at hb
    obtain rfl := hb
    exact ⟨fun t => (hp t).1, rfl⟩
  · rintro ⟨hx, rfl⟩ t
    have hb₀ : b ∈ C := by
      have : b ∈ Inv θ C := by rw [hC]; rfl
      exact Inv_subset C this
    rw [hΦ.flow_eq, hfix]
    exact ⟨hx t, hb₀⟩

theorem SkewContraction.Inv_slice {A : Set X} {C : Set B} (hC : Inv θ C = {b₀}) (l : I) :
    Inv ((c.family hΦ).slice l) (A ×ˢ C) = Inv (fiberFlow hΦ b₀ c.fixed) A ×ˢ {b₀} := by
  ext ⟨x, b⟩
  constructor
  · intro hp
    have hb : b ∈ Inv θ C := fun t => (hp t).2
    rw [hC] at hb
    obtain rfl := hb
    refine ⟨fun t => ?_, rfl⟩
    have := (hp t).1
    rwa [show ((c.family hΦ).slice l t (x, b)).1 = (Φ t (x, c.g (l, b))).1 from rfl,
      c.fix] at this
  · rintro ⟨hx, rfl⟩ t
    have hb₀ : b ∈ C := by
      have : b ∈ Inv θ C := by rw [hC]; rfl
      exact Inv_subset C this
    show ((Φ t (x, c.g (l, b))).1, θ t b) ∈ A ×ˢ C
    rw [c.fix, c.fixed]
    exact ⟨hx t, hb₀⟩

/-- Continuation from the skew product to the product flow `f₀ × θ` near the fiber over a fixed
point `b₀` of the base. -/
theorem skew_continuation [TopologicalSpace.MetrizableSpace X]
    [TopologicalSpace.MetrizableSpace B] {NK : Set X}
    (hNK : IsIsolatingNbhd (fiberFlow hΦ b₀ c.fixed) NK) {C : Set B} (hCc : IsCompact C)
    (hC : Inv θ C = {b₀}) (hb₀ : b₀ ∈ interior C) {N₀ L₀ N₁ L₁ : Set (X × B)}
    (h₀ : IsIndexPair (prodFlow (fiberFlow hΦ b₀ c.fixed) θ)
      (Inv (fiberFlow hΦ b₀ c.fixed) NK ×ˢ {b₀}) N₀ L₀)
    (h₁ : IsIndexPair Φ (Inv (fiberFlow hΦ b₀ c.fixed) NK ×ˢ {b₀}) N₁ L₁) :
    Nonempty (PointedHomotopyEquiv (IndexSpace N₀ L₀) (IndexSpace N₁ L₁)
      (IndexSpace.pt _ _) (IndexSpace.pt _ _)) := by
  have hInv := c.Inv_slice hΦ (A := NK) hC
  refine continuation (c.family hΦ) (hNK.1.prod hCc) (fun l => ?_) ?_ ?_
  · rw [hInv l, interior_prod_eq]
    exact prod_mono hNK.2 (singleton_subset_iff.2 hb₀)
  · rw [hInv 0, c.slice_zero hΦ]
    exact h₀
  · rw [hInv 1, c.slice_one hΦ]
    exact h₁

end Skew

/-! ### Restricting a skew product to an invariant part of the base -/

section Restrict

variable {X B : Type*} [TopologicalSpace X] [TopologicalSpace B] {Φ : Flow ℝ (X × B)}
  {θ : Flow ℝ B} (hΦ : IsSkew Φ θ) {U : Set B} (hU : IsInvariant θ U)

/-- The skew product over the restricted base flow on `U`. -/
def IsSkew.restrict : Flow ℝ (X × U) where
  toFun t p := ((Φ t (p.1, (p.2 : B))).1, θ.restrict hU t p.2)
  cont' := (continuous_fst.comp (Φ.continuous continuous_fst
    ((continuous_fst.comp continuous_snd).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))).prodMk
    ((θ.restrict hU).continuous continuous_fst (continuous_snd.comp continuous_snd))
  map_add' t s p := by
    have e : ((Φ s (p.1, (p.2 : B))).1, θ s (p.2 : B)) = Φ s (p.1, (p.2 : B)) :=
      (hΦ.flow_eq s _).symm
    show ((Φ (t + s) (p.1, (p.2 : B))).1, θ.restrict hU (t + s) p.2) =
      ((Φ t ((Φ s (p.1, (p.2 : B))).1, θ s (p.2 : B))).1,
        θ.restrict hU t (θ.restrict hU s p.2))
    rw [e, Φ.map_add, Flow.map_add]
  map_zero' p := by
    show ((Φ 0 (p.1, (p.2 : B))).1, θ.restrict hU 0 p.2) = p
    rw [Φ.map_zero_apply, Flow.map_zero_apply]

theorem IsSkew.isSkew_restrict : IsSkew (hΦ.restrict hU) (θ.restrict hU) := fun _ _ => rfl

/-- The inclusion `X × U → X × B`. -/
def skewIncl (U : Set B) : X × U → X × B := fun p => (p.1, (p.2 : B))

theorem IsSkew.restrict_conj (t : ℝ) (p : X × U) :
    skewIncl U (hΦ.restrict hU t p) = Φ t (skewIncl U p) :=
  (hΦ.flow_eq t _).symm

theorem isOpenEmbedding_skewIncl (hUo : IsOpen U) : IsOpenEmbedding (skewIncl (X := X) U) :=
  IsOpenEmbedding.id.prodMap hUo.isOpenEmbedding_subtypeVal

omit [TopologicalSpace X] [TopologicalSpace B] in
theorem range_skewIncl : range (skewIncl (X := X) U) = univ ×ˢ U := by
  ext ⟨x, b⟩
  constructor
  · rintro ⟨⟨x', b'⟩, h⟩
    simp only [skewIncl, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨mem_univ _, b'.2⟩
  · rintro ⟨-, hb⟩
    exact ⟨(x, ⟨b, hb⟩), rfl⟩

theorem IsSkew.fiberFlow_restrict {b₀ : B} (hb₀ : b₀ ∈ U)
    (hfix : ∀ t, θ.restrict hU t ⟨b₀, hb₀⟩ = ⟨b₀, hb₀⟩) :
    fiberFlow (hΦ.isSkew_restrict hU) ⟨b₀, hb₀⟩ hfix =
      fiberFlow hΦ b₀ (fun t => congrArg Subtype.val (hfix t)) := by
  ext t x
  rfl

end Restrict

/-! ### Boundary indices of skew products -/

section Boundary

variable {X B : Type*} [TopologicalSpace X] [TopologicalSpace B] [T2Space X] [T2Space B]
  [TopologicalSpace.MetrizableSpace X] [TopologicalSpace.MetrizableSpace B]
  {Φ : Flow ℝ (X × B)} {θ : Flow ℝ B} (hΦ : IsSkew Φ θ) {U : Set B} (hU : IsInvariant θ U)
  (hUo : IsOpen U) {b₀ : B} (hb₀U : b₀ ∈ U)
  (c : SkewContraction (θ.restrict hU) ⟨b₀, hb₀U⟩)

/-- The fiber flow over `b₀`. -/
abbrev SkewContraction.f₀ : Flow ℝ X :=
  fiberFlow hΦ b₀ (fun t => congrArg Subtype.val (c.fixed t))

include hUo in
/-- The common part of the boundary index computations. For an index pair `(Nb, Lb)` of `{b₀}`
in the base with `Nb ⊆ U`, there is an index pair `(N, L)` of `K × {b₀}` whose index space is
equivalent to `(NK × Nb)/(LK × Nb ∪ NK × Lb)` for every index pair `(NK, LK)` of `K`. -/
theorem skew_boundary_setup {M : Set X} (hM : IsIsolatingNbhd (c.f₀ hΦ hU hb₀U) M)
    {Nb Lb : Set B} (hb : IsIndexPair θ {b₀} Nb Lb) (hNbU : Nb ⊆ U) :
    ∃ N L, IsIndexPair Φ (Inv (c.f₀ hΦ hU hb₀U) M ×ˢ {b₀}) N L ∧
      ∀ NK LK, IsIndexPair (c.f₀ hΦ hU hb₀U) (Inv (c.f₀ hΦ hU hb₀U) M) NK LK →
        Nonempty (PointedHomotopyEquiv
          (IndexSpace (NK ×ˢ (Subtype.val ⁻¹' Nb : Set U))
            (LK ×ˢ (Subtype.val ⁻¹' Nb : Set U) ∪ NK ×ˢ (Subtype.val ⁻¹' Lb : Set U)))
          (IndexSpace N L) (IndexSpace.pt _ _) (IndexSpace.pt _ _)) := by
  have hfix : ∀ t, θ t b₀ = b₀ := fun t => congrArg Subtype.val (c.fixed t)
  have hNbc := hb.isCompact_N.isClosed
  set C := closure (Nb \ Lb) with hCdef
  have hCN : C ⊆ Nb := closure_minimal sdiff_subset hNbc
  have hCc : IsCompact C := hb.isolating.1
  have hCinv : Inv θ C = {b₀} := hb.inv_eq
  have hb₀C : b₀ ∈ interior C :=
    interior_mono subset_closure (hb.nhds (mem_singleton b₀))
  -- an index pair of `K × {b₀}` for `Φ` inside `X × U`
  have hMC : IsIsolatingNbhd Φ (M ×ˢ C) := by
    refine ⟨hM.1.prod hCc, ?_⟩
    rw [hΦ.Inv_prod hfix hCinv, interior_prod_eq]
    exact prod_mono hM.2 (singleton_subset_iff.2 hb₀C)
  obtain ⟨N, L, hP0, hNM⟩ := exists_indexPair_of_t2 hMC
  rw [hΦ.Inv_prod hfix hCinv] at hP0
  have hP : IsIndexPair Φ (Inv (c.f₀ hΦ hU hb₀U) M ×ˢ {b₀}) N L := hP0
  refine ⟨N, L, hP, fun NK LK hK => ?_⟩
  have he := isOpenEmbedding_skewIncl (X := X) hUo
  have hNe : N ⊆ range (skewIncl (X := X) U) := by
    rw [range_skewIncl]
    exact hNM.trans (prod_mono (subset_univ _) (hCN.trans hNbU))
  have hP' := hP.preimage_of_isOpenEmbedding he (hΦ.restrict_conj hU) hNe
  have hS : skewIncl U ⁻¹' (Inv (c.f₀ hΦ hU hb₀U) M ×ˢ {b₀}) =
      Inv (c.f₀ hΦ hU hb₀U) M ×ˢ ({⟨b₀, hb₀U⟩} : Set U) := by
    ext ⟨x, b⟩
    simp only [skewIncl, mem_preimage, mem_prod, mem_singleton_iff]
    exact and_congr_right fun _ => ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [hS] at hP'
  -- the base pair and the isolating set pulled back to `U`
  have hUe : IsOpenEmbedding (Subtype.val : U → B) := hUo.isOpenEmbedding_subtypeVal
  have hθc : ∀ t (b : U), ((θ.restrict hU t b : U) : B) = θ t b := fun _ _ => rfl
  have hb' := hb.preimage_of_isOpenEmbedding hUe hθc
    (by rw [Subtype.range_coe]; exact hNbU)
  have hsing : (Subtype.val ⁻¹' {b₀} : Set U) = {⟨b₀, hb₀U⟩} := by
    ext b
    simp only [mem_preimage, mem_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [hsing] at hb'
  have hC'c : IsCompact (Subtype.val ⁻¹' C : Set U) := by
    rw [hUe.isEmbedding.isCompact_iff, image_preimage_eq_of_subset
      (by rw [Subtype.range_coe]; exact hCN.trans hNbU)]
    exact hCc
  have hC'inv : Inv (θ.restrict hU) (Subtype.val ⁻¹' C) = {⟨b₀, hb₀U⟩} := by
    rw [Inv_preimage_of_conj hθc, hCinv, hsing]
  have hb₀C' : (⟨b₀, hb₀U⟩ : U) ∈ interior (Subtype.val ⁻¹' C) := by
    rw [← hUe.isOpenMap.preimage_interior_eq_interior_preimage hUe.continuous]
    exact hb₀C
  have hfib : fiberFlow (hΦ.isSkew_restrict hU) ⟨b₀, hb₀U⟩ c.fixed = c.f₀ hΦ hU hb₀U :=
    hΦ.fiberFlow_restrict hU hb₀U c.fixed
  have hM' : IsIsolatingNbhd (fiberFlow (hΦ.isSkew_restrict hU) ⟨b₀, hb₀U⟩ c.fixed) M := by
    rw [hfib]; exact hM
  have h₀ := hK.prod hb'
  rw [← hfib] at h₀ hP'
  obtain ⟨e₁⟩ := skew_continuation (hΦ.isSkew_restrict hU) c hM' hC'c hC'inv hb₀C' h₀ hP'
  exact ⟨e₁.trans (IndexSpace.embeddingEquiv he.isEmbedding hNe)⟩

include hUo in
/-- A fixed point `b₀` of the base whose index pair `(Nb, Lb)` deforms into `Lb` (a one-sided
repeller) gives `K × {b₀}` the trivial index. -/
theorem skew_indexTrivial {M : Set X} (hM : IsIsolatingNbhd (c.f₀ hΦ hU hb₀U) M)
    {Nb Lb : Set B} (hb : IsIndexPair θ {b₀} Nb Lb) (hNbU : Nb ⊆ U)
    (H : C(I × (Subtype.val ⁻¹' Nb : Set U), (Subtype.val ⁻¹' Nb : Set U)))
    (hH0 : ∀ b, H (0, b) = b) (hH1 : ∀ b, ((H (1, b) : U) : B) ∈ Lb)
    (hHL : ∀ s (b : (Subtype.val ⁻¹' Nb : Set U)), ((b : U) : B) ∈ Lb →
      ((H (s, b) : U) : B) ∈ Lb) :
    IndexTrivial Φ (Inv (c.f₀ hΦ hU hb₀U) M ×ˢ {b₀}) := by
  obtain ⟨N, L, hP, hE⟩ := skew_boundary_setup hΦ hU hUo hb₀U c hM hb hNbU
  obtain ⟨NK, LK, hK, -⟩ := exists_indexPair_of_t2 hM
  obtain ⟨e⟩ := hE NK LK hK
  exact ⟨N, L, hP, PointedContractible.of_equiv e.symm
    (IndexSpace.prod_pointedContractible H hH0 hH1 hHL)⟩

include hUo in
/-- A fixed point `b₀` of the base with an attracting index pair `(Nb, ∅)` that contracts to
`b₀` gives `K × {b₀}` the index of `K` for the fiber flow. -/
theorem skew_hasIndex {M : Set X} (hM : IsIsolatingNbhd (c.f₀ hΦ hU hb₀U) M)
    {Nb : Set B} (hb : IsIndexPair θ {b₀} Nb ∅) (hNbU : Nb ⊆ U) (hb₀ : b₀ ∈ Nb)
    (H : C(I × (Subtype.val ⁻¹' Nb : Set U), (Subtype.val ⁻¹' Nb : Set U)))
    (hH0 : ∀ b, H (0, b) = b) (hH1 : ∀ b, H (1, b) = ⟨⟨b₀, hb₀U⟩, hb₀⟩)
    {NK LK : Set X} (hK : IsIndexPair (c.f₀ hΦ hU hb₀U) (Inv (c.f₀ hΦ hU hb₀U) M) NK LK) :
    HasIndex Φ (Inv (c.f₀ hΦ hU hb₀U) M ×ˢ {b₀}) (IndexSpace NK LK) (IndexSpace.pt _ _) := by
  obtain ⟨N, L, hP, hE⟩ := skew_boundary_setup hΦ hU hUo hb₀U c hM hb hNbU
  obtain ⟨e⟩ := hE NK LK hK
  have hL : LK ×ˢ (Subtype.val ⁻¹' Nb : Set U) ∪ NK ×ˢ (Subtype.val ⁻¹' (∅ : Set B) : Set U) =
      LK ×ˢ (Subtype.val ⁻¹' Nb : Set U) := by simp
  rw [hL] at e
  exact ⟨N, L, hP, ⟨e.symm.trans (IndexSpace.prodEquiv (N₁ := NK) (L₁ := LK)
    (N₂ := (Subtype.val ⁻¹' Nb : Set U)) (b₀ := (⟨b₀, hb₀U⟩ : U)) hb₀ H hH0 hH1)⟩⟩

end Boundary

end ConleyCheck.Conley
