import ConleyCheck.Conley.Index

/-!
# Additivity of the Conley index

If `A` and `R` are disjoint isolated invariant sets, then `A ∪ R` has index `h(A) ∨ h(R)`.
Disjoint isolating neighborhoods give index pairs `(N, L)` and `(N', L')` with `N ∩ N' = ∅`.
Their union `(N ∪ N', L ∪ L')` is an index pair for `A ∪ R`, because orbit segments are connected,
and `(N ∪ N')/(L ∪ L')` is homeomorphic to `N/L ∨ N'/L'`. Finally the wedge of two pointed homotopy
equivalences is a pointed homotopy equivalence.
-/

namespace ConleyCheck.Conley

open Set Topology unitInterval ContinuousMap
open scoped Classical

/-! ### The wedge sum as a functor -/

namespace Wedge

variable {X Y X' Y' X'' Y'' Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y'] [TopologicalSpace X''] [TopologicalSpace Y'']
  [TopologicalSpace Z]

/-- The inclusion `X → X ∨ Y`. -/
def inl (x₀ : X) (y₀ : Y) : C(X, Wedge X Y x₀ y₀) :=
  ⟨fun x => Quotient.mk _ (.inl x), continuous_quotient_mk'.comp continuous_inl⟩

/-- The inclusion `Y → X ∨ Y`. -/
def inr (x₀ : X) (y₀ : Y) : C(Y, Wedge X Y x₀ y₀) :=
  ⟨fun y => Quotient.mk _ (.inr y), continuous_quotient_mk'.comp continuous_inr⟩

theorem inl_pt (x₀ : X) (y₀ : Y) : inl x₀ y₀ x₀ = Wedge.pt x₀ y₀ := rfl

theorem inr_pt (x₀ : X) (y₀ : Y) : inr x₀ y₀ y₀ = Wedge.pt x₀ y₀ :=
  Quotient.sound (Or.inr ⟨(rfl : y₀ = y₀), (rfl : x₀ = x₀)⟩)

theorem elim_respects {x₀ : X} {y₀ : Y} (a : X → Z) (b : Y → Z) (hab : a x₀ = b y₀)
    (p q : X ⊕ Y) (h : (collapseSetoid (wedgeBase x₀ y₀)).r p q) :
    Sum.elim a b p = Sum.elim a b q := by
  have key : ∀ p : X ⊕ Y, wedgeBase x₀ y₀ p → Sum.elim a b p = a x₀ := by
    rintro (x | y) hp
    · exact congrArg a hp
    · exact (congrArg b hp).trans hab.symm
  rcases (h : p = q ∨ (wedgeBase x₀ y₀ p ∧ wedgeBase x₀ y₀ q)) with rfl | ⟨hp, hq⟩
  · rfl
  · rw [key p hp, key q hq]

/-- A pair of maps agreeing on the base points induces a map out of the wedge. -/
def lift {x₀ : X} {y₀ : Y} (a : C(X, Z)) (b : C(Y, Z)) (hab : a x₀ = b y₀) :
    C(Wedge X Y x₀ y₀, Z) where
  toFun := Quotient.lift (s := collapseSetoid (wedgeBase x₀ y₀)) (Sum.elim a b)
    (elim_respects a b hab)
  continuous_toFun := (a.continuous.sumElim b.continuous).quotient_lift _

theorem hom_ext {x₀ : X} {y₀ : Y} {f g : C(Wedge X Y x₀ y₀, Z)}
    (h1 : ∀ x, f (inl x₀ y₀ x) = g (inl x₀ y₀ x)) (h2 : ∀ y, f (inr x₀ y₀ y) = g (inr x₀ y₀ y)) :
    f = g := by
  ext p
  induction p using Quotient.inductionOn
  rename_i p
  rcases p with x | y
  · exact h1 x
  · exact h2 y

/-- The wedge of two pointed maps. -/
def map {x₀ : X} {y₀ : Y} {x₁ : X'} {y₁ : Y'} (f : C(X, X')) (g : C(Y, Y')) (hf : f x₀ = x₁)
    (hg : g y₀ = y₁) : C(Wedge X Y x₀ y₀, Wedge X' Y' x₁ y₁) :=
  lift ((inl x₁ y₁).comp f) ((inr x₁ y₁).comp g) (by
    show inl x₁ y₁ (f x₀) = inr x₁ y₁ (g y₀)
    rw [hf, hg, inl_pt, inr_pt])

theorem map_pt {x₀ : X} {y₀ : Y} {x₁ : X'} {y₁ : Y'} (f : C(X, X')) (g : C(Y, Y'))
    (hf : f x₀ = x₁) (hg : g y₀ = y₁) : map f g hf hg (Wedge.pt x₀ y₀) = Wedge.pt x₁ y₁ := by
  show inl x₁ y₁ (f x₀) = _
  rw [hf]
  rfl

theorem map_comp {x₀ : X} {y₀ : Y} {x₁ : X'} {y₁ : Y'} {x₂ : X''} {y₂ : Y''}
    (f : C(X, X')) (g : C(Y, Y')) (hf : f x₀ = x₁) (hg : g y₀ = y₁)
    (f' : C(X', X'')) (g' : C(Y', Y'')) (hf' : f' x₁ = x₂) (hg' : g' y₁ = y₂) :
    (map f' g' hf' hg').comp (map f g hf hg) =
      map (f'.comp f) (g'.comp g) (by simp [hf, hf']) (by simp [hg, hg']) :=
  hom_ext (fun _ => rfl) (fun _ => rfl)

theorem map_id (x₀ : X) (y₀ : Y) :
    map (ContinuousMap.id X) (ContinuousMap.id Y) (x₀ := x₀) (y₀ := y₀) rfl rfl =
      ContinuousMap.id _ :=
  hom_ext (fun _ => rfl) (fun _ => rfl)

/-- Homotopies relative to the base points glue to a homotopy of wedge maps. -/
theorem homotopicRel_map {x₀ : X} {y₀ : Y} {x₁ : X'} {y₁ : Y'} {f₀ f₁ : C(X, X')}
    {g₀ g₁ : C(Y, Y')} (hf₀ : f₀ x₀ = x₁) (hg₀ : g₀ y₀ = y₁) (hf₁ : f₁ x₀ = x₁)
    (hg₁ : g₁ y₀ = y₁) (F : HomotopyRel f₀ f₁ {x₀}) (G : HomotopyRel g₀ g₁ {y₀}) :
    (map f₀ g₀ hf₀ hg₀).HomotopicRel (map f₁ g₁ hf₁ hg₁) {Wedge.pt x₀ y₀} := by
  have hab : ∀ s : I, inl x₁ y₁ (F (s, x₀)) = inr x₁ y₁ (G (s, y₀)) := fun s => by
    rw [F.eq_fst s (mem_singleton x₀), G.eq_fst s (mem_singleton y₀), hf₀, hg₀, inl_pt, inr_pt]
  refine ⟨
    { toFun := fun p => Quotient.lift (s := collapseSetoid (wedgeBase x₀ y₀))
        (Sum.elim (fun x => inl x₁ y₁ (F (p.1, x))) fun y => inr x₁ y₁ (G (p.1, y)))
        (elim_respects _ _ (hab p.1)) p.2
      continuous_toFun := ?_
      map_zero_left := fun p => ?_
      map_one_left := fun p => ?_
      prop' := fun t p hp => ?_ }⟩
  · apply Topology.IsQuotientMap.continuous_lift_prod_right
      (f := Quotient.mk (collapseSetoid (wedgeBase x₀ y₀))) isQuotientMap_quotient_mk'
    have e : (fun p : I × (X ⊕ Y) => Sum.elim (fun x => inl x₁ y₁ (F (p.1, x)))
        (fun y => inr x₁ y₁ (G (p.1, y))) p.2) =
        (Sum.elim ((inl x₁ y₁).comp F.toContinuousMap) ((inr x₁ y₁).comp G.toContinuousMap)) ∘
          Homeomorph.prodSumDistrib := by
      funext ⟨s, a⟩
      rcases a with x | y <;> rfl
    exact e ▸ (((inl x₁ y₁).comp F.toContinuousMap).continuous.sumElim
      ((inr x₁ y₁).comp G.toContinuousMap).continuous).comp Homeomorph.prodSumDistrib.continuous
  · induction p using Quotient.inductionOn
    rename_i p
    rcases p with x | y
    · exact congrArg (inl x₁ y₁) (F.apply_zero x)
    · exact congrArg (inr x₁ y₁) (G.apply_zero y)
  · induction p using Quotient.inductionOn
    rename_i p
    rcases p with x | y
    · exact congrArg (inl x₁ y₁) (F.apply_one x)
    · exact congrArg (inr x₁ y₁) (G.apply_one y)
  · rw [mem_singleton_iff.1 hp]
    exact congrArg (inl x₁ y₁) (F.eq_fst t (mem_singleton x₀))

end Wedge

/-- The wedge of two pointed homotopy equivalences. -/
def PointedHomotopyEquiv.wedge {X Y X' Y' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y'] {x₀ : X} {y₀ : Y} {x₁ : X'} {y₁ : Y'}
    (e : PointedHomotopyEquiv X X' x₀ x₁) (e' : PointedHomotopyEquiv Y Y' y₀ y₁) :
    PointedHomotopyEquiv (Wedge X Y x₀ y₀) (Wedge X' Y' x₁ y₁) (Wedge.pt x₀ y₀)
      (Wedge.pt x₁ y₁) where
  toFun := Wedge.map e.toFun e'.toFun e.map_pt e'.map_pt
  invFun := Wedge.map e.invFun e'.invFun e.inv_pt e'.inv_pt
  map_pt := Wedge.map_pt _ _ _ _
  inv_pt := Wedge.map_pt _ _ _ _
  left := by
    rw [Wedge.map_comp, ← Wedge.map_id]
    obtain ⟨F⟩ := e.left
    obtain ⟨G⟩ := e'.left
    exact Wedge.homotopicRel_map _ _ _ _ F G
  right := by
    rw [Wedge.map_comp, ← Wedge.map_id]
    obtain ⟨F⟩ := e.right
    obtain ⟨G⟩ := e'.right
    exact Wedge.homotopicRel_map _ _ _ _ F G

/-! ### Disjoint index pairs -/

variable {α : Type*} [TopologicalSpace α] {ϕ : Flow ℝ α}

theorem mem_N_iff_mem_U {N N' U U' : Set α} (hUU : Disjoint U U') (hNU : N ⊆ U)
    (hNU' : N' ⊆ U') (z : ↥(N ∪ N')) : (z : α) ∈ N ↔ (z : α) ∈ U :=
  ⟨fun hz => hNU hz, fun hz => z.2.resolve_right fun h1 => disjoint_left.1 hUU hz (hNU' h1)⟩

/-- `(N ∪ N')/(L ∪ L') → N/L ∨ N'/L'`. -/
noncomputable def toWedge {N L N' L' U U' : Set α} (hNc : IsClosed N) (hLN : L ⊆ N)
    (hLN' : L' ⊆ N') (hU : IsOpen U) (hUU : Disjoint U U') (hNU : N ⊆ U) (hNU' : N' ⊆ U') :
    C(IndexSpace (N ∪ N') (L ∪ L'),
      Wedge (IndexSpace N L) (IndexSpace N' L') (IndexSpace.pt N L) (IndexSpace.pt N' L')) :=
  descend (Wedge.pt _ _)
    ⟨fun z => if (z : α) ∈ N then Wedge.inl _ _ (IndexSpace.Q N L z)
      else Wedge.inr _ _ (IndexSpace.Q N' L' z), by
      have hcl : IsClosed {z : ↥(N ∪ N') | (z : α) ∈ N} :=
        hNc.preimage continuous_subtype_val
      have hop : IsOpen {z : ↥(N ∪ N') | (z : α) ∈ N} := by
        have e : {z : ↥(N ∪ N') | (z : α) ∈ N} = {z : ↥(N ∪ N') | (z : α) ∈ U} :=
          Set.ext fun z => mem_N_iff_mem_U hUU hNU hNU' z
        rw [e]
        exact hU.preimage continuous_subtype_val
      have hcl' : IsClosed {z : ↥(N ∪ N') | ¬ (z : α) ∈ N} := hop.isClosed_compl
      apply continuous_if
      · intro a ha
        rw [(IsClopen.frontier_eq ⟨hcl, hop⟩)] at ha
        exact ha.elim
      · rw [hcl.closure_eq]
        exact (Wedge.inl _ _).continuous.comp_continuousOn
          ((IndexSpace.continuousOn_Q N L).comp continuous_subtype_val.continuousOn
            fun z hz => hz)
      · rw [hcl'.closure_eq]
        exact (Wedge.inr _ _).continuous.comp_continuousOn
          ((IndexSpace.continuousOn_Q N' L').comp continuous_subtype_val.continuousOn
            fun z hz => z.2.resolve_left hz)⟩
    (by
      intro y hy
      show (if (y : α) ∈ N then Wedge.inl _ _ (IndexSpace.Q N L y)
        else Wedge.inr _ _ (IndexSpace.Q N' L' y)) = _
      by_cases hyN : (y : α) ∈ N
      · rw [if_pos hyN]
        have hyL : (y : α) ∈ L := hy.resolve_right fun h1 =>
          disjoint_left.1 hUU (hNU hyN) (hNU' (hLN' h1))
        rw [IndexSpace.Q_of_mem_L hLN hyL]
        rfl
      · rw [if_neg hyN]
        have hyL : (y : α) ∈ L' := hy.resolve_left fun h1 => hyN (hLN h1)
        rw [IndexSpace.Q_of_mem_L hLN' hyL]
        exact Wedge.inr_pt _ _)

/-- `N/L ∨ N'/L' → (N ∪ N')/(L ∪ L')`. -/
noncomputable def ofWedge (N L N' L' : Set α) :
    C(Wedge (IndexSpace N L) (IndexSpace N' L') (IndexSpace.pt N L) (IndexSpace.pt N' L'),
      IndexSpace (N ∪ N') (L ∪ L')) :=
  Wedge.lift
    (descend (IndexSpace.pt _ _) ((IndexSpace.proj (N ∪ N') (L ∪ L')).comp
      ⟨fun x => ⟨x, Or.inl x.2⟩, continuous_subtype_val.subtype_mk _⟩)
      fun _ hy => IndexSpace.proj_eq_pt (Or.inl hy))
    (descend (IndexSpace.pt _ _) ((IndexSpace.proj (N ∪ N') (L ∪ L')).comp
      ⟨fun x => ⟨x, Or.inr x.2⟩, continuous_subtype_val.subtype_mk _⟩)
      fun _ hy => IndexSpace.proj_eq_pt (Or.inr hy))
    rfl


/-- An isolated invariant set has isolating neighborhoods inside any open neighborhood. -/
theorem exists_isolatingNbhd_subset [T2Space α] {S U : Set α} (hS : IsIsolatedInvariantSet ϕ S)
    (hU : IsOpen U) (hSU : S ⊆ U) : ∃ K, IsIsolatingNbhd ϕ K ∧ Inv ϕ K = S ∧ K ⊆ U := by
  obtain ⟨M, hM, rfl⟩ := hS
  have hC : IsCompact (M \ (U ∩ interior M)) := hM.1.diff (hU.inter isOpen_interior)
  obtain ⟨V, W, hV, hW, hSV, hCW, hVW⟩ := SeparatedNhds.of_isCompact_isCompact
    (isCompact_Inv hM.1) hC (disjoint_left.2 fun x hx hxC => hxC.2 ⟨hSU hx, hM.2 hx⟩)
  have hK : IsCompact (M \ W) := hM.1.diff hW
  have hint : Inv ϕ M ⊆ interior (M \ W) := fun x hx =>
    interior_maximal (s := M \ W) (t := interior M ∩ V)
      (fun y hy => ⟨interior_subset hy.1, disjoint_left.1 hVW hy.2⟩)
      (isOpen_interior.inter hV) ⟨hM.2 hx, hSV hx⟩
  refine ⟨M \ W, isIsolatingNbhd_of_between hK hint sdiff_subset,
    Inv_eq_of_between hint sdiff_subset, fun x hx => ?_⟩
  by_contra hxU
  exact hx.2 (hCW ⟨hx.1, fun h => hxU h.1⟩)

/-- An orbit over a preconnected time set inside `U ∪ V`, meeting `U`, stays in `U`. -/
theorem orbit_stays {U V : Set α} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    {T : Set ℝ} (hT : IsPreconnected T) {x : α} (hsub : ∀ t ∈ T, ϕ t x ∈ U ∪ V) {t₀ : ℝ}
    (ht₀ : t₀ ∈ T) (hU₀ : ϕ t₀ x ∈ U) : ∀ t ∈ T, ϕ t x ∈ U := by
  have hc : IsPreconnected ((fun t => ϕ t x) '' T) :=
    hT.image _ (continuous_orbit ϕ x).continuousOn
  rcases hc.subset_or_subset hU hV hUV (by rintro _ ⟨t, ht, rfl⟩; exact hsub t ht) with h | h
  · exact fun t ht => h ⟨t, ht, rfl⟩
  · exact absurd (h ⟨t₀, ht₀, rfl⟩) (disjoint_left.1 hUV hU₀)

theorem Inv_union_of_disjoint {C C' U U' : Set α} (hU : IsOpen U) (hU' : IsOpen U')
    (hUU : Disjoint U U') (hC : C ⊆ U) (hC' : C' ⊆ U') : Inv ϕ (C ∪ C') = Inv ϕ C ∪ Inv ϕ C' := by
  refine subset_antisymm (fun x hx => ?_)
    (union_subset (Inv_mono subset_union_left) (Inv_mono subset_union_right))
  have hsub : ∀ t ∈ (univ : Set ℝ), ϕ t x ∈ U ∪ U' := fun t _ =>
    (hx t).imp (fun h => hC h) (fun h => hC' h)
  have h0 := hx 0
  rw [ϕ.map_zero_apply] at h0
  rcases h0 with h0 | h0
  · have hs := orbit_stays hU hU' hUU isPreconnected_univ hsub (mem_univ 0)
      (by rw [ϕ.map_zero_apply]; exact hC h0)
    exact Or.inl fun t => (hx t).resolve_right fun h => disjoint_left.1 hUU (hs t trivial) (hC' h)
  · have hs := orbit_stays hU' hU hUU.symm isPreconnected_univ
      (fun t ht => (hsub t ht).symm) (mem_univ 0) (by rw [ϕ.map_zero_apply]; exact hC' h0)
    exact Or.inr fun t => (hx t).resolve_left fun h => disjoint_left.1 hUU (hC h) (hs t trivial)

section Union

variable [T2Space α] {S N L S' N' L' U U' : Set α} (h : IsIndexPair ϕ S N L)
  (h' : IsIndexPair ϕ S' N' L') (hU : IsOpen U) (hU' : IsOpen U') (hUU : Disjoint U U')
  (hNU : N ⊆ U) (hNU' : N' ⊆ U')

include h h' hU hU' hUU hNU hNU'

omit [T2Space α] hU hU' in
theorem union_sdiff_union : (N ∪ N') \ (L ∪ L') = (N \ L) ∪ (N' \ L') := by
  ext x
  constructor
  · rintro ⟨hx | hx, hxL⟩
    · exact Or.inl ⟨hx, fun h1 => hxL (Or.inl h1)⟩
    · exact Or.inr ⟨hx, fun h1 => hxL (Or.inr h1)⟩
  · rintro (⟨hx, hxL⟩ | ⟨hx, hxL⟩)
    · refine ⟨Or.inl hx, ?_⟩
      rintro (h1 | h1)
      · exact hxL h1
      · exact disjoint_left.1 hUU (hNU hx) (hNU' (h'.subset h1))
    · refine ⟨Or.inr hx, ?_⟩
      rintro (h1 | h1)
      · exact disjoint_left.1 hUU (hNU (h.subset h1)) (hNU' hx)
      · exact hxL h1

/-- The union of index pairs with disjoint supports is an index pair for the union. -/
theorem IsIndexPair.union : IsIndexPair ϕ (S ∪ S') (N ∪ N') (L ∪ L') := by
  have hd := union_sdiff_union h h' hUU hNU hNU'
  have hCN : closure (N \ L) ⊆ N := closure_minimal sdiff_subset h.isCompact_N.isClosed
  have hCN' : closure (N' \ L') ⊆ N' := closure_minimal sdiff_subset h'.isCompact_N.isClosed
  have hinv : Inv ϕ (closure ((N ∪ N') \ (L ∪ L'))) = S ∪ S' := by
    rw [hd, closure_union, Inv_union_of_disjoint hU hU' hUU (hCN.trans hNU) (hCN'.trans hNU'),
      h.inv_eq, h'.inv_eq]
  have hcN : IsCompact (N ∪ N') := h.isCompact_N.union h'.isCompact_N
  have hS : S ⊆ interior (closure (N \ L)) := by rw [← h.inv_eq]; exact h.isolating.2
  have hS' : S' ⊆ interior (closure (N' \ L')) := by rw [← h'.inv_eq]; exact h'.isolating.2
  exact
    { isCompact_N := hcN
      isCompact_L := h.isCompact_L.union h'.isCompact_L
      subset := union_subset_union h.subset h'.subset
      isolating := ⟨hcN.of_isClosed_subset isClosed_closure
          (closure_minimal sdiff_subset hcN.isClosed), by
        rw [hinv, hd, closure_union]
        exact union_subset (hS.trans (interior_mono subset_union_left))
          (hS'.trans (interior_mono subset_union_right))⟩
      inv_eq := hinv
      nhds := by
        rw [hd]
        exact union_subset (h.nhds.trans (interior_mono subset_union_left))
          (h'.nhds.trans (interior_mono subset_union_right))
      posInv := by
        intro x hx t ht hseg
        have hsub : ∀ s ∈ Icc 0 t, ϕ s x ∈ U ∪ U' := fun s hs =>
          (hseg s hs).imp (fun h1 => hNU h1) (fun h1 => hNU' h1)
        rcases hx with hx | hx
        · have hs := orbit_stays hU hU' hUU isPreconnected_Icc hsub ⟨le_rfl, ht⟩
            (by rw [ϕ.map_zero_apply]; exact hNU (h.subset hx))
          exact Or.inl (h.posInv x hx t ht fun s hs' => (hseg s hs').resolve_right
            fun h1 => disjoint_left.1 hUU (hs s hs') (hNU' h1))
        · have hs := orbit_stays hU' hU hUU.symm isPreconnected_Icc
            (fun s hs' => (hsub s hs').symm) ⟨le_rfl, ht⟩
            (by rw [ϕ.map_zero_apply]; exact hNU' (h'.subset hx))
          exact Or.inr (h'.posInv x hx t ht fun s hs' => (hseg s hs').resolve_left
            fun h1 => disjoint_left.1 hUU (hNU h1) (hs s hs'))
      exit := by
        intro x hx t ht hout
        rcases hx with hx | hx
        · obtain ⟨s, hs, hseg, hL⟩ := h.exit x hx t ht fun h1 => hout (Or.inl h1)
          exact ⟨s, hs, fun r hr => Or.inl (hseg r hr), Or.inl hL⟩
        · obtain ⟨s, hs, hseg, hL⟩ := h'.exit x hx t ht fun h1 => hout (Or.inr h1)
          exact ⟨s, hs, fun r hr => Or.inr (hseg r hr), Or.inr hL⟩ }

theorem ofWedge_toWedge :
    (ofWedge N L N' L').comp (toWedge h.isCompact_N.isClosed h.subset h'.subset hU hUU hNU hNU') = ContinuousMap.id _ := by
  ext q
  induction q using Quotient.inductionOn
  rename_i q
  rcases q with z | ⟨⟩
  · show ofWedge N L N' L' (if (z : α) ∈ N then Wedge.inl _ _ (IndexSpace.Q N L z)
      else Wedge.inr _ _ (IndexSpace.Q N' L' z)) = _
    by_cases hz : (z : α) ∈ N
    · rw [if_pos hz, IndexSpace.Q_of_mem hz]
      rfl
    · rw [if_neg hz, IndexSpace.Q_of_mem (z.2.resolve_left hz)]
      rfl
  · rfl

theorem toWedge_ofWedge :
    (toWedge h.isCompact_N.isClosed h.subset h'.subset hU hUU hNU hNU').comp (ofWedge N L N' L') = ContinuousMap.id _ := by
  refine Wedge.hom_ext (fun p => ?_) (fun p => ?_)
  · induction p using Quotient.inductionOn
    rename_i p
    rcases p with x | ⟨⟩
    · show (if (x : α) ∈ N then Wedge.inl _ _ (IndexSpace.Q N L x)
        else Wedge.inr _ _ (IndexSpace.Q N' L' x)) = _
      rw [if_pos x.2, IndexSpace.Q_of_mem x.2]
      rfl
    · rfl
  · induction p using Quotient.inductionOn
    rename_i p
    rcases p with x | ⟨⟩
    · show (if (x : α) ∈ N then Wedge.inl _ _ (IndexSpace.Q N L x)
        else Wedge.inr _ _ (IndexSpace.Q N' L' x)) = _
      have hx : (x : α) ∉ N := fun h1 => disjoint_left.1 hUU (hNU h1) (hNU' x.2)
      rw [if_neg hx, IndexSpace.Q_of_mem x.2]
      rfl
    · exact (Wedge.inr_pt _ _).symm

/-- `(N ∪ N')/(L ∪ L')` is `N/L ∨ N'/L'`. -/
noncomputable def unionEquiv :
    PointedHomotopyEquiv (IndexSpace (N ∪ N') (L ∪ L'))
      (Wedge (IndexSpace N L) (IndexSpace N' L') (IndexSpace.pt N L) (IndexSpace.pt N' L'))
      (IndexSpace.pt _ _) (Wedge.pt _ _) where
  toFun := toWedge h.isCompact_N.isClosed h.subset h'.subset hU hUU hNU hNU'
  invFun := ofWedge N L N' L'
  map_pt := rfl
  inv_pt := rfl
  left := by rw [ofWedge_toWedge h h' hU hU' hUU hNU hNU']; exact HomotopicRel.refl _
  right := by rw [toWedge_ofWedge h h' hU hU' hUU hNU hNU']; exact HomotopicRel.refl _

end Union

/-- Additivity: the index of a disjoint union is the wedge of the indices. -/
theorem hasIndex_union_of_t2 [T2Space α] {A R : Set α} (hA : IsIsolatedInvariantSet ϕ A)
    (hR : IsIsolatedInvariantSet ϕ R) (hAR : Disjoint A R) {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {x₀ : X} {y₀ : Y} (hX : HasIndex ϕ A X x₀) (hY : HasIndex ϕ R Y y₀) :
    HasIndex ϕ (A ∪ R) (Wedge X Y x₀ y₀) (Wedge.pt x₀ y₀) := by
  obtain ⟨UA, UR, hUA, hUR, hAU, hRU, hdisj⟩ :=
    SeparatedNhds.of_isCompact_isCompact hA.isCompact hR.isCompact hAR
  obtain ⟨KA, hKA, hKAi, hKAU⟩ := exists_isolatingNbhd_subset hA hUA hAU
  obtain ⟨KR, hKR, hKRi, hKRU⟩ := exists_isolatingNbhd_subset hR hUR hRU
  obtain ⟨N, L, hP, hNK⟩ := exists_indexPair hKA
  obtain ⟨N', L', hP', hNK'⟩ := exists_indexPair hKR
  rw [hKAi] at hP
  rw [hKRi] at hP'
  obtain ⟨eA⟩ := hX.of_indexPair hP
  obtain ⟨eR⟩ := hY.of_indexPair hP'
  exact ⟨N ∪ N', L ∪ L', hP.union hP' hUA hUR hdisj (hNK.trans hKAU) (hNK'.trans hKRU),
    ⟨(unionEquiv hP hP' hUA hUR hdisj (hNK.trans hKAU) (hNK'.trans hKRU)).trans
      (eA.wedge eR)⟩⟩

end ConleyCheck.Conley
