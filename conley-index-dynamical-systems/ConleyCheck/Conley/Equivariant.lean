import ConleyCheck.Conley.Suspension

/-!
# Equivariant index pairs, uniqueness and continuation

Let `r` be a continuous involution commuting with a flow. This file shows that the constructions
of the index theory can be made `r`-equivariant:

* `exists_indexPair_equivariant`: an `r`-invariant isolating neighborhood contains an index pair
  `(N₁, L)` with `N₁` and `L` both `r`-invariant;
* `indexPair_unique_equivariant`: the comparison equivalence between two `r`-invariant index pairs
  commutes with the maps induced by `r` on the index spaces;
* `continuation_equivariant`: the same for the continuation equivalence of a family of flows;
* `skew_boundary_setup_equivariant`: the equivalence of `skew_boundary_setup` commutes with
  `R = id × ρ` for an involution `ρ` of the base that preserves the skew product.

These are the inputs for computing how `R` acts on the homology of a boundary index
(`prop:boundary`, `thm:equivariant`(ii)).
-/

namespace ConleyCheck.Conley

open Set Topology unitInterval

open scoped Classical

/-! ### Maps induced on index spaces -/

section MapC

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- The map `N/L → N'/L'` induced by `r` with `r(N) ⊆ N'` and `r(L) ⊆ L'`. -/
noncomputable def IndexSpace.mapC (r : C(α, β)) {N L : Set α} {N' L' : Set β}
    (hN : MapsTo r N N') (hL : MapsTo r L L') : C(IndexSpace N L, IndexSpace N' L') :=
  descend (IndexSpace.pt N' L')
    ((IndexSpace.proj N' L').comp ⟨fun y => ⟨r y, hN y.2⟩,
      (r.continuous.comp continuous_subtype_val).subtype_mk _⟩)
    fun _ hy => IndexSpace.proj_eq_pt (hL hy)

variable {r : C(α, β)} {N L : Set α} {N' L' : Set β} (hN : MapsTo r N N') (hL : MapsTo r L L')

theorem IndexSpace.mapC_proj (y : N) :
    IndexSpace.mapC r hN hL (IndexSpace.proj N L y) = IndexSpace.proj N' L' ⟨r y, hN y.2⟩ :=
  rfl

theorem IndexSpace.mapC_pt :
    IndexSpace.mapC r hN hL (IndexSpace.pt N L) = IndexSpace.pt N' L' := rfl

theorem IndexSpace.mapC_Q (hN' : ∀ z, r z ∈ N' → z ∈ N) (z : α) :
    IndexSpace.mapC r hN hL (IndexSpace.Q N L z) = IndexSpace.Q N' L' (r z) := by
  by_cases hz : z ∈ N
  · rw [IndexSpace.Q_of_mem hz, IndexSpace.Q_of_mem (hN hz)]
    rfl
  · rw [IndexSpace.Q, dite_eq_right hz, IndexSpace.Q, dite_eq_right fun h => hz (hN' z h)]
    rfl

end MapC

/-! ### Invariant sets -/

section RInv

variable {α β : Type*}

/-- `A` is invariant under `r`. -/
def RInv (r : α → α) (A : Set α) : Prop := ∀ x, r x ∈ A ↔ x ∈ A

variable {r : α → α} {A B : Set α}

theorem RInv.mem_iff (h : RInv r A) (x : α) : r x ∈ A ↔ x ∈ A := h x

theorem RInv.mapsTo (h : RInv r A) : MapsTo r A A := fun x hx => (h x).2 hx

theorem RInv.inter (hA : RInv r A) (hB : RInv r B) : RInv r (A ∩ B) :=
  fun x => and_congr (hA x) (hB x)

theorem RInv.union (hA : RInv r A) (hB : RInv r B) : RInv r (A ∪ B) :=
  fun x => or_congr (hA x) (hB x)

theorem RInv.sdiff (hA : RInv r A) (hB : RInv r B) : RInv r (A \ B) :=
  fun x => and_congr (hA x) (not_congr (hB x))

theorem RInv.empty : RInv r (∅ : Set α) := fun _ => Iff.rfl

theorem RInv.univ : RInv r (univ : Set α) := fun _ => Iff.rfl

theorem RInv.preimage {f : β → α} {s : β → β} (hf : ∀ y, f (s y) = r (f y)) (hA : RInv r A) :
    RInv s (f ⁻¹' A) := fun y => by
  simp only [mem_preimage, hf, hA.mem_iff]

theorem RInv.closure [TopologicalSpace α] (hr : Continuous r) (hrr : ∀ x, r (r x) = x)
    (hA : RInv r A) : RInv r (_root_.closure A) := by
  have key : ∀ x, x ∈ _root_.closure A → r x ∈ _root_.closure A := fun x hx => by
    have h1 : _root_.closure (r ⁻¹' A) ⊆ r ⁻¹' _root_.closure A := hr.closure_preimage_subset A
    rw [show r ⁻¹' A = A from Set.ext hA] at h1
    exact h1 hx
  intro x
  refine ⟨fun h => ?_, key x⟩
  have := key _ h
  rwa [hrr] at this

theorem RInv.interior [TopologicalSpace α] (hr : Continuous r) (hrr : ∀ x, r (r x) = x)
    (hA : RInv r A) : RInv r (_root_.interior A) := by
  have key : ∀ x, r x ∈ _root_.interior A → x ∈ _root_.interior A := fun x hx =>
    interior_maximal (fun y hy => (hA y).1 (interior_subset hy))
      (isOpen_interior.preimage hr) hx
  intro x
  exact ⟨key x, fun h => key _ (by rwa [hrr])⟩

end RInv

/-- `id × ρ` on a product. -/
def rprod {X B : Type*} [TopologicalSpace X] [TopologicalSpace B] (ρ : C(B, B)) :
    C(X × B, X × B) :=
  (ContinuousMap.id X).prodMap ρ

@[simp] theorem rprod_apply {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]
    (ρ : C(B, B)) (p : X × B) : rprod ρ p = (p.1, ρ p.2) := rfl

theorem RInv.prod {X B : Type*} [TopologicalSpace X] [TopologicalSpace B] {ρ : C(B, B)}
    {C : Set B} (hC : RInv ρ C) (A : Set X) : RInv (rprod ρ) (A ×ˢ C) :=
  fun p => and_congr Iff.rfl (hC p.2)

/-! ### Equivariant pointed homotopy equivalences -/

section Commutes

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x₀ : X} {y₀ : Y} {z₀ : Z}

/-- `e` intertwines `f` and `g`. -/
def PointedHomotopyEquiv.Commutes (e : PointedHomotopyEquiv X Y x₀ y₀) (f : X → X)
    (g : Y → Y) : Prop :=
  ∀ x, e.toFun (f x) = g (e.toFun x)

theorem PointedHomotopyEquiv.Commutes.refl (f : X → X) :
    (PointedHomotopyEquiv.refl x₀).Commutes f f := fun _ => rfl

theorem PointedHomotopyEquiv.Commutes.trans {e : PointedHomotopyEquiv X Y x₀ y₀}
    {e' : PointedHomotopyEquiv Y Z y₀ z₀} {f : X → X} {g : Y → Y} {h : Z → Z}
    (he : e.Commutes f g) (he' : e'.Commutes g h) : (e.trans e').Commutes f h := fun x => by
  show e'.toFun (e.toFun (f x)) = h (e'.toFun (e.toFun x))
  rw [he, he']

end Commutes

/-! ### Existence and uniqueness -/

section Pairs

variable {α : Type*} [TopologicalSpace α] {ϕ : Flow ℝ α}

/-- An `r`-invariant isolating neighborhood contains an `r`-invariant index pair. -/
theorem exists_indexPair_equivariant [T2Space α] {N : Set α} (hN : IsIsolatingNbhd ϕ N)
    (r : C(α, α)) (hr : ∀ t x, ϕ t (r x) = r (ϕ t x)) (hrr : ∀ x, r (r x) = x)
    (hNr : RInv r N) :
    ∃ N₁ L, IsIndexPair ϕ (Inv ϕ N) N₁ L ∧ N₁ ⊆ N ∧ RInv r N₁ ∧ RInv r L := by
  obtain ⟨n, hn⟩ := exists_nat_mem_interior hN
  have hT : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hint := hNr.interior r.continuous hrr
  have h1 : RInv r (pairN₁ ϕ N n) := fun x => by
    simp only [pairN₁, mem_setOf_eq, hr, hNr.mem_iff]
  refine ⟨_, _, isIndexPair_pairN hN hT hn, pairN₁_subset hT, h1, h1.inter fun x => ?_⟩
  simp only [mem_setOf_eq, hr, hint.mem_iff]

theorem compMap_mapC [T2Space α] {S N L N' L' : Set α} (h : IsIndexPair ϕ S N L)
    (h' : IsIndexPair ϕ S N' L') (T : ℝ) (hT : 0 ≤ T) (hT1 : TimeLemma (ϕ := ϕ) N L N' L' T)
    (hT2 : TimeLemma (ϕ := ϕ) N' L' N L T) {r : C(α, α)} (hr : ∀ t x, ϕ t (r x) = r (ϕ t x))
    (hN : RInv r N) (hL : RInv r L) (hN' : RInv r N') (hL' : RInv r L')
    (x : IndexSpace N L) :
    compMap h h' T hT hT1 hT2 (IndexSpace.mapC r hN.mapsTo hL.mapsTo x) =
      IndexSpace.mapC r hN'.mapsTo hL'.mapsTo (compMap h h' T hT hT1 hT2 x) := by
  have hA : RInv r (compA (ϕ := ϕ) N L N' L' T) := fun y => by
    simp only [compA, mem_setOf_eq, hr, (hN.sdiff hL).mem_iff, (hN'.sdiff hL').mem_iff]
  induction x using Quotient.inductionOn with
  | h a =>
    rcases a with y | u
    · change (if r y ∈ compA (ϕ := ϕ) N L N' L' T then IndexSpace.Q N' L' (ϕ (3 * T) (r y))
          else IndexSpace.pt N' L') = IndexSpace.mapC r hN'.mapsTo hL'.mapsTo
          (if (y : α) ∈ compA (ϕ := ϕ) N L N' L' T then IndexSpace.Q N' L' (ϕ (3 * T) (y : α))
            else IndexSpace.pt N' L')
      by_cases hy : (y : α) ∈ compA (ϕ := ϕ) N L N' L' T
      · rw [if_pos ((hA _).2 hy), if_pos hy,
          IndexSpace.mapC_Q _ _ (fun z hz => (hN' z).1 hz), hr]
      · rw [if_neg (mt (hA _).1 hy), if_neg hy]
        rfl
    · rfl

/-- Independence of the index pair, equivariantly: for `r`-invariant index pairs the comparison
equivalence commutes with the maps induced by `r`. -/
theorem indexPair_unique_equivariant [T2Space α] {S N L N' L' : Set α}
    (h : IsIndexPair ϕ S N L) (h' : IsIndexPair ϕ S N' L') {r : C(α, α)}
    (hr : ∀ t x, ϕ t (r x) = r (ϕ t x)) (hN : RInv r N) (hL : RInv r L) (hN' : RInv r N')
    (hL' : RInv r L') :
    ∃ e : PointedHomotopyEquiv (IndexSpace N L) (IndexSpace N' L')
        (IndexSpace.pt N L) (IndexSpace.pt N' L'),
      e.Commutes (IndexSpace.mapC r hN.mapsTo hL.mapsTo)
        (IndexSpace.mapC r hN'.mapsTo hL'.mapsTo) := by
  have hK : Inv ϕ (closure (N \ L)) ⊆ interior (N' \ L') := by rw [h.inv_eq]; exact h'.nhds
  have hK' : Inv ϕ (closure (N' \ L')) ⊆ interior (N \ L) := by rw [h'.inv_eq]; exact h.nhds
  obtain ⟨n₁, hn₁⟩ := exists_nat_mem_of_Inv_subset h.isolating.1 isOpen_interior hK
  obtain ⟨n₂, hn₂⟩ := exists_nat_mem_of_Inv_subset h'.isolating.1 isOpen_interior hK'
  set T : ℝ := max n₁ n₂
  have hT : 0 ≤ T := le_max_of_le_left (Nat.cast_nonneg n₁)
  have hT1 : TimeLemma (ϕ := ϕ) N L N' L' T := fun x hx =>
    hn₁ x fun s hs => hx s ⟨by linarith [hs.1, le_max_left (n₁ : ℝ) n₂],
      by linarith [hs.2, le_max_left (n₁ : ℝ) n₂]⟩
  have hT2 : TimeLemma (ϕ := ϕ) N' L' N L T := fun x hx =>
    hn₂ x fun s hs => hx s ⟨by linarith [hs.1, le_max_right (n₁ : ℝ) n₂],
      by linarith [hs.2, le_max_right (n₁ : ℝ) n₂]⟩
  refine ⟨{ toFun := compMap h h' T hT hT1 hT2
            invFun := compMap h' h T hT hT2 hT1
            map_pt := rfl
            inv_pt := rfl
            left := ?_
            right := ?_ }, compMap_mapC h h' T hT hT1 hT2 hr hN hL hN' hL'⟩
  · rw [compMap_comp h h' T hT hT1 hT2]
    exact pushMap_homotopicRel h _ _
  · rw [compMap_comp h' h T hT hT2 hT1]
    exact pushMap_homotopicRel h' _ _

/-- The equivalence `(e⁻¹ N)/(e⁻¹ L) ≃ N/L` commutes with maps intertwined by `e`. -/
theorem embeddingEquiv_commutes {β : Type*} [TopologicalSpace β] {e : β → α}
    (he : IsEmbedding e) {N L : Set α} (hN : N ⊆ range e) {r : C(α, α)} {s : C(β, β)}
    (hes : ∀ y, e (s y) = r (e y)) (hNr : RInv r N) (hLr : RInv r L) :
    (IndexSpace.embeddingEquiv he hN).Commutes
      (IndexSpace.mapC s (hNr.preimage hes).mapsTo (hLr.preimage hes).mapsTo)
      (IndexSpace.mapC r hNr.mapsTo hLr.mapsTo) := fun x => by
  induction x using Quotient.inductionOn with
  | h a =>
    rcases a with y | u
    · exact congrArg (IndexSpace.proj N L) (Subtype.ext (hes y))
    · rfl

end Pairs

/-! ### Equivariant continuation -/

namespace FlowFamily

variable {α : Type*} [TopologicalSpace α] {Ψ : FlowFamily α}

/-- `r` acting on the second factor of `[0, 1] × α`. -/
def liftR (r : C(α, α)) : C(I × α, I × α) := (ContinuousMap.id I).prodMap r

theorem liftR_apply (r : C(α, α)) (p : I × α) : liftR r p = (p.1, r p.2) := rfl

variable {r : C(α, α)} (hr : ∀ l t x, Ψ.slice l t (r x) = r (Ψ.slice l t x))

include hr in
theorem flow_liftR (t : ℝ) (p : I × α) : Ψ.flow t (liftR r p) = liftR r (Ψ.flow t p) := by
  rcases p with ⟨l, x⟩
  rw [liftR_apply, Ψ.flow_eq, Ψ.flow_eq, hr]
  rfl

variable {Nt Lt : Set (I × α)} {T η : ℝ}

theorem RInv.fiber {A : Set (I × α)} (hA : RInv (liftR r) A) (l : I) :
    RInv r (Prod.mk l ⁻¹' A) :=
  hA.preimage fun _ => rfl

theorem RInv.strip {A : Set (I × α)} (hA : RInv (liftR r) A) (c : I) :
    RInv (liftR r) (A ∩ strip η c) :=
  hA.inter fun _ => Iff.rfl

theorem fibIncl_mapC (hNt : RInv (liftR r) Nt) (hLt : RInv (liftR r) Lt) (ν c : I)
    (hν : |(ν : ℝ) - c| < η) (x) :
    fibIncl Nt Lt ν c hν (IndexSpace.mapC r (RInv.fiber hNt ν).mapsTo
      (RInv.fiber hLt ν).mapsTo x) =
      IndexSpace.mapC (liftR r) (RInv.strip hNt c).mapsTo (RInv.strip hLt c).mapsTo
        (fibIncl Nt Lt ν c hν x) := by
  induction x using Quotient.inductionOn with
  | h a => rcases a with y | u <;> rfl

include hr in
theorem jumpGood_liftR (hNt : RInv (liftR r) Nt) (hLt : RInv (liftR r) Lt) (p : I × α)
    (ν : I) : JumpGood Ψ Nt Lt T (liftR r p) ν ↔ JumpGood Ψ Nt Lt T p ν := by
  have hj : jumpPt Ψ T (liftR r p) ν = liftR r (jumpPt Ψ T p ν) := by
    show (ν, (Ψ.flow T (liftR r p)).2) = (ν, r (Ψ.flow T p).2)
    rw [flow_liftR hr]
    rfl
  unfold JumpGood
  rw [hj]
  simp only [flow_liftR hr, (hNt.sdiff hLt).mem_iff]

variable [T2Space α] {S : Set (I × α)} (h : IsIndexPair Ψ.flow S Nt Lt) (hT : 0 ≤ T)
  (hH : HybridTime Ψ Nt Lt T η)

include hr in
theorem jumpIn_mapC (hNt : RInv (liftR r) Nt) (hLt : RInv (liftR r) Lt) (c : I) (x) :
    jumpIn h hT hH c (IndexSpace.mapC (liftR r) (RInv.strip hNt c).mapsTo
      (RInv.strip hLt c).mapsTo x) =
      IndexSpace.mapC r (RInv.fiber hNt c).mapsTo (RInv.fiber hLt c).mapsTo
        (jumpIn h hT hH c x) := by
  induction x using Quotient.inductionOn with
  | h a =>
    rcases a with z | u
    · change (if JumpGood Ψ Nt Lt T (liftR r z.1) c then
          IndexSpace.Q _ _ (Ψ.flow T (jumpPt Ψ T (liftR r z.1) c)).2 else IndexSpace.pt _ _) =
        IndexSpace.mapC r (RInv.fiber hNt c).mapsTo (RInv.fiber hLt c).mapsTo
          (if JumpGood Ψ Nt Lt T z.1 c then
            IndexSpace.Q _ _ (Ψ.flow T (jumpPt Ψ T z.1 c)).2 else IndexSpace.pt _ _)
      by_cases hz : JumpGood Ψ Nt Lt T z.1 c
      · have hj : (Ψ.flow T (jumpPt Ψ T (liftR r z.1) c)).2 =
            r (Ψ.flow T (jumpPt Ψ T z.1 c)).2 := by
          have : jumpPt Ψ T (liftR r z.1) c = liftR r (jumpPt Ψ T z.1 c) := by
            show (c, (Ψ.flow T (liftR r z.1)).2) = (c, r (Ψ.flow T z.1).2)
            rw [flow_liftR hr]
            rfl
          rw [this, flow_liftR hr]
          rfl
        rw [if_pos ((jumpGood_liftR hr hNt hLt _ _).2 hz), if_pos hz, hj,
          IndexSpace.mapC_Q (N := Prod.mk c ⁻¹' Nt) (L := Prod.mk c ⁻¹' Lt) _ _
            (fun w hw => (hNt (c, w)).1 hw)]
      · rw [if_neg (mt (jumpGood_liftR hr hNt hLt _ _).1 hz), if_neg hz]
        rfl
    · rfl

/-- The fibers at `a` and `b` have equivariantly equivalent quotients. -/
def EquivFib (Nt Lt : Set (I × α)) (r : C(α, α)) (hNt : RInv (liftR r) Nt)
    (hLt : RInv (liftR r) Lt) (a b : I) : Prop :=
  ∃ e : PointedHomotopyEquiv (IndexSpace (Prod.mk a ⁻¹' Nt) (Prod.mk a ⁻¹' Lt))
      (IndexSpace (Prod.mk b ⁻¹' Nt) (Prod.mk b ⁻¹' Lt)) (IndexSpace.pt _ _)
      (IndexSpace.pt _ _),
    e.Commutes (IndexSpace.mapC r (RInv.fiber hNt a).mapsTo (RInv.fiber hLt a).mapsTo)
      (IndexSpace.mapC r (RInv.fiber hNt b).mapsTo (RInv.fiber hLt b).mapsTo)

include hr h hT hH in
theorem fiber_equiv_of_near_equivariant (hNt : RInv (liftR r) Nt) (hLt : RInv (liftR r) Lt)
    (l l' : I) (hll : |(l : ℝ) - l'| < η) : EquivFib Nt Lt r hNt hLt l l' := by
  have hll' : |(l' : ℝ) - l| < η := by rwa [abs_sub_comm]
  refine ⟨{ toFun := (jumpIn h hT hH l').comp (fibIncl Nt Lt l l' hll)
            invFun := (jumpIn h hT hH l).comp (fibIncl Nt Lt l' l hll')
            map_pt := rfl
            inv_pt := rfl
            left := back_and_forth h hT hH l l' hll hll'
            right := back_and_forth h hT hH l' l hll' hll }, fun x => ?_⟩
  show jumpIn h hT hH l' (fibIncl Nt Lt l l' hll (IndexSpace.mapC r _ _ x)) =
    IndexSpace.mapC r _ _ (jumpIn h hT hH l' (fibIncl Nt Lt l l' hll x))
  rw [fibIncl_mapC hNt hLt, jumpIn_mapC hr h hT hH hNt hLt]

include hr h hT hH in
theorem fiber_equiv_equivariant (hNt : RInv (liftR r) Nt) (hLt : RInv (liftR r) Lt)
    (hη : 0 < η) : EquivFib Nt Lt r hNt hLt 0 1 := by
  set p : ℕ → I := fun k => Set.Icc.addNSMul (zero_le_one : (0 : ℝ) ≤ 1) (η / 2) k
  have hstep : ∀ k, |((p k : I) : ℝ) - p (k + 1)| < η := by
    intro k
    refine (Set.abs_projIcc_sub_projIcc _).trans_lt ?_
    rw [zero_add, zero_add, succ_nsmul, sub_add_cancel_left, abs_neg,
      abs_of_pos (half_pos hη)]
    exact half_lt_self hη
  have hchain : ∀ k, EquivFib Nt Lt r hNt hLt (p 0) (p k) := by
    intro k
    induction k with
    | zero => exact ⟨PointedHomotopyEquiv.refl _, PointedHomotopyEquiv.Commutes.refl _⟩
    | succ k ih =>
      obtain ⟨e, he⟩ := ih
      obtain ⟨e', he'⟩ := fiber_equiv_of_near_equivariant hr h hT hH hNt hLt _ _ (hstep k)
      exact ⟨e.trans e', he.trans he'⟩
  obtain ⟨m, hm⟩ := Set.Icc.addNSMul_eq_right (zero_le_one : (0 : ℝ) ≤ 1) (half_pos hη)
  have h0 : p 0 = 0 := Subtype.ext (Set.Icc.addNSMul_zero _)
  have h1 : p m = 1 := Subtype.ext (hm m le_rfl)
  have := hchain m
  rw [h0, h1] at this
  exact this

end FlowFamily

open FlowFamily in
/-- Equivariant continuation: if `r` commutes with every flow of the family and all the sets are
`r`-invariant, the continuation equivalence commutes with the maps induced by `r`. -/
theorem continuation_equivariant {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.MetrizableSpace α] (Ψ : FlowFamily α) {N : Set α} (hN : IsCompact N)
    (hiso : ∀ l, Inv (Ψ.slice l) N ⊆ interior N) {N₀ L₀ N₁ L₁ : Set α}
    (h₀ : IsIndexPair (Ψ.slice 0) (Inv (Ψ.slice 0) N) N₀ L₀)
    (h₁ : IsIndexPair (Ψ.slice 1) (Inv (Ψ.slice 1) N) N₁ L₁) {r : C(α, α)}
    (hrr : ∀ x, r (r x) = x) (hr : ∀ l t x, Ψ.slice l t (r x) = r (Ψ.slice l t x))
    (hNr : RInv r N) (hN₀ : RInv r N₀) (hL₀ : RInv r L₀) (hN₁ : RInv r N₁)
    (hL₁ : RInv r L₁) :
    ∃ e : PointedHomotopyEquiv (IndexSpace N₀ L₀) (IndexSpace N₁ L₁)
        (IndexSpace.pt N₀ L₀) (IndexSpace.pt N₁ L₁),
      e.Commutes (IndexSpace.mapC r hN₀.mapsTo hL₀.mapsTo)
        (IndexSpace.mapC r hN₁.mapsTo hL₁.mapsTo) := by
  have hiso' : IsIsolatingNbhd Ψ.flow (univ ×ˢ N) := by
    refine ⟨isCompact_univ.prod hN, fun p hp => ?_⟩
    rw [interior_prod_eq, interior_univ]
    exact ⟨mem_univ _, hiso p.1 fun t => (hp t).2⟩
  obtain ⟨Nt, Lt, hP, -, hNt, hLt⟩ := exists_indexPair_equivariant hiso' (liftR r)
    (flow_liftR hr) (fun p => by rw [liftR_apply, liftR_apply, hrr])
    (fun p => and_congr Iff.rfl (hNr p.2))
  have hS : ∀ l, Prod.mk l ⁻¹' Inv Ψ.flow (univ ×ˢ N) = Inv (Ψ.slice l) N := fun l => by
    rw [← Ψ.Inv_fiber]
    congr 1
    ext x
    simp
  have hfib : ∀ l, IsIndexPair (Ψ.slice l) (Inv (Ψ.slice l) N) (Prod.mk l ⁻¹' Nt)
      (Prod.mk l ⁻¹' Lt) := fun l => hS l ▸ FlowFamily.isIndexPair_fiber hP l
  obtain ⟨T, hT, η, hη, hH⟩ := FlowFamily.exists_hybridTime Ψ hP
  obtain ⟨e₀, he₀⟩ := indexPair_unique_equivariant h₀ (hfib 0) (hr 0) hN₀ hL₀
    (RInv.fiber hNt 0) (RInv.fiber hLt 0)
  obtain ⟨e, he⟩ := fiber_equiv_equivariant hr hP hT hH hNt hLt hη
  obtain ⟨e₁, he₁⟩ := indexPair_unique_equivariant (hfib 1) h₁ (hr 1)
    (RInv.fiber hNt 1) (RInv.fiber hLt 1) hN₁ hL₁
  exact ⟨(e₀.trans e).trans e₁, (he₀.trans he).trans he₁⟩

/-! ### Equivariant skew continuation -/

section SkewEquivariant

variable {X B : Type*} [TopologicalSpace X] [TopologicalSpace B] {Φ : Flow ℝ (X × B)}
  {θ : Flow ℝ B} (hΦ : IsSkew Φ θ) {b₀ : B} (c : SkewContraction θ b₀) {ρ : C(B, B)}
  (hρθ : ∀ t b, θ t (ρ b) = ρ (θ t b)) (hΦρ : ∀ t x b, (Φ t (x, ρ b)).1 = (Φ t (x, b)).1)
  (hρc : ∀ l b, c.g (l, ρ b) = ρ (c.g (l, b)))

include hΦ hρθ hΦρ in
theorem IsSkew.flow_rprod (t : ℝ) (p : X × B) : Φ t (rprod ρ p) = rprod ρ (Φ t p) := by
  refine Prod.ext ?_ ?_
  · exact hΦρ t p.1 p.2
  · show (Φ t (p.1, ρ p.2)).2 = ρ (Φ t p).2
    rw [hΦ, hΦ]
    exact hρθ t p.2

include hρθ hΦρ hρc in
theorem SkewContraction.family_rprod (l : I) (t : ℝ) (p : X × B) :
    (c.family hΦ).slice l t (rprod ρ p) = rprod ρ ((c.family hΦ).slice l t p) := by
  show ((Φ t (p.1, c.g (l, ρ p.2))).1, θ t (ρ p.2)) =
    ((Φ t (p.1, c.g (l, p.2))).1, ρ (θ t p.2))
  rw [hρc, hΦρ, hρθ]

include hρθ hΦρ hρc in
/-- `skew_continuation`, equivariantly under `R = id × ρ`. -/
theorem skew_continuation_equivariant [TopologicalSpace.MetrizableSpace X]
    [TopologicalSpace.MetrizableSpace B] (hρρ : ∀ b, ρ (ρ b) = b) {NK : Set X}
    (hNK : IsIsolatingNbhd (fiberFlow hΦ b₀ c.fixed) NK) {C : Set B} (hCc : IsCompact C)
    (hC : Inv θ C = {b₀}) (hb₀ : b₀ ∈ interior C) (hCρ : RInv ρ C)
    {N₀ L₀ N₁ L₁ : Set (X × B)}
    (h₀ : IsIndexPair (prodFlow (fiberFlow hΦ b₀ c.fixed) θ)
      (Inv (fiberFlow hΦ b₀ c.fixed) NK ×ˢ {b₀}) N₀ L₀)
    (h₁ : IsIndexPair Φ (Inv (fiberFlow hΦ b₀ c.fixed) NK ×ˢ {b₀}) N₁ L₁)
    (hN₀ : RInv (rprod ρ) N₀) (hL₀ : RInv (rprod ρ) L₀) (hN₁ : RInv (rprod ρ) N₁)
    (hL₁ : RInv (rprod ρ) L₁) :
    ∃ e : PointedHomotopyEquiv (IndexSpace N₀ L₀) (IndexSpace N₁ L₁)
        (IndexSpace.pt _ _) (IndexSpace.pt _ _),
      e.Commutes (IndexSpace.mapC (rprod ρ) hN₀.mapsTo hL₀.mapsTo)
        (IndexSpace.mapC (rprod ρ) hN₁.mapsTo hL₁.mapsTo) := by
  have hInv := c.Inv_slice hΦ (A := NK) hC
  refine continuation_equivariant (c.family hΦ) (hNK.1.prod hCc) (fun l => ?_) ?_ ?_
    (fun p => by simp [hρρ]) (c.family_rprod hΦ hρθ hΦρ hρc) (hCρ.prod NK) hN₀ hL₀ hN₁ hL₁
  · rw [hInv l, interior_prod_eq]
    exact prod_mono hNK.2 (singleton_subset_iff.2 hb₀)
  · rw [hInv 0, c.slice_zero hΦ]
    exact h₀
  · rw [hInv 1, c.slice_one hΦ]
    exact h₁

end SkewEquivariant

/-- `ρ` restricted to an invariant set. -/
def restrictR {B : Type*} [TopologicalSpace B] (ρ : C(B, B)) {U : Set B} (hρU : RInv ρ U) :
    C(U, U) :=
  ⟨fun b => ⟨ρ b, (hρU b).2 b.2⟩, (ρ.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem RInv.val_preimage {B : Type*} [TopologicalSpace B] {ρ : C(B, B)} {U : Set B}
    (hρU : RInv ρ U) {A : Set B} (hA : RInv ρ A) :
    RInv (restrictR ρ hρU) (Subtype.val ⁻¹' A : Set U) :=
  hA.preimage fun _ => rfl

section BoundaryEquivariant

variable {X B : Type*} [TopologicalSpace X] [TopologicalSpace B] [T2Space X] [T2Space B]
  [TopologicalSpace.MetrizableSpace X] [TopologicalSpace.MetrizableSpace B]
  {Φ : Flow ℝ (X × B)} {θ : Flow ℝ B} (hΦ : IsSkew Φ θ) {U : Set B} (hU : IsInvariant θ U)
  (hUo : IsOpen U) {b₀ : B} (hb₀U : b₀ ∈ U)
  (c : SkewContraction (θ.restrict hU) ⟨b₀, hb₀U⟩)
  {ρ : C(B, B)} (hρρ : ∀ b, ρ (ρ b) = b) (hρθ : ∀ t b, θ t (ρ b) = ρ (θ t b))
  (hΦρ : ∀ t x b, (Φ t (x, ρ b)).1 = (Φ t (x, b)).1) (hρU : RInv ρ U)

include hUo hρρ hρθ hΦρ in
/-- `skew_boundary_setup`, equivariantly: for an involution `ρ` of the base preserving the skew
product, the contraction and the base pair, the index pair `(N, L)` can be taken invariant
under `R = id × ρ`, and the equivalence `(NK × Nb)/(LK × Nb ∪ NK × Lb) ≃ N/L` commutes with
the maps induced by `R`. -/
theorem skew_boundary_setup_equivariant {M : Set X}
    (hM : IsIsolatingNbhd (c.f₀ hΦ hU hb₀U) M)
    {Nb Lb : Set B} (hb : IsIndexPair θ {b₀} Nb Lb) (hNbU : Nb ⊆ U)
    (hρc : ∀ l b, c.g (l, restrictR ρ hρU b) = restrictR ρ hρU (c.g (l, b)))
    (hNb : RInv ρ Nb) (hLb : RInv ρ Lb) :
    ∃ N L, ∃ (hN : RInv (rprod ρ) N) (hL : RInv (rprod ρ) L),
      IsIndexPair Φ (Inv (c.f₀ hΦ hU hb₀U) M ×ˢ {b₀}) N L ∧
      ∀ NK LK, IsIndexPair (c.f₀ hΦ hU hb₀U) (Inv (c.f₀ hΦ hU hb₀U) M) NK LK →
        ∃ e : PointedHomotopyEquiv
          (IndexSpace (NK ×ˢ (Subtype.val ⁻¹' Nb : Set U))
            (LK ×ˢ (Subtype.val ⁻¹' Nb : Set U) ∪ NK ×ˢ (Subtype.val ⁻¹' Lb : Set U)))
          (IndexSpace N L) (IndexSpace.pt _ _) (IndexSpace.pt _ _),
        e.Commutes (IndexSpace.mapC (rprod (restrictR ρ hρU))
            ((RInv.val_preimage hρU hNb).prod NK).mapsTo
            (((RInv.val_preimage hρU hNb).prod LK).union
              ((RInv.val_preimage hρU hLb).prod NK)).mapsTo)
          (IndexSpace.mapC (rprod ρ) hN.mapsTo hL.mapsTo) := by
  have hfix : ∀ t, θ t b₀ = b₀ := fun t => congrArg Subtype.val (c.fixed t)
  have hNbc := hb.isCompact_N.isClosed
  set C := closure (Nb \ Lb) with hCdef
  have hCρ : RInv ρ C := (hNb.sdiff hLb).closure ρ.continuous hρρ
  have hCN : C ⊆ Nb := closure_minimal sdiff_subset hNbc
  have hCc : IsCompact C := hb.isolating.1
  have hCinv : Inv θ C = {b₀} := hb.inv_eq
  have hb₀C : b₀ ∈ interior C :=
    interior_mono subset_closure (hb.nhds (mem_singleton b₀))
  have hMC : IsIsolatingNbhd Φ (M ×ˢ C) := by
    refine ⟨hM.1.prod hCc, ?_⟩
    rw [hΦ.Inv_prod hfix hCinv, interior_prod_eq]
    exact prod_mono hM.2 (singleton_subset_iff.2 hb₀C)
  obtain ⟨N, L, hP0, hNM, hN, hL⟩ := exists_indexPair_equivariant hMC (rprod ρ)
    (hΦ.flow_rprod hρθ hΦρ) (fun p => by simp [hρρ]) (hCρ.prod M)
  rw [hΦ.Inv_prod hfix hCinv] at hP0
  have hP : IsIndexPair Φ (Inv (c.f₀ hΦ hU hb₀U) M ×ˢ {b₀}) N L := hP0
  refine ⟨N, L, hN, hL, hP, fun NK LK hK => ?_⟩
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
  have hes : ∀ y : X × U, skewIncl U (rprod (restrictR ρ hρU) y) = rprod ρ (skewIncl U y) :=
    fun _ => rfl
  obtain ⟨e₁, he₁⟩ := skew_continuation_equivariant (hΦ.isSkew_restrict hU) c
    (ρ := restrictR ρ hρU) (fun t b => Subtype.ext (hρθ t b)) (fun t x b => hΦρ t x b) hρc
    (fun b => Subtype.ext (hρρ b)) hM' hC'c hC'inv hb₀C' (RInv.val_preimage hρU hCρ) h₀ hP'
    ((RInv.val_preimage hρU hNb).prod NK)
    (((RInv.val_preimage hρU hNb).prod LK).union ((RInv.val_preimage hρU hLb).prod NK))
    (hN.preimage hes) (hL.preimage hes)
  exact ⟨e₁.trans (IndexSpace.embeddingEquiv he.isEmbedding hNe),
    he₁.trans (embeddingEquiv_commutes he.isEmbedding hNe hes hN hL)⟩

end BoundaryEquivariant

end ConleyCheck.Conley
