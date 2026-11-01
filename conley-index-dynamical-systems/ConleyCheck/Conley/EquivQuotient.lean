import ConleyCheck.Conley.CircleSign
import ConleyCheck.Conley.Sphere

/-!
# The quotient spaces of Theorem `thm:equivariant`(i)

For a compact pair `(N, L)` in the slab, with `Y = q⁻¹N/q⁻¹L` and `R̄ : Y → Y` induced by the sheet
exchange:

* `IndexSpace.t2Space`: `N/L` is Hausdorff for compact `N` and closed `L` in a Hausdorff space;
* `orbitQuotHomeo`: `Y/R ≅ N/L`, as a homeomorphism of the quotient of `Y` by the `R̄`-orbits;
* `fixedHomeo`: `(N₊/L₊) ∨ (N₋/L₋) ≅ Y^R`, the fixed subspace of `R̄`, with
  `N_± = {x : (x, ±1) ∈ N}`.
-/

namespace ConleyCheck.Conley

open Set Topology

universe u

/-! ### `N/L` is Hausdorff -/

section T2

variable {α : Type*} [TopologicalSpace α] {N L : Set α}

theorem IndexSpace.isOpen_proj_image {U : Set N} (hU : IsOpen U) (hUL : ∀ x ∈ U, (x : α) ∉ L) :
    IsOpen (IndexSpace.proj N L '' U) := by
  have e : Quotient.mk (indexSetoid N L) ⁻¹' (IndexSpace.proj N L '' U) = Sum.inl '' U := by
    ext a
    rcases a with y | u
    · constructor
      · rintro ⟨x, hx, hxy⟩
        rcases (IndexSpace.proj_eq_proj_iff x y).1 hxy with rfl | ⟨hxL, -⟩
        · exact ⟨x, hx, rfl⟩
        · exact absurd hxL (hUL x hx)
      · rintro ⟨x, hx, hxy⟩
        obtain rfl := Sum.inl_injective hxy
        exact ⟨x, hx, rfl⟩
    · constructor
      · rintro ⟨x, hx, hxy⟩
        exact absurd ((IndexSpace.proj_eq_pt_iff x).1 hxy) (hUL x hx)
      · rintro ⟨x, -, hx⟩
        exact absurd hx Sum.inl_ne_inr
  have h : IsOpen (Sum.inl '' U : Set (N ⊕ Unit)) := isOpenMap_inl U hU
  rw [← e] at h
  exact isQuotientMap_quotient_mk'.isOpen_preimage.1 h

theorem IndexSpace.isOpen_insert_pt {V : Set N} (hV : IsOpen V)
    (hLV : ∀ x : N, (x : α) ∈ L → x ∈ V) :
    IsOpen (insert (IndexSpace.pt N L) (IndexSpace.proj N L '' V)) := by
  have e : Quotient.mk (indexSetoid N L) ⁻¹'
      (insert (IndexSpace.pt N L) (IndexSpace.proj N L '' V)) = Sum.inl '' V ∪ range Sum.inr := by
    ext a
    rcases a with y | u
    · constructor
      · rintro (h | ⟨x, hx, hxy⟩)
        · exact Or.inl ⟨y, hLV y ((IndexSpace.proj_eq_pt_iff y).1 h), rfl⟩
        · rcases (IndexSpace.proj_eq_proj_iff x y).1 hxy with rfl | ⟨-, hyL⟩
          · exact Or.inl ⟨x, hx, rfl⟩
          · exact Or.inl ⟨y, hLV y hyL, rfl⟩
      · rintro (⟨x, hx, hxy⟩ | ⟨u, hu⟩)
        · obtain rfl := Sum.inl_injective hxy
          exact Or.inr ⟨x, hx, rfl⟩
        · exact absurd hu Sum.inr_ne_inl
    · exact ⟨fun _ => Or.inr ⟨u, rfl⟩, fun _ => Or.inl rfl⟩
  have h : IsOpen (Sum.inl '' V ∪ range Sum.inr : Set (N ⊕ Unit)) :=
    (isOpenMap_inl V hV).union isOpen_range_inr
  rw [← e] at h
  exact isQuotientMap_quotient_mk'.isOpen_preimage.1 h

/-- `N/L` is Hausdorff for compact `N` and closed `L`. -/
theorem IndexSpace.t2Space [T2Space α] (hN : IsCompact N) (hL : IsClosed L) :
    T2Space (IndexSpace N L) := by
  have : CompactSpace N := isCompact_iff_compactSpace.1 hN
  have hLc : IsClosed (Subtype.val ⁻¹' L : Set N) := hL.preimage continuous_subtype_val
  have sep : ∀ x : N, (x : α) ∉ L → ∃ u v : Set (IndexSpace N L), IsOpen u ∧ IsOpen v ∧
      IndexSpace.proj N L x ∈ u ∧ IndexSpace.pt N L ∈ v ∧ Disjoint u v := by
    intro x hx
    obtain ⟨U, V, hU, hV, hxU, hLV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact
      isCompact_singleton hLc.isCompact (disjoint_singleton_left.2 hx)
    refine ⟨IndexSpace.proj N L '' U, insert (IndexSpace.pt N L) (IndexSpace.proj N L '' V),
      IndexSpace.isOpen_proj_image hU fun y hy hyL => hUV.ne_of_mem hy (hLV hyL) rfl,
      IndexSpace.isOpen_insert_pt hV fun y hy => hLV hy, ⟨x, hxU (mem_singleton x), rfl⟩,
      Or.inl rfl, ?_⟩
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ (h | ⟨b, hb, hab⟩)
    · exact hUV.ne_of_mem ha (hLV ((IndexSpace.proj_eq_pt_iff a).1 h)) rfl
    · rcases (IndexSpace.proj_eq_proj_iff b a).1 hab with rfl | ⟨-, haL⟩
      · exact hUV.ne_of_mem ha hb rfl
      · exact hUV.ne_of_mem ha (hLV haL) rfl
  refine ⟨fun z₁ z₂ hne => ?_⟩
  induction z₁ using Quotient.inductionOn with
  | h a =>
  induction z₂ using Quotient.inductionOn with
  | h b =>
  rcases a with x | u <;> rcases b with y | v
  · by_cases hx : (x : α) ∈ L
    · by_cases hy : (y : α) ∈ L
      · exact absurd ((IndexSpace.proj_eq_proj_iff x y).2 (Or.inr ⟨hx, hy⟩)) hne
      · obtain ⟨u, v, hu, hv, hyu, hpv, huv⟩ := sep y hy
        refine ⟨v, u, hv, hu, ?_, hyu, huv.symm⟩
        show IndexSpace.proj N L x ∈ v
        rw [IndexSpace.proj_eq_pt hx]
        exact hpv
    · by_cases hy : (y : α) ∈ L
      · obtain ⟨u, v, hu, hv, hxu, hpv, huv⟩ := sep x hx
        refine ⟨u, v, hu, hv, hxu, ?_, huv⟩
        show IndexSpace.proj N L y ∈ v
        rw [IndexSpace.proj_eq_pt hy]
        exact hpv
      · have hxy : x ≠ y := fun h => hne (h ▸ rfl)
        obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hxy
        refine ⟨IndexSpace.proj N L '' (U ∩ (Subtype.val ⁻¹' L)ᶜ),
          IndexSpace.proj N L '' (V ∩ (Subtype.val ⁻¹' L)ᶜ),
          IndexSpace.isOpen_proj_image (hU.inter hLc.isOpen_compl) fun z hz => hz.2,
          IndexSpace.isOpen_proj_image (hV.inter hLc.isOpen_compl) fun z hz => hz.2,
          ⟨x, ⟨hxU, hx⟩, rfl⟩, ⟨y, ⟨hyV, hy⟩, rfl⟩, ?_⟩
        rw [Set.disjoint_left]
        rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
        rcases (IndexSpace.proj_eq_proj_iff b a).1 hab with rfl | ⟨hbL, -⟩
        · exact hUV.ne_of_mem ha.1 hb.1 rfl
        · exact hb.2 hbL
  · have hx : (x : α) ∉ L := fun h => hne (IndexSpace.proj_eq_pt h)
    exact sep x hx
  · have hy : (y : α) ∉ L := fun h => hne (IndexSpace.proj_eq_pt h).symm
    obtain ⟨u', v', hu, hv, hyu, hpv, huv⟩ := sep y hy
    exact ⟨v', u', hv, hu, hpv, hyu, huv.symm⟩
  · exact absurd rfl hne

end T2

/-! ### The involution of `Y` -/

section Y

variable {X : Type u} [TopologicalSpace X] (N L : Set (X × Tau))

/-- `q` as a continuous map. -/
def cqC : C(X × Circ, X × Tau) := ⟨cq, continuous_cq⟩

/-- The involution `R̄` of `Y = q⁻¹N/q⁻¹L`. -/
noncomputable def Ybar : C(IndexSpace (cq ⁻¹' N) (cq ⁻¹' L), IndexSpace (cq ⁻¹' N) (cq ⁻¹' L)) :=
  IndexSpace.mapC (rprod Circ.reflC) (rInv_cq_preimage N).mapsTo (rInv_cq_preimage L).mapsTo

theorem Ybar_proj (y : cq ⁻¹' N) :
    Ybar N L (IndexSpace.proj _ _ y) = IndexSpace.proj _ _ ⟨cR (y : X × Circ), y.2⟩ := rfl

theorem Ybar_Ybar (y : IndexSpace (cq ⁻¹' N) (cq ⁻¹' L)) : Ybar N L (Ybar N L y) = y := by
  induction y using Quotient.inductionOn with
  | h a =>
    rcases a with y | u
    · exact congrArg (IndexSpace.proj _ _) (Subtype.ext (cR_cR (y : X × Circ)))
    · rfl

/-- The `R̄`-orbit relation on `Y`. -/
def yOrbit : Setoid (IndexSpace (cq ⁻¹' N) (cq ⁻¹' L)) where
  r y y' := y' = y ∨ y' = Ybar N L y
  iseqv := by
    refine ⟨fun _ => Or.inl rfl, fun {y y'} h => ?_, fun {a b c} h₁ h₂ => ?_⟩
    · rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Ybar_Ybar N L y).symm
    · rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inl (Ybar_Ybar N L a)

/-- The map `Y → N/L` induced by `q`. -/
noncomputable def qbar : C(IndexSpace (cq ⁻¹' N) (cq ⁻¹' L), IndexSpace N L) :=
  IndexSpace.mapC cqC (fun _ h => h) (fun _ h => h)

theorem qbar_Ybar (y : IndexSpace (cq ⁻¹' N) (cq ⁻¹' L)) : qbar N L (Ybar N L y) = qbar N L y := by
  induction y using Quotient.inductionOn with
  | h a => rcases a with y | u <;> rfl

/-- `Y/R → N/L`. -/
noncomputable def orbitQuotMap : C(Quotient (yOrbit N L), IndexSpace N L) :=
  ⟨Quotient.lift (qbar N L) fun a b h => by
    rcases (h : b = a ∨ b = Ybar N L a) with rfl | rfl
    · rfl
    · exact (qbar_Ybar N L a).symm,
    (qbar N L).continuous.quotient_lift _⟩

variable [T2Space X] {N L} (hN : IsCompact N)

/-- `N → Y/R`, through `N ≅ q⁻¹(N)/R`. -/
noncomputable def orbitQuotSec : C(N, Quotient (yOrbit N L)) :=
  ⟨fun x => Quotient.lift (fun y : cq ⁻¹' N => Quotient.mk (yOrbit N L) (IndexSpace.proj _ _ y))
      (fun a b hab => Quotient.sound (by
        rcases (orbitSetoid_r b a).1 hab with h | h
        · exact Or.inl (congrArg (IndexSpace.proj _ _) (Subtype.ext h.symm))
        · have h' : (b : X × Circ) = cR (a : X × Circ) := by rw [h, cR_cR]
          exact Or.inr (congrArg (IndexSpace.proj _ _)
            (Subtype.ext h' : b = (⟨cR (a : X × Circ), a.2⟩ : cq ⁻¹' N)))))
      ((orbitHomeo hN).symm x),
    by
      apply Continuous.comp _ (orbitHomeo hN).symm.continuous
      apply Continuous.quotient_lift
      exact continuous_quotient_mk'.comp (IndexSpace.proj _ _).continuous⟩

theorem orbitQuotSec_cq (y : cq ⁻¹' N) :
    orbitQuotSec (L := L) hN ⟨cq (y : X × Circ), y.2⟩ =
      Quotient.mk (yOrbit N L) (IndexSpace.proj _ _ y) := by
  have e : (orbitHomeo hN).symm ⟨cq (y : X × Circ), y.2⟩ = Quotient.mk _ y :=
    (orbitHomeo hN).symm_apply_eq.2 (Subtype.ext rfl)
  show Quotient.lift _ _ ((orbitHomeo hN).symm _) = _
  rw [e]
  rfl

/-- `N/L → Y/R`. -/
noncomputable def orbitQuotInv : C(IndexSpace N L, Quotient (yOrbit N L)) :=
  descend (Quotient.mk _ (IndexSpace.pt _ _)) (orbitQuotSec hN) fun x hx => by
    obtain ⟨y, hy⟩ := Quotient.exists_rep ((orbitHomeo hN).symm x)
    have hyx : cq (y : X × Circ) = x := by
      have := congrArg Subtype.val ((orbitHomeo hN).apply_symm_apply x)
      rw [← hy] at this
      exact this
    have hx' : x = ⟨cq (y : X × Circ), y.2⟩ := Subtype.ext hyx.symm
    rw [hx', orbitQuotSec_cq]
    exact congrArg _ (IndexSpace.proj_eq_pt (show cq (y : X × Circ) ∈ L by rw [hyx]; exact hx))

/-- Theorem `thm:equivariant`(i): `Y/R ≅ N/L` for compact `N`, the quotient of
`Y = q⁻¹N/q⁻¹L` by the `R̄`-orbits being homeomorphic to `N/L` through `q`. -/
noncomputable def orbitQuotHomeo : Quotient (yOrbit N L) ≃ₜ IndexSpace N L where
  toFun := orbitQuotMap N L
  invFun := orbitQuotInv hN
  left_inv w := by
    induction w using Quotient.inductionOn with
    | h a =>
      induction a using Quotient.inductionOn with
      | h a =>
        rcases a with y | u
        · exact orbitQuotSec_cq hN y
        · rfl
  right_inv z := by
    induction z using Quotient.inductionOn with
    | h a =>
      rcases a with x | u
      · obtain ⟨y, hy⟩ := Quotient.exists_rep ((orbitHomeo hN).symm x)
        have hx' : x = ⟨cq (y : X × Circ), y.2⟩ := by
          have := congrArg Subtype.val ((orbitHomeo hN).apply_symm_apply x)
          rw [← hy] at this
          exact Subtype.ext this.symm
        show orbitQuotMap N L (orbitQuotSec hN x) = IndexSpace.proj N L x
        rw [hx', orbitQuotSec_cq]
        rfl
      · rfl
  continuous_toFun := (orbitQuotMap N L).continuous
  continuous_invFun := (orbitQuotInv hN).continuous

theorem orbitQuotHomeo_mk (y : cq ⁻¹' N) :
    orbitQuotHomeo (L := L) hN (Quotient.mk _ (IndexSpace.proj _ _ y)) =
      IndexSpace.proj N L ⟨cq (y : X × Circ), y.2⟩ := rfl

end Y

/-! ### The fixed subspace -/

section Fixed

variable {X : Type u} [TopologicalSpace X] (N L : Set (X × Tau))

/-- `N_+ = {x : (x, 1) ∈ N}`. -/
abbrev slicePlus (A : Set (X × Tau)) : Set X := {x | (x, Tau.top) ∈ A}

/-- `N_- = {x : (x, -1) ∈ N}`. -/
abbrev sliceMinus (A : Set (X × Tau)) : Set X := {x | (x, Tau.bot) ∈ A}

/-- `N₊/L₊ → Y`, `[x] ↦ [(x, 0)]`. -/
noncomputable def iotaPlus :
    C(IndexSpace (slicePlus N) (slicePlus L), IndexSpace (cq ⁻¹' N) (cq ⁻¹' L)) :=
  IndexSpace.mapC ⟨fun x => (x, Circ.zero), continuous_id.prodMk continuous_const⟩
    (fun _ h => h) (fun _ h => h)

/-- `N₋/L₋ → Y`, `[x] ↦ [(x, π)]`. -/
noncomputable def iotaMinus :
    C(IndexSpace (sliceMinus N) (sliceMinus L), IndexSpace (cq ⁻¹' N) (cq ⁻¹' L)) :=
  IndexSpace.mapC ⟨fun x => (x, Circ.pi), continuous_id.prodMk continuous_const⟩
    (fun _ h => h) (fun _ h => h)

/-- The wedge `(N₊/L₊) ∨ (N₋/L₋)`. -/
abbrev FixWedge :=
  Wedge (IndexSpace (slicePlus N) (slicePlus L)) (IndexSpace (sliceMinus N) (sliceMinus L))
    (IndexSpace.pt _ _) (IndexSpace.pt _ _)

theorem wedge_elim_base (a : IndexSpace (slicePlus N) (slicePlus L) ⊕
      IndexSpace (sliceMinus N) (sliceMinus L))
    (ha : wedgeBase (IndexSpace.pt _ _) (IndexSpace.pt _ _) a) :
    Sum.elim (iotaPlus N L) (iotaMinus N L) a = IndexSpace.pt _ _ := by
  rcases a with z | z
  · obtain rfl : z = _ := ha
    rfl
  · obtain rfl : z = _ := ha
    rfl

/-- `(N₊/L₊) ∨ (N₋/L₋) → Y`. -/
noncomputable def wedgeMap : C(FixWedge N L, IndexSpace (cq ⁻¹' N) (cq ⁻¹' L)) :=
  ⟨Quotient.lift (Sum.elim (iotaPlus N L) (iotaMinus N L)) fun a b h => by
    rcases (h : a = b ∨ _) with rfl | ⟨ha, hb⟩
    · rfl
    · rw [wedge_elim_base N L a ha, wedge_elim_base N L b hb],
    ((iotaPlus N L).continuous.sumElim (iotaMinus N L).continuous).quotient_lift _⟩

theorem Ybar_wedgeMap (w : FixWedge N L) : Ybar N L (wedgeMap N L w) = wedgeMap N L w := by
  induction w using Quotient.inductionOn with
  | h a =>
    rcases a with z | z
    · induction z using Quotient.inductionOn with
      | h b =>
        rcases b with x | u
        · exact congrArg (IndexSpace.proj _ _) (Subtype.ext (Prod.ext rfl Circ.refl_zero))
        · rfl
    · induction z using Quotient.inductionOn with
      | h b =>
        rcases b with x | u
        · exact congrArg (IndexSpace.proj _ _) (Subtype.ext (Prod.ext rfl Circ.refl_pi))
        · rfl

/-- The fixed subspace `Y^R`. -/
abbrev YFix := {y : IndexSpace (cq ⁻¹' N) (cq ⁻¹' L) // Ybar N L y = y}

/-- `(N₊/L₊) ∨ (N₋/L₋) → Y^R`. -/
noncomputable def wedgeFix : C(FixWedge N L, YFix N L) :=
  ⟨fun w => ⟨wedgeMap N L w, Ybar_wedgeMap N L w⟩, (wedgeMap N L).continuous.subtype_mk _⟩

theorem iotaPlus_eq_pt (z : IndexSpace (slicePlus N) (slicePlus L)) :
    iotaPlus N L z = IndexSpace.pt _ _ ↔ z = IndexSpace.pt _ _ := by
  induction z using Quotient.inductionOn with
  | h a =>
    rcases a with x | u
    · exact (IndexSpace.proj_eq_pt_iff (L := cq ⁻¹' L) ⟨(x.1, Circ.zero), x.2⟩).trans
        (IndexSpace.proj_eq_pt_iff (L := slicePlus L) x).symm
    · exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem iotaMinus_eq_pt (z : IndexSpace (sliceMinus N) (sliceMinus L)) :
    iotaMinus N L z = IndexSpace.pt _ _ ↔ z = IndexSpace.pt _ _ := by
  induction z using Quotient.inductionOn with
  | h a =>
    rcases a with x | u
    · exact (IndexSpace.proj_eq_pt_iff (L := cq ⁻¹' L) ⟨(x.1, Circ.pi), x.2⟩).trans
        (IndexSpace.proj_eq_pt_iff (L := sliceMinus L) x).symm
    · exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem iotaPlus_injective : Function.Injective (iotaPlus N L) := by
  intro z₁ z₂ h
  induction z₁ using Quotient.inductionOn with
  | h a =>
  induction z₂ using Quotient.inductionOn with
  | h b =>
  rcases a with x | u <;> rcases b with y | v
  · rcases (IndexSpace.proj_eq_proj_iff (L := cq ⁻¹' L) ⟨(x.1, Circ.zero), x.2⟩
      ⟨(y.1, Circ.zero), y.2⟩).1 h with h' | ⟨hx, hy⟩
    · exact congrArg (IndexSpace.proj _ _)
        (Subtype.ext (congrArg Prod.fst (congrArg Subtype.val h')))
    · exact (IndexSpace.proj_eq_proj_iff x y).2 (Or.inr ⟨hx, hy⟩)
  · exact (iotaPlus_eq_pt N L _).1 h
  · exact ((iotaPlus_eq_pt N L _).1 h.symm).symm
  · rfl

theorem iotaMinus_injective : Function.Injective (iotaMinus N L) := by
  intro z₁ z₂ h
  induction z₁ using Quotient.inductionOn with
  | h a =>
  induction z₂ using Quotient.inductionOn with
  | h b =>
  rcases a with x | u <;> rcases b with y | v
  · rcases (IndexSpace.proj_eq_proj_iff (L := cq ⁻¹' L) ⟨(x.1, Circ.pi), x.2⟩
      ⟨(y.1, Circ.pi), y.2⟩).1 h with h' | ⟨hx, hy⟩
    · exact congrArg (IndexSpace.proj _ _)
        (Subtype.ext (congrArg Prod.fst (congrArg Subtype.val h')))
    · exact (IndexSpace.proj_eq_proj_iff x y).2 (Or.inr ⟨hx, hy⟩)
  · exact (iotaMinus_eq_pt N L _).1 h
  · exact ((iotaMinus_eq_pt N L _).1 h.symm).symm
  · rfl

theorem iota_cross (z₁ : IndexSpace (slicePlus N) (slicePlus L))
    (z₂ : IndexSpace (sliceMinus N) (sliceMinus L)) (h : iotaPlus N L z₁ = iotaMinus N L z₂) :
    iotaPlus N L z₁ = IndexSpace.pt _ _ := by
  induction z₁ using Quotient.inductionOn with
  | h a =>
  induction z₂ using Quotient.inductionOn with
  | h b =>
  rcases a with x | u
  · rcases b with y | v
    · rcases (IndexSpace.proj_eq_proj_iff (L := cq ⁻¹' L) ⟨(x.1, Circ.zero), x.2⟩
        ⟨(y.1, Circ.pi), y.2⟩).1 h with h' | ⟨hx, -⟩
      · have h1 := congrArg (fun p : cq ⁻¹' N => ((p : X × Circ).2 : ℝ × ℝ).1) h'
        norm_num [Circ.zero, Circ.pi] at h1
      · exact IndexSpace.proj_eq_pt hx
    · exact h
  · rfl

theorem wedgeFix_bijective : Function.Bijective (wedgeFix N L) := by
  constructor
  · intro w₁ w₂ h
    have h' : wedgeMap N L w₁ = wedgeMap N L w₂ := congrArg Subtype.val h
    induction w₁ using Quotient.inductionOn with
    | h a =>
    induction w₂ using Quotient.inductionOn with
    | h b =>
    rcases a with z₁ | z₁ <;> rcases b with z₂ | z₂
    · exact congrArg _ (congrArg Sum.inl (iotaPlus_injective N L h'))
    · have hp := iota_cross N L z₁ z₂ h'
      refine Quotient.sound (Or.inr ⟨(iotaPlus_eq_pt N L z₁).1 hp, ?_⟩)
      exact (iotaMinus_eq_pt N L z₂).1 (h'.symm.trans hp)
    · have hp := iota_cross N L z₂ z₁ h'.symm
      refine Quotient.sound (Or.inr ⟨?_, (iotaPlus_eq_pt N L z₂).1 hp⟩)
      exact (iotaMinus_eq_pt N L z₁).1 (h'.trans hp)
    · exact congrArg _ (congrArg Sum.inr (iotaMinus_injective N L h'))
  · rintro ⟨y, hy⟩
    induction y using Quotient.inductionOn with
    | h a =>
    rcases a with p | u
    · by_cases hpL : (p : X × Circ) ∈ cq ⁻¹' L
      · refine ⟨Wedge.pt _ _, Subtype.ext ?_⟩
        exact (IndexSpace.proj_eq_pt hpL).symm
      · have hfix : (⟨cR (p : X × Circ), p.2⟩ : cq ⁻¹' N) = p := by
          rcases (IndexSpace.proj_eq_proj_iff _ _).1 hy with h | ⟨h, -⟩
          · exact h
          · exact absurd h hpL
        have hR : cR (p : X × Circ) = p := congrArg Subtype.val hfix
        rcases (cR_eq_self_iff _).1 hR with hz | hz
        · have hp : ((p : X × Circ).1, Tau.top) ∈ N := by
            have hp0 : cq (p : X × Circ) ∈ N := p.2
            rw [show (p : X × Circ) = ((p : X × Circ).1, Circ.zero) from Prod.ext rfl hz] at hp0
            exact hp0
          refine ⟨Quotient.mk _ (.inl (IndexSpace.proj _ _ ⟨(p : X × Circ).1, hp⟩)),
            Subtype.ext ?_⟩
          exact congrArg (IndexSpace.proj _ _) (Subtype.ext (Prod.ext rfl hz.symm))
        · have hp : ((p : X × Circ).1, Tau.bot) ∈ N := by
            have hp0 : cq (p : X × Circ) ∈ N := p.2
            rw [show (p : X × Circ) = ((p : X × Circ).1, Circ.pi) from Prod.ext rfl hz] at hp0
            exact hp0
          refine ⟨Quotient.mk _ (.inr (IndexSpace.proj _ _ ⟨(p : X × Circ).1, hp⟩)),
            Subtype.ext ?_⟩
          exact congrArg (IndexSpace.proj _ _) (Subtype.ext (Prod.ext rfl hz.symm))
    · exact ⟨Wedge.pt _ _, rfl⟩

variable [T2Space X] {N L}

/-- Theorem `thm:equivariant`(i): `(N₊/L₊) ∨ (N₋/L₋) ≅ Y^R` for compact `N` and closed `L`. -/
noncomputable def fixedHomeo (hN : IsCompact N) (hL : IsClosed L) : FixWedge N L ≃ₜ YFix N L := by
  haveI : CompactSpace (IndexSpace (slicePlus N) (slicePlus L)) :=
    IndexSpace.compactSpace _ (isCompact_fiber_preimage Tau.top hN)
  haveI : CompactSpace (IndexSpace (sliceMinus N) (sliceMinus L)) :=
    IndexSpace.compactSpace _ (isCompact_fiber_preimage Tau.bot hN)
  haveI : CompactSpace (FixWedge N L) := Quotient.compactSpace
  haveI : T2Space (IndexSpace (cq ⁻¹' N) (cq ⁻¹' L)) :=
    IndexSpace.t2Space (isCompact_cq_preimage hN) (hL.preimage continuous_cq)
  exact (wedgeFix N L).continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ (wedgeFix_bijective N L))

end Fixed

end ConleyCheck.Conley
