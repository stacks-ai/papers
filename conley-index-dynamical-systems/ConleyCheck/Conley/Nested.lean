import ConleyCheck.Conley.Collar
import ConleyCheck.Conley.PairFunctor

/-!
# Nested index pairs

* `projMap_bijective`: for a collared index pair, the projection `N → N/L` induces isomorphisms
  `H_*(N, L) ≅ H_*(N/L, [L])`. Unlike `collarEquiv`, this isomorphism is a specific map, so it
  commutes with maps of index pairs.
* `nestMap_homotopyEquiv`: if `(N, L) ⊆ (N', L')` are index pairs of the same `S`, the map
  `N/L → N'/L'` induced by the inclusion is a pointed homotopy equivalence.
* `singIncl_bijective_of_nested`: for nested collared index pairs of the same `S`, the inclusion
  induces isomorphisms `H_*(N, L) ≅ H_*(N', L')`.
-/

namespace ConleyCheck.Conley

open CategoryTheory Limits Set Topology unitInterval

universe u

variable {α : Type u} [TopologicalSpace α]

section Square

variable (K : Type u) [Ring K]

theorem bijective_of_square_left {A B C D : ModuleCat.{u} K} (f : A ⟶ B) (g : B ⟶ D)
    (h : A ⟶ C) (k : C ⟶ D) (hsq : f ≫ g = h ≫ k) (hg : Function.Bijective g.hom)
    (hh : Function.Bijective h.hom) (hk : Function.Bijective k.hom) :
    Function.Bijective f.hom := by
  have e : g.hom ∘ f.hom = k.hom ∘ h.hom := funext fun x => congrArg (fun φ => φ.hom x) hsq
  exact (Function.Bijective.of_comp_iff' hg _).1 (e ▸ hk.comp hh)

theorem bijective_of_square_right {A B C D : ModuleCat.{u} K} (f : A ⟶ B) (g : B ⟶ D)
    (h : A ⟶ C) (k : C ⟶ D) (hsq : f ≫ g = h ≫ k) (hf : Function.Bijective f.hom)
    (hh : Function.Bijective h.hom) (hk : Function.Bijective k.hom) :
    Function.Bijective g.hom := by
  have e : g.hom ∘ f.hom = k.hom ∘ h.hom := funext fun x => congrArg (fun φ => φ.hom x) hsq
  exact (Function.Bijective.of_comp_iff _ hf).1 (e ▸ hk.comp hh)

end Square

/-! ### The projection `(N, L) → (N/L, [L])` -/

section Canonical

variable (K : Type u) [Ring K] (N L : Set α)

/-- `L ∩ N` as a subset of `N`. -/
def subL : Set N := {x | (x : α) ∈ L}

/-- The inclusion `N → α`. -/
def valN : C(N, α) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The map `H_*(N, L ∩ N) → H_*(N/L, [L])` induced by the projection. -/
noncomputable def projMap (k : ℤ) :
    singH K N k univ (subL N L) ⟶ singH K (IndexSpace N L) k univ {IndexSpace.pt N L} :=
  singMap K (IndexSpace.proj N L) (mapsTo_univ _ _) (fun _ _ hx => IndexSpace.proj_eq_pt hx) k

theorem valN_bijective (k : ℤ) {A : Set α} :
    Function.Bijective (singMap K (valN N) (B := univ) (A := {x : N | (x : α) ∈ A}) (B' := N)
      (A' := A) (fun x _ => x.2) (fun _ _ hx => hx) k).hom :=
  singMap_bijective K (valN N) (B := univ) (A := {x : N | (x : α) ∈ A}) (B' := N) (A' := A)
    (fun x _ => x.2) (fun y hy => ⟨⟨y, hy⟩, mem_univ _, rfl⟩)
    (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal) (fun _ _ => Iff.rfl) k

theorem projMap_bijective [T2Space α] {ϕ : Flow ℝ α} {S : Set α} (hP : IsIndexPair ϕ S N L)
    (hc : IsCollared ϕ N L) (k : ℤ) : Function.Bijective (projMap K N L k).hom := by
  obtain ⟨V, O, τ, hO, hLO, hON, hVN, hτc, hτ01, hτL, hseg, hhit⟩ := hc
  have hLc : IsClosed L := hP.isCompact_L.isClosed
  have hLV : L ⊆ V := fun x hx => hON ⟨hLO hx, hP.subset hx⟩
  let Hα : C(I × V, V) := ⟨fun p => ⟨ϕ ((p.1 : ℝ) * τ p.2) p.2, hseg p.2 _
      ⟨mul_nonneg p.1.2.1 (hτ01 _).1, mul_le_of_le_one_left (hτ01 _).1 p.1.2.2⟩⟩, by
    refine Continuous.subtype_mk ?_ _
    exact ϕ.continuous ((continuous_subtype_val.comp continuous_fst).mul (hτc.comp continuous_snd))
      (continuous_subtype_val.comp continuous_snd)⟩
  have hsV : ∀ k, Subsingleton (singH K α k V L) := singH_subsingleton_of_deform K hLV Hα
    (fun x => Subtype.ext (by
      show ϕ (((0 : I) : ℝ) * τ x) x = x
      rw [Icc.coe_zero, zero_mul, ϕ.map_zero_apply]))
    (fun x => by
      show ϕ (((1 : I) : ℝ) * τ x) x ∈ L
      rw [Icc.coe_one, one_mul]
      exact hhit x)
    (fun s x hx => by
      show ϕ ((s : ℝ) * τ x) x ∈ L
      rw [hτL x hx, mul_zero, ϕ.map_zero_apply]
      exact hx)
  have b1 := singIncl_bijective_of_subsingleton K hLV hVN hsV k
  have b2 := excision K hVN (sdiff_subset : N \ L ⊆ N) hO hLc.isOpen_compl
    (fun x _ => by
      by_cases h : x ∈ L
      · exact Or.inl (hLO h)
      · exact Or.inr h)
    hON (fun x hx => ⟨hx.2, hx.1⟩) k
  have b3 := singMap_bijective K (valN N) (B := offL N L) (A := {x : N | (x : α) ∈ V})
    (B' := N \ L) (A' := V) (fun x hx => ⟨x.2, hx⟩) (fun y hy => ⟨⟨y, hy.1⟩, hy.2, rfl⟩)
    (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal) (fun x _ => Iff.rfl) k
  have b4 := singMap_bijective K (IndexSpace.proj N L) (B := offL N L)
    (A := {x : N | (x : α) ∈ V}) (B' := {IndexSpace.pt N L}ᶜ) (A' := liftSet N L V)
    (fun x hx h => hx ((IndexSpace.proj_eq_pt_iff x).1 h)) (fun y hy => exists_proj_of_ne_pt hy)
    (isEmbedding_proj_offL hLc) (fun x _ => (proj_mem_liftSet hLV x).symm) k
  have b5 := excision K (subset_univ (liftSet N L V)) (subset_univ ({IndexSpace.pt N L}ᶜ))
    (isOpen_liftSet hLO hO) (isOpen_compl_pt hLc)
    (fun z _ => by
      by_cases h : z = IndexSpace.pt N L
      · exact Or.inl (Or.inl h)
      · exact Or.inr h)
    (by
      rintro z ⟨h | ⟨x, hx, rfl⟩, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨x, hON ⟨hx, x.2⟩, rfl⟩)
    (fun z hz => hz.1) k
  have hpV : ({IndexSpace.pt N L} : Set (IndexSpace N L)) ⊆ liftSet N L V := by
    rintro _ rfl
    exact pt_mem_liftSet V
  have hmem := pushHom_mem_liftSet hP hLV (fun x => (hτ01 x).1) (fun x => (hτ01 x).2) hseg hhit
  let HQ : C(I × liftSet N L V, liftSet N L V) :=
    ⟨fun p => ⟨pushHom hP 1 zero_le_one (p.1, p.2), (hmem p.1 p.2.2).1⟩, by
      refine Continuous.subtype_mk ?_ _
      exact (pushHom hP 1 zero_le_one).continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩
  have hsQ : ∀ k, Subsingleton (singH K (IndexSpace N L) k (liftSet N L V) {IndexSpace.pt N L}) :=
    singH_subsingleton_of_deform K hpV HQ (fun z => Subtype.ext (pushHom_zero hP z))
      (fun z => (hmem 1 z.2).2 rfl)
      (fun s z hz => by
        rw [mem_singleton_iff] at hz ⊢
        show pushHom hP 1 zero_le_one (s, (z : IndexSpace N L)) = _
        rw [hz]
        rfl)
  have b6 := singIncl_bijective_of_subsingleton K hpV (subset_univ _) hsQ k
  have v1 := valN_bijective K N k (A := L)
  have v2 := valN_bijective K N k (A := V)
  have hLVN : subL N L ⊆ {x : N | (x : α) ∈ V} := fun x hx => hLV hx
  have iN : Function.Bijective (singIncl K k (subset_refl (univ : Set N)) hLVN).hom := by
    refine bijective_of_square_left K _ _ _ _ ?_ v2 v1 b1
    rw [singIncl_eq_singMap, singIncl_eq_singMap]
    exact singMap_square K _ _ _ _ (by ext; rfl) _ _ _ _ _ _ _ _ k
  have eN : Function.Bijective (singIncl K k (subset_univ (offL N L))
      (subset_refl {x : N | (x : α) ∈ V})).hom := by
    refine bijective_of_square_left K _ _ _ _ ?_ v2 b3 b2
    rw [singIncl_eq_singMap, singIncl_eq_singMap]
    exact singMap_square K _ _ _ _ (by ext; rfl) _ _ _ _ _ _ _ _ k
  let pV := singMap K (IndexSpace.proj N L) (B := (univ : Set N)) (A := {x : N | (x : α) ∈ V})
    (B' := univ) (A' := liftSet N L V) (mapsTo_univ _ _)
    (fun x _ hx => (proj_mem_liftSet hLV x).2 hx) k
  have hpVb : Function.Bijective pV.hom := by
    refine bijective_of_square_right K _ pV _ _ ?_ eN b4 b5
    rw [singIncl_eq_singMap, singIncl_eq_singMap]
    exact singMap_square K _ _ _ _ (by ext; rfl) _ _ _ _ _ _ _ _ k
  refine bijective_of_square_left K (projMap K N L k) _ _ _ ?_ b6 iN hpVb
  rw [projMap, singIncl_eq_singMap, singIncl_eq_singMap]
  exact singMap_square K _ _ _ _ (by ext; rfl) _ _ _ _ _ _ _ _ k

end Canonical

/-! ### Nested index pairs -/

section Nested

variable {N L N' L' : Set α}

/-- The map `N/L → N'/L'` induced by the inclusion `(N, L) ⊆ (N', L')`. -/
noncomputable def nestMap (hN : N ⊆ N') (hL : L ⊆ L') : C(IndexSpace N L, IndexSpace N' L') :=
  descend (IndexSpace.pt N' L')
    ((IndexSpace.proj N' L').comp ⟨Set.inclusion hN, continuous_inclusion hN⟩)
    fun _ hy => IndexSpace.proj_eq_pt (hL hy)

variable [T2Space α] {ϕ : Flow ℝ α} {S : Set α}

open scoped Classical in

theorem pushMap_comp_nestMap (h : IsIndexPair ϕ S N L) (h' : IsIndexPair ϕ S N' L')
    (hN : N ⊆ N') (hL : L ⊆ L') (T : ℝ) (hT : 0 ≤ T) (hT1 : TimeLemma (ϕ := ϕ) N L N' L' T)
    (hT2 : TimeLemma (ϕ := ϕ) N' L' N L T) :
    (pushMap h' (3 * T) (by linarith)).comp (nestMap hN hL) = compMap h h' T hT hT1 hT2 := by
  ext x
  induction x using Quotient.inductionOn
  rename_i a
  rcases a with y | u
  · show pushMap h' (3 * T) (by linarith) (IndexSpace.proj N' L' (Set.inclusion hN y)) =
      (if (y : α) ∈ compA (ϕ := ϕ) N L N' L' T then
        IndexSpace.Q N' L' (ϕ (3 * T) (y : α)) else IndexSpace.pt N' L')
    rw [pushMap_proj]
    show (if ∀ r ∈ Icc 0 (3 * T), ϕ r (y : α) ∈ N' then IndexSpace.Q N' L' (ϕ (3 * T) (y : α))
      else IndexSpace.pt N' L') = _
    by_cases hA : (y : α) ∈ compA (ϕ := ϕ) N L N' L' T
    · have hc : ∀ r ∈ Icc 0 (3 * T), ϕ r (y : α) ∈ N' := by
        intro r hr
        by_cases hr2 : r ≤ 2 * T
        · exact hN (hA.1 r ⟨hr.1, hr2⟩).1
        · exact (hA.2 r ⟨by linarith, hr.2⟩).1
      rw [if_pos hA, if_pos hc]
    · rw [if_neg hA]
      split_ifs with hseg
      · apply IndexSpace.Q_of_mem_L h'.subset
        simp only [compA, mem_setOf_eq, not_and_or, not_forall] at hA
        rcases hA with ⟨s, hs, hns⟩ | ⟨s, hs, hns⟩
        · obtain ⟨s', hs', hsL⟩ : ∃ s' ∈ Icc 0 s, ϕ s' (y : α) ∈ L := by
            by_cases hsN : ϕ s (y : α) ∈ N
            · refine ⟨s, ⟨hs.1, le_rfl⟩, ?_⟩
              by_contra hc
              exact hns ⟨hsN, hc⟩
            · obtain ⟨s', hs', -, hL'⟩ := h.exit y y.2 s hs.1 hsN
              exact ⟨s', hs', hL'⟩
          exact posInv_shift h'.posInv (by linarith [hs'.2, hs.2]) (hL hsL)
            fun r hr => hseg r ⟨by linarith [hr.1, hs'.1], hr.2⟩
        · have hsL' : ϕ s (y : α) ∈ L' := by
            by_contra hc
            exact hns ⟨hseg s ⟨by linarith [hs.1], hs.2⟩, hc⟩
          exact posInv_shift h'.posInv hs.2 hsL'
            fun r hr => hseg r ⟨by linarith [hr.1, hs.1], hr.2⟩
      · rfl
  · rfl

/-- For nested index pairs of the same isolated invariant set, the inclusion induces a pointed
homotopy equivalence `N/L → N'/L'`. -/
theorem nestMap_homotopyEquiv (h : IsIndexPair ϕ S N L) (h' : IsIndexPair ϕ S N' L')
    (hN : N ⊆ N') (hL : L ⊆ L') :
    ∃ e : PointedHomotopyEquiv (IndexSpace N L) (IndexSpace N' L') (IndexSpace.pt N L)
      (IndexSpace.pt N' L'), e.toFun = nestMap hN hL := by
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
  have hmap : MapsTo (nestMap hN hL) {IndexSpace.pt N L} {IndexSpace.pt N' L'} :=
    fun x hx => by rw [mem_singleton_iff.1 hx]; rfl
  have h1 : (compMap h h' T hT hT1 hT2).HomotopicRel (nestMap hN hL) {IndexSpace.pt N L} := by
    have := HomotopicRel.precomp (pushMap_homotopicRel h' (3 * T) (by linarith))
      (nestMap hN hL) hmap
    rwa [pushMap_comp_nestMap h h' hN hL T hT hT1 hT2, ContinuousMap.id_comp] at this
  refine ⟨{ toFun := nestMap hN hL
            invFun := compMap h' h T hT hT2 hT1
            map_pt := rfl
            inv_pt := rfl
            left := ?_
            right := ?_ }, rfl⟩
  · have h2 := h1.comp_continuousMap (compMap h' h T hT hT2 hT1)
    rw [compMap_comp h h' T hT hT1 hT2] at h2
    exact h2.symm.trans (pushMap_homotopicRel h _ _)
  · have hmap' : MapsTo (compMap h' h T hT hT2 hT1) {IndexSpace.pt N' L'} {IndexSpace.pt N L} :=
      fun x hx => by rw [mem_singleton_iff.1 hx]; rfl
    have h2 := HomotopicRel.precomp h1 (compMap h' h T hT hT2 hT1) hmap'
    rw [compMap_comp h' h T hT hT2 hT1] at h2
    exact h2.symm.trans (pushMap_homotopicRel h' _ _)

variable (K : Type u) [Ring K]

theorem redMap_eq_of_eq {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (h : f = g) {x₀ : X} {y₀ : Y} (hf : f x₀ = y₀) (hg : g x₀ = y₀) (n : ℕ) :
    redMap K f hf n = redMap K g hg n := by
  subst h
  rfl

theorem nestSing_bijective (h : IsIndexPair ϕ S N L) (h' : IsIndexPair ϕ S N' L')
    (hN : N ⊆ N') (hL : L ⊆ L') (k : ℤ) :
    Function.Bijective (singMap K (nestMap hN hL) (B := univ) (A := {IndexSpace.pt N L})
      (B' := univ) (A' := {IndexSpace.pt N' L'}) (mapsTo_univ _ _)
      (fun x _ hx => by rw [mem_singleton_iff.1 hx]; rfl) k).hom := by
  cases k with
  | negSucc m => exact bijective_of_subsingleton _
  | ofNat n =>
    obtain ⟨e, he⟩ := nestMap_homotopyEquiv h h' hN hL
    have hr : Function.Bijective (redMap K (nestMap hN hL) (x₀ := IndexSpace.pt N L)
        (y₀ := IndexSpace.pt N' L') rfl n).hom := by
      have := redMap_eq_of_eq K he.symm (x₀ := IndexSpace.pt N L) (y₀ := IndexSpace.pt N' L')
        rfl e.map_pt n
      exact (congrArg (fun φ => Function.Bijective φ.hom) this).mpr
        (redIso K e n).toLinearEquiv.bijective
    have e1 := funext (redHEquiv_natural K (nestMap hN hL) (x₀ := IndexSpace.pt N L)
      (y₀ := IndexSpace.pt N' L') rfl n)
    have hc := (redHEquiv K (IndexSpace.pt N' L') n).bijective.comp hr
    refine (Function.Bijective.of_comp_iff _ (redHEquiv K (IndexSpace.pt N L) n).bijective).1 ?_
    convert hc using 1
    exact e1

/-- For nested collared index pairs of the same isolated invariant set, the inclusion induces
isomorphisms `H_*(N, L) ≅ H_*(N', L')`. -/
theorem singIncl_bijective_of_nested (h : IsIndexPair ϕ S N L) (h' : IsIndexPair ϕ S N' L')
    (hc : IsCollared ϕ N L) (hc' : IsCollared ϕ N' L') (hN : N ⊆ N') (hL : L ⊆ L') (k : ℤ) :
    Function.Bijective (singIncl K k hN hL).hom := by
  let ι : C(N, N') := ⟨Set.inclusion hN, continuous_inclusion hN⟩
  let m := singMap K ι (B := (univ : Set N)) (A := subL N L) (B' := univ) (A' := subL N' L')
    (mapsTo_univ _ _) (fun _ _ hx => hL hx) k
  have hm : Function.Bijective m.hom := by
    refine bijective_of_square_left K m (projMap K N' L' k) (projMap K N L k) _ ?_
      (projMap_bijective K N' L' h' hc' k) (projMap_bijective K N L h hc k)
      (nestSing_bijective K h h' hN hL k)
    exact singMap_square K _ _ _ _ (by ext; rfl) _ _ _ _ _ _ _ _ k
  refine bijective_of_square_right K _ (singIncl K k hN hL) m _ ?_ (valN_bijective K N k)
    hm (valN_bijective K N' k)
  rw [singIncl_eq_singMap]
  exact singMap_square K _ _ _ _ (by ext; rfl) _ _ _ _ _ _ _ _ k

end Nested

end ConleyCheck.Conley
