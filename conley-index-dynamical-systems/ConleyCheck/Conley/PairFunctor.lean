import ConleyCheck.Conley.PairMaps

/-!
# Functoriality of the homology of pairs

* `singMap_comp`, `singIncl_eq_singMap`: `H_*(B, A)` is functorial in maps of pairs, and the maps
  induced by inclusions are the maps induced by the identity.
* `redHEquiv_natural`: the isomorphism `H̃_*(X) ≅ H_*(X, {x₀})` commutes with the maps induced by
  pointed maps.
-/

namespace ConleyCheck.Conley

open CategoryTheory Limits Set

universe u

variable (K : Type u) [Ring K] {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

theorem singMap_eq_of_eq {f g : C(X, Y)} (h : f = g) {B A : Set X} {B' A' : Set Y}
    {hB : MapsTo f B B'} {hA : ∀ x ∈ B, x ∈ A → f x ∈ A'} {hB' : MapsTo g B B'}
    {hA' : ∀ x ∈ B, x ∈ A → g x ∈ A'} (k : ℤ) : singMap K f hB hA k = singMap K g hB' hA' k := by
  subst h
  rfl

theorem singMap_comp (f : C(X, Y)) (g : C(Y, Z)) {B A : Set X} {B' A' : Set Y} {B'' A'' : Set Z}
    (hB : MapsTo f B B') (hA : ∀ x ∈ B, x ∈ A → f x ∈ A') (hB' : MapsTo g B' B'')
    (hA' : ∀ y ∈ B', y ∈ A' → g y ∈ A'') (k : ℤ) :
    singMap K f hB hA k ≫ singMap K g hB' hA' k =
      singMap K (g.comp f) (hB'.comp hB) (fun x hx ha => hA' _ (hB hx) (hA x hx ha)) k := by
  cases k with
  | negSucc m => ext x; exact Subsingleton.elim _ _
  | ofNat n =>
    refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
      (congrArg (fun φ => HomologicalComplex.homologyMap φ n) ?_)
    ext m x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      apply Subtype.ext
      change (((singFunctor K).map (TopCat.ofHom g)).f m).hom
          ((((singFunctor K).map (TopCat.ofHom f)).f m).hom x.1) =
        (((singFunctor K).map (TopCat.ofHom (g.comp f))).f m).hom x.1
      rw [TopCat.ofHom_comp, CategoryTheory.Functor.map_comp]
      rfl

theorem singMap_square {W : Type u} [TopologicalSpace W] (f : C(X, Y)) (g : C(Y, Z))
    (f' : C(X, W)) (g' : C(W, Z)) (h : g.comp f = g'.comp f') {B A : Set X} {B₁ A₁ : Set Y}
    {B₂ A₂ : Set W} {B' A' : Set Z} (hB : MapsTo f B B₁) (hA : ∀ x ∈ B, x ∈ A → f x ∈ A₁)
    (hB₁ : MapsTo g B₁ B') (hA₁ : ∀ y ∈ B₁, y ∈ A₁ → g y ∈ A') (hB' : MapsTo f' B B₂)
    (hA' : ∀ x ∈ B, x ∈ A → f' x ∈ A₂) (hB₂ : MapsTo g' B₂ B')
    (hA₂ : ∀ y ∈ B₂, y ∈ A₂ → g' y ∈ A') (k : ℤ) :
    singMap K f hB hA k ≫ singMap K g hB₁ hA₁ k = singMap K f' hB' hA' k ≫ singMap K g' hB₂ hA₂ k :=
  (singMap_comp K _ _ _ _ _ _ k).trans
    ((singMap_eq_of_eq K h k).trans (singMap_comp K _ _ _ _ _ _ k).symm)

theorem singIncl_eq_singMap (k : ℤ) {N L N' L' : Set X} (hN : N ⊆ N') (hL : L ⊆ L') :
    singIncl K k hN hL =
      singMap K (ContinuousMap.id X) (fun _ hx => mem_of_subset_of_mem hN hx)
        (fun _ _ hx => mem_of_subset_of_mem hL hx) k := by
  cases k with
  | negSucc m => rfl
  | ofNat n =>
    refine congrArg (fun φ => HomologicalComplex.homologyMap φ n) ?_
    ext m x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      apply Subtype.ext
      change x.1 = (((singFunctor K).map (TopCat.ofHom (ContinuousMap.id X))).f m).hom x.1
      rw [TopCat.ofHom_id, CategoryTheory.Functor.map_id]
      rfl

theorem singIncl_comp (k : ℤ) {N L N' L' N'' L'' : Set X} (hN : N ⊆ N') (hL : L ⊆ L')
    (hN' : N' ⊆ N'') (hL' : L' ⊆ L'') :
    singIncl K k hN hL ≫ singIncl K k hN' hL' = singIncl K k (hN.trans hN') (hL.trans hL') := by
  cases k with
  | negSucc m => rfl
  | ofNat n =>
    refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
      (congrArg (fun φ => HomologicalComplex.homologyMap φ n) ?_)
    ext m x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

/-- The restriction of `f` to a map `B → B'`. -/
def restrictC (f : C(X, Y)) {B : Set X} {B' : Set Y} (hB : MapsTo f B B') : C(B, B') :=
  ⟨fun x => ⟨f x, hB x.2⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem toRel_singMap (f : C(X, Y)) {B : Set X} {B' : Set Y} (hB : MapsTo f B B') (n : ℕ) :
    toRelH K B n ≫ singMap K f hB (fun x _ hx => absurd hx (notMem_empty x)) (Int.ofNat n) =
      hMap K (restrictC f hB) n ≫ toRelH K B' n := by
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun φ => HomologicalComplex.homologyMap φ n) ?_).trans
      (HomologicalComplex.homologyMap_comp _ _ n))
  ext m x
  have e : (singFunctor K).map (subsetι B) ≫ (singFunctor K).map (TopCat.ofHom f) =
      (singFunctor K).map (TopCat.ofHom (restrictC f hB)) ≫ (singFunctor K).map (subsetι B') := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    rfl
  have he := congrArg
    (fun φ : (singFunctor K).obj (TopCat.of B) ⟶ (singFunctor K).obj (TopCat.of Y) =>
      (φ.f m).hom x) e
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at he
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  exact Subtype.ext he

theorem absToRel_natural (f : C(X, Y)) (n : ℕ) (a : absH K X n) :
    (singMap K f (mapsTo_univ f univ) (fun x _ hx => absurd hx (notMem_empty x))
      (Int.ofNat n)).hom (absToRel K n a) = absToRel K n ((hMap K f n).hom a) := by
  have e1 := congrArg (fun φ => φ.hom ((hMap K univC n).hom a))
    (toRel_singMap K f (mapsTo_univ f univ) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1
  simp only [absToRel, LinearMap.comp_apply]
  rw [e1, hMap_comp_apply, hMap_comp_apply]
  rfl

theorem redHEquiv_π (x₀ : X) (n : ℕ) (a : absH K X n) :
    redHEquiv K x₀ n ((cokernel.π (hMap K (ptMap x₀) n)).hom a) =
      (singIncl K (Int.ofNat n) (subset_refl (univ : Set X)) (empty_subset ({x₀} : Set X))).hom
        (absToRel K n a) := by
  have e := congrArg (fun φ => φ.hom a)
    (ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom (hMap K (ptMap x₀) n))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    Submodule.mkQ_apply] at e
  simp only [redHEquiv, LinearEquiv.trans_apply]
  erw [e]
  rfl

theorem redHEquiv_natural (f : C(X, Y)) {x₀ : X} {y₀ : Y} (hf : f x₀ = y₀) (n : ℕ)
    (z : redH K X x₀ n) :
    (singMap K f (mapsTo_univ f univ)
      (fun x _ hx => by rw [mem_singleton_iff.1 hx, hf]; exact mem_singleton _) (Int.ofNat n)).hom
        (redHEquiv K x₀ n z) = redHEquiv K y₀ n ((redMap K f hf n).hom z) := by
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi (cokernel.π (hMap K (ptMap x₀) n))) z
  have e := congrArg (fun φ => φ.hom a) (π_redMap K f hf n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
  erw [e, redHEquiv_π, redHEquiv_π]
  rw [← absToRel_natural]
  have e2 : singIncl K (Int.ofNat n) (subset_refl (univ : Set X)) (empty_subset ({x₀} : Set X)) ≫
      singMap K f (mapsTo_univ f univ)
        (fun x _ hx => by rw [mem_singleton_iff.1 hx, hf]; exact mem_singleton _) (Int.ofNat n) =
      singMap K f (mapsTo_univ f univ) (fun x _ hx => absurd hx (notMem_empty x)) (Int.ofNat n) ≫
        singIncl K (Int.ofNat n) (subset_refl (univ : Set Y)) (empty_subset ({y₀} : Set Y)) := by
    rw [singIncl_eq_singMap, singIncl_eq_singMap]
    exact (singMap_comp K _ _ _ _ _ _ _).trans
      ((singMap_eq_of_eq K (by ext; rfl) _).trans (singMap_comp K _ _ _ _ _ _ _).symm)
  exact congrArg (fun φ => φ.hom (absToRel K n a)) e2

end ConleyCheck.Conley
