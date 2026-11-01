import ConleyCheck.Conley.Excision
import ConleyCheck.Conley.HomologyIndex

/-!
# Maps of pairs and reduced homology

* `singMap`: the map `H_*(B, A) → H_*(B', A')` induced by a continuous map `f : X → Z` with
  `f(B) ⊆ B'` and `f(A ∩ B) ⊆ A'`. If `f` restricts to an embedding of `B` onto `B'` with
  `A ∩ B = B ∩ f⁻¹(A')`, it is an isomorphism (`singMap_bijective`).
* `singH_subsingleton_of_deform`: if `W` deforms into `Y ⊆ W` inside `W`, keeping `Y` in `Y`,
  then `H_*(W, Y) = 0`.
* `singIncl_bijective_of_subsingleton`: `H_*(N, L) ≅ H_*(N, V)` if `H_*(V, L) = 0`.
* `redHEquiv`: `H_*(X, {x₀}) ≅ H̃_*(X)`.
-/

namespace ConleyCheck.Conley

open CategoryTheory Limits Set Topology

universe u

variable {K : Type u} [Ring K]

/-! ### Chain maps between relative complexes -/

section RelGen

variable {C D : ChainComplex (ModuleCat.{u} K) ℕ}

/-- The map `Q/P → Q'/P'` induced by a chain map `φ : C → D`. -/
def relMapGenF (φ : C ⟶ D) {Q P : SubCx C} {Q' P' : SubCx D}
    (hQ : ∀ n, ∀ x ∈ Q.S n, (φ.f n).hom x ∈ Q'.S n)
    (hP : ∀ n, ∀ x ∈ Q.S n, x ∈ P.S n → (φ.f n).hom x ∈ P'.S n) (n : ℕ) :
    (Q.S n ⧸ relSub Q P n) →ₗ[K] (Q'.S n ⧸ relSub Q' P' n) :=
  (relSub Q P n).mapQ (relSub Q' P' n) ((φ.f n).hom.restrict (hQ n))
    fun x hx => hP n x.1 x.2 hx

theorem relMapGenF_mk (φ : C ⟶ D) {Q P : SubCx C} {Q' P' : SubCx D}
    (hQ : ∀ n, ∀ x ∈ Q.S n, (φ.f n).hom x ∈ Q'.S n)
    (hP : ∀ n, ∀ x ∈ Q.S n, x ∈ P.S n → (φ.f n).hom x ∈ P'.S n) (n : ℕ) (x : Q.S n) :
    relMapGenF φ hQ hP n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨(φ.f n).hom x, hQ n x x.2⟩ := rfl

/-- The chain map `Q/P → Q'/P'` induced by a chain map `φ : C → D`. -/
noncomputable def relMapGen (φ : C ⟶ D) {Q P : SubCx C} {Q' P' : SubCx D}
    (hQ : ∀ n, ∀ x ∈ Q.S n, (φ.f n).hom x ∈ Q'.S n)
    (hP : ∀ n, ∀ x ∈ Q.S n, x ∈ P.S n → (φ.f n).hom x ∈ P'.S n) :
    relCx C Q P ⟶ relCx D Q' P' where
  f n := ModuleCat.ofHom (relMapGenF φ hQ hP n)
  comm' i j _ := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      change relD Q' P' i j (relMapGenF φ hQ hP i (Submodule.Quotient.mk x)) =
        relMapGenF φ hQ hP j (relD Q P i j (Submodule.Quotient.mk x))
      rw [relMapGenF_mk, relD_mk, relD_mk, relMapGenF_mk]
      congr 1
      apply Subtype.ext
      exact congrArg (fun ψ => ψ.hom x.1) (φ.comm i j)

theorem homologyMap_bijective_of_bijective {X Y : ChainComplex (ModuleCat.{u} K) ℕ} (φ : X ⟶ Y)
    (h : ∀ n, Function.Bijective (φ.f n).hom) (n : ℕ) :
    Function.Bijective (HomologicalComplex.homologyMap φ n).hom := by
  have : ∀ n, IsIso (φ.f n) := fun n => (ConcreteCategory.isIso_iff_bijective _).2 (h n)
  have := HomologicalComplex.Hom.isIso_of_components φ
  exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

end RelGen

/-! ### Maps of pairs -/

section Maps

variable (K) {X Z : Type u} [TopologicalSpace X] [TopologicalSpace Z]

theorem mapF_supported (f : C(X, Z)) {n : ℕ} {S : Set (Simp (TopCat.of X) n)}
    {S' : Set (Simp (TopCat.of Z) n)} (h : ∀ σ ∈ S, f.comp σ ∈ S')
    {g : Simp (TopCat.of X) n →₀ K} (hg : g ∈ Finsupp.supported K K S) :
    mapF K (TopCat.ofHom f) n g ∈ Finsupp.supported K K S' := by
  classical
  rw [Finsupp.mem_supported] at hg ⊢
  intro x hx
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support
    (f := fun σ : Simp (TopCat.of X) n => f.comp σ) (s := g) (Finset.mem_coe.1 hx))
  exact h σ (hg hσ)

theorem sing_map_mem (f : C(X, Z)) {B : Set X} {B' : Set Z} (hB : MapsTo f B B') (n : ℕ)
    (x : CX K (TopCat.of X) n) (hx : x ∈ (chainSub K B).S n) :
    (((singFunctor K).map (TopCat.ofHom f)).f n).hom x ∈ (chainSub K B').S n := by
  obtain ⟨g, rfl⟩ := (basEquiv K _ n).surjective x
  rw [mem_chainSub_iff, LinearEquiv.symm_apply_apply] at hx
  rw [mem_chainSub_iff, basEquiv_apply, bas_map, ← basEquiv_apply, LinearEquiv.symm_apply_apply]
  exact mapF_supported K f (fun σ hσ => by rintro _ ⟨t, rfl⟩; exact hB (hσ ⟨t, rfl⟩)) hx

theorem sing_map_mem' (f : C(X, Z)) {B A : Set X} {A' : Set Z} (hA : ∀ x ∈ B, x ∈ A → f x ∈ A')
    (n : ℕ) (x : CX K (TopCat.of X) n) (hxB : x ∈ (chainSub K B).S n)
    (hxA : x ∈ (chainSub K A).S n) :
    (((singFunctor K).map (TopCat.ofHom f)).f n).hom x ∈ (chainSub K A').S n := by
  obtain ⟨g, rfl⟩ := (basEquiv K _ n).surjective x
  rw [mem_chainSub_iff, LinearEquiv.symm_apply_apply] at hxB hxA
  have hg : g ∈ Finsupp.supported K K (onSet B n ∩ onSet A n) := by
    rw [Finsupp.supported_inter]
    exact ⟨hxB, hxA⟩
  rw [mem_chainSub_iff, basEquiv_apply, bas_map, ← basEquiv_apply, LinearEquiv.symm_apply_apply]
  refine mapF_supported K f (fun σ hσ => ?_) hg
  rintro _ ⟨t, rfl⟩
  exact hA _ (hσ.1 ⟨t, rfl⟩) (hσ.2 ⟨t, rfl⟩)

/-- The map `H_*(B, A) → H_*(B', A')` induced by `f : X → Z`. -/
noncomputable def singMap (f : C(X, Z)) {B A : Set X} {B' A' : Set Z} (hB : MapsTo f B B')
    (hA : ∀ x ∈ B, x ∈ A → f x ∈ A') (k : ℤ) : singH K X k B A ⟶ singH K Z k B' A' :=
  match k with
  | .ofNat n => HomologicalComplex.homologyMap
      (relMapGen ((singFunctor K).map (TopCat.ofHom f)) (fun n x hx => sing_map_mem K f hB n x hx)
        (fun n x hx hx' => sing_map_mem' K f hA n x hx hx')) n
  | .negSucc _ => 0

theorem bijective_of_subsingleton {M₁ M₂ : Type*} [Subsingleton M₁] [Subsingleton M₂]
    [Nonempty M₁] (f : M₁ → M₂) : Function.Bijective f :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩

theorem singMapF_bijective (f : C(X, Z)) {B A : Set X} {B' A' : Set Z} (hB : MapsTo f B B')
    (hsurj : ∀ y ∈ B', ∃ x ∈ B, f x = y) (hemb : IsEmbedding (B.restrict f))
    (hA : ∀ x ∈ B, x ∈ A ↔ f x ∈ A') (n : ℕ) :
    Function.Bijective (relMapGenF ((singFunctor K).map (TopCat.ofHom f))
      (fun n x hx => sing_map_mem K f hB n x hx)
      (fun n x hx hx' => sing_map_mem' K f (fun x hx h => (hA x hx).1 h) n x hx hx') n) := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      induction x using Submodule.Quotient.induction_on with
      | H x =>
        obtain ⟨y, hy⟩ := x
        obtain ⟨g, rfl⟩ := (basEquiv K _ n).surjective y
        rw [relMapGenF_mk, Submodule.Quotient.mk_eq_zero] at hx
        change (((singFunctor K).map (TopCat.ofHom f)).f n).hom (basEquiv K _ n g) ∈
          (chainSub K A').S n at hx
        rw [Submodule.Quotient.mk_eq_zero]
        change basEquiv K _ n g ∈ (chainSub K A).S n
        have hgB := (mem_chainSub_iff B n _).1 hy
        rw [LinearEquiv.symm_apply_apply] at hgB
        rw [mem_chainSub_iff, basEquiv_apply, bas_map, ← basEquiv_apply,
          LinearEquiv.symm_apply_apply] at hx
        rw [mem_chainSub_iff, LinearEquiv.symm_apply_apply, Finsupp.mem_supported]
        classical
        intro σ hσ
        have hσB : σ ∈ onSet B n := hgB hσ
        have hinj : Set.InjOn (fun σ : Simp (TopCat.of X) n => f.comp σ) g.support := by
          intro σ₁ h₁ σ₂ h₂ he
          ext t
          have := congrArg (fun τ : C(Dl n, Z) => τ t) he
          have h := hemb.injective (a₁ := ⟨σ₁ t, hgB h₁ ⟨t, rfl⟩⟩) (a₂ := ⟨σ₂ t, hgB h₂ ⟨t, rfl⟩⟩)
            this
          exact congrArg Subtype.val h
        have hmem : f.comp σ ∈ (mapF K (TopCat.ofHom f) n g).support := by
          show f.comp σ ∈ (Finsupp.mapDomain (fun σ : Simp (TopCat.of X) n => f.comp σ) g).support
          rw [Finsupp.mapDomain_support_of_injOn g hinj]
          exact Finset.mem_image_of_mem _ hσ
        rintro _ ⟨t, rfl⟩
        exact (hA _ (hσB ⟨t, rfl⟩)).2 (hx hmem ⟨t, rfl⟩)
    · intro z
      induction z using Submodule.Quotient.induction_on with
      | H z =>
        obtain ⟨y, hy⟩ := z
        obtain ⟨g', rfl⟩ := (basEquiv K _ n).surjective y
        have hg' := (mem_chainSub_iff B' n _).1 hy
        rw [LinearEquiv.symm_apply_apply] at hg'
        have hlift : g' ∈ (Finsupp.supported K K (onSet B n)).map (mapF K (TopCat.ofHom f) n) := by
          rw [Finsupp.supported_eq_span_single] at hg'
          refine (Submodule.span_le.2 ?_) hg'
          rintro _ ⟨σ', hσ', rfl⟩
          have hc : ∀ t, ∃ x ∈ B, f x = σ' t := fun t => hsurj _ (hσ' ⟨t, rfl⟩)
          let τ : Dl n → B := fun t => ⟨(hc t).choose, (hc t).choose_spec.1⟩
          have hτ : Continuous τ := by
            rw [hemb.continuous_iff]
            convert σ'.continuous using 1
            funext t
            exact (hc t).choose_spec.2
          let σ : Simp (TopCat.of X) n := ⟨fun t => (τ t : X), continuous_subtype_val.comp hτ⟩
          refine ⟨Finsupp.single σ 1, Finsupp.single_mem_supported K _ ?_, ?_⟩
          · rintro _ ⟨t, rfl⟩
            exact (τ t).2
          · show Finsupp.mapDomain _ (Finsupp.single σ 1) = _
            rw [Finsupp.mapDomain_single]
            congr 1
            ext t
            exact (hc t).choose_spec.2
        obtain ⟨g, hg, hgg⟩ := hlift
        have hgmem : basEquiv K _ n g ∈ (chainSub K B).S n := by
          rw [mem_chainSub_iff, LinearEquiv.symm_apply_apply]
          exact hg
        refine ⟨Submodule.Quotient.mk ⟨_, hgmem⟩, ?_⟩
        rw [relMapGenF_mk]
        congr 1
        apply Subtype.ext
        change (((singFunctor K).map (TopCat.ofHom f)).f n).hom (bas K _ n g) = bas K _ n g'
        rw [bas_map, hgg]

/-- A map restricting to an embedding of `B` onto `B'`, with `A ∩ B = B ∩ f⁻¹(A')`, induces
isomorphisms `H_*(B, A) ≅ H_*(B', A')`. -/
theorem singMap_bijective (f : C(X, Z)) {B A : Set X} {B' A' : Set Z} (hB : MapsTo f B B')
    (hsurj : ∀ y ∈ B', ∃ x ∈ B, f x = y) (hemb : IsEmbedding (B.restrict f))
    (hA : ∀ x ∈ B, x ∈ A ↔ f x ∈ A') (k : ℤ) :
    Function.Bijective (singMap K f hB (fun x hx h => (hA x hx).1 h) k).hom := by
  cases k with
  | negSucc m => exact bijective_of_subsingleton _
  | ofNat n =>
    exact homologyMap_bijective_of_bijective _
      (fun n => singMapF_bijective K f hB hsurj hemb hA n) n

end Maps

/-! ### Absolute chains of a subset -/

section Abs

variable (K) {X : Type u} [TopologicalSpace X]

theorem chainSub_empty {n : ℕ} {x : CX K (TopCat.of X) n} (hx : x ∈ (chainSub K (∅ : Set X)).S n) :
    x = 0 := by
  rw [mem_chainSub_iff] at hx
  have he : onSet (∅ : Set X) n = ∅ := by
    ext σ
    simp only [onSet, mem_ofPred_eq, subset_empty_iff, range_eq_empty_iff, mem_empty_iff_false,
      iff_false, not_isEmpty_iff]
    exact ⟨vert n 0⟩
  rw [he, Finsupp.supported_empty, Submodule.mem_bot] at hx
  rw [← (basEquiv K _ n).apply_symm_apply x, hx, map_zero]

/-- The singular chains of `B ⊆ X`, as the relative complex `S(B)/S(∅)` in `X`. -/
noncomputable def toRel (B : Set X) :
    (singFunctor K).obj (TopCat.of B) ⟶ relCx _ (chainSub K B) (chainSub K (∅ : Set X)) where
  f n := ModuleCat.ofHom ((relSub (chainSub K B) (chainSub K ∅) n).mkQ ∘ₗ
    (((singFunctor K).map (subsetι B)).f n).hom.rangeRestrict)
  comm' i j _ := by
    ext x
    change relD _ _ i j (Submodule.Quotient.mk _) = Submodule.Quotient.mk _
    rw [relD_mk]
    congr 1
    apply Subtype.ext
    exact congrArg (fun ψ => ψ.hom x) (((singFunctor K).map (subsetι B)).comm i j)

theorem toRel_bijective (B : Set X) (n : ℕ) :
    Function.Bijective (HomologicalComplex.homologyMap (toRel K B) n).hom := by
  refine homologyMap_bijective_of_bijective _ (fun n => ⟨?_, ?_⟩) n
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    change Submodule.Quotient.mk _ = 0 at hx
    rw [Submodule.Quotient.mk_eq_zero] at hx
    have h0 := chainSub_empty K hx
    exact chainMap_injective K B n (h0.trans (map_zero _).symm)
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨_, x, rfl⟩ := y
      exact ⟨x, rfl⟩

theorem toRel_natural {Y W : Set X} (h : Y ⊆ W) :
    (singFunctor K).map (subsetIncl h) ≫ toRel K W =
      toRel K Y ≫ relMap _ (chainSub_mono K h) (chainSub_mono K (subset_refl ∅)) := by
  have e : (singFunctor K).map (subsetIncl h) ≫ (singFunctor K).map (subsetι W) =
      (singFunctor K).map (subsetι Y) := by
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  ext n x
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  exact congrArg (fun φ : (singFunctor K).obj (TopCat.of Y) ⟶ (singFunctor K).obj (TopCat.of X) =>
    (φ.f n).hom x) e

theorem hMap_comp_apply {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) (a : absH K X n) :
    (hMap K g n).hom ((hMap K f n).hom a) = (hMap K (g.comp f) n).hom a := by
  rw [hMap_comp]
  rfl

theorem hMap_id_apply {X : Type u} [TopologicalSpace X] (n : ℕ) (a : absH K X n) :
    (hMap K (ContinuousMap.id X) n).hom a = a := by
  rw [hMap_id]
  rfl

/-- The inclusion `Y → W` as a continuous map. -/
def inclC {Y W : Set X} (h : Y ⊆ W) : C(Y, W) := ⟨inclusion h, continuous_inclusion h⟩

/-- `H_n(B) → H_n(B, ∅)`, with `B ⊆ X` and `H_n(B, ∅)` computed in `X`. -/
noncomputable def toRelH (B : Set X) (n : ℕ) : absH K B n ⟶ singH K X (Int.ofNat n) B ∅ :=
  HomologicalComplex.homologyMap (toRel K B) n

theorem toRelH_bijective (B : Set X) (n : ℕ) : Function.Bijective (toRelH K B n).hom :=
  toRel_bijective K B n

theorem singIncl_comp_toRelH {Y W : Set X} (h : Y ⊆ W) (n : ℕ) :
    toRelH K Y n ≫ singIncl K (Int.ofNat n) h (subset_refl (∅ : Set X)) =
      hMap K (inclC h) n ≫ toRelH K W n := by
  have e := congrArg (fun φ => HomologicalComplex.homologyMap φ n) (toRel_natural K h)
  simp only [HomologicalComplex.homologyMap_comp] at e
  exact e.symm

theorem singIncl_toRelH_apply {Y W : Set X} (h : Y ⊆ W) (n : ℕ) (a : absH K Y n) :
    (singIncl K (Int.ofNat n) h (subset_refl (∅ : Set X))).hom ((toRelH K Y n).hom a) =
      (toRelH K W n).hom ((hMap K (inclC h) n).hom a) :=
  congrArg (fun φ => φ.hom a) (singIncl_comp_toRelH K h n)

theorem singIncl_bijective_of_hMap {Y W : Set X} (h : Y ⊆ W)
    (hb : ∀ n, Function.Bijective (hMap K (inclC h) n).hom) (k : ℤ) :
    Function.Bijective (singIncl K k h (subset_refl (∅ : Set X))).hom := by
  cases k with
  | negSucc m => exact bijective_of_subsingleton _
  | ofNat n =>
    have hc : Function.Bijective ((singIncl K (Int.ofNat n) h (subset_refl (∅ : Set X))).hom ∘
        (toRelH K Y n).hom) := by
      have : (singIncl K (Int.ofNat n) h (subset_refl (∅ : Set X))).hom ∘ (toRelH K Y n).hom =
          (toRelH K W n).hom ∘ (hMap K (inclC h) n).hom :=
        funext (singIncl_toRelH_apply K h n)
      rw [this]
      exact (toRelH_bijective K W n).comp (hb n)
    exact (Function.Bijective.of_comp_iff _ (toRelH_bijective K Y n)).1 hc

end Abs

/-! ### Exact sequences -/

section Les

variable (K) {X : Type u} [TopologicalSpace X]

theorem exists_succ (k : ℤ) : ∃ k', k = k' + 1 := ⟨k - 1, by ring⟩

/-- If `H_*(Y) → H_*(W)` is an isomorphism, then `H_*(W, Y) = 0`. -/
theorem singH_subsingleton_of_bijective {Y W : Set X} (h : Y ⊆ W)
    (hb : ∀ k, Function.Bijective (singIncl K k h (subset_refl (∅ : Set X))).hom) (k : ℤ) :
    Subsingleton (singH K X k W Y) := by
  obtain ⟨k, rfl⟩ := exists_succ k
  have hz : ∀ y : singH K X (k + 1) W Y, y = 0 := by
    intro y
    have h1 := sing_exact_δ' K k (empty_subset Y) h
    have h2 := sing_exact_δ K k (empty_subset Y) h
    have h3 := sing_exact_incl K (k + 1) (empty_subset Y) h
    have hδ : (singδ K k W Y ∅).hom y = 0 := by
      apply (hb k).1
      rw [map_zero]
      exact (h1 _).2 ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := (h2 y).1 hδ
    obtain ⟨w, rfl⟩ := (hb (k + 1)).2 z
    exact (h3 _).2 ⟨w, rfl⟩
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- If `W` deforms into `Y` inside `W`, keeping `Y` in `Y`, then `H_*(W, Y) = 0`. -/
theorem singH_subsingleton_of_deform {Y W : Set X} (h : Y ⊆ W)
    (H : C(unitInterval × W, W)) (h0 : ∀ x : W, H (0, x) = x) (h1 : ∀ x : W, (H (1, x) : X) ∈ Y)
    (hY : ∀ (s : unitInterval) (x : W), (x : X) ∈ Y → (H (s, x) : X) ∈ Y) (k : ℤ) :
    Subsingleton (singH K X k W Y) := by
  refine singH_subsingleton_of_bijective K h (singIncl_bijective_of_hMap K h fun n => ?_) k
  let r : C(W, Y) := ⟨fun x => ⟨H (1, x), h1 x⟩, by fun_prop⟩
  have hW : (ContinuousMap.id W).Homotopic ((inclC h).comp r) :=
    ⟨{ toFun := H
       continuous_toFun := H.continuous
       map_zero_left := h0
       map_one_left := fun x => rfl }⟩
  have hYY : (ContinuousMap.id Y).Homotopic (r.comp (inclC h)) :=
    ⟨{ toFun := fun p => ⟨H (p.1, inclC h p.2), hY _ _ p.2.2⟩
       continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp
         (H.continuous.comp (continuous_fst.prodMk ((inclC h).continuous.comp continuous_snd)))) _
       map_zero_left := fun x => Subtype.ext (by
         show (H (0, inclC h x) : X) = x
         rw [h0]
         rfl)
       map_one_left := fun x => rfl }⟩
  refine ⟨fun a b hab => ?_, fun y => ⟨(hMap K r n).hom y, ?_⟩⟩
  · have := congrArg (hMap K r n).hom hab
    rwa [hMap_comp_apply, hMap_comp_apply, ← hMap_congr K hYY, hMap_id_apply,
      hMap_id_apply] at this
  · rw [hMap_comp_apply, ← hMap_congr K hW, hMap_id_apply]

/-- If `H_*(V, L) = 0`, then `H_*(N, L) ≅ H_*(N, V)`. -/
theorem singIncl_bijective_of_subsingleton {N V L : Set X} (hLV : L ⊆ V) (hVN : V ⊆ N)
    (hs : ∀ k, Subsingleton (singH K X k V L)) (k : ℤ) :
    Function.Bijective (singIncl K k (subset_refl N) hLV).hom := by
  obtain ⟨k, rfl⟩ := exists_succ k
  have := hs (k + 1)
  have := hs k
  exact bijective_of_exact_of_subsingleton (sing_exact_incl K (k + 1) hLV hVN)
    (sing_exact_δ K k hLV hVN)

end Les

/-! ### Reduced homology -/

section Reduced

variable (K) {X : Type u} [TopologicalSpace X] (x₀ : X)

/-- `{x₀} → X` restricted to the image, as a map from the point. -/
def ptC : C(PUnit.{u + 1}, ({x₀} : Set X)) := ContinuousMap.const _ ⟨x₀, rfl⟩

theorem hMap_ptC_surjective (n : ℕ) : Function.Surjective (hMap K (ptC x₀) n).hom := by
  let c : C(({x₀} : Set X), PUnit.{u + 1}) := ContinuousMap.const _ PUnit.unit
  have e : (ptC x₀).comp c = ContinuousMap.id _ := by
    ext ⟨y, hy⟩
    exact hy.symm
  intro y
  refine ⟨(hMap K c n).hom y, ?_⟩
  rw [hMap_comp_apply, e, hMap_id_apply]

theorem hMap_inclC_point_injective (n : ℕ) :
    Function.Injective (hMap K (inclC (subset_univ ({x₀} : Set X))) n).hom := by
  let r : C((univ : Set X), ({x₀} : Set X)) := ContinuousMap.const _ ⟨x₀, rfl⟩
  have e : r.comp (inclC (subset_univ ({x₀} : Set X))) = ContinuousMap.id _ := by
    ext ⟨y, hy⟩
    exact hy.symm
  intro a b hab
  have := congrArg (hMap K r n).hom hab
  rwa [hMap_comp_apply, hMap_comp_apply, e, hMap_id_apply, hMap_id_apply] at this

theorem singIncl_point_injective (k : ℤ) :
    Function.Injective (singIncl K k (subset_univ ({x₀} : Set X))
      (subset_refl (∅ : Set X))).hom := by
  cases k with
  | negSucc m => exact fun _ _ _ => Subsingleton.elim _ _
  | ofNat n =>
    intro a b hab
    obtain ⟨a, rfl⟩ := (toRelH_bijective K _ n).2 a
    obtain ⟨b, rfl⟩ := (toRelH_bijective K _ n).2 b
    rw [singIncl_toRelH_apply, singIncl_toRelH_apply] at hab
    exact congrArg _ (hMap_inclC_point_injective K x₀ n ((toRelH_bijective K _ n).1 hab))

theorem singIncl_point_surjective (k : ℤ) :
    Function.Surjective (singIncl K k (subset_refl (univ : Set X))
      (empty_subset ({x₀} : Set X))).hom := by
  obtain ⟨k, rfl⟩ := exists_succ k
  intro y
  have hδ : (singδ K k univ {x₀} ∅).hom y = 0 := by
    apply singIncl_point_injective K x₀ k
    rw [map_zero]
    exact (sing_exact_δ' K k (empty_subset _) (subset_univ _) _).2 ⟨y, rfl⟩
  exact (sing_exact_δ K k (empty_subset _) (subset_univ _) y).1 hδ

/-- `X ≅ univ` as a continuous map. -/
def univC : C(X, (univ : Set X)) := ⟨fun x => ⟨x, trivial⟩, by fun_prop⟩

theorem hMap_univC_bijective (n : ℕ) : Function.Bijective (hMap K (univC (X := X)) n).hom := by
  let v : C((univ : Set X), X) := ⟨Subtype.val, continuous_subtype_val⟩
  have e1 : v.comp univC = ContinuousMap.id X := rfl
  have e2 : univC.comp v = ContinuousMap.id _ := rfl
  refine ⟨fun a b hab => ?_, fun y => ⟨(hMap K v n).hom y, ?_⟩⟩
  · have := congrArg (hMap K v n).hom hab
    rwa [hMap_comp_apply, hMap_comp_apply, e1, hMap_id_apply, hMap_id_apply] at this
  · rw [hMap_comp_apply, e2, hMap_id_apply]

/-- `H_n(X) → H_n(X, ∅)` in the ambient `X`. -/
noncomputable def absToRel (n : ℕ) : absH K X n →ₗ[K] singH K X (Int.ofNat n) univ ∅ :=
  (toRelH K (univ : Set X) n).hom ∘ₗ (hMap K univC n).hom

theorem absToRel_bijective (n : ℕ) : Function.Bijective (absToRel K (X := X) n) := by
  unfold absToRel
  rw [LinearMap.coe_comp]
  exact (toRelH_bijective K (univ : Set X) n).comp (hMap_univC_bijective K n)

theorem absToRel_ptMap (n : ℕ) (y : absH K PUnit.{u + 1} n) :
    absToRel K n ((hMap K (ptMap x₀) n).hom y) =
      (singIncl K (Int.ofNat n) (subset_univ ({x₀} : Set X)) (subset_refl (∅ : Set X))).hom
        ((toRelH K ({x₀} : Set X) n).hom ((hMap K (ptC x₀) n).hom y)) := by
  have e1 : univC.comp (ptMap x₀) = (inclC (subset_univ ({x₀} : Set X))).comp (ptC x₀) := rfl
  rw [singIncl_toRelH_apply]
  simp only [absToRel, LinearMap.comp_apply]
  rw [hMap_comp_apply, hMap_comp_apply, e1]

theorem ker_eq_range (n : ℕ) :
    LinearMap.ker ((singIncl K (Int.ofNat n) (subset_refl (univ : Set X))
      (empty_subset ({x₀} : Set X))).hom ∘ₗ absToRel K n) =
      LinearMap.range (hMap K (ptMap x₀) n).hom := by
  have hex := sing_exact_incl K (Int.ofNat n) (empty_subset ({x₀} : Set X)) (subset_univ _)
  ext x
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mem_range]
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := (hex _).1 hx
    obtain ⟨w, rfl⟩ := (toRelH_bijective K _ n).2 z
    obtain ⟨y, rfl⟩ := hMap_ptC_surjective K x₀ n w
    refine ⟨y, (absToRel_bijective K n).1 ?_⟩
    rw [absToRel_ptMap, hz]
  · rintro ⟨y, rfl⟩
    rw [absToRel_ptMap]
    exact (hex _).2 ⟨_, rfl⟩

/-- `H_n(X, {x₀}) ≅ H̃_n(X)`. -/
noncomputable def redHEquiv (n : ℕ) :
    redH K X x₀ n ≃ₗ[K] singH K X (Int.ofNat n) univ {x₀} :=
  (ModuleCat.cokernelIsoRangeQuotient (hMap K (ptMap x₀) n)).toLinearEquiv.trans
    ((Submodule.quotEquivOfEq _ _ (ker_eq_range K x₀ n).symm).trans
      (LinearMap.quotKerEquivOfSurjective _
        ((singIncl_point_surjective K x₀ (Int.ofNat n)).comp (absToRel_bijective K n).2)))

end Reduced

end ConleyCheck.Conley
