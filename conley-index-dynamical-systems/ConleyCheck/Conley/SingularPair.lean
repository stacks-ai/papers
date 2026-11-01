import ConleyCheck.Conley.Homology

/-!
# Relative singular homology

For a chain complex `C` of `K`-modules, a subcomplex is a family of submodules stable under the
differential. For subcomplexes `P` and `Q`, `relCx C Q P` is the quotient complex
`Q / (Q ∩ P)`. If `P ≤ Q ≤ R`, then `0 → Q/P → R/P → R/Q → 0` is a short exact sequence of
complexes (third isomorphism theorem in each degree), so the homology sequence of a short exact
sequence gives the exact sequence of the triple.

Taking for `C` the singular chain complex of `α` and, for `A ⊆ α`, the image of the singular chains
of `A`, gives `singularPairHomology : PairHomology K α`, namely singular homology of pairs of
subsets of `α` with the exact sequence of every triple `L ⊆ M ⊆ N`. The singular chains of `A`
embed injectively (`chainSubEquiv`), so for `L ⊆ N` this is the usual `H_*(C(N) / C(L))`.
-/

namespace ConleyCheck.Conley

open CategoryTheory Limits Set

universe u

variable {K : Type u} [Ring K]

/-! ### Subcomplexes and relative complexes -/

section Rel

variable (C : ChainComplex (ModuleCat.{u} K) ℕ)

/-- A subcomplex of `C`, namely submodules stable under the differential. -/
structure SubCx where
  S : ∀ n, Submodule K (C.X n)
  stable : ∀ i j, ∀ x ∈ S i, (C.d i j).hom x ∈ S j

variable {C}

/-- `Q ∩ P`, as a submodule of `Q`. -/
def relSub (Q P : SubCx C) (n : ℕ) : Submodule K (Q.S n) := (P.S n).comap (Q.S n).subtype

/-- The differential of `C` restricted to `Q`. -/
def subD (Q : SubCx C) (i j : ℕ) : Q.S i →ₗ[K] Q.S j :=
  (C.d i j).hom.restrict fun x hx => Q.stable i j x hx

/-- The differential of `Q / (Q ∩ P)`. -/
def relD (Q P : SubCx C) (i j : ℕ) : (Q.S i ⧸ relSub Q P i) →ₗ[K] (Q.S j ⧸ relSub Q P j) :=
  (relSub Q P i).mapQ (relSub Q P j) (subD Q i j) fun _ hx => P.stable i j _ hx

theorem relD_mk (Q P : SubCx C) (i j : ℕ) (x : Q.S i) :
    relD Q P i j (Submodule.Quotient.mk x) = Submodule.Quotient.mk (subD Q i j x) := rfl

variable (C) in
/-- The relative complex `Q / (Q ∩ P)`. -/
noncomputable def relCx (Q P : SubCx C) : ChainComplex (ModuleCat.{u} K) ℕ where
  X n := ModuleCat.of K (Q.S n ⧸ relSub Q P n)
  d i j := ModuleCat.ofHom (relD Q P i j)
  shape i j hij := by
    ext x
    show relD Q P i j (Submodule.Quotient.mk x) = 0
    rw [relD_mk, (Submodule.Quotient.mk_eq_zero _)]
    show (C.d i j).hom x.1 ∈ P.S j
    rw [C.shape i j hij]
    exact Submodule.zero_mem _
  d_comp_d' i j k _ _ := by
    ext x
    show relD Q P j k (relD Q P i j (Submodule.Quotient.mk x)) = 0
    rw [relD_mk, relD_mk, Submodule.Quotient.mk_eq_zero]
    show (C.d j k).hom ((C.d i j).hom x.1) ∈ P.S k
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, C.d_comp_d]
    exact Submodule.zero_mem _

/-- The map `Q/P → Q'/P'` for `Q ≤ Q'` and `P ≤ P'`. -/
def relMapF {Q Q' P P' : SubCx C} (hQ : ∀ n, Q.S n ≤ Q'.S n) (hP : ∀ n, P.S n ≤ P'.S n)
    (n : ℕ) : (Q.S n ⧸ relSub Q P n) →ₗ[K] (Q'.S n ⧸ relSub Q' P' n) :=
  (relSub Q P n).mapQ (relSub Q' P' n) (Submodule.inclusion (hQ n)) fun _ hx => hP n hx

theorem relMapF_mk {Q Q' P P' : SubCx C} (hQ : ∀ n, Q.S n ≤ Q'.S n) (hP : ∀ n, P.S n ≤ P'.S n)
    (n : ℕ) (x : Q.S n) :
    relMapF hQ hP n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Submodule.inclusion (hQ n) x) := rfl

variable (C) in
/-- The chain map `Q/P → Q'/P'` for `Q ≤ Q'` and `P ≤ P'`. -/
noncomputable def relMap {Q Q' P P' : SubCx C} (hQ : ∀ n, Q.S n ≤ Q'.S n)
    (hP : ∀ n, P.S n ≤ P'.S n) : relCx C Q P ⟶ relCx C Q' P' where
  f n := ModuleCat.ofHom (relMapF hQ hP n)
  comm' i j _ := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

variable (C) in
/-- The short complex `Q/P → R/P → R/Q` of a triple `P ≤ Q ≤ R`. -/
noncomputable def tripleSC {P Q R : SubCx C} (hPQ : ∀ n, P.S n ≤ Q.S n)
    (hQR : ∀ n, Q.S n ≤ R.S n) : ShortComplex (ChainComplex (ModuleCat.{u} K) ℕ) :=
  ShortComplex.mk (relMap C hQR fun _ => le_rfl) (relMap C (fun _ => le_rfl) hPQ) (by
    ext n x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      show relMapF (fun _ => le_rfl) hPQ n (relMapF hQR (fun _ => le_rfl) n
        (Submodule.Quotient.mk x)) = 0
      rw [relMapF_mk, relMapF_mk, Submodule.Quotient.mk_eq_zero]
      exact x.2)

theorem tripleSC_shortExact {P Q R : SubCx C} (hPQ : ∀ n, P.S n ≤ Q.S n)
    (hQR : ∀ n, Q.S n ≤ R.S n) : (tripleSC C hPQ hQR).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
  have hf : Function.Injective (relMapF (C := C) (P := P) (P' := P) hQR (fun _ => le_rfl) n) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [relMapF_mk, Submodule.Quotient.mk_eq_zero] at hx
      exact (Submodule.Quotient.mk_eq_zero _).2 hx
  have hg : Function.Surjective (relMapF (C := C) (Q := R) (Q' := R) (fun _ => le_rfl) hPQ n) := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H y => exact ⟨Submodule.Quotient.mk y, rfl⟩
  refine ShortComplex.ShortExact.mk' ?_ ((ModuleCat.mono_iff_injective _).2 hf)
    ((ModuleCat.epi_iff_surjective _).2 hg)
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    have hx' : relMapF (C := C) (Q := R) (Q' := R) (fun _ => le_rfl) hPQ n
        (Submodule.Quotient.mk x) = 0 := hx
    rw [relMapF_mk, Submodule.Quotient.mk_eq_zero] at hx'
    exact ⟨Submodule.Quotient.mk ⟨x.1, hx'⟩, rfl⟩

end Rel

/-! ### Singular chains of subsets -/

section Singular

variable (K) {α : Type u} [TopologicalSpace α]

/-- The singular chain functor with coefficients in `K`. -/
noncomputable abbrev singFunctor : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} K) ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} K)).obj (ModuleCat.of K K)

/-- The inclusion `A → α` in `TopCat`. -/
def subsetι (A : Set α) : TopCat.of A ⟶ TopCat.of α :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion `A → B` in `TopCat`. -/
def subsetIncl {A B : Set α} (h : A ⊆ B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨Set.inclusion h, continuous_inclusion h⟩

/-- The image of the singular chains of `A` in the singular chains of `α`. -/
noncomputable def chainSub (A : Set α) : SubCx ((singFunctor K).obj (TopCat.of α)) where
  S n := LinearMap.range (((singFunctor K).map (subsetι A)).f n).hom
  stable i j x := by
    rintro ⟨y, rfl⟩
    exact ⟨(((singFunctor K).obj (TopCat.of A)).d i j).hom y,
      (congrArg (fun φ => φ.hom y) (((singFunctor K).map (subsetι A)).comm i j)).symm⟩

theorem chainSub_mono {A B : Set α} (h : A ⊆ B) (n : ℕ) :
    (chainSub K A).S n ≤ (chainSub K B).S n := by
  rintro _ ⟨y, rfl⟩
  have e : (singFunctor K).map (subsetIncl h) ≫ (singFunctor K).map (subsetι B) =
      (singFunctor K).map (subsetι A) := by
    rw [← Functor.map_comp]
    rfl
  exact ⟨(((singFunctor K).map (subsetIncl h)).f n).hom y,
    congrArg (fun φ : (singFunctor K).obj (TopCat.of A) ⟶ (singFunctor K).obj (TopCat.of α) =>
      (φ.f n).hom y) e⟩

theorem chainMap_injective (A : Set α) (n : ℕ) :
    Function.Injective (((singFunctor K).map (subsetι A)).f n).hom := by
  have : Mono (subsetι A) := (TopCat.mono_iff_injective _).2 Subtype.val_injective
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

/-- `chainSub K A` is a copy of the singular chains of `A`. -/
noncomputable def chainSubEquiv (A : Set α) (n : ℕ) :
    ((singFunctor K).obj (TopCat.of A)).X n ≃ₗ[K] (chainSub K A).S n :=
  LinearEquiv.ofInjective _ (chainMap_injective K A n)

variable (α)

/-- `H_k(N, L)`, the homology of `C(N) / (C(N) ∩ C(L))`, zero in negative degrees. -/
noncomputable def singH : ℤ → Set α → Set α → ModuleCat.{u} K
  | .ofNat n, N, L => (relCx _ (chainSub K N) (chainSub K L)).homology n
  | .negSucc _, _, _ => ModuleCat.of K PUnit

variable {α}

/-- The map induced by an inclusion of pairs. -/
noncomputable def singIncl (k : ℤ) {N L N' L' : Set α} (hN : N ⊆ N') (hL : L ⊆ L') :
    singH K α k N L ⟶ singH K α k N' L' :=
  match k with
  | .ofNat n => HomologicalComplex.homologyMap
      (relMap _ (chainSub_mono K hN) (chainSub_mono K hL)) n
  | .negSucc _ => 0

open scoped Classical in
/-- The connecting map of the triple `L ⊆ M ⊆ N`, and `0` otherwise. -/
noncomputable def singδ (k : ℤ) (N M L : Set α) : singH K α (k + 1) N M ⟶ singH K α k M L :=
  match k with
  | .ofNat n => if h : L ⊆ M ∧ M ⊆ N then
      (tripleSC_shortExact (chainSub_mono K h.1) (chainSub_mono K h.2)).δ (n + 1) n rfl
    else 0
  | .negSucc _ => 0

theorem singδ_ofNat (n : ℕ) {N M L : Set α} (h : L ⊆ M ∧ M ⊆ N) :
    singδ K (Int.ofNat n) N M L =
      (tripleSC_shortExact (chainSub_mono K h.1) (chainSub_mono K h.2)).δ (n + 1) n rfl := by
  unfold singδ
  exact dite_eq_left h

end Singular

/-! ### Exactness -/

section Exactness

variable (K) {α : Type u} [TopologicalSpace α]

theorem exact_of_shortComplex {S : ShortComplex (ModuleCat.{u} K)} (h : S.Exact) :
    Function.Exact S.f.hom S.g.hom :=
  LinearMap.exact_iff.2 ((ShortComplex.moduleCat_exact_iff_range_eq_ker S).1 h).symm

theorem exact_of_subsingleton {A B D : ModuleCat.{u} K} (f : A ⟶ B) (g : B ⟶ D)
    [Subsingleton B] : Function.Exact f.hom g.hom := by
  intro y
  constructor
  · intro _
    exact ⟨0, Subsingleton.elim _ _⟩
  · rintro -
    rw [Subsingleton.elim y 0, map_zero]

instance (n : ℕ) (N L : Set α) : Subsingleton (singH K α (Int.negSucc n) N L) :=
  inferInstanceAs (Subsingleton PUnit)

theorem sing_exact_incl (k : ℤ) {N M L : Set α} (hLM : L ⊆ M) (hMN : M ⊆ N) :
    Function.Exact (singIncl K k hMN (subset_refl L)).hom
      (singIncl K k (subset_refl N) hLM).hom := by
  cases k with
  | ofNat n =>
    exact exact_of_shortComplex K
      ((tripleSC_shortExact (chainSub_mono K hLM) (chainSub_mono K hMN)).homology_exact₂ n)
  | negSucc m => exact exact_of_subsingleton K _ _

theorem sing_exact_δ (k : ℤ) {N M L : Set α} (hLM : L ⊆ M) (hMN : M ⊆ N) :
    Function.Exact (singIncl K (k + 1) (subset_refl N) hLM).hom (singδ K k N M L).hom := by
  cases k with
  | ofNat n =>
    rw [singδ_ofNat K n ⟨hLM, hMN⟩]
    exact exact_of_shortComplex K
      ((tripleSC_shortExact (chainSub_mono K hLM) (chainSub_mono K hMN)).homology_exact₃
        (n + 1) n rfl)
  | negSucc m =>
    cases m with
    | zero =>
      let S := tripleSC _ (chainSub_mono K hLM) (chainSub_mono K hMN)
      have hg : Function.Surjective (S.g.f 0).hom := by
        intro y
        induction y using Submodule.Quotient.induction_on with
        | H y => exact ⟨Submodule.Quotient.mk y, rfl⟩
      have : Epi (S.g.f 0) := (ModuleCat.epi_iff_surjective _).2 hg
      have hepi := HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0
        fun j (hj : j + 1 = 0) => Nat.succ_ne_zero j hj
      have hs : Function.Surjective (HomologicalComplex.homologyMap S.g 0).hom :=
        (ModuleCat.epi_iff_surjective _).1 hepi
      intro y
      constructor
      · intro _
        exact hs y
      · rintro -
        exact Subsingleton.elim _ _
    | succ m =>
      have : Subsingleton (singH K α (Int.negSucc (m + 1) + 1) N M) :=
        inferInstanceAs (Subsingleton (singH K α (Int.negSucc m) N M))
      exact exact_of_subsingleton K _ _

theorem sing_exact_δ' (k : ℤ) {N M L : Set α} (hLM : L ⊆ M) (hMN : M ⊆ N) :
    Function.Exact (singδ K k N M L).hom (singIncl K k hMN (subset_refl L)).hom := by
  cases k with
  | ofNat n =>
    rw [singδ_ofNat K n ⟨hLM, hMN⟩]
    exact exact_of_shortComplex K
      ((tripleSC_shortExact (chainSub_mono K hLM) (chainSub_mono K hMN)).homology_exact₁
        (n + 1) n rfl)
  | negSucc m => exact exact_of_subsingleton K _ _

variable (α)

/-- Relative singular homology with coefficients in `K`, as a `PairHomology`. -/
noncomputable def singularPairHomology : PairHomology.{u, u, u} K α where
  H := singH K α
  incl k _ _ _ _ hN hL := singIncl K k hN hL
  δ := singδ K
  exact_incl k _ _ _ hLM hMN := sing_exact_incl K k hLM hMN
  exact_δ k _ _ _ hLM hMN := sing_exact_δ K k hLM hMN
  exact_δ' k _ _ _ hLM hMN := sing_exact_δ' K k hLM hMN

end Exactness

end ConleyCheck.Conley
