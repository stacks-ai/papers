import ConleyCheck.Conley.Deform
import ConleyCheck.Conley.PairFunctor

/-!
# Naturality of the exact sequence, homotopy invariance of pairs, and the reflection sign

* `singδ_natural`: the connecting map of a triple commutes with the maps induced by continuous maps
  of triples.
* `singMap_bijective_of_abs`: a map of pairs inducing isomorphisms on the absolute homology of both
  members induces isomorphisms on relative homology (five lemma).
* `singMap_eq_of_homotopy`: homotopic maps of pairs induce the same map on relative homology.
* `cylRefl_neg`: the reflection `(x, t) ↦ (x, 1 - t)` acts by `-1` on
  `H_*(N × [0, 1], L × [0, 1] ∪ N × {0, 1})`. The proof splits `H_*(∂, L × [0, 1])` along the two
  ends by excision and uses that the reflection is homotopic to the identity on
  `(N × [0, 1], L × [0, 1])`.
-/

namespace ConleyCheck.Conley

open CategoryTheory Set Topology unitInterval

universe u

/-! ### The five lemma -/

section Five

variable {R : Type*} [Ring R] {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : Type*} [AddCommGroup A₁]
  [AddCommGroup A₂] [AddCommGroup A₃] [AddCommGroup A₄] [AddCommGroup A₅] [AddCommGroup B₁]
  [AddCommGroup B₂] [AddCommGroup B₃] [AddCommGroup B₄] [AddCommGroup B₅] [Module R A₁]
  [Module R A₂] [Module R A₃] [Module R A₄] [Module R A₅] [Module R B₁] [Module R B₂]
  [Module R B₃] [Module R B₄] [Module R B₅]

/-- The five lemma for modules. -/
theorem five_bijective {f₁ : A₁ →ₗ[R] A₂} {f₂ : A₂ →ₗ[R] A₃} {f₃ : A₃ →ₗ[R] A₄}
    {f₄ : A₄ →ₗ[R] A₅} {g₁ : B₁ →ₗ[R] B₂} {g₂ : B₂ →ₗ[R] B₃} {g₃ : B₃ →ₗ[R] B₄}
    {g₄ : B₄ →ₗ[R] B₅} {v₁ : A₁ →ₗ[R] B₁} {v₂ : A₂ →ₗ[R] B₂} {v₃ : A₃ →ₗ[R] B₃}
    {v₄ : A₄ →ₗ[R] B₄} {v₅ : A₅ →ₗ[R] B₅} (hf₂ : Function.Exact f₁ f₂)
    (hf₃ : Function.Exact f₂ f₃) (hf₄ : Function.Exact f₃ f₄) (hg₂ : Function.Exact g₁ g₂)
    (hg₃ : Function.Exact g₂ g₃) (hg₄ : Function.Exact g₃ g₄)
    (c₁ : ∀ x, g₁ (v₁ x) = v₂ (f₁ x)) (c₂ : ∀ x, g₂ (v₂ x) = v₃ (f₂ x))
    (c₃ : ∀ x, g₃ (v₃ x) = v₄ (f₃ x)) (c₄ : ∀ x, g₄ (v₄ x) = v₅ (f₄ x))
    (hv₁ : Function.Surjective v₁) (hv₂ : Function.Bijective v₂) (hv₄ : Function.Bijective v₄)
    (hv₅ : Function.Injective v₅) : Function.Bijective v₃ := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h4 : f₃ x = 0 := hv₄.1 (by rw [← c₃, hx, map_zero, map_zero])
    obtain ⟨y, rfl⟩ := (hf₃ x).1 h4
    have h3 : g₂ (v₂ y) = 0 := by rw [c₂, hx]
    obtain ⟨z, hz⟩ := (hg₂ _).1 h3
    obtain ⟨w, rfl⟩ := hv₁ z
    rw [c₁] at hz
    rw [← hv₂.1 hz]
    exact (hf₂ _).2 ⟨w, rfl⟩
  · intro y
    obtain ⟨a, ha⟩ := hv₄.2 (g₃ y)
    have h5 : f₄ a = 0 := hv₅ (by rw [← c₄, ha, map_zero]; exact (hg₄ _).2 ⟨y, rfl⟩)
    obtain ⟨x, rfl⟩ := (hf₄ a).1 h5
    have h3 : g₃ (y - v₃ x) = 0 := by rw [map_sub, c₃, ha, sub_self]
    obtain ⟨b, hb⟩ := (hg₃ _).1 h3
    obtain ⟨c, rfl⟩ := hv₂.2 b
    refine ⟨x + f₂ c, ?_⟩
    rw [map_add, ← c₂, hb, add_sub_cancel]

end Five

/-! ### Naturality of the connecting map -/

section Natural

variable (K : Type u) [Ring K] {X Z : Type u} [TopologicalSpace X] [TopologicalSpace Z]

/-- The morphism of the short exact sequences of two triples induced by a map of triples. -/
noncomputable def tripleMap (f : C(X, Z)) {N M L : Set X} {N' M' L' : Set Z} (hLM : L ⊆ M)
    (hMN : M ⊆ N) (hLM' : L' ⊆ M') (hMN' : M' ⊆ N') (hN : MapsTo f N N') (hM : MapsTo f M M')
    (hL : MapsTo f L L') :
    tripleSC _ (chainSub_mono K hLM) (chainSub_mono K hMN) ⟶
      tripleSC _ (chainSub_mono K hLM') (chainSub_mono K hMN') where
  τ₁ := relMapGen ((singFunctor K).map (TopCat.ofHom f)) (fun n x hx => sing_map_mem K f hM n x hx)
    (fun n x hx hx' => sing_map_mem' K f (fun x _ h => hL h) n x hx hx')
  τ₂ := relMapGen ((singFunctor K).map (TopCat.ofHom f)) (fun n x hx => sing_map_mem K f hN n x hx)
    (fun n x hx hx' => sing_map_mem' K f (fun x _ h => hL h) n x hx hx')
  τ₃ := relMapGen ((singFunctor K).map (TopCat.ofHom f)) (fun n x hx => sing_map_mem K f hN n x hx)
    (fun n x hx hx' => sing_map_mem' K f (fun x _ h => hM h) n x hx hx')
  comm₁₂ := by
    ext n x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl
  comm₂₃ := by
    ext n x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

/-- The connecting map of a triple is natural under continuous maps of triples. -/
theorem singδ_natural (f : C(X, Z)) {N M L : Set X} {N' M' L' : Set Z} (hLM : L ⊆ M)
    (hMN : M ⊆ N) (hLM' : L' ⊆ M') (hMN' : M' ⊆ N') (hN : MapsTo f N N') (hM : MapsTo f M M')
    (hL : MapsTo f L L') (k : ℤ) :
    singδ K k N M L ≫ singMap K f hM (fun _ _ h => hL h) k =
      singMap K f hN (fun _ _ h => hM h) (k + 1) ≫ singδ K k N' M' L' := by
  cases k with
  | negSucc m =>
    ext x
    exact Subsingleton.elim _ _
  | ofNat n =>
    rw [singδ_ofNat K n ⟨hLM, hMN⟩, singδ_ofNat K n ⟨hLM', hMN'⟩]
    exact HomologicalComplex.HomologySequence.δ_naturality
      (tripleMap K f hLM hMN hLM' hMN' hN hM hL) _ _ (n + 1) n rfl

theorem singδ_natural_apply (f : C(X, Z)) {N M L : Set X} {N' M' L' : Set Z} (hLM : L ⊆ M)
    (hMN : M ⊆ N) (hLM' : L' ⊆ M') (hMN' : M' ⊆ N') (hN : MapsTo f N N') (hM : MapsTo f M M')
    (hL : MapsTo f L L') (k : ℤ) (z : singH K X (k + 1) N M) :
    (singMap K f hM (fun _ _ h => hL h) k).hom ((singδ K k N M L).hom z) =
      (singδ K k N' M' L').hom ((singMap K f hN (fun _ _ h => hM h) (k + 1)).hom z) :=
  congrArg (fun φ => φ.hom z) (singδ_natural K f hLM hMN hLM' hMN' hN hM hL k)

theorem singMap_id (k : ℤ) {B A : Set X} :
    singMap K (ContinuousMap.id X) (B := B) (A := A) (B' := B) (A' := A) (mapsTo_id B)
      (fun _ _ h => h) k = 𝟙 _ := by
  cases k with
  | negSucc m =>
    ext x
    exact Subsingleton.elim _ _
  | ofNat n =>
    refine (congrArg (fun φ => HomologicalComplex.homologyMap φ n) ?_).trans
      (HomologicalComplex.homologyMap_id _ n)
    ext m x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      apply Subtype.ext
      change (((singFunctor K).map (TopCat.ofHom (ContinuousMap.id X))).f m).hom x.1 = x.1
      rw [TopCat.ofHom_id, CategoryTheory.Functor.map_id]
      rfl

theorem singMap_id_apply (k : ℤ) {B A : Set X} (z : singH K X k B A) :
    (singMap K (ContinuousMap.id X) (B := B) (A := A) (B' := B) (A' := A) (mapsTo_id B)
      (fun _ _ h => h) k).hom z = z := by
  rw [singMap_id]
  rfl

theorem singMap_singIncl (f : C(X, Z)) {B A : Set X} {B' A' B'' A'' : Set Z} (hB : MapsTo f B B')
    (hA : ∀ x ∈ B, x ∈ A → f x ∈ A') (hB' : B' ⊆ B'') (hA' : A' ⊆ A'') (k : ℤ) :
    singMap K f hB hA k ≫ singIncl K k hB' hA' =
      singMap K f (hB.mono_right hB') (fun x hx h => hA' (hA x hx h)) k := by
  rw [singIncl_eq_singMap]
  exact singMap_comp K _ _ _ _ _ _ k

theorem singIncl_singMap (f : C(X, Z)) {B₀ A₀ B A : Set X} {B' A' : Set Z} (hB₀ : B₀ ⊆ B)
    (hA₀ : A₀ ⊆ A) (hB : MapsTo f B B') (hA : ∀ x ∈ B, x ∈ A → f x ∈ A') (k : ℤ) :
    singIncl K k hB₀ hA₀ ≫ singMap K f hB hA k =
      singMap K f (hB.mono_left hB₀) (fun x hx h => hA x (hB₀ hx) (hA₀ h)) k := by
  rw [singIncl_eq_singMap]
  exact singMap_comp K _ _ _ _ _ _ k

end Natural

/-! ### The five lemma for pairs -/

section Abs

variable (K : Type u) [Ring K] {X Z : Type u} [TopologicalSpace X] [TopologicalSpace Z]

theorem singMap_abs_bijective (f : C(X, Z)) {B : Set X} {B' : Set Z} (hB : MapsTo f B B')
    (hb : ∀ n, Function.Bijective (hMap K (restrictC f hB) n).hom) (k : ℤ) :
    Function.Bijective
      (singMap K f hB (A := ∅) (A' := ∅) (fun x _ hx => absurd hx (notMem_empty x)) k).hom := by
  cases k with
  | negSucc m => exact bijective_of_subsingleton _
  | ofNat n =>
    have hc : (singMap K f hB (A := ∅) (A' := ∅) (fun x _ hx => absurd hx (notMem_empty x))
        (Int.ofNat n)).hom ∘
        (toRelH K B n).hom = (toRelH K B' n).hom ∘ (hMap K (restrictC f hB) n).hom :=
      funext fun a => congrArg (fun φ => φ.hom a) (toRel_singMap K f hB n)
    have : Function.Bijective
        ((singMap K f hB (A := ∅) (A' := ∅) (fun x _ hx => absurd hx (notMem_empty x))
          (Int.ofNat n)).hom ∘ (toRelH K B n).hom) := by
      rw [hc]
      exact (toRelH_bijective K B' n).comp (hb n)
    exact (Function.Bijective.of_comp_iff _ (toRelH_bijective K B n)).1 this

/-- A map of pairs `(B, A) → (B', A')` that induces isomorphisms `H_*(B) ≅ H_*(B')` and
`H_*(A) ≅ H_*(A')` induces isomorphisms `H_*(B, A) ≅ H_*(B', A')`. -/
theorem singMap_bijective_of_abs (f : C(X, Z)) {B A : Set X} {B' A' : Set Z} (hAB : A ⊆ B)
    (hAB' : A' ⊆ B') (hB : MapsTo f B B') (hA : MapsTo f A A')
    (hbB : ∀ n, Function.Bijective (hMap K (restrictC f hB) n).hom)
    (hbA : ∀ n, Function.Bijective (hMap K (restrictC f hA) n).hom) (k : ℤ) :
    Function.Bijective (singMap K f hB (fun _ _ h => hA h) k).hom := by
  obtain ⟨k, rfl⟩ := exists_succ k
  have sq : ∀ {B₀ A₀ B₁ A₁ : Set X} {B₀' A₀' B₁' A₁' : Set Z} (h₀ : MapsTo f B₀ B₀')
      (h₀' : ∀ x ∈ B₀, x ∈ A₀ → f x ∈ A₀') (h₁ : MapsTo f B₁ B₁')
      (h₁' : ∀ x ∈ B₁, x ∈ A₁ → f x ∈ A₁') (hB₀ : B₀ ⊆ B₁) (hA₀ : A₀ ⊆ A₁) (hB₀' : B₀' ⊆ B₁')
      (hA₀' : A₀' ⊆ A₁') (j : ℤ) (x : singH K X j B₀ A₀),
      (singIncl K j hB₀' hA₀').hom ((singMap K f h₀ h₀' j).hom x) =
        (singMap K f h₁ h₁' j).hom ((singIncl K j hB₀ hA₀).hom x) := by
    intro B₀ A₀ B₁ A₁ B₀' A₀' B₁' A₁' h₀ h₀' h₁ h₁' hB₀ hA₀ hB₀' hA₀' j x
    exact congrArg (fun φ => φ.hom x)
      ((singMap_singIncl K f h₀ h₀' hB₀' hA₀' j).trans (singIncl_singMap K f hB₀ hA₀ h₁ h₁' j).symm)
  refine five_bijective (sing_exact_incl K (k + 1) (empty_subset A) hAB)
    (sing_exact_δ K k (empty_subset A) hAB) (sing_exact_δ' K k (empty_subset A) hAB)
    (sing_exact_incl K (k + 1) (empty_subset A') hAB') (sing_exact_δ K k (empty_subset A') hAB')
    (sing_exact_δ' K k (empty_subset A') hAB') (fun x => sq _ _ _ _ _ _ _ _ _ x)
    (fun x => sq _ _ _ _ _ _ _ _ _ x) (fun x => ?_) (fun x => sq _ _ _ _ _ _ _ _ _ x)
    (singMap_abs_bijective K f hA (hbA) (k + 1)).2 (singMap_abs_bijective K f hB hbB (k + 1))
    (singMap_abs_bijective K f hA hbA k) (singMap_abs_bijective K f hB hbB k).1
  exact (singδ_natural_apply K f (empty_subset A) hAB (empty_subset A') hAB' hB hA
    (mapsTo_empty f ∅) k x).symm

end Abs

/-! ### Homotopy invariance of relative homology -/

section Homotopy

variable (K : Type u) [Ring K] {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

theorem hMap_bijective_of_homotopy_inverse (f : C(X, Y)) (g : C(Y, X))
    (h₁ : (g.comp f).Homotopic (ContinuousMap.id X))
    (h₂ : (f.comp g).Homotopic (ContinuousMap.id Y)) (n : ℕ) :
    Function.Bijective (hMap K f n).hom := by
  refine ⟨fun a b hab => ?_, fun y => ⟨(hMap K g n).hom y, ?_⟩⟩
  · have := congrArg (hMap K g n).hom hab
    rwa [hMap_comp_apply, hMap_comp_apply, hMap_congr K h₁, hMap_id_apply,
      hMap_id_apply] at this
  · rw [hMap_comp_apply, hMap_congr K h₂, hMap_id_apply]

/-- The projection `I × X → X`. -/
def prI : C(I × X, X) := ⟨Prod.snd, continuous_snd⟩

/-- The slice `x ↦ (s, x)`. -/
def incI (s : I) : C(X, I × X) := ⟨fun x => (s, x), continuous_const.prodMk continuous_id⟩

/-- `I × B → B` is a homotopy equivalence. -/
theorem hMap_prI_bijective (B : Set X) (n : ℕ) :
    Function.Bijective (hMap K (restrictC (prI (X := X)) (B := {p : I × X | p.2 ∈ B}) (B' := B)
      fun _ hp => hp) n).hom := by
  let g : C(B, {p : I × X | p.2 ∈ B}) :=
    ⟨fun b => ⟨((0 : I), (b : X)), b.2⟩, (continuous_const.prodMk continuous_subtype_val).subtype_mk _⟩
  refine hMap_bijective_of_homotopy_inverse K _ g ⟨?_⟩ (ContinuousMap.Homotopic.refl _) n
  exact
    { toFun := fun q => ⟨(⟨(q.1 : ℝ) * ((q.2 : I × X).1 : ℝ),
        unitInterval.mul_mem q.1.2 (q.2 : I × X).1.2⟩, (q.2 : I × X).2), q.2.2⟩
      continuous_toFun := by
        refine Continuous.subtype_mk (Continuous.prodMk (Continuous.subtype_mk ?_ _) ?_) _
        · exact (continuous_subtype_val.comp continuous_fst).mul
            (continuous_subtype_val.comp (continuous_fst.comp
              (continuous_subtype_val.comp continuous_snd)))
        · exact continuous_snd.comp (continuous_subtype_val.comp continuous_snd)
      map_zero_left := fun q => Subtype.ext (Prod.ext (Subtype.ext (zero_mul _)) rfl)
      map_one_left := fun q => Subtype.ext (Prod.ext (Subtype.ext (one_mul _)) rfl) }

theorem singMap_prI_bijective {B A : Set X} (hAB : A ⊆ B) (k : ℤ) :
    Function.Bijective (singMap K (prI (X := X)) (B := {p : I × X | p.2 ∈ B})
      (A := {p : I × X | p.2 ∈ A}) (B' := B) (A' := A) (fun _ hp => hp) (fun _ _ hp => hp) k).hom :=
  singMap_bijective_of_abs K prI (fun _ hp => hAB hp) hAB (fun _ hp => hp) (fun _ hp => hp)
    (hMap_prI_bijective K B) (hMap_prI_bijective K A) k

/-- Maps of pairs homotopic through maps of pairs induce the same map on relative homology. -/
theorem singMap_eq_of_homotopy (f g : C(X, Z)) (F : C(I × X, Z)) (hf : ∀ x, F (0, x) = f x)
    (hg : ∀ x, F (1, x) = g x) {B A : Set X} {B' A' : Set Z} (hAB : A ⊆ B)
    (hB : ∀ s, ∀ x ∈ B, F (s, x) ∈ B') (hA : ∀ s, ∀ x ∈ A, F (s, x) ∈ A')
    (hfB : MapsTo f B B') (hfA : ∀ x ∈ B, x ∈ A → f x ∈ A') (hgB : MapsTo g B B')
    (hgA : ∀ x ∈ B, x ∈ A → g x ∈ A') (k : ℤ) :
    singMap K f hfB hfA k = singMap K g hgB hgA k := by
  have hF : ∀ s : I, singMap K (F.comp (incI s)) (fun x hx => hB s x hx)
      (fun x _ hx => hA s x hx) k =
      singMap K (incI s) (B' := {p : I × X | p.2 ∈ B}) (A' := {p : I × X | p.2 ∈ A})
        (fun _ hx => hx) (fun _ _ hx => hx) k ≫
      singMap K F (B' := B') (A' := A') (fun p hp => hB p.1 p.2 hp)
        (fun p _ hp => hA p.1 p.2 hp) k :=
    fun s => (singMap_comp K _ _ _ _ _ _ k).symm
  have hi : singMap K (incI 0) (B' := {p : I × X | p.2 ∈ B}) (A' := {p : I × X | p.2 ∈ A})
      (fun _ hx => hx) (fun _ _ hx => hx) k =
      singMap K (incI 1) (B' := {p : I × X | p.2 ∈ B}) (A' := {p : I × X | p.2 ∈ A})
        (fun _ hx => hx) (fun _ _ hx => hx) k := by
    have hpi : ∀ s : I, singMap K (incI s) (B' := {p : I × X | p.2 ∈ B})
        (A' := {p : I × X | p.2 ∈ A}) (fun _ hx => hx) (fun _ _ hx => hx) k ≫
        singMap K (prI (X := X)) (fun _ hp => hp) (fun _ _ hp => hp) k = 𝟙 _ := fun s =>
      (singMap_comp K _ _ _ _ _ _ k).trans (singMap_id K k)
    ext z
    apply (singMap_prI_bijective K hAB k).1
    exact (congrArg (fun φ => φ.hom z) (hpi 0)).trans (congrArg (fun φ => φ.hom z) (hpi 1)).symm
  have e0 : f = F.comp (incI 0) := by ext x; exact (hf x).symm
  have e1 : g = F.comp (incI 1) := by ext x; exact (hg x).symm
  exact (singMap_eq_of_eq K e0 k).trans ((hF 0).trans ((congrArg (· ≫ _) hi).trans
    ((hF 1).symm.trans (singMap_eq_of_eq K e1 k).symm)))

end Homotopy

/-! ### The reflection of the cylinder -/

section Reflection

variable (K : Type u) [Ring K] {X : Type u} [TopologicalSpace X]

/-- The reflection `(x, t) ↦ (x, 1 - t)`. -/
def cylRefl : C(X × ℝ, X × ℝ) := ⟨fun p => (p.1, 1 - p.2), by fun_prop⟩

theorem cylRefl_apply (p : X × ℝ) : cylRefl p = (p.1, 1 - p.2) := rfl

theorem one_sub_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 1 - t ∈ Icc (0 : ℝ) 1 :=
  ⟨by linarith [ht.2], by linarith [ht.1]⟩

theorem cylRefl_mapsTo_N (N : Set X) : MapsTo cylRefl (cylN N) (cylN N) := fun _ hp =>
  ⟨hp.1, one_sub_mem_Icc hp.2⟩

theorem cylRefl_mapsTo_L (N L : Set X) : MapsTo cylRefl (cylL N L) (cylL N L) := by
  rintro p (⟨hx, ht⟩ | ⟨hx, ht | ht⟩)
  · exact Or.inl ⟨hx, one_sub_mem_Icc ht⟩
  · exact Or.inr ⟨hx, Or.inr (by show 1 - p.2 = 1; rw [ht]; ring)⟩
  · exact Or.inr ⟨hx, Or.inl (by show 1 - p.2 = 0; rw [ht]; ring)⟩

/-- The reflection acts by `-1` on `H_*(N × [0, 1], L × [0, 1] ∪ N × {0, 1})`. -/
theorem cylRefl_neg {N L : Set X} (hLN : L ⊆ N) (k : ℤ)
    (z : singH K (X × ℝ) k (cylN N) (cylL N L)) :
    (singMap K cylRefl (cylRefl_mapsTo_N N) (fun _ _ h => cylRefl_mapsTo_L N L h) k).hom z = -z := by
  obtain ⟨k, rfl⟩ := exists_succ k
  let A : Set (X × ℝ) := L ×ˢ Icc 0 1
  let E₀ : Set (X × ℝ) := A ∪ N ×ˢ {0}
  let E₁ : Set (X × ℝ) := A ∪ N ×ˢ {1}
  have hAE₀ : A ⊆ E₀ := subset_union_left
  have hAE₁ : A ⊆ E₁ := subset_union_left
  have hE₀L : E₀ ⊆ cylL N L := by
    rintro p (h | ⟨hx, ht⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hx, Or.inl ht⟩
  have hE₁L : E₁ ⊆ cylL N L := by
    rintro p (h | ⟨hx, ht⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hx, Or.inr ht⟩
  have hLN' : cylL N L ⊆ cylN N := by
    rintro p (⟨hx, ht⟩ | ⟨hx, ht | ht⟩)
    · exact ⟨hLN hx, ht⟩
    · exact ⟨hx, by rw [mem_Icc, ht]; norm_num⟩
    · exact ⟨hx, by rw [mem_Icc, ht]; norm_num⟩
  have hAL : A ⊆ cylL N L := hAE₀.trans hE₀L
  have hE₀N : E₀ ⊆ cylN N := hE₀L.trans hLN'
  have hE₁N : E₁ ⊆ cylN N := hE₁L.trans hLN'
  have hAN : A ⊆ cylN N := hAL.trans hLN'
  have hρA : MapsTo (cylRefl (X := X)) A A := fun p hp => ⟨hp.1, one_sub_mem_Icc hp.2⟩
  have hρ01 : MapsTo (cylRefl (X := X)) E₀ E₁ := by
    rintro p (h | ⟨hx, ht⟩)
    · exact Or.inl (hρA h)
    · exact Or.inr ⟨hx, by show 1 - p.2 = 1; rw [mem_singleton_iff.1 ht]; ring⟩
  have hρ10 : MapsTo (cylRefl (X := X)) E₁ E₀ := by
    rintro p (h | ⟨hx, ht⟩)
    · exact Or.inl (hρA h)
    · exact Or.inr ⟨hx, by show 1 - p.2 = 0; rw [mem_singleton_iff.1 ht]; ring⟩
  -- `H_*(N × [0, 1], E_j) = 0`
  have hmul : ∀ (s : I) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → (1 - (s : ℝ)) * t ∈ Icc (0 : ℝ) 1 :=
    fun s t ht => ⟨mul_nonneg (by linarith [s.2.2]) ht.1,
      (mul_le_of_le_one_left ht.1 (by linarith [s.2.1])).trans ht.2⟩
  have hup : ∀ (s : I) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → t + (s : ℝ) * (1 - t) ∈ Icc (0 : ℝ) 1 :=
    fun s t ht => ⟨by nlinarith [s.2.1, ht.2, ht.1], by nlinarith [s.2.2, ht.1, ht.2]⟩
  have hs₀ : ∀ j, Subsingleton (singH K (X × ℝ) j (cylN N) E₀) :=
    singH_subsingleton_of_cylDeform K hE₀N (fun s t => (1 - (s : ℝ)) * t)
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul continuous_snd)
      (fun s p hp => ⟨hp.1, hmul s _ hp.2⟩) (fun t => by simp)
      (fun p hp => Or.inr ⟨hp.1, by simp⟩)
      (by
        rintro s p (⟨hx, ht⟩ | ⟨hx, ht⟩)
        · exact Or.inl ⟨hx, hmul s _ ht⟩
        · refine Or.inr ⟨hx, ?_⟩
          rw [mem_singleton_iff] at ht ⊢
          simp [ht])
  have hs₁ : ∀ j, Subsingleton (singH K (X × ℝ) j (cylN N) E₁) :=
    singH_subsingleton_of_cylDeform K hE₁N (fun s t => t + (s : ℝ) * (1 - t))
      (continuous_snd.add ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_const.sub continuous_snd)))
      (fun s p hp => ⟨hp.1, hup s _ hp.2⟩) (fun t => by simp)
      (fun p hp => Or.inr ⟨hp.1, by simp⟩)
      (by
        rintro s p (⟨hx, ht⟩ | ⟨hx, ht⟩)
        · exact Or.inl ⟨hx, hup s _ ht⟩
        · refine Or.inr ⟨hx, ?_⟩
          rw [mem_singleton_iff] at ht ⊢
          simp [ht])
  -- the reflection is the identity on `H_*(N × [0, 1], L × [0, 1])`
  have hρid : ∀ w : singH K (X × ℝ) k (cylN N) A,
      (singMap K cylRefl (cylRefl_mapsTo_N N) (fun _ _ h => hρA h) k).hom w = w := by
    intro w
    have hlin : ∀ (s : I) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
        (1 - (s : ℝ)) * (1 - t) + (s : ℝ) * t ∈ Icc (0 : ℝ) 1 := fun s t ht =>
      ⟨by nlinarith [s.2.1, s.2.2, ht.1, ht.2], by nlinarith [s.2.1, s.2.2, ht.1, ht.2]⟩
    let F : C(I × (X × ℝ), X × ℝ) :=
      ⟨fun q => (q.2.1, (1 - (q.1 : ℝ)) * (1 - q.2.2) + (q.1 : ℝ) * q.2.2), by fun_prop⟩
    rw [singMap_eq_of_homotopy K cylRefl (ContinuousMap.id _) F
      (fun p => by simp [F, cylRefl_apply]) (fun p => by simp [F]) (B' := cylN N) (A' := A) hAN
      (fun s p hp => ⟨hp.1, hlin s _ hp.2⟩) (fun s p hp => ⟨hp.1, hlin s _ hp.2⟩) _ _
      (mapsTo_id _) (fun _ _ h => h)]
    exact singMap_id_apply K k w
  -- the connecting map `H_{k+1}(N × [0, 1], ∂) → H_k(∂, A)` is injective
  have hδinj : Function.Injective (singδ K k (cylN N) (cylL N L) A).hom := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    obtain ⟨v, rfl⟩ := (sing_exact_δ K k hAL hLN' w).1 hw
    have e := congrArg (fun φ => φ.hom v)
      (singIncl_comp K (k + 1) (subset_refl (cylN N)) hAE₀ (subset_refl (cylN N)) hE₀L)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    rw [← e, Subsingleton.elim ((singIncl K (k + 1) (subset_refl (cylN N)) hAE₀).hom v) 0,
      map_zero]
  -- `c_j : H_k(E_j, A) → H_k(N × [0, 1], A)` is injective
  have hc₀ : Function.Injective (singIncl K k hE₀N (subset_refl A)).hom := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    obtain ⟨v, rfl⟩ := (sing_exact_δ' K k hAE₀ hE₀N w).1 hw
    rw [Subsingleton.elim v 0, map_zero]
  have hc₁ : Function.Injective (singIncl K k hE₁N (subset_refl A)).hom := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    obtain ⟨v, rfl⟩ := (sing_exact_δ' K k hAE₁ hE₁N w).1 hw
    rw [Subsingleton.elim v 0, map_zero]
  -- splitting `δ z = i₀ a + i₁ b` by excision
  have hexc := excision K hE₀L hE₁L (isOpen_lt continuous_snd continuous_const :
      IsOpen {p : X × ℝ | p.2 < 2 / 3})
    (isOpen_lt continuous_const continuous_snd : IsOpen {p : X × ℝ | 1 / 3 < p.2})
    (fun p _ => by
      by_cases h : p.2 < 2 / 3
      · exact Or.inl h
      · exact Or.inr (show 1 / 3 < p.2 by linarith [not_lt.1 h]))
    (by
      rintro p ⟨hp, ⟨hx, ht⟩ | ⟨hx, ht | ht⟩⟩
      · exact Or.inl ⟨hx, ht⟩
      · exact Or.inr ⟨hx, ht⟩
      · exfalso
        have : p.2 < 2 / 3 := hp
        rw [ht] at this
        norm_num at this)
    (by
      rintro p ⟨hp, ⟨hx, ht⟩ | ⟨hx, ht | ht⟩⟩
      · exact Or.inl ⟨hx, ht⟩
      · exfalso
        have : 1 / 3 < p.2 := hp
        rw [ht] at this
        norm_num at this
      · exact Or.inr ⟨hx, ht⟩) k
  have hE₁A : Function.Bijective (singIncl K k (subset_refl E₁) hAE₀).hom := by
    rw [singIncl_eq_singMap]
    refine singMap_bijective K (ContinuousMap.id _) (B := E₁) (A := A) (B' := E₁) (A' := E₀)
      (fun p hp => hp) (fun p hp => ⟨p, hp, rfl⟩) IsEmbedding.subtypeVal (fun p hp => ?_) k
    refine ⟨fun h => hAE₀ h, fun h => ?_⟩
    rcases hp with hp | ⟨-, ht1⟩
    · exact hp
    rcases h with h | ⟨-, ht0⟩
    · exact h
    · exfalso
      have h0 : p.2 = 0 := ht0
      have h1 : p.2 = 1 := ht1
      rw [h0] at h1
      exact zero_ne_one h1
  set y := (singδ K k (cylN N) (cylL N L) A).hom z with hy
  obtain ⟨w, hw⟩ := hexc.2 ((singIncl K k (subset_refl (cylL N L)) hAE₀).hom y)
  obtain ⟨b, rfl⟩ := hE₁A.2 w
  have hb : (singIncl K k (subset_refl (cylL N L)) hAE₀).hom
      (y - (singIncl K k hE₁L (subset_refl A)).hom b) = 0 := by
    rw [map_sub, ← hw]
    have e := congrArg (fun φ => φ.hom b)
      ((singIncl_comp K k hE₁L (subset_refl A) (subset_refl (cylL N L)) hAE₀).trans
        (singIncl_comp K k (subset_refl E₁) hAE₀ hE₁L (subset_refl E₀)).symm)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    rw [e, sub_self]
  obtain ⟨a, ha⟩ := (sing_exact_incl K k hAE₀ hE₀L _).1 hb
  have hsplit : y = (singIncl K k hE₀L (subset_refl A)).hom a +
      (singIncl K k hE₁L (subset_refl A)).hom b := by
    rw [ha, sub_add_cancel]
  -- `c₀ a + c₁ b = 0`
  have hzero : (singIncl K k hE₀N (subset_refl A)).hom a +
      (singIncl K k hE₁N (subset_refl A)).hom b = 0 := by
    have h0 := (sing_exact_δ' K k hAL hLN' _).2 ⟨z, rfl⟩
    rw [← hy, hsplit, map_add] at h0
    have e0 := congrArg (fun φ => φ.hom a)
      (singIncl_comp K k hE₀L (subset_refl A) hLN' (subset_refl A))
    have e1 := congrArg (fun φ => φ.hom b)
      (singIncl_comp K k hE₁L (subset_refl A) hLN' (subset_refl A))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e0 e1
    rw [e0, e1] at h0
    exact h0
  -- the reflection on the pieces
  have hcomm : ∀ {E E' : Set (X × ℝ)} (hE : E ⊆ cylN N) (hE' : E' ⊆ cylN N)
      (hρ : MapsTo (cylRefl (X := X)) E E') (v : singH K (X × ℝ) k E A),
      (singIncl K k hE' (subset_refl A)).hom
        ((singMap K cylRefl hρ (fun _ _ h => hρA h) k).hom v) =
        (singIncl K k hE (subset_refl A)).hom v := by
    intro E E' hE hE' hρ v
    have e := congrArg (fun φ => φ.hom v)
      ((singMap_singIncl K cylRefl hρ (fun _ _ h => hρA h) hE' (subset_refl A) k).trans
        (singIncl_singMap K cylRefl hE (subset_refl A) (cylRefl_mapsTo_N N)
          (fun _ _ h => hρA h) k).symm)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    rw [e, hρid]
  have ha' : (singMap K cylRefl hρ01 (fun _ _ h => hρA h) k).hom a = -b := by
    apply hc₁
    rw [hcomm hE₀N hE₁N hρ01, map_neg, eq_neg_iff_add_eq_zero, hzero]
  have hb' : (singMap K cylRefl hρ10 (fun _ _ h => hρA h) k).hom b = -a := by
    apply hc₀
    rw [hcomm hE₁N hE₀N hρ10, map_neg, eq_neg_iff_add_eq_zero, add_comm, hzero]
  -- the reflection on `H_k(∂, A)` and the connecting map
  have hsq : ∀ {E E' : Set (X × ℝ)} (hE : E ⊆ cylL N L) (hE' : E' ⊆ cylL N L)
      (hρ : MapsTo (cylRefl (X := X)) E E') (v : singH K (X × ℝ) k E A),
      (singMap K cylRefl (cylRefl_mapsTo_L N L) (fun _ _ h => hρA h) k).hom
        ((singIncl K k hE (subset_refl A)).hom v) =
        (singIncl K k hE' (subset_refl A)).hom
          ((singMap K cylRefl hρ (fun _ _ h => hρA h) k).hom v) := by
    intro E E' hE hE' hρ v
    exact congrArg (fun φ => φ.hom v)
      ((singIncl_singMap K cylRefl hE (subset_refl A) (cylRefl_mapsTo_L N L)
        (fun _ _ h => hρA h) k).trans
        (singMap_singIncl K cylRefl hρ (fun _ _ h => hρA h) hE' (subset_refl A) k).symm)
  apply hδinj
  rw [← singδ_natural_apply K cylRefl hAL hLN' hAL hLN' (cylRefl_mapsTo_N N)
    (cylRefl_mapsTo_L N L) hρA k z, ← hy, hsplit, map_add, hsq hE₀L hE₁L hρ01,
    hsq hE₁L hE₀L hρ10, ha', hb', map_neg, map_neg, map_neg, ← hy, hsplit]
  abel

end Reflection

end ConleyCheck.Conley
