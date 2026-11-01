import ConleyCheck.Conley.SingularPair

/-!
# A basis for singular chains

Mathlib's singular `n`-chains `C_n(X)` are a coproduct of copies of `K` indexed by the singular
`n`-simplices. Here `bas K X n : (Simp X n →₀ K) ≃ C_n(X)` identifies them with finitely supported
functions on continuous maps `Δ^n → X`. Under this identification the differential is the
alternating sum of faces (`bas_d`), maps induced by continuous maps act by composition
(`bas_map`), and the chains of a subset `A` are the functions supported on simplices with image in
`A` (`mem_chainSub_iff`).
-/

namespace ConleyCheck.Conley

open CategoryTheory Limits Simplicial Opposite Convexity

universe u

/-- The standard topological `m`-simplex. -/
abbrev Dl (m : ℕ) : Type := StdSimplex ℝ (Fin (m + 1))

/-- Singular `n`-simplices of `X`, as continuous maps. -/
abbrev Simp (X : TopCat.{u}) (n : ℕ) : Type u := C(Dl n, X)

/-- The `i`-th face map `Δ^n → Δ^(n+1)`. -/
noncomputable def faceC {n : ℕ} (i : Fin (n + 2)) : C(Dl n, Dl (n + 1)) :=
  ⟨StdSimplex.map i.succAbove, StdSimplex.continuous_map ℝ _⟩

/-- Singular `n`-simplices of `X`, as simplices of the singular simplicial set. -/
abbrev SimS (X : TopCat.{u}) (n : ℕ) : Type u := (TopCat.toSSet.obj X) _⦋n⦌

noncomputable def simEquiv (X : TopCat.{u}) (n : ℕ) :
    (TopCat.toSSet.obj X) _⦋n⦌ ≃ Simp X n :=
  TopCat.toSSetObjEquiv X (op ⦋n⦌)

theorem simEquiv_δ (X : TopCat.{u}) {n : ℕ} (i : Fin (n + 2))
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    simEquiv X n ((TopCat.toSSet.obj X).δ i s) = (simEquiv X (n + 1) s).comp (faceC i) :=
  rfl

theorem simEquiv_map {X Y : TopCat.{u}} (f : X ⟶ Y) {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    simEquiv Y n ((TopCat.toSSet.map f).app _ s) = f.hom.comp (simEquiv X n s) :=
  rfl

variable (K : Type u) [Ring K]

/-- Singular `n`-chains of `X`. -/
noncomputable abbrev CX (X : TopCat.{u}) (n : ℕ) : ModuleCat.{u} K := ((singFunctor K).obj X).X n

/-- The generator of `C_n(X)` given by a singular simplex. -/
noncomputable def gen (X : TopCat.{u}) (n : ℕ) (σ : Simp X n) : CX K X n :=
  (Sigma.ι (fun _ : SimS X n => ModuleCat.of K K) ((simEquiv X n).symm σ)).hom (1 : K)

/-- Finitely supported functions on simplices, as chains. -/
noncomputable def bas (X : TopCat.{u}) (n : ℕ) : (Simp X n →₀ K) →ₗ[K] CX K X n :=
  Finsupp.linearCombination K (gen K X n)

variable {K}

theorem bas_single {X : TopCat.{u}} {n : ℕ} (σ : Simp X n) (c : K) :
    bas K X n (Finsupp.single σ c) = c • gen K X n σ := by
  simp [bas]

theorem ι_d' {X : TopCat.{u}} {n : ℕ} (s : SimS X (n + 1)) :
    Sigma.ι (fun _ : SimS X (n + 1) => ModuleCat.of K K) s ≫
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          Sigma.map' (f := fun _ : SimS X n => ModuleCat.of K K)
            ((TopCat.toSSet.obj X).δ i) (fun _ => 𝟙 (ModuleCat.of K K))) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        Sigma.ι (fun _ : SimS X n => ModuleCat.of K K) ((TopCat.toSSet.obj X).δ i s) := by
  rw [Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.comp_zsmul, Sigma.ι_comp_map', Category.id_comp]

theorem gen_d {X : TopCat.{u}} {n : ℕ} (σ : Simp X (n + 1)) :
    (((singFunctor K).obj X).d (n + 1) n).hom (gen K X (n + 1) σ) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • gen K X n (σ.comp (faceC i)) := by
  have hd : ((singFunctor K).obj X).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        Sigma.map' (f := fun _ : SimS X n => ModuleCat.of K K)
          ((TopCat.toSSet.obj X).δ i) (fun _ => 𝟙 (ModuleCat.of K K)) := by
    rw [show ((singFunctor K).obj X).d (n + 1) n =
      (AlgebraicTopology.AlternatingFaceMapComplex.obj _).d (n + 1) n from rfl,
      AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
    rfl
  have h := congrArg (fun φ => φ.hom (1 : K)) (ι_d' (K := K) ((simEquiv X (n + 1)).symm σ))
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply] at h
  rw [hd]
  refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
  unfold gen
  congr 3

theorem gen_map {X Y : TopCat.{u}} (f : X ⟶ Y) {n : ℕ} (σ : Simp X n) :
    (((singFunctor K).map f).f n).hom (gen K X n σ) = gen K Y n (f.hom.comp σ) := by
  have h := congrArg (fun φ => φ.hom (1 : K)) (Sigma.ι_comp_map'
    (f := fun _ : SimS Y n => ModuleCat.of K K) (g := fun _ : SimS X n => ModuleCat.of K K)
    ((TopCat.toSSet.map f).app (op ⦋n⦌)) (fun _ => 𝟙 (ModuleCat.of K K)) ((simEquiv X n).symm σ))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at h
  refine h.trans ?_
  unfold gen
  congr 2

variable (K)

/-- The boundary on finitely supported functions on simplices. -/
noncomputable def dF (X : TopCat.{u}) (n : ℕ) : (Simp X (n + 1) →₀ K) →ₗ[K] (Simp X n →₀ K) :=
  Finsupp.linearCombination K fun σ =>
    ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (σ.comp (faceC i)) (1 : K)

/-- The map on finitely supported functions on simplices induced by a continuous map. -/
noncomputable def mapF {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    (Simp X n →₀ K) →ₗ[K] (Simp Y n →₀ K) :=
  Finsupp.lmapDomain K K fun σ => f.hom.comp σ

variable {K}

theorem bas_d {X : TopCat.{u}} {n : ℕ} (g : Simp X (n + 1) →₀ K) :
    (((singFunctor K).obj X).d (n + 1) n).hom (bas K X (n + 1) g) = bas K X n (dF K X n g) := by
  have : (((singFunctor K).obj X).d (n + 1) n).hom ∘ₗ bas K X (n + 1) = bas K X n ∘ₗ dF K X n := by
    refine Finsupp.lhom_ext fun σ c => ?_
    simp only [LinearMap.comp_apply, bas_single, map_smul, gen_d, dF,
      Finsupp.linearCombination_single, map_sum, map_zsmul, one_smul]
  exact congrArg (fun φ => φ g) this

theorem bas_map {X Y : TopCat.{u}} (f : X ⟶ Y) {n : ℕ} (g : Simp X n →₀ K) :
    (((singFunctor K).map f).f n).hom (bas K X n g) = bas K Y n (mapF K f n g) := by
  have : (((singFunctor K).map f).f n).hom ∘ₗ bas K X n = bas K Y n ∘ₗ mapF K f n := by
    refine Finsupp.lhom_ext fun σ c => ?_
    simp only [LinearMap.comp_apply, bas_single, map_smul, gen_map, mapF,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  exact congrArg (fun φ => φ g) this

theorem bas_bijective (X : TopCat.{u}) (n : ℕ) : Function.Bijective (bas K X n) := by
  classical
  let e : CX K X n ≅ ModuleCat.of K (DirectSum (SimS X n) fun _ => K) :=
    ModuleCat.coprodIsoDirectSum (fun _ : SimS X n => ModuleCat.of K K)
  let L := (Finsupp.domLCongr (simEquiv X n).symm).trans
    (finsuppLEquivDirectSum K K (SimS X n))
  have h : ∀ g, e.hom.hom (bas K X n g) = L g := by
    intro g
    refine congrArg (fun φ : (Simp X n →₀ K) →ₗ[K] _ => φ g)
      (Finsupp.lhom_ext (φ := e.hom.hom ∘ₗ bas K X n) (ψ := L.toLinearMap) fun σ c => ?_)
    have h1 : e.hom.hom (gen K X n σ) = DirectSum.lof K (SimS X n) (fun _ => K)
        ((simEquiv X n).symm σ) 1 :=
      ModuleCat.ι_coprodIsoDirectSum_hom_apply (Z := fun _ : SimS X n => ModuleCat.of K K) _ _
    simp only [LinearMap.comp_apply, bas_single, LinearEquiv.coe_coe, L, LinearEquiv.trans_apply,
      Finsupp.domLCongr_single, finsuppLEquivDirectSum_single]
    calc e.hom.hom (c • gen K X n σ) = c • e.hom.hom (gen K X n σ) := map_smul _ _ _
      _ = _ := by rw [h1, ← map_smul, smul_eq_mul, mul_one]
  have he : Function.Injective e.hom.hom := fun a b hab => by
    simpa using congrArg e.inv.hom hab
  refine ⟨fun a b hab => L.injective ?_, fun y => ⟨L.symm (e.hom.hom y), he ?_⟩⟩
  · rw [← h, ← h, hab]
  · rw [h, LinearEquiv.apply_symm_apply]

variable (K)

/-- `bas` as a linear equivalence. -/
noncomputable def basEquiv (X : TopCat.{u}) (n : ℕ) : (Simp X n →₀ K) ≃ₗ[K] CX K X n :=
  LinearEquiv.ofBijective _ (bas_bijective X n)

variable {K}

@[simp]
theorem basEquiv_apply {X : TopCat.{u}} {n : ℕ} (g : Simp X n →₀ K) :
    basEquiv K X n g = bas K X n g := rfl

section Subsets

variable {α : Type u} [TopologicalSpace α]

/-- Simplices with image in `A`. -/
def onSet (A : Set α) (n : ℕ) : Set (Simp (TopCat.of α) n) := {σ | Set.range σ ⊆ A}

theorem gen_mem_chainSub {A : Set α} {n : ℕ} {σ : Simp (TopCat.of α) n} (hσ : σ ∈ onSet A n) :
    gen K _ n σ ∈ (chainSub K A).S n := by
  let σ' : Simp (TopCat.of A) n := ⟨fun t => ⟨σ t, hσ ⟨t, rfl⟩⟩, by fun_prop⟩
  refine ⟨gen K _ n σ', ?_⟩
  rw [gen_map]
  rfl

theorem mem_chainSub_iff (A : Set α) (n : ℕ) (x : CX K (TopCat.of α) n) :
    x ∈ (chainSub K A).S n ↔
      (basEquiv K _ n).symm x ∈ Finsupp.supported K K (onSet A n) := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨g, rfl⟩ := (bas_bijective (K := K) (TopCat.of A) n).2 y
    rw [bas_map, ← basEquiv_apply, LinearEquiv.symm_apply_apply]
    have hm : mapF K (subsetι A) n g ∈ Finsupp.supported K K
        ((fun σ : Simp (TopCat.of A) n => (subsetι A).hom.comp σ) '' Set.univ) := by
      rw [← Finsupp.lmapDomain_supported]
      exact ⟨g, by simp, rfl⟩
    refine Finsupp.supported_mono ?_ hm
    rintro _ ⟨σ, -, rfl⟩ _ ⟨t, rfl⟩
    exact (σ t).2
  · intro hx
    rw [← (basEquiv K _ n).apply_symm_apply x]
    generalize (basEquiv K _ n).symm x = g at hx
    rw [Finsupp.supported_eq_span_single] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨σ, hσ, rfl⟩
      rw [basEquiv_apply, bas_single, one_smul]
      exact gen_mem_chainSub hσ
    · simp
    · intro a b _ _ ha hb
      rw [map_add]
      exact add_mem ha hb
    · intro c a _ ha
      rw [map_smul]
      exact Submodule.smul_mem _ c ha

end Subsets

end ConleyCheck.Conley
