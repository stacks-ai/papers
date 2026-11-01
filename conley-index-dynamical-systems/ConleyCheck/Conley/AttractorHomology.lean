import ConleyCheck.Conley.MorseHomology
import ConleyCheck.Conley.SphereHomology
import ConleyCheck.Conley.PointIndex

/-!
# Homology indices of attractors

* `indexPair_of_fwd`: a compact positively invariant neighborhood `B` of `S = Inv(B)` gives the
  index pair `(B, ∅)`, and then `CH_*(S) ≅ H_*(B)` (`homologyIndex_equiv_of_fwd`).
* `IsAttractorRepellerPair.exists_attractorPair` (in `Morse.lean`): an attractor in a set with an
  index pair `(N, ∅)` has an index pair `(B, ∅)`.
* `surjective_collapse`: for an index pair `(B, ∅)` of `S ≠ ∅`, collapsing `B` to a point gives a
  surjection `CH_0(S) → K`.
* `homologyIndex_point_circle`: over a commutative ring, if `S` has an index pair `(B, ∅)` and an
  attractor–repeller pair `(A, R)` with `CH_*(A) = K[0]` and `CH_*(R) = K[1]`, then
  `CH_*(S) = K[0] ⊕ K[1]`. No connection matrix is used.
-/

namespace ConleyCheck.Conley

open CategoryTheory Set

section Reduced

variable (K : Type) [Ring K] {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

theorem redMap_comp (f : C(X, Y)) (g : C(Y, Z)) {x₀ : X} {y₀ : Y} {z₀ : Z} (hf : f x₀ = y₀)
    (hg : g y₀ = z₀) (n : ℕ) :
    redMap K (g.comp f) (show g (f x₀) = z₀ by rw [hf, hg]) n =
      redMap K f hf n ≫ redMap K g hg n := by
  refine redH_hom_ext K ?_
  rw [π_redMap, hMap_comp K f g, π_redMap_assoc, π_redMap, Category.assoc]

theorem redMap_eq_id {f : C(X, X)} {x₀ : X} (hf : f x₀ = x₀) (h : f = ContinuousMap.id X)
    (n : ℕ) : redMap K f hf n = 𝟙 _ := by
  subst h
  refine redH_hom_ext K ?_
  rw [π_redMap, hMap_id, Category.id_comp, Category.comp_id]

/-- A pointed map with a pointed section induces a surjection on reduced homology. -/
theorem surjective_redMap_of_section (f : C(X, Y)) (s : C(Y, X)) {x₀ : X} {y₀ : Y}
    (hf : f x₀ = y₀) (hs : s y₀ = x₀) (h : f.comp s = ContinuousMap.id Y) (n : ℕ) :
    Function.Surjective (redMap K f hf n).hom := fun y => by
  have e := congrArg (fun φ => φ.hom y)
    ((redMap_comp K s f hs hf n).symm.trans (redMap_eq_id K _ h n))
  exact ⟨_, e⟩

end Reduced

instance : Finite (Sphere 0) := by
  have : (univ : Set (Sphere 0)) ⊆ {Sphere.pt 0, Sphere.npt} := fun p _ => by
    by_cases h : p = Sphere.pt 0
    · exact Or.inl h
    · exact Or.inr (Sphere.eq_npt h)
  exact Set.finite_univ_iff.1 ((Set.toFinite _).subset this)

instance : DiscreteTopology (Sphere 0) := inferInstance

variable (K : Type) {α : Type} [TopologicalSpace α] [T2Space α] {ϕ : Flow ℝ α}

/-- Collapsing `B` to the second point of `S⁰`. -/
noncomputable def collapse (B : Set α) : C(IndexSpace B ∅, Sphere 0) :=
  descend (Sphere.pt 0) (ContinuousMap.const _ Sphere.npt) fun _ h => h.elim

omit [T2Space α] in
theorem surjective_collapse [Ring K] {B : Set α} {b : α} (hb : b ∈ B) (n : ℕ) :
    Function.Surjective (redMap K (collapse B) (descend_pt _ _ _) n).hom := by
  classical
  let s : C(Sphere 0, IndexSpace B ∅) :=
    ⟨fun p => if p = Sphere.pt 0 then IndexSpace.pt B ∅ else IndexSpace.proj B ∅ ⟨b, hb⟩,
      continuous_of_discreteTopology⟩
  refine surjective_redMap_of_section K _ s _ (by simp [s]) ?_ n
  ext1 p
  by_cases h : p = Sphere.pt 0
  · subst h
    show collapse B (s (Sphere.pt 0)) = _
    rw [show s (Sphere.pt 0) = IndexSpace.pt B ∅ by simp [s]]
    rfl
  · show collapse B (s p) = p
    rw [show s p = IndexSpace.proj B ∅ ⟨b, hb⟩ by simp [s, h]]
    exact (Sphere.eq_npt h).symm

/-- A surjective endomorphism of a commutative ring, as a module over itself, is injective. -/
theorem injective_of_surjective_self {K : Type*} [CommRing K] (f : K →ₗ[K] K)
    (hf : Function.Surjective f) : Function.Injective f := by
  obtain ⟨y, hy⟩ := hf 1
  have h1 : ∀ x, f x = x * f 1 := fun x => by
    rw [← smul_eq_mul, ← f.map_smul, smul_eq_mul, mul_one]
  have hy1 : y * f 1 = 1 := by rw [← h1, hy]
  intro a b hab
  calc a = a * f 1 * y := by rw [mul_assoc, mul_comm (f 1), hy1, mul_one]
    _ = b * f 1 * y := by rw [← h1, ← h1, hab]
    _ = b := by rw [mul_assoc, mul_comm (f 1), hy1, mul_one]

/-- `CH_*(S) = K[0] ⊕ K[1]`. -/
def HasPointCircleIndex [Ring K] {S : Set α} (hS : IsIsolatedInvariantSet ϕ S) : Prop :=
  Nonempty (homologyIndex K ϕ hS 0 ≃ₗ[K] K) ∧ Nonempty (homologyIndex K ϕ hS 1 ≃ₗ[K] K) ∧
    ∀ n, 2 ≤ n → Subsingleton (homologyIndex K ϕ hS n)

variable {K}

theorem HasPointCircleIndex.of_bijective [Ring K] {S T : Set α} {hS : IsIsolatedInvariantSet ϕ S}
    {hT : IsIsolatedInvariantSet ϕ T} (h : HasPointCircleIndex K hS)
    (f : ∀ n, homologyIndex K ϕ hS n →ₗ[K] homologyIndex K ϕ hT n)
    (hf : ∀ n, Function.Bijective (f n)) : HasPointCircleIndex K hT := by
  obtain ⟨⟨e0⟩, ⟨e1⟩, h2⟩ := h
  refine ⟨⟨(LinearEquiv.ofBijective (f 0) (hf 0)).symm.trans e0⟩,
    ⟨(LinearEquiv.ofBijective (f 1) (hf 1)).symm.trans e1⟩, fun n hn => ?_⟩
  have := h2 n hn
  exact (hf n).2.subsingleton

omit [T2Space α] in
/-- If `(B, ∅)` is an index pair, then `B` is positively invariant. -/
theorem IsIndexPair.fwd_of_empty {S B : Set α} (hP : IsIndexPair ϕ S B ∅) :
    ∀ x ∈ B, ∀ t, 0 ≤ t → ϕ t x ∈ B := fun x hx t ht => by
  by_contra h
  obtain ⟨s, -, -, hs⟩ := hP.exit x hx t ht h
  exact hs

theorem IsIndexPair.inv_of_empty {S B : Set α} (hP : IsIndexPair ϕ S B ∅) : Inv ϕ B = S := by
  have := hP.inv_eq
  rwa [sdiff_empty, hP.isCompact_N.isClosed.closure_eq] at this

omit [T2Space α] in
theorem IsIndexPair.subset_interior_of_empty {S B : Set α} (hP : IsIndexPair ϕ S B ∅) :
    S ⊆ interior B := by
  have := hP.nhds
  rwa [sdiff_empty] at this

/-- A compact positively invariant neighborhood `B` of `S = Inv(B)` gives the index pair
`(B, ∅)`. -/
theorem indexPair_of_fwd {S B : Set α} (hB : IsCompact B) (hfwd : ∀ x ∈ B, ∀ t, 0 ≤ t → ϕ t x ∈ B)
    (hS : Inv ϕ B = S) (hint : S ⊆ interior B) : IsIndexPair ϕ S B ∅ := by
  have hcl : closure (B \ ∅) = B := by rw [sdiff_empty, hB.isClosed.closure_eq]
  refine ⟨hB, isCompact_empty, empty_subset _, ?_, ?_, ?_, fun _ h => h.elim, ?_⟩
  · rw [hcl]; exact ⟨hB, hS ▸ hint⟩
  · rw [hcl, hS]
  · rwa [sdiff_empty]
  · exact fun x hx t ht hxt => absurd (hfwd x hx t ht) hxt

omit [T2Space α] in
theorem isDeformCollared_empty (N : Set α) : IsDeformCollared N ∅ :=
  ⟨∅, ∅, ⟨fun p => p.2, continuous_snd⟩, isOpen_empty, subset_refl _, by simp, empty_subset _,
    fun _ => rfl, fun _ _ h => h.elim, fun _ _ h => h.elim, fun _ h => h.elim⟩

variable (K)

/-- `CH_*(S) ≅ H_*(B)` for a compact positively invariant neighborhood `B` of `S = Inv(B)`. -/
theorem homologyIndex_equiv_of_fwd [Ring K] {S B : Set α} (hS : IsIsolatedInvariantSet ϕ S)
    (hB : IsCompact B) (hfwd : ∀ x ∈ B, ∀ t, 0 ≤ t → ϕ t x ∈ B) (hSB : Inv ϕ B = S)
    (hint : S ⊆ interior B) (n : ℕ) :
    Nonempty (homologyIndex K ϕ hS n ≃ₗ[K] singH K α (Int.ofNat n) B ∅) :=
  homologyIndex_equiv_of_deformCollared K hS (indexPair_of_fwd hB hfwd hSB hint)
    (isDeformCollared_empty B) n

/-- `H_*(B) = K[0] ⊕ K[1]` for a compact positively invariant neighborhood `B` of `S = Inv(B)`
with `CH_*(S) = K[0] ⊕ K[1]`. -/
theorem HasPointCircleIndex.singH [Ring K] {S B : Set α} {hS : IsIsolatedInvariantSet ϕ S}
    (h : HasPointCircleIndex K hS) (hB : IsCompact B) (hfwd : ∀ x ∈ B, ∀ t, 0 ≤ t → ϕ t x ∈ B)
    (hSB : Inv ϕ B = S) (hint : S ⊆ interior B) :
    Nonempty (singH K α (Int.ofNat 0) B ∅ ≃ₗ[K] K) ∧
      Nonempty (singH K α (Int.ofNat 1) B ∅ ≃ₗ[K] K) ∧
      ∀ n, 2 ≤ n → Subsingleton (singH K α (Int.ofNat n) B ∅) := by
  have e := fun n => (homologyIndex_equiv_of_fwd K hS hB hfwd hSB hint n).some
  obtain ⟨⟨e0⟩, ⟨e1⟩, h2⟩ := h
  refine ⟨⟨(e 0).symm.trans e0⟩, ⟨(e 1).symm.trans e1⟩, fun n hn => ?_⟩
  have := h2 n hn
  exact (e n).symm.toEquiv.subsingleton

/-- On a compact space, `(univ, ∅)` is an index pair of `univ`. -/
theorem indexPair_univ [CompactSpace α] : IsIndexPair ϕ univ univ ∅ :=
  indexPair_of_fwd isCompact_univ (fun _ _ _ _ => trivial)
    (eq_univ_of_forall fun _ _ => trivial) (by rw [interior_univ])

/-- On a compact space, an attractor has a compact positively invariant neighborhood `B` with
`Inv(B) = A`, and `(B, ∅)` is an index pair of `A`. -/
theorem IsAttractorRepellerPair.exists_trapping [CompactSpace α] {A R : Set α}
    (h : IsAttractorRepellerPair ϕ univ A R) :
    ∃ B, IsIndexPair ϕ A B ∅ ∧ IsCompact B ∧ (∀ x ∈ B, ∀ t, 0 ≤ t → ϕ t x ∈ B) ∧
      Inv ϕ B = A ∧ A ⊆ interior B := by
  obtain ⟨B, -, hB⟩ := h.exists_attractorPair indexPair_univ
  exact ⟨B, hB, hB.isCompact_N, hB.fwd_of_empty, hB.inv_of_empty, hB.subset_interior_of_empty⟩

/-- If `(B, ∅)` is an index pair of a nonempty `S`, there is a surjection `CH_0(S) → K`. -/
theorem exists_surjective_zero [Ring K] {S B : Set α} (hS : IsIsolatedInvariantSet ϕ S)
    (hB : IsIndexPair ϕ S B ∅) (hne : S.Nonempty) :
    ∃ q : homologyIndex K ϕ hS 0 →ₗ[K] K, Function.Surjective q := by
  obtain ⟨x, hx⟩ := hne
  have hb : x ∈ B := (interior_subset (hB.nhds hx)).1
  obtain ⟨iso⟩ := homologyIndexIso K hS hB 0
  obtain ⟨eS⟩ := (sphere_homology K 0).1
  exact ⟨eS.toLinearMap ∘ₗ (redMap K (collapse B) (descend_pt _ _ _) 0).hom ∘ₗ
      iso.toLinearEquiv.toLinearMap,
    eS.surjective.comp ((surjective_collapse K hb 0).comp iso.toLinearEquiv.surjective)⟩

/-- Over a commutative ring, if `S` has an index pair `(B, ∅)` and an attractor–repeller pair
`(A, R)` with `CH_*(A) = K[0]` and `CH_*(R) = K[1]`, then `CH_*(S) = K[0] ⊕ K[1]`. -/
theorem homologyIndex_point_circle [CommRing K] {S A R B : Set α}
    (h : IsAttractorRepellerPair ϕ S A R) (hB : IsIndexPair ϕ S B ∅) (hne : S.Nonempty)
    (hA : HasHomologyIndex K h.isolated_A 0) (hR : HasHomologyIndex K h.isolated_R 1) :
    HasPointCircleIndex K h.isolated := by
  obtain ⟨i, p, d, e1, e2, e3, -⟩ := homologyIndex_attractor_repeller_of_pair K h
  obtain ⟨⟨eA⟩, hA0⟩ := hA
  obtain ⟨⟨eR⟩, hR0⟩ := hR
  obtain ⟨q, hq⟩ := exists_surjective_zero K h.isolated hB hne
  have hi0 : Function.Surjective (i 0) := fun y => by
    have := hR0 0 (by norm_num)
    exact (e1 0 y).1 (Subsingleton.elim _ _)
  have hf := injective_of_surjective_self (q ∘ₗ i 0 ∘ₗ eA.symm.toLinearMap)
    (hq.comp (hi0.comp eA.symm.surjective))
  have hi0' : Function.Injective (i 0) := fun a b hab => by
    have : (q ∘ₗ i 0 ∘ₗ eA.symm.toLinearMap) (eA a) = (q ∘ₗ i 0 ∘ₗ eA.symm.toLinearMap) (eA b) := by
      simp [hab]
    exact eA.injective (hf this)
  have hd0 : ∀ y, d 0 y = 0 := fun y =>
    hi0' (((e3 0 (d 0 y)).2 ⟨y, rfl⟩).trans (map_zero (i 0)).symm)
  have hp1 : Function.Bijective (p 1) := by
    refine ⟨(injective_iff_map_eq_zero (p 1)).2 fun x hx => ?_, fun y => (e2 0 y).1 (hd0 y)⟩
    obtain ⟨z, rfl⟩ := (e1 1 x).1 hx
    have := hA0 1 (by norm_num)
    rw [Subsingleton.elim z 0, map_zero]
  refine ⟨⟨(LinearEquiv.ofBijective (i 0) ⟨hi0', hi0⟩).symm.trans eA⟩,
    ⟨(LinearEquiv.ofBijective (p 1) hp1).trans eR⟩, fun n hn => ⟨fun x y => ?_⟩⟩
  have := hA0 n (by omega)
  have := hR0 n (by omega)
  have h0 : ∀ z : homologyIndex K ϕ h.isolated n, z = 0 := fun x => by
    obtain ⟨z, rfl⟩ := (e1 n x).1 (Subsingleton.elim _ _)
    rw [Subsingleton.elim z 0, map_zero]
  rw [h0 x, h0 y]

end ConleyCheck.Conley
