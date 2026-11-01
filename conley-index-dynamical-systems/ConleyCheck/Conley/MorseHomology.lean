import ConleyCheck.Conley.MorseSets
import ConleyCheck.Conley.Regular

/-!
# Homology indices of Morse decompositions

Consequences of the attractor–repeller sequence that replace the use of connection matrices.

* `connecting_bijective_of_trivial`: in an isolated invariant set with trivial homology index, the
  connecting homomorphisms of an attractor–repeller pair are isomorphisms.
* `HasHomologyIndex.shift`: in that situation `CH_*(A) = K[m]` gives `CH_*(R) = K[m+1]`.
* `IsTrivialPair.exists_connecting`: in that situation there are connecting orbits from `R` to `A`
  unless `CH_*(A) = 0`.
* `diamond_*`: for a Morse decomposition `M₀ < M₁, M₂ < M₃` of a set with trivial homology index,
  with `CH_*(M₀) = K[0]` and `CH_*(M₀ ∪ M₁ ∪ ...) = 0` for the attractors over the two middle sets,
  the indices are `K[0], K[1], K[1], K[2]`, the four connecting homomorphisms along the edges are
  isomorphisms, and the four connecting orbits exist.
-/

universe u

namespace ConleyCheck.Conley

open Set

variable (K : Type u) [Ring K] {α : Type u} [TopologicalSpace α] [T2Space α] {ϕ : Flow ℝ α}

/-- `CH_*(S) = K[m]`. -/
def HasHomologyIndex {S : Set α} (hS : IsIsolatedInvariantSet ϕ S) (m : ℕ) : Prop :=
  Nonempty (homologyIndex K ϕ hS m ≃ₗ[K] K) ∧ ∀ n, n ≠ m → Subsingleton (homologyIndex K ϕ hS n)

/-- `CH_*(S) = 0`. -/
def HasTrivialHomologyIndex {S : Set α} (hS : IsIsolatedInvariantSet ϕ S) : Prop :=
  ∀ n, Subsingleton (homologyIndex K ϕ hS n)

variable {K}

theorem HasHomologyIndex.not_trivial [Nontrivial K] {S : Set α} {hS : IsIsolatedInvariantSet ϕ S}
    {m : ℕ} (h : HasHomologyIndex K hS m) : ¬ HasTrivialHomologyIndex K hS := fun ht => by
  obtain ⟨e⟩ := h.1
  have := ht m
  have : Subsingleton K := e.symm.toEquiv.subsingleton
  exact not_subsingleton K this

theorem HasHomologyIndex.of_bijective {S T : Set α} {hS : IsIsolatedInvariantSet ϕ S}
    {hT : IsIsolatedInvariantSet ϕ T} {m : ℕ} (h : HasHomologyIndex K hS m)
    (f : ∀ n, homologyIndex K ϕ hS n →ₗ[K] homologyIndex K ϕ hT n)
    (hf : ∀ n, Function.Bijective (f n)) : HasHomologyIndex K hT m := by
  obtain ⟨⟨e⟩, h0⟩ := h
  refine ⟨⟨(LinearEquiv.ofBijective (f m) (hf m)).symm.trans e⟩, fun n hn => ?_⟩
  have := h0 n hn
  exact (hf n).2.subsingleton

theorem HasTrivialHomologyIndex.of_bijective {S T : Set α} {hS : IsIsolatedInvariantSet ϕ S}
    {hT : IsIsolatedInvariantSet ϕ T} (h : HasTrivialHomologyIndex K hS)
    (f : ∀ n, homologyIndex K ϕ hS n →ₗ[K] homologyIndex K ϕ hT n)
    (hf : ∀ n, Function.Bijective (f n)) : HasTrivialHomologyIndex K hT := fun n => by
  have := h n
  exact (hf n).2.subsingleton

/-- An index pair with contractible quotient gives `CH_*(S) = 0`. -/
theorem hasTrivialHomologyIndex_of_indexPair {S N L : Set α} (hS : IsIsolatedInvariantSet ϕ S)
    (hP : IsIndexPair ϕ S N L) (hc : PointedContractible (IndexSpace N L) (IndexSpace.pt N L)) :
    HasTrivialHomologyIndex K hS := fun k => by
  obtain ⟨iso⟩ := homologyIndexIso K hS hP k
  have := redH_subsingleton K hc k
  exact iso.toLinearEquiv.toEquiv.subsingleton

/-! ## Attractor–repeller pairs in sets with trivial index -/

section Pair

variable {S A R : Set α} (h : IsAttractorRepellerPair ϕ S A R)
include h

/-- In an isolated invariant set with trivial homology index, the connecting homomorphisms of an
attractor–repeller sequence are isomorphisms. -/
theorem connecting_bijective_of_trivial (hS : HasTrivialHomologyIndex K h.isolated)
    {i : ∀ n, homologyIndex K ϕ h.isolated_A n →ₗ[K] homologyIndex K ϕ h.isolated n}
    {p : ∀ n, homologyIndex K ϕ h.isolated n →ₗ[K] homologyIndex K ϕ h.isolated_R n}
    {d : ∀ n, homologyIndex K ϕ h.isolated_R (n + 1) →ₗ[K] homologyIndex K ϕ h.isolated_A n}
    (h2 : ∀ n, Function.Exact (p (n + 1)) (d n)) (h3 : ∀ n, Function.Exact (d n) (i n))
    (n : ℕ) : Function.Bijective (d n) := by
  have := hS n
  have := hS (n + 1)
  refine ⟨(injective_iff_map_eq_zero (d n)).2 fun a ha => ?_, fun a => ?_⟩
  · obtain ⟨b, rfl⟩ := (h2 n a).1 ha
    rw [Subsingleton.elim b 0, map_zero]
  · exact (h3 n a).1 (Subsingleton.elim _ _)

/-- If `CH_*(S) = 0` then `CH_*(R) ≅ CH_{*-1}(A)` through the connecting homomorphisms, and
`CH_0(R) = 0`. -/
theorem exists_connecting_iso_of_trivial (hS : HasTrivialHomologyIndex K h.isolated) :
    Subsingleton (homologyIndex K ϕ h.isolated_R 0) ∧
      ∃ d : ∀ n, homologyIndex K ϕ h.isolated_R (n + 1) →ₗ[K] homologyIndex K ϕ h.isolated_A n,
        ∀ n, Function.Bijective (d n) := by
  obtain ⟨i, p, d, -, h2, h3, h4⟩ := homologyIndex_attractor_repeller_of_pair K h
  have := hS 0
  exact ⟨h4.subsingleton, d, connecting_bijective_of_trivial h hS h2 h3⟩

/-- If `CH_*(S) = 0` and `CH_*(A) = K[m]`, then `CH_*(R) = K[m+1]`. -/
theorem HasHomologyIndex.shift (hS : HasTrivialHomologyIndex K h.isolated) {m : ℕ}
    (hA : HasHomologyIndex K h.isolated_A m) : HasHomologyIndex K h.isolated_R (m + 1) := by
  obtain ⟨h0, d, hd⟩ := exists_connecting_iso_of_trivial h hS
  obtain ⟨⟨e⟩, hA0⟩ := hA
  refine ⟨⟨(LinearEquiv.ofBijective (d m) (hd m)).trans e⟩, fun n hn => ?_⟩
  cases n with
  | zero => exact h0
  | succ n =>
    have := hA0 n fun h => hn (by rw [h])
    exact (hd n).1.subsingleton

/-- If `CH_*(S) = 0` and `S` has no connecting orbits from `R` to `A`, then
`CH_*(A) = CH_*(R) = 0`. -/
theorem trivial_of_subset_union (hS : HasTrivialHomologyIndex K h.isolated) (hAR : S ⊆ A ∪ R) :
    HasTrivialHomologyIndex K h.isolated_A ∧ HasTrivialHomologyIndex K h.isolated_R := by
  obtain ⟨hR0, d, hd⟩ := exists_connecting_iso_of_trivial h hS
  obtain ⟨hA0, d', hd'⟩ := exists_connecting_iso_of_trivial (h.swap hAR) hS
  have key : ∀ n, Subsingleton (homologyIndex K ϕ h.isolated_A n) ∧
      Subsingleton (homologyIndex K ϕ h.isolated_R n) := by
    intro n
    induction n with
    | zero => exact ⟨hA0, hR0⟩
    | succ n ih =>
      obtain ⟨hA, hR⟩ := ih
      exact ⟨(hd' n).1.subsingleton, (hd n).1.subsingleton⟩
  exact ⟨fun n => (key n).1, fun n => (key n).2⟩

/-- If `CH_*(S) = 0` and `CH_*(A) ≠ 0`, there is an orbit in `S` running from `R` to `A`. -/
theorem exists_connecting_of_trivial (hS : HasTrivialHomologyIndex K h.isolated)
    (hA0 : ¬ HasTrivialHomologyIndex K h.isolated_A) :
    ∃ x ∈ S, x ∉ A ∧ x ∉ R ∧ omegaLim ϕ x ⊆ A ∧ alphaLim ϕ x ⊆ R := by
  by_contra hno
  push Not at hno
  refine hA0 (trivial_of_subset_union h hS fun x hx => ?_).1
  by_contra hxAR
  rw [mem_union, not_or] at hxAR
  have := h.connecting x hx hxAR.1 hxAR.2
  exact hno x hx hxAR.1 hxAR.2 this.1 this.2

end Pair

/-- `A` and `R` form an attractor–repeller pair in an isolated invariant set with trivial homology
index. Then every connecting homomorphism `CH_{n+1}(R) → CH_n(A)` of the pair is an isomorphism. -/
def IsTrivialPair (K : Type u) [Ring K] (ϕ : Flow ℝ α) (A R : Set α) : Prop :=
  ∃ S, ∃ h : IsAttractorRepellerPair ϕ S A R, HasTrivialHomologyIndex K h.isolated

namespace IsTrivialPair

variable {A R : Set α}

/-- The attractor–repeller sequence of the pair, whose connecting homomorphisms are all
isomorphisms. -/
theorem connecting (H : IsTrivialPair K ϕ A R) :
    ∃ S, ∃ h : IsAttractorRepellerPair ϕ S A R,
      ∃ (i : ∀ n, homologyIndex K ϕ h.isolated_A n →ₗ[K] homologyIndex K ϕ h.isolated n)
        (p : ∀ n, homologyIndex K ϕ h.isolated n →ₗ[K] homologyIndex K ϕ h.isolated_R n)
        (d : ∀ n, homologyIndex K ϕ h.isolated_R (n + 1) →ₗ[K] homologyIndex K ϕ h.isolated_A n),
        (∀ n, Function.Exact (i n) (p n)) ∧ (∀ n, Function.Exact (p (n + 1)) (d n)) ∧
          (∀ n, Function.Exact (d n) (i n)) ∧ ∀ n, Function.Bijective (d n) := by
  obtain ⟨S, h, hS⟩ := H
  obtain ⟨i, p, d, h1, h2, h3, -⟩ := homologyIndex_attractor_repeller_of_pair K h
  exact ⟨S, h, i, p, d, h1, h2, h3, connecting_bijective_of_trivial h hS h2 h3⟩

/-- If `CH_*(A) ≠ 0`, there is an orbit running from `R` to `A`. -/
theorem exists_connecting (H : IsTrivialPair K ϕ A R) (hA : IsIsolatedInvariantSet ϕ A)
    (hA0 : ¬ HasTrivialHomologyIndex K hA) :
    ∃ S, A ⊆ S ∧ R ⊆ S ∧ ∃ x ∈ S, x ∉ A ∧ x ∉ R ∧ omegaLim ϕ x ⊆ A ∧ alphaLim ϕ x ⊆ R := by
  obtain ⟨S, h, hS⟩ := H
  exact ⟨S, h.subset_A, h.subset_R, exists_connecting_of_trivial h hS hA0⟩

end IsTrivialPair

/-! ## Four Morse sets in a diamond -/

/-- The order of a Morse decomposition `M₀ < M₁, M₂ < M₃`, with `M₁` and `M₂` unrelated. -/
def diamond (i j : Fin 4) : Prop := (i = 0 ∧ j ≠ 0) ∨ (j = 3 ∧ i ≠ 3)

theorem diamond_irrefl (i : Fin 4) : ¬ diamond i i := by
  unfold diamond; omega

theorem diamond_trans (i j k : Fin 4) : diamond i j → diamond j k → diamond i k := by
  unfold diamond; omega

theorem isDown_diamond {P : Set (Fin 4)} (h0 : 0 ∈ P) (h3 : 3 ∈ P → P = univ) :
    IsDown diamond P := by
  intro i j hij hj
  rcases hij with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact h0
  · rw [h3 hj]; exact mem_univ i

section Diamond

variable {S : Set α} {M : Fin 4 → Set α} (h : IsMorseDecomp ϕ S M diamond)
  (hS : HasTrivialHomologyIndex K h.isolated) (h0 : HasHomologyIndex K (h.isolated_M 0) 0)
  (h01 : ∀ hA : IsIsolatedInvariantSet ϕ (morseAttr ϕ S M {0, 1}), HasTrivialHomologyIndex K hA)
  (h02 : ∀ hA : IsIsolatedInvariantSet ϕ (morseAttr ϕ S M {0, 2}), HasTrivialHomologyIndex K hA)

omit [T2Space α] in
theorem down0 : IsDown diamond ({0} : Set (Fin 4)) :=
  isDown_diamond rfl fun h => absurd h (by decide)

theorem down01 : IsDown diamond ({0, 1} : Set (Fin 4)) :=
  isDown_diamond (by simp) fun h => absurd h (by simp)

theorem down02 : IsDown diamond ({0, 2} : Set (Fin 4)) :=
  isDown_diamond (by simp) fun h => absurd h (by simp)

theorem down012 : IsDown diamond ({0, 1, 2} : Set (Fin 4)) :=
  isDown_diamond (by simp) fun h => absurd h (by simp)

include h in
/-- The pair `(M₀, M_k)` in `M₀ ∪ M_k` with its connecting orbits, for `k = 1, 2`. -/
theorem diamond_pair_bottom {k : Fin 4} (hk : k = 1 ∨ k = 2) :
    IsAttractorRepellerPair ϕ (morseAttr ϕ S M {0, k}) (M 0) (M k) := by
  have hP : IsDown diamond ({0, k} : Set (Fin 4)) := by
    rcases hk with rfl | rfl
    · exact down01
    · exact down02
  have hk0 : k ≠ 0 := by rcases hk with rfl | rfl <;> decide
  have hpair := h.isAttractorRepellerPair hP down0 (by simp)
  rwa [h.attr_singleton down0, h.attr_inter_rep_eq hP down0 (k := k) (by simp) (by simpa using hk0)
    (fun l hl hl0 => by simp only [mem_insert_iff, mem_singleton_iff] at hl hl0; tauto)] at hpair

include h in
/-- The pair `(M_k, M₃)`, for `k = 1, 2`, in the Morse set of `{k, 3}`. -/
theorem diamond_pair_top {k l : Fin 4} (hkl : (k = 1 ∧ l = 2) ∨ (k = 2 ∧ l = 1)) :
    IsAttractorRepellerPair ϕ (morseAttr ϕ S M univ ∩ morseRep ϕ S M {0, l}ᶜ) (M k) (M 3) := by
  have hQ : IsDown diamond ({0, l} : Set (Fin 4)) := by
    rcases hkl with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact down02
    · exact down01
  have hQP' : ({0, l} : Set (Fin 4)) ⊆ {0, 1, 2} := by
    rcases hkl with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> intro x hx <;>
      simp only [mem_insert_iff, mem_singleton_iff] at hx ⊢ <;> omega
  have hpair := h.isAttractorRepellerPair_interval (isDown_diamond (mem_univ 0) fun _ => rfl)
    down012 hQ hQP' (subset_univ _)
  rwa [h.attr_inter_rep_eq down012 hQ (k := k) (by rcases hkl with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp)
      (by rcases hkl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
      (fun m hm hmQ => by
        rcases hkl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp only [mem_insert_iff, mem_singleton_iff] at hm hmQ <;> omega),
    h.attr_inter_rep_eq (isDown_diamond (mem_univ 0) fun _ => rfl) down012 (k := 3)
      (mem_univ 3) (by decide)
      (fun m _ hmQ => by simp only [mem_insert_iff, mem_singleton_iff] at hmQ; omega)] at hpair

include h0 h01 h02

/-- `CH_*(M₁) = CH_*(M₂) = K[1]`. -/
theorem diamond_middle {k : Fin 4} (hk : k = 1 ∨ k = 2) :
    HasHomologyIndex K (h.isolated_M k) 1 := by
  have hpair := diamond_pair_bottom h hk
  have hS' : HasTrivialHomologyIndex K hpair.isolated := by
    rcases hk with rfl | rfl
    · exact h01 _
    · exact h02 _
  exact HasHomologyIndex.shift hpair hS' h0

include hS in
/-- `CH_*(M₃) = K[2]`. -/
theorem diamond_top : HasHomologyIndex K (h.isolated_M 3) 2 := by
  have hpair := h.isAttractorRepellerPair (isDown_diamond (mem_univ 0) fun _ => rfl) down012
    (subset_univ _)
  rw [h.attr_inter_rep_eq (isDown_diamond (mem_univ 0) fun _ => rfl) down012 (k := 3)
    (mem_univ 3) (by decide)
    (fun m _ hmQ => by simp only [mem_insert_iff, mem_singleton_iff] at hmQ; omega)] at hpair
  have hS' : HasTrivialHomologyIndex K hpair.isolated := by
    have he := h.attr_univ
    exact fun n => by
      have := hS n
      convert this using 3
  have hmid : HasHomologyIndex K hpair.isolated_A 1 := by
    have hpair' := h.isAttractorRepellerPair down012 down01 (by
      intro x hx; simp only [mem_insert_iff, mem_singleton_iff] at hx ⊢; omega)
    rw [h.attr_inter_rep_eq down012 down01 (k := 2) (by simp) (by simp)
      (fun m hm hmQ => by simp only [mem_insert_iff, mem_singleton_iff] at hm hmQ; omega)]
      at hpair'
    obtain ⟨p, hp⟩ := homologyIndex_repeller_iso_of_pair K hpair' (h01 _)
    obtain ⟨⟨e⟩, hz⟩ := diamond_middle h h0 h01 h02 (k := 2) (Or.inr rfl)
    refine ⟨⟨(LinearEquiv.ofBijective (p 1) (hp 1)).trans e⟩, fun n hn => ?_⟩
    have := hz n hn
    exact (hp n).1.subsingleton
  exact HasHomologyIndex.shift hpair hS' hmid

include h in
omit h0 in
/-- The pairs `(M₀, M_k)` for `k = 1, 2` live in sets with trivial homology index. -/
theorem diamond_trivialPair_bottom {k : Fin 4} (hk : k = 1 ∨ k = 2) :
    IsTrivialPair K ϕ (M 0) (M k) := by
  refine ⟨_, diamond_pair_bottom h hk, ?_⟩
  rcases hk with rfl | rfl
  · exact h01 _
  · exact h02 _

include hS in
omit h0 in
/-- The Morse set of `{k, 3}` has trivial homology index, for `k = 1, 2`. -/
theorem diamond_top_trivial {k l : Fin 4} (hkl : (k = 1 ∧ l = 2) ∨ (k = 2 ∧ l = 1)) :
    HasTrivialHomologyIndex K (diamond_pair_top h hkl).isolated := by
  have hQ : IsDown diamond ({0, l} : Set (Fin 4)) := by
    rcases hkl with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact down02
    · exact down01
  have hpair := h.isAttractorRepellerPair (isDown_diamond (mem_univ 0) fun _ => rfl) hQ
    (subset_univ _)
  have hA : HasTrivialHomologyIndex K hpair.isolated_A := by
    rcases hkl with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact h02 _
    · exact h01 _
  obtain ⟨p, hp⟩ := homologyIndex_repeller_iso_of_pair K hpair hA
  have hS' : HasTrivialHomologyIndex K hpair.isolated := by
    have he := h.attr_univ
    exact fun n => by
      have := hS n
      convert this using 3
  exact HasTrivialHomologyIndex.of_bijective hS' p hp

include hS in
omit h0 in
/-- The pairs `(M_k, M₃)` for `k = 1, 2` live in sets with trivial homology index. -/
theorem diamond_trivialPair_top {k l : Fin 4} (hkl : (k = 1 ∧ l = 2) ∨ (k = 2 ∧ l = 1)) :
    IsTrivialPair K ϕ (M k) (M 3) :=
  ⟨_, diamond_pair_top h hkl, diamond_top_trivial h hS h01 h02 hkl⟩

omit h0 in
include h in
/-- For `CH_*(M₀) ≠ 0` there are orbits from `M_k` to `M₀`, `k = 1, 2`. -/
theorem diamond_orbit_bottom (h0' : ¬ HasTrivialHomologyIndex K (h.isolated_M 0)) {k : Fin 4}
    (hk : k = 1 ∨ k = 2) :
    ∃ x ∈ S, x ∉ M 0 ∧ x ∉ M k ∧ omegaLim ϕ x ⊆ M 0 ∧ alphaLim ϕ x ⊆ M k := by
  have hpair := diamond_pair_bottom h hk
  have hS' : HasTrivialHomologyIndex K hpair.isolated := by
    rcases hk with rfl | rfl
    · exact h01 _
    · exact h02 _
  obtain ⟨x, hx, h1, h2, h3, h4⟩ := exists_connecting_of_trivial hpair hS' h0'
  exact ⟨x, hx.1, h1, h2, h3, h4⟩

include hS in
/-- There are orbits from `M₃` to `M_k`, `k = 1, 2`, for `K` nontrivial. -/
theorem diamond_orbit_top [Nontrivial K] {k l : Fin 4} (hkl : (k = 1 ∧ l = 2) ∨ (k = 2 ∧ l = 1)) :
    ∃ x ∈ S, x ∉ M k ∧ x ∉ M 3 ∧ omegaLim ϕ x ⊆ M k ∧ alphaLim ϕ x ⊆ M 3 := by
  have hk : k = 1 ∨ k = 2 := by rcases hkl with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have hA := (diamond_middle h h0 h01 h02 hk).not_trivial
  obtain ⟨x, hx, h1, h2, h3, h4⟩ :=
    exists_connecting_of_trivial (diamond_pair_top h hkl) (diamond_top_trivial h hS h01 h02 hkl) hA
  exact ⟨x, hx.1.1, h1, h2, h3, h4⟩

end Diamond

end ConleyCheck.Conley
