import ConleyCheck.Conley.EquivEuler
import ConleyCheck.Conley.EquivQuotient

/-!
# The homology of the fixed-point set `Y^R`

Theorem `thm:equivariant`(iii) uses `χ̃(Y^R) = χ̃(h(K₊)) + χ̃(h(K₋))`, which follows from
`Y^R ≅ (N₊/L₊) ∨ (N₋/L₋)` (`fixedHomeo`) once reduced homology is additive. Here the additivity is
proved directly for `Y^R`, for every index pair `(N, L)` of `S`:
`H̃_n(Y^R) ≅ CH_n(K₊; f₊) × CH_n(K₋; f₋)` (`fixed_homology`).

* `singH_disjoint`: if `P` lies in the union of disjoint open sets `U₁, U₂`, then
  `H_*(P, Q) ≅ H_*(P ∩ U₁, Q ∩ U₁) × H_*(P ∩ U₂, Q ∩ U₂)`. The proof uses excision and the exact
  sequence of a triple.
* `IsIndexPair.restrictInv`, `IsCollared.restrictInv`: a (collared) index pair restricts to a
  (collared) index pair of the flow on a closed invariant set.
* `fixHomeo`: `Y^R` is the index space of the fixed part `(N_F, L_F)` of `(q⁻¹N, q⁻¹L)`, an index
  pair for the flow on `Fix(R) = X × {0} ⊔ X × {π}`.
* `fixed_homology_of_collared`: the additivity for a collared pair, by excision on `(N_F, L_F)`.
* `fixed_homology`, `euler_fixed`, `equivariant_iii_fixed`: the additivity, and Theorem
  `thm:equivariant`(iii) in the form `χ(S̃) = 2 χ(S) - χ̃(Y^R)`.
* `euler_rel_fixed`: `χ̃(h(S)) - χ̃(Y^R) = -χ̃(h(K₋))`, the remark after `thm:equivariant` that
  homology relative to the fixed points is UV data.
-/

namespace ConleyCheck.Conley

open CategoryTheory Limits Set Function Topology Finset

universe u

/-! ### Relative homology of a disjoint union -/

section Disjoint

variable (K : Type u) [Ring K] {α : Type u} [TopologicalSpace α]

theorem singIncl_comp_apply (k : ℤ) {N L N' L' N'' L'' : Set α} (hN : N ⊆ N') (hL : L ⊆ L')
    (hN' : N' ⊆ N'') (hL' : L' ⊆ L'') (x : singH K α k N L) :
    (singIncl K k hN' hL').hom ((singIncl K k hN hL).hom x) =
      (singIncl K k (hN.trans hN') (hL.trans hL')).hom x :=
  congrArg (fun φ => φ.hom x) (singIncl_comp K k hN hL hN' hL')

/-- `H_*(B, A)` depends only on `B ∩ A`. -/
theorem singIncl_bijective_of_inter {B A A' : Set α} (hA : A' ⊆ A) (h : B ∩ A ⊆ A') (k : ℤ) :
    Bijective (singIncl K k (subset_refl B) hA).hom := by
  cases k with
  | negSucc m => exact bijective_of_subsingleton _
  | ofNat n =>
    have hc : ∀ n, Bijective (relMapF (C := (singFunctor K).obj (TopCat.of α))
        (Q := chainSub K B) (Q' := chainSub K B) (P := chainSub K A') (P' := chainSub K A)
        (chainSub_mono K (subset_refl B)) (chainSub_mono K hA) n) := by
      intro n
      constructor
      · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro x hx
        induction x using Submodule.Quotient.induction_on with
        | H x =>
          rw [relMapF_mk, Submodule.Quotient.mk_eq_zero] at hx
          refine (Submodule.Quotient.mk_eq_zero _).2 ?_
          change (x : CX K (TopCat.of α) n) ∈ (chainSub K A').S n
          have hB := (mem_chainSub_iff B n (x : CX K (TopCat.of α) n)).1 x.2
          have hA₁ := (mem_chainSub_iff A n (x : CX K (TopCat.of α) n)).1 hx
          refine (mem_chainSub_iff A' n _).2 ?_
          have hBA : (basEquiv K _ n).symm (x : CX K (TopCat.of α) n) ∈
              Finsupp.supported K K (onSet B n ∩ onSet A n) := by
            rw [Finsupp.supported_inter]
            exact ⟨hB, hA₁⟩
          exact Finsupp.supported_mono (fun σ hσ => (subset_inter hσ.1 hσ.2).trans h) hBA
      · intro y
        induction y using Submodule.Quotient.induction_on with
        | H y => exact ⟨Submodule.Quotient.mk y, rfl⟩
    have : ∀ n, IsIso ((relMap _ (chainSub_mono K (subset_refl B)) (chainSub_mono K hA)).f n) :=
      fun n => (ConcreteCategory.isIso_iff_bijective _).2 (hc n)
    have := HomologicalComplex.Hom.isIso_of_components
      (relMap ((singFunctor K).obj (TopCat.of α)) (chainSub_mono K (subset_refl B))
        (chainSub_mono K hA))
    change Bijective (HomologicalComplex.homologyMap (relMap ((singFunctor K).obj (TopCat.of α))
      (chainSub_mono K (subset_refl B)) (chainSub_mono K hA)) n).hom
    exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

/-- `H_*(B, A) = 0` if `B ⊆ A`. -/
theorem singH_subsingleton_of_subset {B A : Set α} (h : B ⊆ A) (k : ℤ) :
    Subsingleton (singH K α k B A) := by
  cases k with
  | negSucc m => infer_instance
  | ofNat n =>
    exact relCx_homology_subsingleton (chainSub K B) (chainSub K A) n fun z hz _ =>
      ⟨0, zero_mem _, by rw [map_zero, sub_zero]; exact chainSub_mono K h n hz⟩

variable {K} {P Q U₁ U₂ : Set α}

theorem bijective_singIncl_comp {N L N' L' N'' L'' : Set α} {k : ℤ} {hN : N ⊆ N'} {hL : L ⊆ L'}
    {hN' : N' ⊆ N''} {hL' : L' ⊆ L''} (h₁ : Bijective (singIncl K k hN hL).hom)
    (h₂ : Bijective (singIncl K k hN' hL').hom) :
    Bijective (singIncl K k (hN.trans hN') (hL.trans hL')).hom := by
  have e : ⇑(singIncl K k (hN.trans hN') (hL.trans hL')).hom =
      ⇑(singIncl K k hN' hL').hom ∘ ⇑(singIncl K k hN hL).hom :=
    funext fun x => (singIncl_comp_apply K k hN hL hN' hL' x).symm
  rw [e]
  exact h₂.comp h₁

/-- One half of the splitting of `H_*(P, Q)` along `P = (P ∩ U₁) ⊔ (P ∩ U₂)`. -/
theorem disjoint_side (hQP : Q ⊆ P) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU : Disjoint U₁ U₂)
    (hPU : P ⊆ U₁ ∪ U₂) (k : ℤ) :
    Bijective (singIncl K k (inter_subset_left : P ∩ U₁ ⊆ P)
      (fun _ hx => Or.inl hx.1 : Q ∩ U₁ ⊆ Q ∪ P ∩ U₂)).hom ∧
    Bijective (singIncl K k (inter_subset_left : P ∩ U₁ ⊆ P)
      (subset_union_left : Q ⊆ Q ∪ P ∩ U₂)).hom ∧
    (∀ x, (singIncl K k (subset_refl P) (subset_union_left : Q ⊆ Q ∪ P ∩ U₂)).hom x = 0 →
      ∃ w, (singIncl K k (inter_subset_left : P ∩ U₂ ⊆ P) (subset_refl Q)).hom w = x) ∧
    (∀ z, (singIncl K k (subset_refl P) (subset_union_left : Q ⊆ Q ∪ P ∩ U₂)).hom
      ((singIncl K k (inter_subset_left : P ∩ U₂ ⊆ P) (inter_subset_left : Q ∩ U₂ ⊆ Q)).hom z) =
        0) := by
  have hdis : ∀ x, x ∈ U₁ → x ∉ U₂ := fun x h1 h2 => hU.ne_of_mem h1 h2 rfl
  have exc : Bijective (singIncl K k (inter_subset_left : P ∩ U₁ ⊆ P)
      (subset_refl (Q ∪ P ∩ U₂))).hom :=
    excision K (X := P) (A := Q ∪ P ∩ U₂) (B := P ∩ U₁) (OA := U₂) (OB := U₁)
      (union_subset hQP inter_subset_left) inter_subset_left hU₂ hU₁
      (fun x hx => (hPU hx).symm) (fun x hx => Or.inr ⟨hx.2, hx.1⟩) (fun x hx => ⟨hx.2, hx.1⟩) k
  refine ⟨?_, ?_, fun x hx => ?_, fun z => ?_⟩
  · refine bijective_singIncl_comp (hN := subset_refl _) (hL := fun _ hx => Or.inl hx.1)
      (singIncl_bijective_of_inter K _ ?_ k) exc
    rintro x ⟨hP, hq | hp⟩
    · exact ⟨hq, hP.2⟩
    · exact absurd hp.2 (hdis x hP.2)
  · refine bijective_singIncl_comp (hN := subset_refl _) (hL := subset_union_left)
      (singIncl_bijective_of_inter K _ ?_ k) exc
    rintro x ⟨hP, hq | hp⟩
    · exact hq
    · exact absurd hp.2 (hdis x hP.2)
  · obtain ⟨y, rfl⟩ := (sing_exact_incl K k (subset_union_left : Q ⊆ Q ∪ P ∩ U₂)
      (union_subset hQP inter_subset_left) x).1 hx
    have c := excision K (X := Q ∪ P ∩ U₂) (A := Q) (B := P ∩ U₂) (OA := U₁) (OB := U₂)
      subset_union_left subset_union_right hU₁ hU₂
      (fun x hx => by
        rcases hx with hq | hp
        · exact hPU (hQP hq)
        · exact Or.inr hp.2)
      (fun x ⟨h1, hx⟩ => by
        rcases hx with hq | hp
        · exact hq
        · exact absurd hp.2 (hdis x h1))
      (fun x ⟨h2, hx⟩ => by
        rcases hx with hq | hp
        · exact ⟨hQP hq, h2⟩
        · exact hp) k
    obtain ⟨w, rfl⟩ := c.2 y
    exact ⟨w, (singIncl_comp_apply K k _ _ _ _ w).symm⟩
  · rw [singIncl_comp_apply]
    have hs : (singIncl K k (inter_subset_left.trans (subset_refl P))
        ((inter_subset_left : Q ∩ U₂ ⊆ Q).trans subset_union_left)).hom z =
        (singIncl K k (inter_subset_left : P ∩ U₂ ⊆ P) (subset_refl _)).hom
          ((singIncl K k (subset_refl _) (fun _ hx => Or.inl hx.1 :
            Q ∩ U₂ ⊆ Q ∪ P ∩ U₂)).hom z) :=
      (singIncl_comp_apply K k _ _ _ _ z).symm
    rw [hs]
    have hsub := singH_subsingleton_of_subset K (subset_union_right : P ∩ U₂ ⊆ Q ∪ P ∩ U₂) k
    exact (congrArg (singIncl K k (inter_subset_left : P ∩ U₂ ⊆ P) (subset_refl _)).hom
      (@Subsingleton.elim _ hsub _ 0)).trans (map_zero _)

variable (K) in
/-- Additivity of relative homology: if `P ⊆ U₁ ∪ U₂` with `U₁, U₂` open and disjoint, then
`H_*(P, Q) ≅ H_*(P ∩ U₁, Q ∩ U₁) × H_*(P ∩ U₂, Q ∩ U₂)`. -/
theorem singH_disjoint (hQP : Q ⊆ P) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU : Disjoint U₁ U₂)
    (hPU : P ⊆ U₁ ∪ U₂) (k : ℤ) :
    Nonempty (singH K α k P Q ≃ₗ[K]
      singH K α k (P ∩ U₁) (Q ∩ U₁) × singH K α k (P ∩ U₂) (Q ∩ U₂)) := by
  obtain ⟨E₁, -, ex₁, z₁⟩ := disjoint_side (K := K) hQP hU₁ hU₂ hU hPU k
  obtain ⟨E₂, b₂, -, z₂⟩ := disjoint_side (K := K) hQP hU₂ hU₁ hU.symm (fun x hx => (hPU hx).symm) k
  let e₁ := LinearEquiv.ofBijective _ E₁
  let e₂ := LinearEquiv.ofBijective _ E₂
  let π₁ := (singIncl K k (subset_refl P) (subset_union_left : Q ⊆ Q ∪ P ∩ U₂)).hom
  let π₂ := (singIncl K k (subset_refl P) (subset_union_left : Q ⊆ Q ∪ P ∩ U₁)).hom
  let j₁ := (singIncl K k (inter_subset_left : P ∩ U₁ ⊆ P) (inter_subset_left : Q ∩ U₁ ⊆ Q)).hom
  let j₂ := (singIncl K k (inter_subset_left : P ∩ U₂ ⊆ P) (inter_subset_left : Q ∩ U₂ ⊆ Q)).hom
  have hj₁ : ∀ a, π₁ (j₁ a) = e₁ a := fun a => singIncl_comp_apply K k _ _ _ _ a
  have hj₂ : ∀ b, π₂ (j₂ b) = e₂ b := fun b => singIncl_comp_apply K k _ _ _ _ b
  let Ψ := (e₁.symm.toLinearMap ∘ₗ π₁).prod (e₂.symm.toLinearMap ∘ₗ π₂)
  refine ⟨LinearEquiv.ofBijective Ψ ⟨?_, fun ab => ⟨j₁ ab.1 + j₂ ab.2, ?_⟩⟩⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : π₁ x = 0 := by
      have h := congrArg Prod.fst hx
      change e₁.symm (π₁ x) = 0 at h
      exact e₁.symm.map_eq_zero_iff.1 h
    have h2 : π₂ x = 0 := by
      have h := congrArg Prod.snd hx
      change e₂.symm (π₂ x) = 0 at h
      exact e₂.symm.map_eq_zero_iff.1 h
    obtain ⟨w, rfl⟩ := ex₁ x h1
    have hw : (singIncl K k (inter_subset_left : P ∩ U₂ ⊆ P)
        (subset_union_left : Q ⊆ Q ∪ P ∩ U₁)).hom w = 0 :=
      (singIncl_comp_apply K k _ _ _ _ w).symm.trans h2
    rw [b₂.1 (hw.trans (map_zero _).symm), map_zero]
  · refine Prod.ext ?_ ?_
    · change e₁.symm (π₁ (j₁ ab.1 + j₂ ab.2)) = ab.1
      have e : π₁ (j₁ ab.1 + j₂ ab.2) = e₁ ab.1 :=
        ((map_add π₁ _ _).trans (congrArg₂ (· + ·) (hj₁ ab.1) (z₁ ab.2))).trans (add_zero _)
      rw [e, LinearEquiv.symm_apply_apply]
    · change e₂.symm (π₂ (j₁ ab.1 + j₂ ab.2)) = ab.2
      have e : π₂ (j₁ ab.1 + j₂ ab.2) = e₂ ab.2 :=
        ((map_add π₂ _ _).trans (congrArg₂ (· + ·) (z₂ ab.1) (hj₂ ab.2))).trans (zero_add _)
      rw [e, LinearEquiv.symm_apply_apply]

end Disjoint

/-! ### Restriction to a closed invariant set -/

section Restrict

variable {α : Type u} [TopologicalSpace α] {ϕ : Flow ℝ α} {F : Set α} (hF : IsInvariant ϕ F)

include hF in
/-- An index pair of `S` restricts to an index pair of `S ∩ F` for the flow on a closed invariant
set `F`. -/
theorem IsIndexPair.restrictInv [T2Space α] {S N L : Set α} (h : IsIndexPair ϕ S N L)
    (hFc : IsClosed F) :
    IsIndexPair (ϕ.restrict hF) (Subtype.val ⁻¹' S) (Subtype.val ⁻¹' N) (Subtype.val ⁻¹' L) := by
  have hemb := hFc.isClosedEmbedding_subtypeVal
  have hint : (Subtype.val ⁻¹' S : Set F) ⊆
      interior ((Subtype.val ⁻¹' N : Set F) \ Subtype.val ⁻¹' L) := fun x hx =>
    preimage_interior_subset_interior_preimage continuous_subtype_val (h.nhds hx)
  have hSinv : ∀ x ∈ S, ∀ t, ϕ t x ∈ S := by
    intro x hx t
    rw [← h.inv_eq] at hx ⊢
    exact flow_mem_Inv hx t
  have hinv : Inv (ϕ.restrict hF) (closure ((Subtype.val ⁻¹' N : Set F) \ Subtype.val ⁻¹' L)) =
      Subtype.val ⁻¹' S := by
    ext x
    constructor
    · intro hx
      change (x : α) ∈ S
      rw [← h.inv_eq]
      intro t
      have hcl : closure ((Subtype.val ⁻¹' N : Set F) \ Subtype.val ⁻¹' L) ⊆
          Subtype.val ⁻¹' closure (N \ L) :=
        closure_minimal (fun y hy => subset_closure hy)
          (isClosed_closure.preimage continuous_subtype_val)
      exact hcl (hx t)
    · intro hx t
      exact subset_closure (interior_subset (hint (hSinv _ hx t)))
  refine ⟨hemb.isCompact_preimage h.isCompact_N, hemb.isCompact_preimage h.isCompact_L,
    fun x hx => h.subset hx, ⟨?_, ?_⟩, hinv, hint, fun x hx t ht hseg => h.posInv x hx t ht hseg,
    fun x hx t ht hout => h.exit x hx t ht hout⟩
  · exact (hemb.isCompact_preimage h.isCompact_N).of_isClosed_subset isClosed_closure
      (closure_minimal (fun x hx => hx.1)
        (h.isCompact_N.isClosed.preimage continuous_subtype_val))
  · rw [hinv]
    exact hint.trans (interior_mono subset_closure)

/-- A collar restricts to the flow on an invariant set. -/
theorem IsCollared.restrictInv {N L : Set α} (hc : IsCollared ϕ N L) :
    IsCollared (ϕ.restrict hF) (Subtype.val ⁻¹' N) (Subtype.val ⁻¹' L) := by
  obtain ⟨V, O, τ, hO, hLO, hON, hVN, hτc, hτ01, hτL, hseg, hhit⟩ := hc
  let f : (Subtype.val ⁻¹' V : Set F) → V := fun y => ⟨((y : F) : α), y.2⟩
  have hf : Continuous f := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  exact ⟨Subtype.val ⁻¹' V, Subtype.val ⁻¹' O, τ ∘ f, hO.preimage continuous_subtype_val,
    preimage_mono hLO, fun y hy => hON hy, preimage_mono hVN, hτc.comp hf, fun y => hτ01 (f y),
    fun y hy => hτL (f y) hy, fun y s hs => hseg (f y) s hs, fun y => hhit (f y)⟩

end Restrict

/-- A collar restricts to an invariant fiber of a skew product. -/
theorem IsCollared.fiber {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]
    {Φ : Flow ℝ (X × B)} {θ : Flow ℝ B} (hΦ : IsSkew Φ θ) {b₀ : B} (hb₀ : ∀ t, θ t b₀ = b₀)
    {N L : Set (X × B)} (hc : IsCollared Φ N L) :
    IsCollared (fiberFlow hΦ b₀ hb₀) {x | (x, b₀) ∈ N} {x | (x, b₀) ∈ L} := by
  obtain ⟨V, O, τ, hO, hLO, hON, hVN, hτc, hτ01, hτL, hseg, hhit⟩ := hc
  have hfib : ∀ t x, (fiberFlow hΦ b₀ hb₀ t x, b₀) = Φ t (x, b₀) := fun t x =>
    Prod.ext rfl (by rw [hΦ, hb₀])
  let f : {x | (x, b₀) ∈ V} → V := fun x => ⟨((x : X), b₀), x.2⟩
  have hf : Continuous f := (continuous_subtype_val.prodMk continuous_const).subtype_mk _
  refine ⟨{x | (x, b₀) ∈ V}, {x | (x, b₀) ∈ O}, τ ∘ f,
    hO.preimage (continuous_id.prodMk continuous_const), fun x hx => hLO hx,
    fun x hx => hON hx, fun x hx => hVN hx, hτc.comp hf, fun x => hτ01 (f x),
    fun x hx => hτL (f x) hx, fun x s hs => ?_, fun x => ?_⟩
  · change (fiberFlow hΦ b₀ hb₀ s x, b₀) ∈ V
    rw [hfib]
    exact hseg (f x) s hs
  · change (fiberFlow hΦ b₀ hb₀ (τ (f x)) x, b₀) ∈ L
    rw [hfib]
    exact hhit (f x)

/-- A homeomorphism preserving base points is a pointed homotopy equivalence. -/
def PointedHomotopyEquiv.ofHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {x₀ : X} {y₀ : Y} (h : e x₀ = y₀) : PointedHomotopyEquiv X Y x₀ y₀ where
  toFun := e
  invFun := e.symm
  map_pt := h
  inv_pt := by rw [← h]; exact e.symm_apply_apply x₀
  left := by
    have : (e.symm : C(Y, X)).comp (e : C(X, Y)) = ContinuousMap.id X := by
      ext x; exact e.symm_apply_apply x
    rw [this]
    exact ContinuousMap.HomotopicRel.refl _
  right := by
    have : (e : C(X, Y)).comp (e.symm : C(Y, X)) = ContinuousMap.id Y := by
      ext y; exact e.apply_symm_apply y
    rw [this]
    exact ContinuousMap.HomotopicRel.refl _

/-! ### The fixed part of the doubled index pair -/

section Fixed

variable {X : Type u} [TopologicalSpace X]

/-- `Fix(R) = X × {0} ⊔ X × {π}`. -/
abbrev fixR : Set (X × Circ) := {p | cR p = p}

/-- The fixed part `q⁻¹(N) ∩ Fix(R)`, as a subset of `Fix(R)`. -/
abbrev fixN (N : Set (X × Tau)) : Set (fixR : Set (X × Circ)) := Subtype.val ⁻¹' (cq ⁻¹' N)

/-- The sheet `θ = 0` of `Fix(R)`. -/
def fixU₀ : Set (fixR : Set (X × Circ)) := {p | 0 < ((p : X × Circ).2 : ℝ × ℝ).1}

/-- The sheet `θ = π` of `Fix(R)`. -/
def fixUπ : Set (fixR : Set (X × Circ)) := {p | ((p : X × Circ).2 : ℝ × ℝ).1 < 0}

theorem continuous_fixCos :
    Continuous fun p : (fixR : Set (X × Circ)) => ((p : X × Circ).2 : ℝ × ℝ).1 :=
  continuous_fst.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))

theorem isOpen_fixU₀ : IsOpen (fixU₀ : Set (fixR : Set (X × Circ))) :=
  isOpen_lt continuous_const continuous_fixCos

theorem isOpen_fixUπ : IsOpen (fixUπ : Set (fixR : Set (X × Circ))) :=
  isOpen_lt continuous_fixCos continuous_const

omit [TopologicalSpace X] in
theorem disjoint_fixU : Disjoint (fixU₀ : Set (fixR : Set (X × Circ))) fixUπ :=
  disjoint_left.2 fun p (h₀ : 0 < ((p : X × Circ).2 : ℝ × ℝ).1)
    (hπ : ((p : X × Circ).2 : ℝ × ℝ).1 < 0) => lt_asymm h₀ hπ

omit [TopologicalSpace X] in
theorem fixR_eq (p : (fixR : Set (X × Circ))) :
    (p : X × Circ).2 = Circ.zero ∨ (p : X × Circ).2 = Circ.pi :=
  (cR_eq_self_iff _).1 p.2

omit [TopologicalSpace X] in
theorem fixU_cover : (univ : Set (fixR : Set (X × Circ))) ⊆ fixU₀ ∪ fixUπ := by
  intro p _
  rcases fixR_eq p with h | h
  · left
    change 0 < ((p : X × Circ).2 : ℝ × ℝ).1
    rw [h]
    exact one_pos
  · right
    change ((p : X × Circ).2 : ℝ × ℝ).1 < 0
    rw [h]
    change (-1 : ℝ) < 0
    norm_num

/-- `x ↦ (x, 0)`. -/
def fixIota₀ : C(X, (fixR : Set (X × Circ))) :=
  ⟨fun x => ⟨(x, Circ.zero), (cR_eq_self_iff _).2 (Or.inl rfl)⟩,
    (continuous_id.prodMk continuous_const).subtype_mk _⟩

/-- `x ↦ (x, π)`. -/
def fixIotaπ : C(X, (fixR : Set (X × Circ))) :=
  ⟨fun x => ⟨(x, Circ.pi), (cR_eq_self_iff _).2 (Or.inr rfl)⟩,
    (continuous_id.prodMk continuous_const).subtype_mk _⟩

theorem isEmbedding_fixIota₀ (A : Set X) : IsEmbedding (A.domRestrict (fixIota₀ (X := X))) :=
  (IsEmbedding.of_comp fixIota₀.continuous
    (continuous_fst.comp continuous_subtype_val : Continuous fun p : (fixR : Set (X × Circ)) =>
      (p : X × Circ).1) IsEmbedding.id).comp IsEmbedding.subtypeVal

theorem isEmbedding_fixIotaπ (A : Set X) : IsEmbedding (A.domRestrict (fixIotaπ (X := X))) :=
  (IsEmbedding.of_comp fixIotaπ.continuous
    (continuous_fst.comp continuous_subtype_val : Continuous fun p : (fixR : Set (X × Circ)) =>
      (p : X × Circ).1) IsEmbedding.id).comp IsEmbedding.subtypeVal

variable (N L : Set (X × Tau))

/-- The base point of `Y^R`. -/
def YFix.pt : YFix N L := ⟨IndexSpace.pt _ _, rfl⟩

/-- `N_F / L_F → Y`. -/
noncomputable def fixMapY : C(IndexSpace (fixN N) (fixN L), IndexSpace (cq ⁻¹' N) (cq ⁻¹' L)) :=
  IndexSpace.mapC ⟨Subtype.val, continuous_subtype_val⟩ (fun _ h => h) (fun _ h => h)

theorem Ybar_fixMapY (z : IndexSpace (fixN N) (fixN L)) :
    Ybar N L (fixMapY N L z) = fixMapY N L z := by
  induction z using Quotient.inductionOn with
  | h a =>
    rcases a with y | u
    · exact congrArg (IndexSpace.proj _ _) (Subtype.ext (y.1.2))
    · rfl

/-- `N_F / L_F → Y^R`. -/
noncomputable def fixMap : C(IndexSpace (fixN N) (fixN L), YFix N L) :=
  ⟨fun z => ⟨fixMapY N L z, Ybar_fixMapY N L z⟩, (fixMapY N L).continuous.subtype_mk _⟩

theorem fixMap_pt : fixMap N L (IndexSpace.pt _ _) = YFix.pt N L := rfl

theorem fixMap_bijective : Bijective (fixMap N L) := by
  constructor
  · intro z₁ z₂ h
    have h' := congrArg Subtype.val h
    induction z₁ using Quotient.inductionOn with
    | h a =>
    induction z₂ using Quotient.inductionOn with
    | h b =>
    rcases a with y₁ | u <;> rcases b with y₂ | v
    · rcases (IndexSpace.proj_eq_proj_iff (L := cq ⁻¹' L)
        ⟨((y₁ : (fixR : Set (X × Circ))) : X × Circ), y₁.2⟩
        ⟨((y₂ : (fixR : Set (X × Circ))) : X × Circ), y₂.2⟩).1 h' with e | ⟨h1, h2⟩
      · exact congrArg (IndexSpace.proj _ _)
          (Subtype.ext (Subtype.ext (congrArg (fun q : cq ⁻¹' N => (q : X × Circ)) e)))
      · exact (IndexSpace.proj_eq_proj_iff y₁ y₂).2 (Or.inr ⟨h1, h2⟩)
    · exact IndexSpace.proj_eq_pt (L := fixN L) (x := y₁) ((IndexSpace.proj_eq_pt_iff
        (L := cq ⁻¹' L) ⟨((y₁ : (fixR : Set (X × Circ))) : X × Circ), y₁.2⟩).1 h')
    · exact (IndexSpace.proj_eq_pt (L := fixN L) (x := y₂) ((IndexSpace.proj_eq_pt_iff
        (L := cq ⁻¹' L) ⟨((y₂ : (fixR : Set (X × Circ))) : X × Circ), y₂.2⟩).1 h'.symm)).symm
    · rfl
  · rintro ⟨w, hw⟩
    induction w using Quotient.inductionOn with
    | h a =>
    rcases a with p | u
    · by_cases hpL : (p : X × Circ) ∈ cq ⁻¹' L
      · exact ⟨IndexSpace.pt _ _, Subtype.ext (IndexSpace.proj_eq_pt hpL).symm⟩
      · have hfix : cR (p : X × Circ) = p := by
          rcases (IndexSpace.proj_eq_proj_iff (L := cq ⁻¹' L) ⟨cR (p : X × Circ), p.2⟩ p).1 hw
            with e | ⟨-, h⟩
          · exact congrArg Subtype.val e
          · exact absurd h hpL
        exact ⟨IndexSpace.proj _ _ ⟨⟨p, hfix⟩, p.2⟩, rfl⟩
    · exact ⟨IndexSpace.pt _ _, rfl⟩

variable [T2Space X] {N L}

/-- `Y^R` is the index space `N_F / L_F` of the fixed part. -/
noncomputable def fixHomeo (hN : IsCompact N) (hL : IsClosed L) :
    IndexSpace (fixN N) (fixN L) ≃ₜ YFix N L := by
  have hNF : IsCompact (fixN N : Set (fixR : Set (X × Circ))) :=
    (isClosed_eq continuous_cR continuous_id).isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_cq_preimage hN)
  haveI := IndexSpace.compactSpace (fixN L) hNF
  haveI : T2Space (IndexSpace (cq ⁻¹' N) (cq ⁻¹' L)) :=
    IndexSpace.t2Space (isCompact_cq_preimage hN) (hL.preimage continuous_cq)
  exact (fixMap N L).continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ (fixMap_bijective N L))

end Fixed

/-! ### Additivity for `Y^R` -/

section Double

variable {X : Type u} [TopologicalSpace X] [T2Space X] [TopologicalSpace.MetrizableSpace X]
  {Φ : Flow ℝ (X × Tau)} {θ : Flow ℝ Tau} (hΦ : IsSkew Φ θ) (hθ : IsHeight θ (fun b => (b : ℝ)))

omit [T2Space X] [TopologicalSpace.MetrizableSpace X] in
theorem isInvariant_fixR : IsInvariant (circΦ hΦ hθ) (fixR : Set (X × Circ)) :=
  fun t p (hp : cR p = p) => show cR (circΦ hΦ hθ t p) = circΦ hΦ hθ t p by
    rw [cR_circΦ, hp]

omit [TopologicalSpace.MetrizableSpace X] in
include hΦ hθ in
/-- `H̃_n(Y^R) ≅ CH_n(K₊; f₊) × CH_n(K₋; f₋)` for a collared index pair `(N, L)` of `S`, where
`Y = q⁻¹(N)/q⁻¹(L)`. -/
theorem fixed_homology_of_collared (K : Type u) [Ring K] {S N L : Set (X × Tau)}
    (hP : IsIndexPair Φ S N L)
    (hc : IsCollared Φ N L)
    (hKp : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ)) {x | (x, Tau.top) ∈ S})
    (hKm : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ)) {x | (x, Tau.bot) ∈ S})
    (n : ℕ) :
    Nonempty (redH K (YFix N L) (YFix.pt N L) n ≃ₗ[K]
      homologyIndex K _ hKp n × homologyIndex K _ hKm n) := by
  obtain ⟨hPc, -, -, -, -, hPp, hPm⟩ := equivariant_i hΦ hθ hP
  have hinv := isInvariant_fixR hΦ hθ (X := X)
  have hPF := hPc.restrictInv hinv (isClosed_eq continuous_cR continuous_id)
  have hcF := (circ_collared hΦ hθ hc).restrictInv hinv
  let e0 := (redIso K (PointedHomotopyEquiv.ofHomeomorph
    (fixHomeo hP.isCompact_N hP.isCompact_L.isClosed) (fixMap_pt N L)) n).toLinearEquiv
  let e1 := collarEquiv K hPF hcF n
  obtain ⟨e2⟩ := singH_disjoint K (P := fixN N) (Q := fixN L) (fun _ h => hPc.subset h)
    isOpen_fixU₀ isOpen_fixUπ disjoint_fixU (fun p _ => fixU_cover (mem_univ p)) (Int.ofNat n)
  have bp := singMap_bijective K fixIota₀ (B := {x | (x, Tau.top) ∈ N})
    (A := {x | (x, Tau.top) ∈ L}) (B' := fixN N ∩ fixU₀) (A' := fixN L ∩ fixU₀)
    (fun x hx => ⟨hx, show (0 : ℝ) < 1 from one_pos⟩)
    (fun y hy => by
      rcases fixR_eq y with h | h
      · refine ⟨(y : X × Circ).1, ?_, Subtype.ext (Prod.ext rfl h.symm)⟩
        have hy0 : cq (y : X × Circ) ∈ N := hy.1
        rw [show (y : X × Circ) = ((y : X × Circ).1, Circ.zero) from Prod.ext rfl h] at hy0
        exact hy0
      · have h0 := hy.2
        simp only [fixU₀, mem_ofPred_eq, h] at h0
        exact absurd h0 (by change ¬ (0 : ℝ) < -1; norm_num))
    (isEmbedding_fixIota₀ _)
    (fun x _ => ⟨fun h => ⟨h, show (0 : ℝ) < 1 from one_pos⟩, fun h => h.1⟩) (Int.ofNat n)
  have bm := singMap_bijective K fixIotaπ (B := {x | (x, Tau.bot) ∈ N})
    (A := {x | (x, Tau.bot) ∈ L}) (B' := fixN N ∩ fixUπ) (A' := fixN L ∩ fixUπ)
    (fun x hx => ⟨hx, show (-1 : ℝ) < 0 by norm_num⟩)
    (fun y hy => by
      rcases fixR_eq y with h | h
      · have h0 := hy.2
        simp only [fixUπ, mem_ofPred_eq, h] at h0
        exact absurd h0 (by change ¬ (1 : ℝ) < 0; norm_num)
      · refine ⟨(y : X × Circ).1, ?_, Subtype.ext (Prod.ext rfl h.symm)⟩
        have hy0 : cq (y : X × Circ) ∈ N := hy.1
        rw [show (y : X × Circ) = ((y : X × Circ).1, Circ.pi) from Prod.ext rfl h] at hy0
        exact hy0)
    (isEmbedding_fixIotaπ _)
    (fun x _ => ⟨fun h => ⟨h, show (-1 : ℝ) < 0 by norm_num⟩, fun h => h.1⟩) (Int.ofNat n)
  let ep := homologyIndexEquiv K hKp hPp (hc.fiber hΦ (base_top hθ)) n
  let em := homologyIndexEquiv K hKm hPm (hc.fiber hΦ (base_bot hθ)) n
  exact ⟨e0.symm.trans (e1.symm.trans (e2.trans (LinearEquiv.prodCongr
    ((LinearEquiv.ofBijective _ bp).symm.trans ep.symm)
    ((LinearEquiv.ofBijective _ bm).symm.trans em.symm))))⟩

omit [TopologicalSpace.MetrizableSpace X] in
include hΦ hθ in
/-- `H̃_n(Y^R) ≅ CH_n(K₊; f₊) × CH_n(K₋; f₋)` for every index pair `(N, L)` of `S`. The fixed
parts of `(q⁻¹N, q⁻¹L)` and of a collared pair are index pairs of the same set for the flow on
`Fix(R)`, so their index spaces are homotopy equivalent. -/
theorem fixed_homology (K : Type u) [Ring K] {S N L : Set (X × Tau)} (hP : IsIndexPair Φ S N L)
    (hKp : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ)) {x | (x, Tau.top) ∈ S})
    (hKm : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ)) {x | (x, Tau.bot) ∈ S})
    (n : ℕ) :
    Nonempty (redH K (YFix N L) (YFix.pt N L) n ≃ₗ[K]
      homologyIndex K _ hKp n × homologyIndex K _ hKm n) := by
  obtain ⟨N', L', hP', hc'⟩ := exists_collared_indexPair hP.isIsolatedInvariantSet
  obtain ⟨e⟩ := fixed_homology_of_collared hΦ hθ K hP' hc' hKp hKm n
  obtain ⟨hPc, -⟩ := equivariant_i hΦ hθ hP
  obtain ⟨hPc', -⟩ := equivariant_i hΦ hθ hP'
  have hinv := isInvariant_fixR hΦ hθ (X := X)
  have hFc : IsClosed (fixR : Set (X × Circ)) := isClosed_eq continuous_cR continuous_id
  obtain ⟨u⟩ := indexPair_unique (hPc.restrictInv hinv hFc) (hPc'.restrictInv hinv hFc)
  let h0 := PointedHomotopyEquiv.ofHomeomorph
    (fixHomeo hP.isCompact_N hP.isCompact_L.isClosed) (fixMap_pt N L)
  let h0' := PointedHomotopyEquiv.ofHomeomorph
    (fixHomeo hP'.isCompact_N hP'.isCompact_L.isClosed) (fixMap_pt N' L')
  exact ⟨(redIso K h0 n).toLinearEquiv.symm.trans ((redIso K u n).toLinearEquiv.trans
    ((redIso K h0' n).toLinearEquiv.trans e))⟩

omit [TopologicalSpace.MetrizableSpace X] in
include hΦ hθ in
/-- `χ̃(Y^R) = χ̃(h(K₊)) + χ̃(h(K₋))`, truncated at degree `d`. -/
theorem euler_fixed (F : Type u) [Field F] {S N L : Set (X × Tau)} (hP : IsIndexPair Φ S N L)
    (hKp : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ)) {x | (x, Tau.top) ∈ S})
    (hKm : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ)) {x | (x, Tau.bot) ∈ S})
    [∀ k, FiniteDimensional F (homologyIndex F (fiberFlow hΦ Tau.top (base_top hθ)) hKp k)]
    [∀ k, FiniteDimensional F (homologyIndex F (fiberFlow hΦ Tau.bot (base_bot hθ)) hKm k)]
    (d : ℕ) :
    eulerSum (fun k => Module.finrank F (redH F (YFix N L) (YFix.pt N L) k)) d =
      eulerSum (fun k => Module.finrank F
          (homologyIndex F (fiberFlow hΦ Tau.top (base_top hθ)) hKp k)) d +
        eulerSum (fun k => Module.finrank F
          (homologyIndex F (fiberFlow hΦ Tau.bot (base_bot hθ)) hKm k)) d := by
  unfold eulerSum
  rw [← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  beta_reduce
  obtain ⟨e⟩ := fixed_homology hΦ hθ F hP hKp hKm k
  rw [e.finrank_eq, Module.finrank_prod]
  push_cast
  ring

include hΦ hθ in
/-- Theorem `thm:equivariant`(iii) with `Y^R`: for a collared index pair `(N, L)` of `S` and
`Y = q⁻¹(N)/q⁻¹(L)`, `χ(S̃) = 2 χ(S) - χ̃(Y^R)`, truncated at a degree `d` with `CH_d(K₋) = 0`. -/
theorem equivariant_iii_fixed (F : Type u) [Field F] {S N L : Set (X × Tau)}
    (hS : IsIsolatedInvariantSet Φ S)
    (h : IsAttractorRepellerPair (circΦ hΦ hθ) (cq ⁻¹' S) ({x | (x, Tau.top) ∈ S} ×ˢ {Circ.zero})
      ({x | (x, Tau.bot) ∈ S} ×ˢ {Circ.pi}))
    (hP : IsIndexPair Φ S N L)
    (hKp : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ)) {x | (x, Tau.top) ∈ S})
    (hKm : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ)) {x | (x, Tau.bot) ∈ S})
    [∀ k, FiniteDimensional F (homologyIndex F (fiberFlow hΦ Tau.top (base_top hθ)) hKp k)]
    [∀ k, FiniteDimensional F (homologyIndex F (fiberFlow hΦ Tau.bot (base_bot hθ)) hKm k)]
    (d : ℕ) (hd : Subsingleton (homologyIndex F (fiberFlow hΦ Tau.bot (base_bot hθ)) hKm d)) :
    eulerSum (fun k => Module.finrank F (homologyIndex F (circΦ hΦ hθ) h.isolated k)) d =
      2 * eulerSum (fun k => Module.finrank F (homologyIndex F Φ hS k)) d -
        eulerSum (fun k => Module.finrank F (redH F (YFix N L) (YFix.pt N L) k)) d := by
  rw [(equivariant_iii hΦ hθ F hS h hKp hKm d hd).2, euler_fixed hΦ hθ F hP hKp hKm d]
  unfold eulerSum
  rw [sum_range_succ (fun k => (-1 : ℤ) ^ k * (Module.finrank F
    (homologyIndex F (fiberFlow hΦ Tau.bot (base_bot hθ)) hKm k) : ℤ)),
    Module.finrank_zero_of_subsingleton]
  push_cast
  ring

include hΦ hθ in
/-- The homology of `h(S) ≅ Y/R` relative to `Y^R` is UV data:
`χ̃(h(S)) - χ̃(Y^R) = -χ̃(h(K₋))`. -/
theorem euler_rel_fixed (F : Type u) [Field F] {S N L : Set (X × Tau)}
    (hS : IsIsolatedInvariantSet Φ S) (hP : IsIndexPair Φ S N L)
    (hKp : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ)) {x | (x, Tau.top) ∈ S})
    (hKm : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ)) {x | (x, Tau.bot) ∈ S})
    [∀ k, FiniteDimensional F (homologyIndex F (fiberFlow hΦ Tau.top (base_top hθ)) hKp k)]
    [∀ k, FiniteDimensional F (homologyIndex F (fiberFlow hΦ Tau.bot (base_bot hθ)) hKm k)]
    (d : ℕ) :
    eulerSum (fun k => Module.finrank F (homologyIndex F Φ hS k)) d -
        eulerSum (fun k => Module.finrank F (redH F (YFix N L) (YFix.pt N L) k)) d =
      -eulerSum (fun k => Module.finrank F
          (homologyIndex F (fiberFlow hΦ Tau.bot (base_bot hθ)) hKm k)) d := by
  obtain ⟨-, hK', hslab⟩ := slab_index hΦ hθ F hS
  have eS : eulerSum (fun k => Module.finrank F (homologyIndex F Φ hS k)) d =
      eulerSum (fun k => Module.finrank F
        (homologyIndex F (fiberFlow hΦ Tau.top (base_top hθ)) hKp k)) d := by
    simp only [eulerSum]
    refine sum_congr rfl fun k _ => ?_
    rw [← (hslab k).some.finrank_eq]
  rw [eS, euler_fixed hΦ hθ F hP hKp hKm d]
  ring

end Double

end ConleyCheck.Conley
