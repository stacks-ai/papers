import ConleyCheck.Conley.Subdivision

/-!
# Excision for singular homology

Let `A, B ⊆ X ⊆ α` and let `O_A, O_B` be open sets with `X ⊆ O_A ∪ O_B`, `O_A ∩ X ⊆ A` and
`O_B ∩ X ⊆ B`, namely the interiors of `A` and `B` relative to `X` cover `X`. Then the inclusion
induces isomorphisms `H_*(B, A) ≅ H_*(X, A)` (`excision`).

The proof is the classical one. Iterated barycentric subdivision shows that the complex
`S(X) / (S(A) + S(B))` is acyclic (`homology_sup_subsingleton`), so the sequence of the triple
`S(A) ≤ S(A) + S(B) ≤ S(X)` gives `H_*((S(A) + S(B)) / S(A)) ≅ H_*(X, A)`, and the second
isomorphism theorem gives `S(B) / (S(A) ∩ S(B)) ≅ (S(A) + S(B)) / S(A)`.
-/

namespace ConleyCheck.Conley

open CategoryTheory Limits Set

universe u

variable {K : Type u} [Ring K]

/-! ### Sums of subcomplexes and acyclicity -/

section Abstract

variable {C : ChainComplex (ModuleCat.{u} K) ℕ}

/-- The sum `P + Q` of two subcomplexes. -/
def SubCx.sup (P Q : SubCx C) : SubCx C where
  S n := P.S n ⊔ Q.S n
  stable i j x hx := by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (P.stable i j y hy) (Q.stable i j z hz)

theorem SubCx.le_sup_right (P Q : SubCx C) (n : ℕ) : Q.S n ≤ (P.sup Q).S n :=
  _root_.le_sup_right

/-- The second isomorphism theorem `Q / (Q ∩ P) ≅ (P + Q) / P`, in each degree. -/
theorem relMapF_sup_bijective (P Q : SubCx C) (n : ℕ) :
    Function.Bijective (relMapF (Q := Q) (Q' := P.sup Q) (P := P) (P' := P)
      (SubCx.le_sup_right P Q) (fun _ => le_rfl) n) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [relMapF_mk, Submodule.Quotient.mk_eq_zero] at hx
      exact (Submodule.Quotient.mk_eq_zero _).2 hx
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨p, hp, q, hq, hy⟩ := Submodule.mem_sup.1 y.2
      refine ⟨Submodule.Quotient.mk ⟨q, hq⟩, ?_⟩
      rw [relMapF_mk, Submodule.Quotient.eq]
      show q - (y : C.X n) ∈ P.S n
      rw [← hy, show q - (p + q) = -p by abel]
      exact neg_mem hp

theorem homologyMap_sup_bijective (P Q : SubCx C) (n : ℕ) :
    Function.Bijective (HomologicalComplex.homologyMap
      (relMap C (Q := Q) (Q' := P.sup Q) (P := P) (P' := P) (SubCx.le_sup_right P Q)
        (fun _ => le_rfl)) n).hom := by
  have : ∀ n, IsIso ((relMap C (Q := Q) (Q' := P.sup Q) (P := P) (P' := P)
      (SubCx.le_sup_right P Q) (fun _ => le_rfl)).f n) := fun n =>
    (ConcreteCategory.isIso_iff_bijective _).2 (relMapF_sup_bijective P Q n)
  have := HomologicalComplex.Hom.isIso_of_components (relMap C (Q := Q) (Q' := P.sup Q)
    (P := P) (P' := P) (SubCx.le_sup_right P Q) (fun _ => le_rfl))
  exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

/-- `Q / P` has zero homology in degree `n` if every relative cycle is a relative boundary. -/
theorem relCx_homology_subsingleton (Q P : SubCx C) (n : ℕ)
    (h : ∀ z ∈ Q.S n, (C.d n (n - 1)).hom z ∈ P.S (n - 1) →
      ∃ w ∈ Q.S (n + 1), z - (C.d (n + 1) n).hom w ∈ P.S n) :
    Subsingleton ((relCx C Q P).homology n) := by
  refine ModuleCat.subsingleton_of_isZero ?_
  have hk : (ComplexShape.down ℕ).next n = n - 1 := by
    cases n with
    | zero => exact ChainComplex.next_nat_zero
    | succ m => exact ChainComplex.next_nat_succ m
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (n + 1) n (n - 1) (ChainComplex.prev ℕ n) hk,
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    change relD Q P n (n - 1) (Submodule.Quotient.mk z) = 0 at hx
    rw [relD_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨w, hw, hzw⟩ := h z.1 z.2 hx
    refine ⟨Submodule.Quotient.mk ⟨w, hw⟩, ?_⟩
    change relD Q P (n + 1) n (Submodule.Quotient.mk ⟨w, hw⟩) = Submodule.Quotient.mk z
    rw [relD_mk, Submodule.Quotient.eq]
    change (C.d (n + 1) n).hom w - z.1 ∈ P.S n
    rw [← neg_sub]
    exact neg_mem hzw

end Abstract

/-! ### Small chains -/

section Small

variable {α : Type u} [TopologicalSpace α]

theorem mem_sup_chainSub_iff (A B : Set α) (n : ℕ) (x : CX K (TopCat.of α) n) :
    x ∈ ((chainSub K A).sup (chainSub K B)).S n ↔
      (basEquiv K _ n).symm x ∈ Finsupp.supported K K (onSet A n ∪ onSet B n) := by
  rw [Finsupp.supported_union]
  constructor
  · intro hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup ((mem_chainSub_iff A n y).1 hy) ((mem_chainSub_iff B n z).1 hz)
  · intro hx
    obtain ⟨g, hg, h, hh, he⟩ := Submodule.mem_sup.1 hx
    rw [← (basEquiv K _ n).apply_symm_apply x, ← he, map_add]
    refine Submodule.add_mem_sup ((mem_chainSub_iff A n _).2 ?_) ((mem_chainSub_iff B n _).2 ?_)
    · rwa [LinearEquiv.symm_apply_apply]
    · rwa [LinearEquiv.symm_apply_apply]

theorem map_supported_union {k k' : ℕ}
    (f : (Simp (TopCat.of α) k →₀ K) →ₗ[K] (Simp (TopCat.of α) k' →₀ K))
    (hf : ∀ (A : Set α) (g : Simp (TopCat.of α) k →₀ K),
      g ∈ Finsupp.supported K K (onSet A k) → f g ∈ Finsupp.supported K K (onSet A k'))
    (A B : Set α) {g : Simp (TopCat.of α) k →₀ K}
    (hg : g ∈ Finsupp.supported K K (onSet A k ∪ onSet B k)) :
    f g ∈ Finsupp.supported K K (onSet A k' ∪ onSet B k') := by
  rw [Finsupp.supported_union] at hg ⊢
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hg
  rw [map_add]
  exact Submodule.add_mem_sup (hf A y hy) (hf B z hz)

theorem SdF_pow_supported {A : Set α} {k : ℕ} (r : ℕ) {g : Simp (TopCat.of α) k →₀ K}
    (hg : g ∈ Finsupp.supported K K (onSet A k)) :
    (SdF K _ k ^ r) g ∈ Finsupp.supported K K (onSet A k) := by
  induction r with
  | zero => rwa [pow_zero, Module.End.one_apply]
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact SdF_supported ih

theorem SdF_pow_zero (r : ℕ) (g : Simp (TopCat.of α) 0 →₀ K) : (SdF K _ 0 ^ r) g = g := by
  induction r with
  | zero => rw [pow_zero, Module.End.one_apply]
  | succ r ih => rw [pow_succ', Module.End.mul_apply, ih, SdF_zero]

theorem dF_SdF_pow {k : ℕ} (r : ℕ) (g : Simp (TopCat.of α) (k + 1) →₀ K) :
    dF K _ k ((SdF K _ (k + 1) ^ r) g) = (SdF K _ k ^ r) (dF K _ k g) := by
  induction r with
  | zero => rw [pow_zero, pow_zero, Module.End.one_apply, Module.End.one_apply]
  | succ r ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, dF_SdF, ih]

variable (K α) in
/-- The chain homotopy `Σ_{j < r} T ∘ Sd^j` between the identity and `Sd^r`. -/
noncomputable def TrF (k r : ℕ) :
    (Simp (TopCat.of α) k →₀ K) →ₗ[K] (Simp (TopCat.of α) (k + 1) →₀ K) :=
  ∑ j ∈ Finset.range r, TF K _ k ∘ₗ SdF K _ k ^ j

theorem dF_TrF {k : ℕ} (r : ℕ) (g : Simp (TopCat.of α) (k + 1) →₀ K) :
    dF K _ (k + 1) (TrF K α (k + 1) r g) + TrF K α k r (dF K _ k g) =
      g - (SdF K _ (k + 1) ^ r) g := by
  induction r with
  | zero => simp [TrF]
  | succ r ih =>
    simp only [TrF, Finset.sum_range_succ, LinearMap.add_apply, LinearMap.comp_apply,
      map_add] at ih ⊢
    rw [← dF_SdF_pow, show ∀ a b c d : Simp (TopCat.of α) (k + 1) →₀ K,
      a + c + (b + d) = (a + b) + (c + d) from fun _ _ _ _ => by abel, ih, dF_TF,
      pow_succ', Module.End.mul_apply]
    abel

theorem TrF_supported {A : Set α} {k : ℕ} (r : ℕ) {g : Simp (TopCat.of α) k →₀ K}
    (hg : g ∈ Finsupp.supported K K (onSet A k)) :
    TrF K α k r g ∈ Finsupp.supported K K (onSet A (k + 1)) := by
  rw [TrF, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun j _ => TF_supported (SdF_pow_supported j hg)

variable {X A B OA OB : Set α} (hOA : IsOpen OA) (hOB : IsOpen OB) (hX : X ⊆ OA ∪ OB)
  (hA' : OA ∩ X ⊆ A) (hB' : OB ∩ X ⊆ B)
include hOA hOB hX hA' hB'

/-- Every chain in `X` becomes, after enough subdivisions, a sum of chains in `A` and in `B`. -/
theorem exists_SdF_pow_small {k : ℕ} {g : Simp (TopCat.of α) k →₀ K}
    (hg : g ∈ Finsupp.supported K K (onSet X k)) :
    ∃ r, ∀ r' ≥ r, (SdF K _ k ^ r') g ∈ Finsupp.supported K K (onSet A k ∪ onSet B k) := by
  rw [Finsupp.supported_eq_span_single] at hg
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨r, hr⟩ := sdF_iterate_small (K := K) σ hOA hOB (hσ.trans hX)
    refine ⟨r, fun r' hr' => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hr'
    rw [add_comm, pow_add, Module.End.mul_apply]
    refine map_supported_union _ (fun A g hg => SdF_pow_supported m hg) A B ?_
    rw [Module.End.pow_apply]
    have hXs : (SdF K _ k)^[r] (Finsupp.single σ 1) ∈ Finsupp.supported K K (onSet X k) := by
      rw [← Module.End.pow_apply]
      exact SdF_pow_supported r (Finsupp.single_mem_supported K _ hσ)
    have hboth : (SdF K _ k)^[r] (Finsupp.single σ 1) ∈
        Finsupp.supported K K ((onSet OA k ∪ onSet OB k) ∩ onSet X k) := by
      rw [Finsupp.supported_inter]
      exact ⟨hr, hXs⟩
    refine Finsupp.supported_mono ?_ hboth
    rintro τ ⟨h | h, hτ⟩
    · exact Or.inl fun p hp => hA' ⟨h hp, hτ hp⟩
    · exact Or.inr fun p hp => hB' ⟨h hp, hτ hp⟩
  · exact ⟨0, fun _ _ => by rw [map_zero]; exact zero_mem _⟩
  · rintro a b - - ⟨r₁, h₁⟩ ⟨r₂, h₂⟩
    exact ⟨max r₁ r₂, fun r' hr' => by
      rw [map_add]
      exact add_mem (h₁ r' (le_of_max_le_left hr')) (h₂ r' (le_of_max_le_right hr'))⟩
  · rintro c a - ⟨r, h⟩
    exact ⟨r, fun r' hr' => by
      rw [map_smul]
      exact Submodule.smul_mem _ c (h r' hr')⟩

theorem acyclic_zero {g : Simp (TopCat.of α) 0 →₀ K}
    (hg : g ∈ Finsupp.supported K K (onSet X 0)) :
    g ∈ Finsupp.supported K K (onSet A 0 ∪ onSet B 0) := by
  obtain ⟨r, hr⟩ := exists_SdF_pow_small hOA hOB hX hA' hB' hg
  have := hr r le_rfl
  rwa [SdF_pow_zero] at this

theorem acyclic_succ {k : ℕ} {g : Simp (TopCat.of α) (k + 1) →₀ K}
    (hg : g ∈ Finsupp.supported K K (onSet X (k + 1)))
    (hdg : dF K _ k g ∈ Finsupp.supported K K (onSet A k ∪ onSet B k)) :
    ∃ w ∈ Finsupp.supported K K (onSet X (k + 2)),
      g - dF K _ (k + 1) w ∈ Finsupp.supported K K (onSet A (k + 1) ∪ onSet B (k + 1)) := by
  obtain ⟨r, hr⟩ := exists_SdF_pow_small hOA hOB hX hA' hB' hg
  refine ⟨TrF K α (k + 1) r g, TrF_supported r hg, ?_⟩
  have e := dF_TrF r g
  have h2 : g - dF K _ (k + 1) (TrF K α (k + 1) r g) =
      (SdF K _ (k + 1) ^ r) g + TrF K α k r (dF K _ k g) := by
    rw [sub_eq_iff_eq_add]
    conv_lhs => rw [sub_eq_iff_eq_add.1 e.symm]
    abel
  rw [h2]
  exact add_mem (hr r le_rfl)
    (map_supported_union _ (fun A g hg => TrF_supported r hg) A B hdg)

variable (K) in
/-- `S(X) / (S(A) + S(B))` is acyclic. -/
theorem homology_sup_subsingleton (n : ℕ) :
    Subsingleton ((relCx _ (chainSub K X) ((chainSub K A).sup (chainSub K B))).homology n) := by
  refine relCx_homology_subsingleton _ _ n fun z hz hdz => ?_
  obtain ⟨g, rfl⟩ := (basEquiv K _ n).surjective z
  have hg := (mem_chainSub_iff X n _).1 hz
  rw [LinearEquiv.symm_apply_apply] at hg
  cases n with
  | zero =>
    refine ⟨0, zero_mem _, ?_⟩
    rw [map_zero, sub_zero, mem_sup_chainSub_iff, LinearEquiv.symm_apply_apply]
    exact acyclic_zero hOA hOB hX hA' hB' hg
  | succ m =>
    change (((singFunctor K).obj (TopCat.of α)).d (m + 1) m).hom (basEquiv K _ (m + 1) g) ∈
      ((chainSub K A).sup (chainSub K B)).S m at hdz
    rw [mem_sup_chainSub_iff, basEquiv_apply, bas_d, ← basEquiv_apply,
      LinearEquiv.symm_apply_apply] at hdz
    obtain ⟨w, hw, hgw⟩ := acyclic_succ hOA hOB hX hA' hB' hg hdz
    refine ⟨basEquiv K _ (m + 2) w, (mem_chainSub_iff X _ _).2 (by
      rwa [LinearEquiv.symm_apply_apply]), ?_⟩
    rw [mem_sup_chainSub_iff, map_sub, LinearEquiv.symm_apply_apply, basEquiv_apply w, bas_d,
      ← basEquiv_apply, LinearEquiv.symm_apply_apply]
    exact hgw

end Small

/-! ### Excision -/

section Excision

variable (K) {α : Type u} [TopologicalSpace α]

/-- Excision. If the interiors of `A` and `B` relative to `X` cover `X`, the inclusion induces
isomorphisms `H_*(B, A) ≅ H_*(X, A)`. -/
theorem excision {X A B OA OB : Set α} (hA : A ⊆ X) (hB : B ⊆ X) (hOA : IsOpen OA)
    (hOB : IsOpen OB) (hX : X ⊆ OA ∪ OB) (hA' : OA ∩ X ⊆ A) (hB' : OB ∩ X ⊆ B) (k : ℤ) :
    Function.Bijective (singIncl K k hB (subset_refl A)).hom := by
  cases k with
  | negSucc m => exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  | ofNat n =>
    let C := (singFunctor K).obj (TopCat.of α)
    let P := chainSub K A
    let M := P.sup (chainSub K B)
    have hMR : ∀ n, M.S n ≤ (chainSub K X).S n := fun n =>
      sup_le (chainSub_mono K hA n) (chainSub_mono K hB n)
    have hPM : ∀ n, P.S n ≤ M.S n := fun _ => le_sup_left
    have hfac : relMap C (chainSub_mono K hB) (chainSub_mono K (subset_refl A)) =
        relMap C (Q := chainSub K B) (Q' := M) (P := P) (P' := P) (SubCx.le_sup_right P (chainSub K B))
          (fun _ => le_rfl) ≫ relMap C hMR (fun _ => le_rfl) := by
      ext n x
      induction x using Submodule.Quotient.induction_on with
      | H x => rfl
    change Function.Bijective (HomologicalComplex.homologyMap
      (relMap C (chainSub_mono K hB) (chainSub_mono K (subset_refl A))) n).hom
    rw [hfac, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp, LinearMap.coe_comp]
    refine Function.Bijective.comp ?_ (homologyMap_sup_bijective P (chainSub K B) n)
    have hSE := tripleSC_shortExact hPM hMR
    have : Subsingleton ((tripleSC C hPM hMR).X₃.homology n) :=
      homology_sup_subsingleton K hOA hOB hX hA' hB' n
    have : Subsingleton ((tripleSC C hPM hMR).X₃.homology (n + 1)) :=
      homology_sup_subsingleton K hOA hOB hX hA' hB' (n + 1)
    exact bijective_of_exact_of_subsingleton
      (exact_of_shortComplex K (hSE.homology_exact₁ (n + 1) n rfl))
      (exact_of_shortComplex K (hSE.homology_exact₂ n))

end Excision

end ConleyCheck.Conley
