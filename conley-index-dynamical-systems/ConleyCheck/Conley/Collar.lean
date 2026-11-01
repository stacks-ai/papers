import ConleyCheck.Conley.PairMaps

/-!
# The homology index of collared index pairs

An index pair `(N, L)` is collared (`IsCollared`) if `L` has a neighborhood `V` in `N` on which the
time `τ ≤ 1` needed to reach `L` is continuous, with `ϕ([0, τ(x)], x) ⊆ V`. Regular index pairs,
namely those with continuous exit time, are collared.

For a collared index pair, `H_*(N, L) ≅ H̃_*(N/L) = CH_*(S)` (`collarEquiv`). The proof pushes `V`
into `L` along the flow, so `H_*(N, L) ≅ H_*(N, V)`, excises `L` on both sides, uses that
`N ∖ L → N/L ∖ [L]` is a homeomorphism, and contracts the image of `V` in `N/L` by the push map.

Hence, for an index triple whose three pairs are collared, the attractor–repeller sequence holds
for the paper's `CH_*` (`homologyIndex_attractor_repeller`), together with its two consequences
(`homologyIndex_attractor_iso`, `homologyIndex_repeller_iso`).
-/

namespace ConleyCheck.Conley

open CategoryTheory Limits Set Topology unitInterval

universe u

variable {α : Type u} [TopologicalSpace α]

/-- `L` has a flow collar in `N`, namely a neighborhood `V` of `L` in `N` whose points reach `L`
within time `τ ≤ 1` along orbit segments in `V`, with `τ` continuous and `τ = 0` on `L`. -/
def IsCollared (ϕ : Flow ℝ α) (N L : Set α) : Prop :=
  ∃ (V O : Set α) (τ : V → ℝ), IsOpen O ∧ L ⊆ O ∧ O ∩ N ⊆ V ∧ V ⊆ N ∧ Continuous τ ∧
    (∀ x, 0 ≤ τ x ∧ τ x ≤ 1) ∧ (∀ x : V, (x : α) ∈ L → τ x = 0) ∧
    (∀ x : V, ∀ s ∈ Icc 0 (τ x), ϕ s x ∈ V) ∧ (∀ x : V, ϕ (τ x) x ∈ L)

/-! ### Subsets of `N/L` -/

section Quot

variable {N L : Set α}

theorem IndexSpace.proj_eq_pt_iff (x : N) :
    IndexSpace.proj N L x = IndexSpace.pt N L ↔ (x : α) ∈ L := by
  constructor
  · intro h
    have : Sum.inl x = Sum.inr () ∨ (collapsed N L (.inl x) ∧ collapsed N L (.inr ())) :=
      Quotient.exact h
    rcases this with h | ⟨h, -⟩
    · exact absurd h Sum.inl_ne_inr
    · exact h
  · exact IndexSpace.proj_eq_pt

theorem IndexSpace.proj_eq_proj_iff (x y : N) :
    IndexSpace.proj N L x = IndexSpace.proj N L y ↔ x = y ∨ ((x : α) ∈ L ∧ (y : α) ∈ L) := by
  constructor
  · intro h
    have : Sum.inl x = Sum.inl y ∨ (collapsed N L (.inl x) ∧ collapsed N L (.inl y)) :=
      Quotient.exact h
    rcases this with h | h
    · exact Or.inl (Sum.inl_injective h)
    · exact Or.inr h
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · rw [IndexSpace.proj_eq_pt hx, IndexSpace.proj_eq_pt hy]

/-- The image `{[L]} ∪ [U ∩ N]` of `U` in `N/L`. -/
def liftSet (N L U : Set α) : Set (IndexSpace N L) :=
  {z | z = IndexSpace.pt N L ∨ ∃ x : N, (x : α) ∈ U ∧ IndexSpace.proj N L x = z}

theorem pt_mem_liftSet (U : Set α) : IndexSpace.pt N L ∈ liftSet N L U := Or.inl rfl

theorem proj_mem_liftSet {U : Set α} (hLU : L ⊆ U) (x : N) :
    IndexSpace.proj N L x ∈ liftSet N L U ↔ (x : α) ∈ U := by
  constructor
  · rintro (h | ⟨y, hy, he⟩)
    · exact hLU ((IndexSpace.proj_eq_pt_iff x).1 h)
    · rcases (IndexSpace.proj_eq_proj_iff y x).1 he with rfl | ⟨-, hx⟩
      · exact hy
      · exact hLU hx
  · exact fun h => Or.inr ⟨x, h, rfl⟩

theorem isOpen_liftSet {U : Set α} (hLU : L ⊆ U) (hU : IsOpen U) : IsOpen (liftSet N L U) := by
  apply (isQuotientMap_quotient_mk' (s := indexSetoid N L)).isOpen_preimage.1
  rw [isOpen_sum_iff]
  constructor
  · convert hU.preimage (continuous_subtype_val (p := fun x => x ∈ N)) using 1
    ext x
    exact proj_mem_liftSet hLU x
  · convert isOpen_univ using 1
    exact eq_univ_of_forall fun _ => pt_mem_liftSet U

theorem isOpen_compl_pt (hL : IsClosed L) : IsOpen ({IndexSpace.pt N L}ᶜ) := by
  apply (isQuotientMap_quotient_mk' (s := indexSetoid N L)).isOpen_preimage.1
  rw [isOpen_sum_iff]
  constructor
  · convert (hL.preimage (continuous_subtype_val (p := fun x => x ∈ N))).isOpen_compl using 1
    ext x
    exact not_congr (IndexSpace.proj_eq_pt_iff x)
  · convert isOpen_empty using 1
    exact eq_empty_of_forall_notMem fun _ h => h rfl

/-- The points of `N` outside `L`. -/
def offL (N L : Set α) : Set N := {x | (x : α) ∉ L}

theorem isEmbedding_proj_offL (hL : IsClosed L) :
    IsEmbedding ((offL N L).domRestrict (IndexSpace.proj N L)) := by
  refine (IsOpenEmbedding.of_continuous_injective_isOpenMap
    ((IndexSpace.proj N L).continuous.comp continuous_subtype_val) ?_ ?_).isEmbedding
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    rcases (IndexSpace.proj_eq_proj_iff x y).1 h with rfl | ⟨h', -⟩
    · rfl
    · exact absurd h' hx
  · intro U hU
    obtain ⟨U', hU', rfl⟩ := isOpen_induced_iff.1 hU
    apply (isQuotientMap_quotient_mk' (s := indexSetoid N L)).isOpen_preimage.1
    rw [isOpen_sum_iff]
    constructor
    · convert (hL.preimage (continuous_subtype_val (p := fun x => x ∈ N))).isOpen_compl.inter hU'
        using 1
      ext y
      constructor
      · rintro ⟨x, hx, he⟩
        rcases (IndexSpace.proj_eq_proj_iff x.1 y).1 he with h | ⟨h, -⟩
        · rw [← h]
          exact ⟨x.2, hx⟩
        · exact absurd h x.2
      · rintro ⟨hy, hyU⟩
        exact ⟨⟨y, hy⟩, hyU, rfl⟩
    · convert isOpen_empty using 1
      refine eq_empty_of_forall_notMem fun u hu => ?_
      obtain ⟨x, -, he⟩ := hu
      exact x.2 ((IndexSpace.proj_eq_pt_iff x.1).1 he)

theorem exists_proj_of_ne_pt {z : IndexSpace N L} (hz : z ≠ IndexSpace.pt N L) :
    ∃ x ∈ offL N L, IndexSpace.proj N L x = z := by
  induction z using Quotient.inductionOn with
  | h a =>
    rcases a with x | u
    · refine ⟨x, fun hx => hz ?_, rfl⟩
      exact IndexSpace.proj_eq_pt hx
    · exact absurd rfl hz

end Quot

/-! ### The push map on the image of the collar -/

section PushCollar

open scoped Classical

variable [T2Space α] {ϕ : Flow ℝ α} {S N L : Set α} (hP : IsIndexPair ϕ S N L)

theorem pushHom_zero (z : IndexSpace N L) : pushHom hP 1 zero_le_one (0, z) = z := by
  induction z using Quotient.inductionOn with
  | h a =>
    rcases a with y | u
    · show (if ((0 : I), y) ∈ pushA (ϕ := ϕ) (N := N) 1 then
          IndexSpace.Q N L (ϕ (((0 : I) : ℝ) * 1) (y : α)) else IndexSpace.pt N L) =
        IndexSpace.proj N L y
      have hp : ((0 : I), y) ∈ pushA (ϕ := ϕ) (N := N) 1 := by
        intro u _
        simp only [Icc.coe_zero, zero_mul, mul_zero, ϕ.map_zero_apply]
        exact y.2
      rw [if_pos hp]
      simp only [Icc.coe_zero, zero_mul, ϕ.map_zero_apply]
      exact IndexSpace.Q_of_mem y.2
    · rfl

variable {V : Set α} {τ : V → ℝ} (hLV : L ⊆ V) (hτ0 : ∀ x, 0 ≤ τ x) (hτ1 : ∀ x, τ x ≤ 1)
  (hseg : ∀ x : V, ∀ s ∈ Icc 0 (τ x), ϕ s x ∈ V) (hhit : ∀ x : V, ϕ (τ x) x ∈ L)
include hLV hτ0 hτ1 hseg hhit

theorem pushHom_mem_liftSet (s : I) {z : IndexSpace N L} (hz : z ∈ liftSet N L V) :
    pushHom hP 1 zero_le_one (s, z) ∈ liftSet N L V ∧
      (s = 1 → pushHom hP 1 zero_le_one (s, z) = IndexSpace.pt N L) := by
  rcases hz with rfl | ⟨x, hx, rfl⟩
  · exact ⟨pt_mem_liftSet V, fun _ => rfl⟩
  · show (if (s, x) ∈ pushA (ϕ := ϕ) (N := N) 1 then
        IndexSpace.Q N L (ϕ ((s : ℝ) * 1) (x : α)) else IndexSpace.pt N L) ∈ liftSet N L V ∧
      (s = 1 → (if (s, x) ∈ pushA (ϕ := ϕ) (N := N) 1 then
        IndexSpace.Q N L (ϕ ((s : ℝ) * 1) (x : α)) else IndexSpace.pt N L) = IndexSpace.pt N L)
    split_ifs with hp
    · have hseg' := (mem_pushA_iff hP 1 zero_le_one (s, x)).1 hp
      have hN : ϕ ((s : ℝ) * 1) (x : α) ∈ N := hseg' _ ⟨mul_nonneg s.2.1 zero_le_one, le_rfl⟩
      let xv : V := ⟨x, hx⟩
      by_cases hle : τ xv ≤ (s : ℝ) * 1
      · have hL : ϕ ((s : ℝ) * 1) (x : α) ∈ L := posInv_shift hP.posInv hle (hhit xv)
          fun r hr => hseg' r ⟨(hτ0 xv).trans hr.1, hr.2⟩
        rw [IndexSpace.Q_of_mem_L hP.subset hL]
        exact ⟨pt_mem_liftSet V, fun _ => rfl⟩
      · push Not at hle
        have hV : ϕ ((s : ℝ) * 1) (x : α) ∈ V :=
          hseg xv _ ⟨mul_nonneg s.2.1 zero_le_one, hle.le⟩
        refine ⟨?_, fun hs1 => ?_⟩
        · rw [IndexSpace.Q_of_mem hN]
          exact (proj_mem_liftSet hLV _).2 hV
        · exfalso
          rw [hs1, Icc.coe_one, one_mul] at hle
          exact absurd (hτ1 xv) (not_le.2 hle)
    · exact ⟨pt_mem_liftSet V, fun _ => rfl⟩

end PushCollar

/-! ### `H_*(N, L) ≅ H̃_*(N/L)` for collared index pairs -/

section Main

variable (K : Type u) [Ring K] [T2Space α] {ϕ : Flow ℝ α}

theorem collarEquiv_nonempty {S N L : Set α} (hP : IsIndexPair ϕ S N L) (hc : IsCollared ϕ N L)
    (n : ℕ) :
    Nonempty (singH K α (Int.ofNat n) N L ≃ₗ[K] redH K (IndexSpace N L) (IndexSpace.pt N L) n) := by
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
  have b1 := singIncl_bijective_of_subsingleton K hLV hVN hsV (Int.ofNat n)
  have b2 := excision K hVN (sdiff_subset : N \ L ⊆ N) hO hLc.isOpen_compl
    (fun x _ => by
      by_cases h : x ∈ L
      · exact Or.inl (hLO h)
      · exact Or.inr h)
    hON (fun x hx => ⟨hx.2, hx.1⟩) (Int.ofNat n)
  let valC : C(N, α) := ⟨Subtype.val, continuous_subtype_val⟩
  have b3 := singMap_bijective K valC (B := offL N L) (A := {x : N | (x : α) ∈ V})
    (B' := N \ L) (A' := V) (fun x hx => ⟨x.2, hx⟩) (fun y hy => ⟨⟨y, hy.1⟩, hy.2, rfl⟩)
    (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal) (fun x _ => Iff.rfl) (Int.ofNat n)
  have b4 := singMap_bijective K (IndexSpace.proj N L) (B := offL N L)
    (A := {x : N | (x : α) ∈ V}) (B' := {IndexSpace.pt N L}ᶜ) (A' := liftSet N L V)
    (fun x hx h => hx ((IndexSpace.proj_eq_pt_iff x).1 h)) (fun y hy => exists_proj_of_ne_pt hy)
    (isEmbedding_proj_offL hLc) (fun x _ => (proj_mem_liftSet hLV x).symm) (Int.ofNat n)
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
    (fun z hz => hz.1) (Int.ofNat n)
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
  have b6 := singIncl_bijective_of_subsingleton K hpV (subset_univ _) hsQ (Int.ofNat n)
  exact ⟨(LinearEquiv.ofBijective _ b1).trans ((LinearEquiv.ofBijective _ b2).symm.trans
    ((LinearEquiv.ofBijective _ b3).symm.trans ((LinearEquiv.ofBijective _ b4).trans
    ((LinearEquiv.ofBijective _ b5).trans ((LinearEquiv.ofBijective _ b6).symm.trans
    (redHEquiv K (IndexSpace.pt N L) n).symm)))))⟩

/-- `H_n(N, L) ≅ H̃_n(N/L)` for a collared index pair. -/
noncomputable def collarEquiv {S N L : Set α} (hP : IsIndexPair ϕ S N L) (hc : IsCollared ϕ N L)
    (n : ℕ) : singH K α (Int.ofNat n) N L ≃ₗ[K] redH K (IndexSpace N L) (IndexSpace.pt N L) n :=
  (collarEquiv_nonempty K hP hc n).some

/-- `CH_n(S) ≅ H_n(N, L)` for a collared index pair `(N, L)` of `S`. -/
noncomputable def homologyIndexEquiv {S N L : Set α} (hS : IsIsolatedInvariantSet ϕ S)
    (hP : IsIndexPair ϕ S N L) (hc : IsCollared ϕ N L) (n : ℕ) :
    homologyIndex K ϕ hS n ≃ₗ[K] singH K α (Int.ofNat n) N L :=
  (homologyIndexIso K hS hP n).some.toLinearEquiv.trans (collarEquiv K hP hc n).symm

theorem exact_conj {M₁ M₂ M₃ P₁ P₂ P₃ : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
    [AddCommGroup M₃] [AddCommGroup P₁] [AddCommGroup P₂] [AddCommGroup P₃] [Module K M₁]
    [Module K M₂] [Module K M₃] [Module K P₁] [Module K P₂] [Module K P₃]
    {f : M₁ →ₗ[K] M₂} {g : M₂ →ₗ[K] M₃} (e₁ : P₁ ≃ₗ[K] M₁) (e₂ : P₂ ≃ₗ[K] M₂) (e₃ : P₃ ≃ₗ[K] M₃)
    (h : Function.Exact f g) :
    Function.Exact (e₂.symm.toLinearMap ∘ₗ f ∘ₗ e₁.toLinearMap)
      (e₃.symm.toLinearMap ∘ₗ g ∘ₗ e₂.toLinearMap) := by
  intro y
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.map_eq_zero_iff, Set.mem_range]
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (h _).1 hy
    exact ⟨e₁.symm x, by rw [LinearEquiv.apply_symm_apply, hx, LinearEquiv.symm_apply_apply]⟩
  · rintro ⟨x, rfl⟩
    rw [LinearEquiv.apply_symm_apply]
    exact (h _).2 ⟨_, rfl⟩

/-- The attractor–repeller sequence
`⋯ → CH_n(A) → CH_n(S) → CH_n(R) → CH_{n-1}(A) → ⋯ → CH_0(R) → 0` for an index triple whose
three pairs are collared. -/
theorem homologyIndex_attractor_repeller {S A R N₀ N₁ N₂ : Set α}
    (hT : IsIndexTriple ϕ S A R N₀ N₁ N₂) (hS : IsIsolatedInvariantSet ϕ S)
    (hA : IsIsolatedInvariantSet ϕ A) (hR : IsIsolatedInvariantSet ϕ R)
    (c₁ : IsCollared ϕ N₁ N₀) (c₂ : IsCollared ϕ N₂ N₀) (c₃ : IsCollared ϕ N₂ N₁) :
    ∃ (i : ∀ n, homologyIndex K ϕ hA n →ₗ[K] homologyIndex K ϕ hS n)
      (p : ∀ n, homologyIndex K ϕ hS n →ₗ[K] homologyIndex K ϕ hR n)
      (d : ∀ n, homologyIndex K ϕ hR (n + 1) →ₗ[K] homologyIndex K ϕ hA n),
      (∀ n, Function.Exact (i n) (p n)) ∧ (∀ n, Function.Exact (p (n + 1)) (d n)) ∧
        (∀ n, Function.Exact (d n) (i n)) ∧ Function.Surjective (p 0) := by
  let eA := homologyIndexEquiv K hA hT.pair_A c₁
  let eS := homologyIndexEquiv K hS hT.pair_S c₂
  let eR := homologyIndexEquiv K hR hT.pair_R c₃
  refine ⟨fun n => (eS n).symm.toLinearMap ∘ₗ
      (singIncl K (Int.ofNat n) hT.sub₁₂ (subset_refl N₀)).hom ∘ₗ (eA n).toLinearMap,
    fun n => (eR n).symm.toLinearMap ∘ₗ
      (singIncl K (Int.ofNat n) (subset_refl N₂) hT.sub₀₁).hom ∘ₗ (eS n).toLinearMap,
    fun n => (eA n).symm.toLinearMap ∘ₗ (singδ K (Int.ofNat n) N₂ N₁ N₀).hom ∘ₗ
      (eR (n + 1)).toLinearMap, fun n => ?_, fun n => ?_, fun n => ?_, ?_⟩
  · exact exact_conj K (eA n) (eS n) (eR n) (sing_exact_incl K (Int.ofNat n) hT.sub₀₁ hT.sub₁₂)
  · exact exact_conj K (eS (n + 1)) (eR (n + 1)) (eA n)
      (sing_exact_δ K (Int.ofNat n) hT.sub₀₁ hT.sub₁₂)
  · exact exact_conj K (eR (n + 1)) (eA n) (eS n)
      (sing_exact_δ' K (Int.ofNat n) hT.sub₀₁ hT.sub₁₂)
  · intro y
    obtain ⟨x, hx⟩ := (sing_exact_δ K (Int.negSucc 0) hT.sub₀₁ hT.sub₁₂ (eR 0 y)).1
      (Subsingleton.elim _ _)
    refine ⟨(eS 0).symm x, ?_⟩
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.apply_symm_apply]
    rw [LinearEquiv.symm_apply_eq]
    exact hx

/-- If the repeller has trivial homology index, then `CH_*(A) ≅ CH_*(S)`. -/
theorem homologyIndex_attractor_iso {S A R N₀ N₁ N₂ : Set α}
    (hT : IsIndexTriple ϕ S A R N₀ N₁ N₂) (hS : IsIsolatedInvariantSet ϕ S)
    (hA : IsIsolatedInvariantSet ϕ A) (hR : IsIsolatedInvariantSet ϕ R)
    (c₁ : IsCollared ϕ N₁ N₀) (c₂ : IsCollared ϕ N₂ N₀) (c₃ : IsCollared ϕ N₂ N₁)
    (hRt : ∀ n, Subsingleton (homologyIndex K ϕ hR n)) :
    ∃ i : ∀ n, homologyIndex K ϕ hA n →ₗ[K] homologyIndex K ϕ hS n,
      ∀ n, Function.Bijective (i n) := by
  obtain ⟨i, p, d, h1, -, h3, -⟩ := homologyIndex_attractor_repeller K hT hS hA hR c₁ c₂ c₃
  refine ⟨i, fun n => ?_⟩
  have := hRt (n + 1)
  have := hRt n
  exact bijective_of_exact_of_subsingleton (h3 n) (h1 n)

/-- If the attractor has trivial homology index, then `CH_*(S) ≅ CH_*(R)`. -/
theorem homologyIndex_repeller_iso {S A R N₀ N₁ N₂ : Set α}
    (hT : IsIndexTriple ϕ S A R N₀ N₁ N₂) (hS : IsIsolatedInvariantSet ϕ S)
    (hA : IsIsolatedInvariantSet ϕ A) (hR : IsIsolatedInvariantSet ϕ R)
    (c₁ : IsCollared ϕ N₁ N₀) (c₂ : IsCollared ϕ N₂ N₀) (c₃ : IsCollared ϕ N₂ N₁)
    (hAt : ∀ n, Subsingleton (homologyIndex K ϕ hA n)) :
    ∃ p : ∀ n, homologyIndex K ϕ hS n →ₗ[K] homologyIndex K ϕ hR n,
      ∀ n, Function.Bijective (p n) := by
  obtain ⟨i, p, d, h1, h2, -, h4⟩ := homologyIndex_attractor_repeller K hT hS hA hR c₁ c₂ c₃
  refine ⟨p, fun n => ?_⟩
  cases n with
  | zero =>
    refine ⟨fun a b hab => ?_, h4⟩
    have hz : p 0 (a - b) = 0 := by rw [map_sub, hab, sub_self]
    obtain ⟨c, hc⟩ := (h1 0 _).1 hz
    have := hAt 0
    rw [Subsingleton.elim c 0, map_zero] at hc
    exact sub_eq_zero.1 hc.symm
  | succ m =>
    have := hAt (m + 1)
    have := hAt m
    exact bijective_of_exact_of_subsingleton (h1 (m + 1)) (h2 m)

end Main

end ConleyCheck.Conley
