import ConleyCheck.Conley.DoubleBase
import ConleyCheck.Conley.Connecting
import ConleyCheck.Algebra.ExactSplit

/-!
# The double of the extended phase space and the transport sequence

The double is the skew product over the lifted base flow `dblFlow` on `[-1, 2]` (the variable
`u = θ / π`), with fiber flow pulled back along the tent map `tentT` (playing `cos θ`). The upper
sheet is `u ∈ [0, 1]`, the IR point is `u = 0` and the UV point is `u = 1`.

* `dblΦ`, `isSkew_dbl`, `dblQ_dblΦ`: Lemma `lem:double`(a), the semiconjugacy `q` to the slab.
* `dbl_upper`: the restriction of `q` to the upper sheet is a conjugacy with inverse `upper`.
* `dbl_isolated_preimage`, `snat_isolated`: Lemma `lem:isolation`(b), in the lifted model.
* `snat_attractorRepeller`: Lemma `lem:isolation`(c).
* `dbl_boundary_IR`, `dbl_boundary_UV`, `dbl_boundary_UV_zero`: Proposition `prop:boundary`,
  double rows.
* `snat_attractor_index`, `snat_repeller_index`: Remark `rem:boundary-iso`, the boundary
  isomorphisms `a_k : CH_k(K_+; f_+) ≅ CH_k(K_+ × {0})` and
  `s_k : CH_k(K_-; f_-) ≅ CH_{k+1}(K_- × {π})` in `S♮`, in homology.
* `transport`: Theorem `thm:transport`, the defining square `Ψ_k = a_k⁻¹ ∘ ∂_{k+1} ∘ s_k`, the long
  exact sequence and part (ii), together with
  `transport_split`, part (i), the splitting over a field. Part (ii) does not depend on the index
  triple used to define `Ψ`: by `exists_connecting_of_singδ_ne_zero`, a nonzero connecting map for
  any index triple with `(N₁, N₀)` collared gives a connecting orbit.
* `transport_finrank`: part (iii) over a field. The ranks of `Ψ` are determined by the dimensions
  of `CH_*(K_-)`, `CH_*(K_+)` and `CH_*(S♮)`. Invariance of `Ψ` itself over `ℤ` under continuation
  is not formalized.
-/

namespace ConleyCheck.Conley

open Set Function
open scoped unitInterval

universe u

/-- Changing the flow and the set along equalities does not change the homology index. -/
theorem homologyIndex_congr (K : Type u) [Ring K] {α : Type u} [TopologicalSpace α] [T2Space α]
    {ϕ ψ : Flow ℝ α} {S T : Set α} (h : ϕ = ψ) (h' : S = T)
    (hS : IsIsolatedInvariantSet ϕ S) (hT : IsIsolatedInvariantSet ψ T) (n : ℕ) :
    Nonempty (homologyIndex K ϕ hS n ≃ₗ[K] homologyIndex K ψ hT n) := by
  subst h h'
  exact ⟨LinearEquiv.refl _ _⟩

section Double

variable {X : Type u} [TopologicalSpace X] {Φ : Flow ℝ (X × Tau)} {θ : Flow ℝ Tau}
  (hΦ : IsSkew Φ θ) (hθ : IsHeight θ (fun b => (b : ℝ)))

/-- The semiconjugacy `q(x, u) = (x, cos(π u))` from the double to the slab. -/
noncomputable def dblQ (p : X × Dbl) : X × Tau := (p.1, tentT p.2)

omit [TopologicalSpace X] in
theorem dblQ_apply (p : X × Dbl) : dblQ p = (p.1, tentT p.2) := rfl

theorem continuous_dblQ : Continuous (dblQ : X × Dbl → X × Tau) :=
  continuous_fst.prodMk (continuous_tentT.comp continuous_snd)

/-- The double `Φ̃_t(x, u) = (Φ_t(x, cos(π u)).1, ϑ_t u)`. -/
noncomputable def dblΦ : Flow ℝ (X × Dbl) where
  toFun t p := ((Φ t (dblQ p)).1, dblFlow hθ t p.2)
  cont' := (continuous_fst.comp (Φ.continuous continuous_fst
    (continuous_dblQ.comp continuous_snd))).prodMk
    ((dblFlow hθ).continuous continuous_fst (continuous_snd.comp continuous_snd))
  map_add' s t p := by
    have e : ((Φ t (dblQ p)).1, tentT (dblFlow hθ t p.2)) = Φ t (dblQ p) :=
      Prod.ext rfl (by rw [tentT_dblFlow, hΦ]; rfl)
    show ((Φ (s + t) (dblQ p)).1, dblFlow hθ (s + t) p.2) =
      ((Φ s ((Φ t (dblQ p)).1, tentT (dblFlow hθ t p.2))).1, dblFlow hθ s (dblFlow hθ t p.2))
    rw [e, Φ.map_add, Flow.map_add]
  map_zero' p := by
    show ((Φ 0 (dblQ p)).1, dblFlow hθ 0 p.2) = p
    rw [Φ.map_zero_apply, Flow.map_zero_apply]
    rfl

theorem dblΦ_apply (t : ℝ) (p : X × Dbl) :
    dblΦ hΦ hθ t p = ((Φ t (dblQ p)).1, dblFlow hθ t p.2) := rfl

theorem isSkew_dbl : IsSkew (dblΦ hΦ hθ) (dblFlow hθ) := fun _ _ => rfl

/-- Lemma `lem:double`(a): `q ∘ Φ̃_t = Φ_t ∘ q`. -/
theorem dblQ_dblΦ (t : ℝ) (p : X × Dbl) : dblQ (dblΦ hΦ hθ t p) = Φ t (dblQ p) :=
  Prod.ext rfl (by
    show tentT (dblFlow hθ t p.2) = (Φ t (dblQ p)).2
    rw [tentT_dblFlow, hΦ]; rfl)

omit hΦ in
theorem br₁_mem (b : Tau) : br₁ b ∈ Icc (-1 : ℝ) 2 := by
  have h := b.2
  unfold br₁; constructor <;> linarith [h.1, h.2]

/-- The inverse of `q` on the upper sheet. -/
noncomputable def upper (p : X × Tau) : X × Dbl := (p.1, ⟨br₁ p.2, br₁_mem p.2⟩)

omit hΦ hθ in
theorem continuous_upper : Continuous (upper : X × Tau → X × Dbl) :=
  continuous_fst.prodMk (((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).div_const
    _).subtype_mk _)

/-- Lemma `lem:double`(a): on the upper sheet `X × [0, 1]`, `q` is a homeomorphism onto the slab
conjugating the flows, with inverse `upper`. -/
theorem dbl_upper :
    (∀ p : X × Tau, dblQ (upper p) = p) ∧
      (∀ p : X × Dbl, (p.2 : ℝ) ∈ Icc (0 : ℝ) 1 → upper (dblQ p) = p) ∧
      (∀ p : X × Tau, ((upper p).2 : ℝ) ∈ Icc (0 : ℝ) 1) ∧
      ∀ t (p : X × Tau), dblΦ hΦ hθ t (upper p) = upper (Φ t p) := by
  have h1 : ∀ p : X × Tau, dblQ (upper p) = p := fun p =>
    Prod.ext rfl (Subtype.ext (tent_br₁ p.2.2))
  have hu : ∀ p : X × Tau, ((upper p).2 : ℝ) ∈ Icc (0 : ℝ) 1 := fun p => by
    have h := p.2.2
    show br₁ p.2 ∈ Icc (0 : ℝ) 1
    unfold br₁; constructor <;> linarith [h.1, h.2]
  have h2 : ∀ p : X × Dbl, (p.2 : ℝ) ∈ Icc (0 : ℝ) 1 → upper (dblQ p) = p := fun p hp =>
    Prod.ext rfl (Subtype.ext (br₁_tent hp.1 hp.2))
  refine ⟨h1, h2, hu, fun t p => ?_⟩
  have e := dblQ_dblΦ hΦ hθ t (upper p)
  rw [h1] at e
  have hm : ((dblΦ hΦ hθ t (upper p)).2 : ℝ) ∈ Icc (0 : ℝ) 1 :=
    dblFlow_mem_01 hθ (hu p).1 (hu p).2 t
  rw [← h2 _ hm, e]

/-- `τ ∘ q` is a height function on the double. -/
theorem isHeight_dbl : IsHeight (dblΦ hΦ hθ) (fun p => ((dblQ p).2 : ℝ)) where
  continuous := continuous_subtype_val.comp (continuous_snd.comp continuous_dblQ)
  mem p := (dblQ p).2.2
  fix p h t := by
    show ((dblQ (dblΦ hΦ hθ t p)).2 : ℝ) = (dblQ p).2
    rw [dblQ_dblΦ, hΦ]
    exact hθ.fix _ h t
  strict p h1 h2 t ht := by
    show ((dblQ p).2 : ℝ) < (dblQ (dblΦ hΦ hθ t p)).2
    rw [dblQ_dblΦ, hΦ]
    exact hθ.strict _ h1 h2 t ht

theorem Inv_dblQ_preimage (N : Set (X × Tau)) :
    Inv (dblΦ hΦ hθ) (dblQ ⁻¹' N) = dblQ ⁻¹' Inv Φ N := by
  ext p
  simp only [Inv, mem_ofPred_eq, mem_preimage, dblQ_dblΦ]

variable [T2Space X]

/-- Lemma `lem:isolation`(b) in the lifted model: `q⁻¹(N)` isolates `q⁻¹(S)`. -/
theorem dbl_isolated_preimage {N : Set (X × Tau)} (hN : IsIsolatingNbhd Φ N) :
    IsIsolatingNbhd (dblΦ hΦ hθ) (dblQ ⁻¹' N) ∧
      Inv (dblΦ hΦ hθ) (dblQ ⁻¹' N) = dblQ ⁻¹' Inv Φ N := by
  refine ⟨⟨?_, ?_⟩, Inv_dblQ_preimage hΦ hθ N⟩
  · refine ((hN.1.image continuous_fst).prod isCompact_univ).of_isClosed_subset
      (hN.1.isClosed.preimage continuous_dblQ) ?_
    intro p hp
    exact ⟨⟨dblQ p, hp, rfl⟩, mem_univ _⟩
  · rw [Inv_dblQ_preimage]
    exact (preimage_mono hN.2).trans (preimage_interior_subset_interior_preimage continuous_dblQ)

/-- The upper half `S♮ = q⁻¹(S) ∩ X × [0, 1]`. -/
def snat (S : Set (X × Tau)) : Set (X × Dbl) := {p | dblQ p ∈ S ∧ (p.2 : ℝ) ∈ Icc (0 : ℝ) 1}

/-- The isolating neighborhood `q⁻¹(N) ∩ X × [-1/2, 3/2]` of `S♮`. -/
def nnat (N : Set (X × Tau)) : Set (X × Dbl) :=
  {p | dblQ p ∈ N ∧ (p.2 : ℝ) ∈ Icc (-1 / 2 : ℝ) (3 / 2)}

omit [T2Space X] in
/-- An orbit staying in `u ∈ [-1/2, 3/2]` lies in the upper sheet. -/
theorem upper_of_forall {u : Dbl} (h : ∀ t, (dblFlow hθ t u : ℝ) ∈ Icc (-1 / 2 : ℝ) (3 / 2)) :
    (u : ℝ) ∈ Icc (0 : ℝ) 1 := by
  by_contra hu
  rw [mem_Icc, not_and_or, not_le, not_le] at hu
  rcases hu with h0 | h1
  · rcases lt_or_ge (-1) (u : ℝ) with hm | hm
    · obtain ⟨T, hT⟩ := dblFlow_tendsto_neg_one hθ h0 (ε := 1 / 4) (by norm_num)
      have := (h (min T 0)).1
      have := hT (min T 0) (min_le_left _ _)
      linarith
    · have : (u : ℝ) = -1 := le_antisymm hm u.2.1
      have := (h 0).1
      rw [Flow.map_zero_apply] at this
      linarith
  · obtain ⟨T, hT⟩ := dblFlow_tendsto_two hθ h1 (ε := 1 / 4) (by norm_num)
    have := (h (max T 0)).2
    have := hT (max T 0) (le_max_left _ _)
    linarith

/-- Lemma `lem:isolation`(b): `S♮` is an isolated invariant set of the double. -/
theorem snat_isolated {N : Set (X × Tau)} (hN : IsIsolatingNbhd Φ N) :
    IsIsolatingNbhd (dblΦ hΦ hθ) (nnat N) ∧ Inv (dblΦ hΦ hθ) (nnat N) = snat (Inv Φ N) := by
  have hc : Continuous fun p : X × Dbl => ((p.2 : Dbl) : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hInv : Inv (dblΦ hΦ hθ) (nnat N) = snat (Inv Φ N) := by
    ext p
    constructor
    · intro hp
      have hup : (p.2 : ℝ) ∈ Icc (0 : ℝ) 1 := upper_of_forall hθ fun t => (hp t).2
      refine ⟨fun t => ?_, hup⟩
      have := (hp t).1
      rwa [dblQ_dblΦ] at this
    · rintro ⟨hp, hup⟩ t
      refine ⟨?_, ?_⟩
      · show dblQ (dblΦ hΦ hθ t p) ∈ N
        rw [dblQ_dblΦ]; exact hp t
      · have := dblFlow_mem_01 hθ hup.1 hup.2 t
        exact ⟨le_trans (by norm_num) this.1, this.2.trans (by norm_num)⟩
  refine ⟨⟨?_, ?_⟩, hInv⟩
  · refine ((hN.1.image continuous_fst).prod isCompact_univ).of_isClosed_subset
      ((hN.1.isClosed.preimage continuous_dblQ).inter (isClosed_Icc.preimage hc)) ?_
    intro p hp
    exact ⟨⟨dblQ p, hp.1, rfl⟩, mem_univ _⟩
  · rw [hInv]
    have hO : IsOpen (dblQ ⁻¹' interior N ∩ (fun p : X × Dbl => (p.2 : ℝ)) ⁻¹' Ioo (-1 / 2) (3 / 2)) :=
      (isOpen_interior.preimage continuous_dblQ).inter (isOpen_Ioo.preimage hc)
    have hsub : dblQ ⁻¹' interior N ∩ (fun p : X × Dbl => (p.2 : ℝ)) ⁻¹' Ioo (-1 / 2) (3 / 2) ⊆
        nnat N := fun q hq => ⟨interior_subset hq.1, Ioo_subset_Icc_self hq.2⟩
    intro p hp
    exact interior_maximal hsub hO ⟨hN.2 hp.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩

omit [TopologicalSpace X] [T2Space X] in
theorem snat_inter_top (S : Set (X × Tau)) :
    snat S ∩ (fun p => ((dblQ p).2 : ℝ)) ⁻¹' {1} = {x | (x, Tau.top) ∈ S} ×ˢ {Dbl.zero} := by
  ext ⟨x, u⟩
  simp only [snat, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff, mem_prod]
  constructor
  · rintro ⟨⟨hS, h0, h1⟩, ht⟩
    have ht' : tent u = 1 := ht
    rw [tent_of_mem h0 h1] at ht'
    have hu : u = Dbl.zero := Subtype.ext (show (u : ℝ) = 0 by linarith)
    subst hu
    rw [dblQ_apply, tentT_zero] at hS
    exact ⟨hS, rfl⟩
  · rintro ⟨hS, rfl⟩
    refine ⟨⟨?_, show (0 : ℝ) ≤ 0 from le_rfl, show (0 : ℝ) ≤ 1 by norm_num⟩, ?_⟩
    · rw [dblQ_apply, tentT_zero]; exact hS
    · show ((tentT Dbl.zero : Tau) : ℝ) = 1
      rw [tentT_zero]; rfl

omit [TopologicalSpace X] [T2Space X] in
theorem snat_inter_bot (S : Set (X × Tau)) :
    snat S ∩ (fun p => ((dblQ p).2 : ℝ)) ⁻¹' {-1} = {x | (x, Tau.bot) ∈ S} ×ˢ {Dbl.one} := by
  ext ⟨x, u⟩
  simp only [snat, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff, mem_prod]
  constructor
  · rintro ⟨⟨hS, h0, h1⟩, ht⟩
    have ht' : tent u = -1 := ht
    rw [tent_of_mem h0 h1] at ht'
    have hu : u = Dbl.one := Subtype.ext (show (u : ℝ) = 1 by linarith)
    subst hu
    rw [dblQ_apply, tentT_one] at hS
    exact ⟨hS, rfl⟩
  · rintro ⟨hS, rfl⟩
    refine ⟨⟨?_, show (0 : ℝ) ≤ 1 by norm_num, show (1 : ℝ) ≤ 1 from le_rfl⟩, ?_⟩
    · rw [dblQ_apply, tentT_one]; exact hS
    · show ((tentT Dbl.one : Tau) : ℝ) = -1
      rw [tentT_one]; rfl

/-- Lemma `lem:isolation`(c): `(K_+ × {0}, K_- × {π})` is an attractor–repeller pair of `S♮`. -/
theorem snat_attractorRepeller {S : Set (X × Tau)} (hS : IsIsolatedInvariantSet Φ S) :
    IsIsolatedInvariantSet (dblΦ hΦ hθ) (snat S) ∧
      IsAttractorRepellerPair (dblΦ hΦ hθ) (snat S) ({x | (x, Tau.top) ∈ S} ×ˢ {Dbl.zero})
        ({x | (x, Tau.bot) ∈ S} ×ˢ {Dbl.one}) := by
  obtain ⟨N, hN, rfl⟩ := hS
  obtain ⟨hNn, hInv⟩ := snat_isolated hΦ hθ hN
  have hSn : IsIsolatedInvariantSet (dblΦ hΦ hθ) (snat (Inv Φ N)) := ⟨_, hNn, hInv⟩
  have h := (isHeight_dbl hΦ hθ).isAttractorRepellerPair hSn
  rw [snat_inter_top, snat_inter_bot] at h
  exact ⟨hSn, h⟩

omit [T2Space X] in
/-- The fiber flow of the double over the IR point is the infrared flow `f_+`. -/
theorem f₀_dbl_zero :
    (contraction0 hθ).f₀ (isSkew_dbl hΦ hθ) (isInvariant_U0 hθ) zero_mem_U0 =
      fiberFlow hΦ Tau.top (base_top hθ) :=
  Flow.ext fun t x => by
    show (Φ t (x, tentT Dbl.zero)).1 = (Φ t (x, Tau.top)).1
    rw [tentT_zero]

omit [T2Space X] in
/-- The fiber flow of the double over the UV point is the ultraviolet flow `f_-`. -/
theorem f₀_dbl_one :
    (contraction1 hθ).f₀ (isSkew_dbl hΦ hθ) (isInvariant_U1 hθ) one_mem_U1 =
      fiberFlow hΦ Tau.bot (base_bot hθ) :=
  Flow.ext fun t x => by
    show (Φ t (x, tentT Dbl.one)).1 = (Φ t (x, Tau.bot)).1
    rw [tentT_one]

variable [TopologicalSpace.MetrizableSpace X] (K : Type u) [Ring K]

/-- Proposition `prop:boundary`, double row at the IR point: `h_D(K × {0}) ≅ h_{f_+}(K)`. -/
theorem dbl_boundary_IR {M : Set X}
    (hM : IsIsolatingNbhd (fiberFlow hΦ Tau.top (base_top hθ)) M)
    (hS : IsIsolatedInvariantSet (dblΦ hΦ hθ)
      (Inv (fiberFlow hΦ Tau.top (base_top hθ)) M ×ˢ {Dbl.zero}))
    (hK : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ))
      (Inv (fiberFlow hΦ Tau.top (base_top hθ)) M)) (n : ℕ) :
    Nonempty (homologyIndex K (dblΦ hΦ hθ) hS n ≃ₗ[K]
      homologyIndex K (fiberFlow hΦ Tau.top (base_top hθ)) hK n) := by
  have he := f₀_dbl_zero hΦ hθ
  have hM' : IsIsolatingNbhd ((contraction0 hθ).f₀ (isSkew_dbl hΦ hθ) (isInvariant_U0 hθ)
      zero_mem_U0) M := by rw [he]; exact hM
  obtain ⟨NK, LK, hPK, -⟩ := exists_indexPair_of_t2 hM
  have hPK' : IsIndexPair ((contraction0 hθ).f₀ (isSkew_dbl hΦ hθ) (isInvariant_U0 hθ)
      zero_mem_U0) (Inv ((contraction0 hθ).f₀ (isSkew_dbl hΦ hθ) (isInvariant_U0 hθ)
        zero_mem_U0) M) NK LK := by rw [he]; exact hPK
  have hI := skew_hasIndex (isSkew_dbl hΦ hθ) (isInvariant_U0 hθ) isOpen_U0 zero_mem_U0
    (contraction0 hθ) hM' (isIndexPair0 hθ) N0_subset_U0
    (show ((0 : ℝ)) ∈ Icc (-1 / 2 : ℝ) (1 / 2) by norm_num) deform0
    (fun b => Subtype.ext (Subtype.ext (Subtype.ext (by
      show (1 - ((0 : I) : ℝ)) * _ = _
      simp))))
    (fun b => Subtype.ext (Subtype.ext (Subtype.ext (by
      show (1 - ((1 : I) : ℝ)) * _ = (0 : ℝ)
      simp)))) hPK'
  rw [he] at hI
  obtain ⟨NA, LA, hPA, ⟨e⟩⟩ := hI
  obtain ⟨iso₁⟩ := homologyIndexIso K hS hPA n
  obtain ⟨iso₃⟩ := homologyIndexIso K hK hPK n
  exact ⟨iso₁.toLinearEquiv.trans ((redIso K e n).toLinearEquiv.trans iso₃.symm.toLinearEquiv)⟩

/-- Proposition `prop:boundary`, double row at the UV point: `CH_{n+1}(K × {π}) ≅ CH_n(K; f_-)`,
the homological form of `h_D(K × {π}) ≅ Σ h_{f_-}(K)`. -/
theorem dbl_boundary_UV {M : Set X}
    (hM : IsIsolatingNbhd (fiberFlow hΦ Tau.bot (base_bot hθ)) M)
    (hS : IsIsolatedInvariantSet (dblΦ hΦ hθ)
      (Inv (fiberFlow hΦ Tau.bot (base_bot hθ)) M ×ˢ {Dbl.one}))
    (hK : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ))
      (Inv (fiberFlow hΦ Tau.bot (base_bot hθ)) M)) (n : ℕ) :
    Nonempty (homologyIndex K (dblΦ hΦ hθ) hS (n + 1) ≃ₗ[K]
      homologyIndex K (fiberFlow hΦ Tau.bot (base_bot hθ)) hK n) := by
  have he := f₀_dbl_one hΦ hθ
  set f := (contraction1 hθ).f₀ (isSkew_dbl hΦ hθ) (isInvariant_U1 hθ) one_mem_U1
  have hM' : IsIsolatingNbhd f M := by rw [he]; exact hM
  have hS' : IsIsolatedInvariantSet (dblΦ hΦ hθ) (Inv f M ×ˢ {Dbl.one}) := by rw [he]; exact hS
  have hK' : IsIsolatedInvariantSet f (Inv f M) := by rw [he]; exact hK
  obtain ⟨e₁⟩ := homologyIndex_congr K rfl (by rw [he]) hS hS' (n + 1)
  obtain ⟨e₂⟩ := skew_suspension K (isSkew_dbl hΦ hθ) (isInvariant_U1 hθ) isOpen_U1 one_mem_U1
    (contraction1 hθ) hM' (isIndexPair1 hθ) N1_subset_U1 chart1 hS' hK' n
  obtain ⟨e₃⟩ := homologyIndex_congr K he (by rw [he]) hK' hK n
  exact ⟨e₁.trans (e₂.trans e₃)⟩

/-- `CH_0(K × {π}) = 0` for the double. -/
theorem dbl_boundary_UV_zero {M : Set X}
    (hM : IsIsolatingNbhd (fiberFlow hΦ Tau.bot (base_bot hθ)) M)
    (hS : IsIsolatedInvariantSet (dblΦ hΦ hθ)
      (Inv (fiberFlow hΦ Tau.bot (base_bot hθ)) M ×ˢ {Dbl.one}))
    (hK : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ))
      (Inv (fiberFlow hΦ Tau.bot (base_bot hθ)) M)) :
    Subsingleton (homologyIndex K (dblΦ hΦ hθ) hS 0) := by
  have he := f₀_dbl_one hΦ hθ
  set f := (contraction1 hθ).f₀ (isSkew_dbl hΦ hθ) (isInvariant_U1 hθ) one_mem_U1
  have hM' : IsIsolatingNbhd f M := by rw [he]; exact hM
  have hS' : IsIsolatedInvariantSet (dblΦ hΦ hθ) (Inv f M ×ˢ {Dbl.one}) := by rw [he]; exact hS
  have hK' : IsIsolatedInvariantSet f (Inv f M) := by rw [he]; exact hK
  obtain ⟨e₁⟩ := homologyIndex_congr K rfl (by rw [he]) hS hS' 0
  have := skew_suspension_zero K (isSkew_dbl hΦ hθ) (isInvariant_U1 hθ) isOpen_U1 one_mem_U1
    (contraction1 hθ) hM' (isIndexPair1 hθ) N1_subset_U1 chart1 hS' hK'
  exact e₁.toEquiv.subsingleton

/-- The attractor `K_+ × {0}` of `S♮` has the homology index of `K_+` for `f_+`. -/
theorem snat_attractor_index {S : Set (X × Tau)} (hS : IsIsolatedInvariantSet Φ S)
    (hA : IsIsolatedInvariantSet (dblΦ hΦ hθ) ({x | (x, Tau.top) ∈ S} ×ˢ {Dbl.zero}))
    (hKp : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ)) {x | (x, Tau.top) ∈ S})
    (k : ℕ) : Nonempty (homologyIndex K _ hA k ≃ₗ[K] homologyIndex K _ hKp k) := by
  obtain ⟨N, hN, hNS⟩ := id hS
  obtain ⟨hMT, hInvT⟩ := hΦ.fiber_isolating (base_top hθ) hN
  rw [hNS] at hInvT
  have hKp' : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ))
      (Inv (fiberFlow hΦ Tau.top (base_top hθ)) ((fun x => (x, Tau.top)) ⁻¹' N)) := ⟨_, hMT, rfl⟩
  have hA' : IsIsolatedInvariantSet (dblΦ hΦ hθ)
      (Inv (fiberFlow hΦ Tau.top (base_top hθ)) ((fun x => (x, Tau.top)) ⁻¹' N) ×ˢ {Dbl.zero}) := by
    rw [hInvT]; exact hA
  exact ⟨((homologyIndex_congr K rfl (by rw [hInvT]) hA hA' k).some.trans
    (dbl_boundary_IR hΦ hθ K hMT hA' hKp' k).some).trans
    (homologyIndex_congr K rfl hInvT hKp' hKp k).some⟩

/-- The repeller `K_- × {π}` of `S♮` has the suspended homology index of `K_-` for `f_-`. -/
theorem snat_repeller_index {S : Set (X × Tau)} (hS : IsIsolatedInvariantSet Φ S)
    (hR : IsIsolatedInvariantSet (dblΦ hΦ hθ) ({x | (x, Tau.bot) ∈ S} ×ˢ {Dbl.one}))
    (hKm : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ)) {x | (x, Tau.bot) ∈ S})
    (k : ℕ) : Nonempty (homologyIndex K _ hR (k + 1) ≃ₗ[K] homologyIndex K _ hKm k) := by
  obtain ⟨N, hN, hNS⟩ := id hS
  obtain ⟨hMB, hInvB⟩ := hΦ.fiber_isolating (base_bot hθ) hN
  rw [hNS] at hInvB
  have hKm' : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ))
      (Inv (fiberFlow hΦ Tau.bot (base_bot hθ)) ((fun x => (x, Tau.bot)) ⁻¹' N)) := ⟨_, hMB, rfl⟩
  have hR' : IsIsolatedInvariantSet (dblΦ hΦ hθ)
      (Inv (fiberFlow hΦ Tau.bot (base_bot hθ)) ((fun x => (x, Tau.bot)) ⁻¹' N) ×ˢ {Dbl.one}) := by
    rw [hInvB]; exact hR
  exact ⟨((homologyIndex_congr K rfl (by rw [hInvB]) hR hR' (k + 1)).some.trans
    (dbl_boundary_UV hΦ hθ K hMB hR' hKm' k).some).trans
    (homologyIndex_congr K rfl hInvB hKm' hKm k).some⟩

/-- `CH_0(K_- × {π}) = 0` in `S♮`. -/
theorem snat_repeller_zero {S : Set (X × Tau)} (hS : IsIsolatedInvariantSet Φ S)
    (hR : IsIsolatedInvariantSet (dblΦ hΦ hθ) ({x | (x, Tau.bot) ∈ S} ×ˢ {Dbl.one})) :
    Subsingleton (homologyIndex K _ hR 0) := by
  obtain ⟨N, hN, hNS⟩ := id hS
  obtain ⟨hMB, hInvB⟩ := hΦ.fiber_isolating (base_bot hθ) hN
  rw [hNS] at hInvB
  have hKm' : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ))
      (Inv (fiberFlow hΦ Tau.bot (base_bot hθ)) ((fun x => (x, Tau.bot)) ⁻¹' N)) := ⟨_, hMB, rfl⟩
  have hR' : IsIsolatedInvariantSet (dblΦ hΦ hθ)
      (Inv (fiberFlow hΦ Tau.bot (base_bot hθ)) ((fun x => (x, Tau.bot)) ⁻¹' N) ×ˢ {Dbl.one}) := by
    rw [hInvB]; exact hR
  have := dbl_boundary_UV_zero hΦ hθ K hMB hR' hKm'
  exact (homologyIndex_congr K rfl (by rw [hInvB]) hR hR' 0).some.toEquiv.subsingleton

/-- Theorem `thm:transport`. For an isolated invariant set `S` of the extended phase space, with
`K_± = {x : (x, ±1) ∈ S}`, there are maps `Ψ_k : CH_k(K_-; f_-) → CH_k(K_+; f_+)` fitting into the
long exact sequence
`⋯ → CH_k(K_-) → CH_k(K_+) → CH_k(S♮) → CH_{k-1}(K_-) → CH_{k-1}(K_+) → ⋯`
ending with `CH_0(K_+) → CH_0(S♮) → 0`. Part (ii): if some `Ψ_k ≠ 0`, then `S` contains an orbit
with `-1 < τ < 1` whose `α`- and `ω`-limit sets lie in `K_- × {-1}` and `K_+ × {1}`. The last
conjunct is the square defining `Ψ`: `Ψ_k = a_k⁻¹ ∘ ∂_{k+1} ∘ s_k`, where `s_k`, `a_k` are the
boundary isomorphisms of Remark `rem:boundary-iso` and `∂` is the connecting homomorphism of the
attractor–repeller sequence of `(K_+ × {0}, K_- × {π})` in `S♮`. This is Remark `rem:status`. -/
theorem transport {S : Set (X × Tau)} (hS : IsIsolatedInvariantSet Φ S) :
    ∃ (hSn : IsIsolatedInvariantSet (dblΦ hΦ hθ) (snat S))
      (hKp : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ)) {x | (x, Tau.top) ∈ S})
      (hKm : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ)) {x | (x, Tau.bot) ∈ S})
      (Ψ : ∀ k, homologyIndex K _ hKm k →ₗ[K] homologyIndex K _ hKp k)
      (i : ∀ k, homologyIndex K _ hKp k →ₗ[K] homologyIndex K _ hSn k)
      (p : ∀ k, homologyIndex K _ hSn (k + 1) →ₗ[K] homologyIndex K _ hKm k),
      (∀ k, Exact (Ψ k) (i k)) ∧ (∀ k, Exact (i (k + 1)) (p k)) ∧
        (∀ k, Exact (p k) (Ψ k)) ∧ Surjective (i 0) ∧
        (∀ k, Ψ k ≠ 0 → ∃ q ∈ S, (q.2 : ℝ) ∈ Ioo (-1) 1 ∧
          omegaLim Φ q ⊆ S ∩ (fun q => (q.2 : ℝ)) ⁻¹' {1} ∧
          alphaLim Φ q ⊆ S ∩ (fun q => (q.2 : ℝ)) ⁻¹' {-1}) ∧
        ∃ (hA : IsIsolatedInvariantSet (dblΦ hΦ hθ) ({x | (x, Tau.top) ∈ S} ×ˢ {Dbl.zero}))
          (hR : IsIsolatedInvariantSet (dblΦ hΦ hθ) ({x | (x, Tau.bot) ∈ S} ×ˢ {Dbl.one}))
          (s : ∀ k, homologyIndex K _ hKm k ≃ₗ[K] homologyIndex K _ hR (k + 1))
          (a : ∀ k, homologyIndex K _ hKp k ≃ₗ[K] homologyIndex K _ hA k)
          (iA : ∀ k, homologyIndex K _ hA k →ₗ[K] homologyIndex K _ hSn k)
          (pR : ∀ k, homologyIndex K _ hSn k →ₗ[K] homologyIndex K _ hR k)
          (d : ∀ k, homologyIndex K _ hR (k + 1) →ₗ[K] homologyIndex K _ hA k),
          (∀ k, Exact (iA k) (pR k)) ∧ (∀ k, Exact (pR (k + 1)) (d k)) ∧
            (∀ k, Exact (d k) (iA k)) ∧
            ∀ k, Ψ k = (a k).symm.toLinearMap ∘ₗ d k ∘ₗ (s k).toLinearMap := by
  obtain ⟨hSn, hAR⟩ := snat_attractorRepeller hΦ hθ hS
  obtain ⟨N, hN, hNS⟩ := id hS
  obtain ⟨hMT, hInvT⟩ := hΦ.fiber_isolating (base_top hθ) hN
  obtain ⟨hMB, hInvB⟩ := hΦ.fiber_isolating (base_bot hθ) hN
  rw [hNS] at hInvT hInvB
  have hKp : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ)) {x | (x, Tau.top) ∈ S} :=
    ⟨_, hMT, hInvT⟩
  have hKm : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ)) {x | (x, Tau.bot) ∈ S} :=
    ⟨_, hMB, hInvB⟩
  have eA := fun k => (snat_attractor_index hΦ hθ K hS hAR.isolated_A hKp k).some
  have eR := fun k => (snat_repeller_index hΦ hθ K hS hAR.isolated_R hKm k).some
  have hR0 := snat_repeller_zero hΦ hθ K hS hAR.isolated_R
  obtain ⟨iA, pR, d, h1, h2, h3, -, hd⟩ := homologyIndex_attractor_repeller_connecting K hAR
  refine ⟨hSn, hKp, hKm, fun k => (eA k).toLinearMap ∘ₗ d k ∘ₗ (eR k).symm.toLinearMap,
    fun k => iA k ∘ₗ (eA k).symm.toLinearMap, fun k => (eR k).toLinearMap ∘ₗ pR (k + 1),
    fun k => ?_, fun k => ?_, fun k => ?_, ?_, fun k hΨ => ?_, hAR.isolated_A, hAR.isolated_R,
    fun k => (eR k).symm, fun k => (eA k).symm, iA, pR, d, h1, h2, h3,
    fun k => by rw [LinearEquiv.symm_symm]⟩
  · exact ConleyCheck.exact_equiv_middle (eA k)
      (ConleyCheck.exact_comp_equiv_left (eR k).symm (h3 k))
  · exact ConleyCheck.exact_equiv_comp_right (eR k)
      (ConleyCheck.exact_comp_equiv_left (eA (k + 1)).symm (h1 (k + 1)))
  · exact ConleyCheck.exact_equiv_comp_right (eA k)
      (ConleyCheck.exact_equiv_middle (eR k) (h2 k))
  · intro y
    obtain ⟨x, hx⟩ := ((h1 0) y).1 (Subsingleton.elim _ _)
    exact ⟨eA 0 x, by simp [hx]⟩
  · have hdk : d k ≠ 0 := fun h0 => hΨ (by
      show (eA k).toLinearMap ∘ₗ d k ∘ₗ (eR k).symm.toLinearMap = 0
      rw [h0, LinearMap.zero_comp, LinearMap.comp_zero])
    obtain ⟨q, hq, hqA, hqR, -, -⟩ := hd k hdk
    have ht : tent q.2 = 1 - 2 * q.2 := tent_of_mem hq.2.1 hq.2.2
    have hτ : tent q.2 ∈ Ioo (-1 : ℝ) 1 := by
      constructor
      · by_contra hle
        refine hqR ?_
        rw [← snat_inter_bot]
        exact ⟨hq, show tent q.2 = -1 by rw [ht] at hle ⊢; linarith [hq.2.2]⟩
      · by_contra hle
        refine hqA ?_
        rw [← snat_inter_top]
        exact ⟨hq, show tent q.2 = 1 by rw [ht] at hle ⊢; linarith [hq.2.1]⟩
    have hARs := (hΦ.isHeight hθ).isAttractorRepellerPair hS
    exact ⟨dblQ q, hq.1, hτ,
      hARs.connecting _ hq.1 (fun h => hτ.2.ne h.2) (fun h => hτ.1.ne' h.2)⟩

/-- Theorem `thm:transport`(i): over a field, `CH_{k+1}(S♮) ≅ coker Ψ_{k+1} ⊕ ker Ψ_k` and
`CH_0(S♮) ≅ coker Ψ_0`. -/
theorem transport_split (K : Type u) [Field K] {S : Set (X × Tau)}
    (hS : IsIsolatedInvariantSet Φ S) :
    ∃ (hSn : IsIsolatedInvariantSet (dblΦ hΦ hθ) (snat S))
      (hKp : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ)) {x | (x, Tau.top) ∈ S})
      (hKm : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ)) {x | (x, Tau.bot) ∈ S})
      (Ψ : ∀ k, homologyIndex K _ hKm k →ₗ[K] homologyIndex K _ hKp k),
      (∀ k, Nonempty (homologyIndex K _ hSn (k + 1) ≃ₗ[K]
        (homologyIndex K _ hKp (k + 1) ⧸ LinearMap.range (Ψ (k + 1))) × LinearMap.ker (Ψ k))) ∧
      Nonempty (homologyIndex K _ hSn 0 ≃ₗ[K] homologyIndex K _ hKp 0 ⧸ LinearMap.range (Ψ 0)) := by
  obtain ⟨hSn, hKp, hKm, Ψ, i, p, h1, h2, h3, h0, -⟩ := transport hΦ hθ K hS
  exact ⟨hSn, hKp, hKm, Ψ, fun k => ConleyCheck.exact_split (h1 (k + 1)) (h2 k) (h3 k),
    ConleyCheck.exact_coker (h1 0) h0⟩

/-- Theorem `thm:transport`(iii), over a field: if `CH_*(K_±)` are finite-dimensional, then
`rk Ψ_0 = dim CH_0(K_+) - dim CH_0(S♮)` and
`rk Ψ_{k+1} = dim CH_{k+1}(K_+) + dim CH_k(K_-) - rk Ψ_k - dim CH_{k+1}(S♮)`. So the ranks of `Ψ`,
and hence `Ψ` up to isomorphism, are determined by the homology indices of `K_-`, `K_+` and `S♮`
(`ConleyCheck.les_finrank_range_eq`), which are invariant under continuation. -/
theorem transport_finrank (K : Type u) [Field K] {S : Set (X × Tau)}
    (hS : IsIsolatedInvariantSet Φ S) (hSn : IsIsolatedInvariantSet (dblΦ hΦ hθ) (snat S))
    (hKp : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ)) {x | (x, Tau.top) ∈ S})
    (hKm : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ)) {x | (x, Tau.bot) ∈ S})
    [∀ k, FiniteDimensional K (homologyIndex K _ hKp k)]
    [∀ k, FiniteDimensional K (homologyIndex K _ hKm k)] :
    ∃ Ψ : ∀ k, homologyIndex K _ hKm k →ₗ[K] homologyIndex K _ hKp k,
      Module.finrank K (homologyIndex K _ hSn 0) + Module.finrank K (LinearMap.range (Ψ 0)) =
        Module.finrank K (homologyIndex K _ hKp 0) ∧
      ∀ k, Module.finrank K (homologyIndex K _ hSn (k + 1)) +
        Module.finrank K (LinearMap.range (Ψ (k + 1))) +
        Module.finrank K (LinearMap.range (Ψ k)) =
          Module.finrank K (homologyIndex K _ hKp (k + 1)) +
            Module.finrank K (homologyIndex K _ hKm k) := by
  obtain ⟨hSn', hKp', hKm', Ψ, i, p, h1, h2, h3, h0, -⟩ := transport hΦ hθ K hS
  exact ⟨Ψ, ConleyCheck.les_finrank h1 h2 h3 h0⟩

end Double

end ConleyCheck.Conley
