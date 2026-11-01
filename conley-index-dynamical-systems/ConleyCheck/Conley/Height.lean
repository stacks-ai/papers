import ConleyCheck.Conley.Regular

/-!
# Height functions and the attractor–repeller pair of the extended phase space

A height function `τ : α → [-1, 1]` for a flow is constant along orbits in the levels `τ = ±1`
and strictly increasing along all other orbits. This is the `τ`-coordinate of the compactified
extended phase space `X × [-1, 1]` (equation `eq:slab`), and the `θ`-coordinate of the one-sided
extension after the change of variable `τ = cos θ`.

For every isolated invariant set `S`, the parts of `S` in the two levels form an attractor–repeller
pair (`isAttractorRepellerPair_of_height`). This is the first statement of Theorem `thm:slab` and
of Lemma `lem:isolation`(c).
-/

namespace ConleyCheck.Conley

open Set Filter Topology

variable {α : Type*} [TopologicalSpace α] {ϕ : Flow ℝ α}

/-- A height function: `τ` takes values in `[-1, 1]`, is constant along orbits through the levels
`±1`, and strictly increases along every other orbit. -/
structure IsHeight (ϕ : Flow ℝ α) (τ : α → ℝ) : Prop where
  continuous : Continuous τ
  mem : ∀ x, τ x ∈ Icc (-1 : ℝ) 1
  fix : ∀ x, (τ x = 1 ∨ τ x = -1) → ∀ t, τ (ϕ t x) = τ x
  strict : ∀ x, -1 < τ x → τ x < 1 → ∀ t, 0 < t → τ x < τ (ϕ t x)

namespace IsHeight

variable {τ : α → ℝ} (hτ : IsHeight ϕ τ)
include hτ

theorem le_flow (x : α) {t : ℝ} (ht : 0 ≤ t) : τ x ≤ τ (ϕ t x) := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [Flow.map_zero_apply]
  by_cases h1 : τ x = 1
  · rw [hτ.fix x (Or.inl h1)]
  by_cases h2 : τ x = -1
  · rw [hτ.fix x (Or.inr h2)]
  exact (hτ.strict x (lt_of_le_of_ne (hτ.mem x).1 (Ne.symm h2))
    (lt_of_le_of_ne (hτ.mem x).2 h1) t ht).le

theorem monotone_flow (x : α) {s t : ℝ} (hst : s ≤ t) : τ (ϕ s x) ≤ τ (ϕ t x) := by
  have e : ϕ t x = ϕ (t - s) (ϕ s x) := by rw [← Flow.map_add, sub_add_cancel]
  rw [e]
  exact hτ.le_flow _ (sub_nonneg.2 hst)

theorem le_of_mem_omegaLim {x z : α} (hz : z ∈ omegaLim ϕ x) (u : ℝ) : τ (ϕ u x) ≤ τ z := by
  have hcl := omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ.toFun) (s := {x})
    (Ici_mem_atTop u) hz
  rw [image2_singleton_right] at hcl
  refine closure_minimal ?_ (isClosed_le continuous_const hτ.continuous) hcl
  rintro _ ⟨t, ht, rfl⟩
  exact hτ.monotone_flow x ht

theorem ge_of_mem_alphaLim {x z : α} (hz : z ∈ alphaLim ϕ x) (u : ℝ) : τ z ≤ τ (ϕ u x) := by
  have hcl := omegaLimit_subset_closure_image2 (f := atBot) (ϕ := ϕ.toFun) (s := {x})
    (Iic_mem_atBot u) hz
  rw [image2_singleton_right] at hcl
  refine closure_minimal ?_ (isClosed_le hτ.continuous continuous_const) hcl
  rintro _ ⟨t, ht, rfl⟩
  exact hτ.monotone_flow x ht

/-- A point of the ω-limit set of a point above the bottom level lies in the top level. -/
theorem omegaLim_top {x z : α} (hx : -1 < τ x) (hz : z ∈ omegaLim ϕ x) : τ z = 1 := by
  by_contra h1
  have hz0 : τ x ≤ τ z := by simpa using hτ.le_of_mem_omegaLim hz 0
  have hz' : ϕ 1 z ∈ omegaLim ϕ x :=
    Flow.isInvariant_omegaLimit atTop ϕ {x} (fun r => tendsto_atTop_add_const_left _ r tendsto_id)
      1 hz
  have hlt := hτ.strict z (hx.trans_le hz0) (lt_of_le_of_ne (hτ.mem z).2 h1) 1 one_pos
  have hcl := omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ.toFun) (s := {x})
    (Ici_mem_atTop 0) hz'
  rw [image2_singleton_right] at hcl
  have hle : τ (ϕ 1 z) ≤ τ z := by
    refine closure_minimal ?_ (isClosed_le hτ.continuous continuous_const) hcl
    rintro _ ⟨t, -, rfl⟩
    exact hτ.le_of_mem_omegaLim hz t
  linarith

/-- A point of the α-limit set of a point below the top level lies in the bottom level. -/
theorem alphaLim_bot {x z : α} (hx : τ x < 1) (hz : z ∈ alphaLim ϕ x) : τ z = -1 := by
  by_contra h1
  have hz0 : τ z ≤ τ x := by simpa using hτ.ge_of_mem_alphaLim hz 0
  have hz' : ϕ (-1) z ∈ alphaLim ϕ x :=
    Flow.isInvariant_omegaLimit atBot ϕ {x} (fun r => tendsto_atBot_add_const_left _ r tendsto_id)
      (-1) hz
  have hz'' : ϕ 1 (ϕ (-1) z) = z := by rw [← Flow.map_add]; norm_num
  have hlow : -1 < τ (ϕ (-1) z) := by
    refine lt_of_le_of_ne (hτ.mem _).1 fun h => h1 ?_
    rw [← hz'', hτ.fix _ (Or.inr h.symm), ← h]
  have hhigh : τ (ϕ (-1) z) < 1 := by
    refine lt_of_le_of_ne (hτ.mem _).2 fun h => ?_
    have := hτ.fix _ (Or.inl h) 1
    rw [hz'', h] at this
    linarith
  have hlt := hτ.strict _ hlow hhigh 1 one_pos
  rw [hz''] at hlt
  have hcl := omegaLimit_subset_closure_image2 (f := atBot) (ϕ := ϕ.toFun) (s := {x})
    (Iic_mem_atBot 0) hz'
  rw [image2_singleton_right] at hcl
  have hle : τ z ≤ τ (ϕ (-1) z) := by
    refine closure_minimal ?_ (isClosed_le continuous_const hτ.continuous) hcl
    rintro _ ⟨t, -, rfl⟩
    exact hτ.ge_of_mem_alphaLim hz t
  linarith

variable [T2Space α]

/-- A full orbit in a compact invariant set that starts strictly between the levels accumulates
on both levels. -/
theorem exists_levels {S : Set α} (hS : IsCompact S) (hSi : IsInvariantSet ϕ S) {x : α}
    (hx : x ∈ S) (h1 : -1 < τ x) (h2 : τ x < 1) :
    (∃ z ∈ closure ((fun t => ϕ t x) '' univ), τ z = -1) ∧
      ∃ z ∈ closure ((fun t => ϕ t x) '' univ), τ z = 1 := by
  obtain ⟨a, ha⟩ := alphaLim_nonempty hS hSi hx
  obtain ⟨w, hw⟩ := omegaLim_nonempty hS hSi hx
  refine ⟨⟨a, closure_mono (image_mono (subset_univ _)) (mem_closure_of_mem_alphaLim ha),
    hτ.alphaLim_bot h2 ha⟩, ⟨w, closure_mono (image_mono (subset_univ _))
    (mem_closure_of_mem_omegaLim hw), hτ.omegaLim_top h1 hw⟩⟩

theorem isIsolatingNbhd_top {N : Set α} (hN : IsIsolatingNbhd ϕ N) :
    IsIsolatingNbhd ϕ (N ∩ τ ⁻¹' Icc 0 1) ∧ Inv ϕ (N ∩ τ ⁻¹' Icc 0 1) = Inv ϕ N ∩ τ ⁻¹' {1} := by
  have hS := isCompact_Inv (ϕ := ϕ) hN.1
  have heq : Inv ϕ (N ∩ τ ⁻¹' Icc 0 1) = Inv ϕ N ∩ τ ⁻¹' {1} := by
    ext x
    refine ⟨fun hx => ⟨Inv_mono inter_subset_left hx, ?_⟩, fun ⟨hx, h1⟩ t => ⟨hx t, ?_⟩⟩
    · have hxS : x ∈ Inv ϕ N := Inv_mono inter_subset_left hx
      by_contra hne
      have h2 : τ x < 1 := lt_of_le_of_ne (hτ.mem x).2 hne
      have h0 : 0 ≤ τ x := by simpa using ((hx 0).2).1
      obtain ⟨⟨z, hz, hz1⟩, -⟩ := hτ.exists_levels hS (isInvariantSet_Inv N) hxS (by linarith) h2
      have : 0 ≤ τ z := by
        refine closure_minimal ?_ (isClosed_le continuous_const hτ.continuous) hz
        rintro _ ⟨t, -, rfl⟩
        exact (hx t).2.1
      linarith
    · show τ (ϕ t x) ∈ Icc 0 1
      rw [hτ.fix x (Or.inl h1), h1]
      exact ⟨zero_le_one, le_rfl⟩
  refine ⟨⟨hN.1.inter_right (isClosed_Icc.preimage hτ.continuous), ?_⟩, heq⟩
  rw [heq]
  rintro x ⟨hx, h1⟩
  have hopen : IsOpen (interior N ∩ τ ⁻¹' Ioi 0) := isOpen_interior.inter
    (isOpen_Ioi.preimage hτ.continuous)
  refine interior_maximal (t := interior N ∩ τ ⁻¹' Ioi 0) ?_ hopen ⟨hN.2 hx, ?_⟩
  · rintro y ⟨hy, hy0⟩
    exact ⟨interior_subset hy, le_of_lt hy0, (hτ.mem y).2⟩
  · show (0 : ℝ) < τ x
    rw [show τ x = 1 from h1]
    exact one_pos

theorem isIsolatingNbhd_bot {N : Set α} (hN : IsIsolatingNbhd ϕ N) :
    IsIsolatingNbhd ϕ (N ∩ τ ⁻¹' Icc (-1) 0) ∧
      Inv ϕ (N ∩ τ ⁻¹' Icc (-1) 0) = Inv ϕ N ∩ τ ⁻¹' {-1} := by
  have hS := isCompact_Inv (ϕ := ϕ) hN.1
  have heq : Inv ϕ (N ∩ τ ⁻¹' Icc (-1) 0) = Inv ϕ N ∩ τ ⁻¹' {-1} := by
    ext x
    refine ⟨fun hx => ⟨Inv_mono inter_subset_left hx, ?_⟩, fun ⟨hx, h1⟩ t => ⟨hx t, ?_⟩⟩
    · have hxS : x ∈ Inv ϕ N := Inv_mono inter_subset_left hx
      by_contra hne
      have h2 : -1 < τ x := lt_of_le_of_ne (hτ.mem x).1 (Ne.symm hne)
      have h0 : τ x ≤ 0 := by simpa using ((hx 0).2).2
      obtain ⟨-, ⟨z, hz, hz1⟩⟩ := hτ.exists_levels hS (isInvariantSet_Inv N) hxS h2 (by linarith)
      have : τ z ≤ 0 := by
        refine closure_minimal ?_ (isClosed_le hτ.continuous continuous_const) hz
        rintro _ ⟨t, -, rfl⟩
        exact (hx t).2.2
      linarith
    · show τ (ϕ t x) ∈ Icc (-1) 0
      rw [hτ.fix x (Or.inr h1), h1]
      norm_num
  refine ⟨⟨hN.1.inter_right (isClosed_Icc.preimage hτ.continuous), ?_⟩, heq⟩
  rw [heq]
  rintro x ⟨hx, h1⟩
  have hopen : IsOpen (interior N ∩ τ ⁻¹' Iio 0) := isOpen_interior.inter
    (isOpen_Iio.preimage hτ.continuous)
  refine interior_maximal (t := interior N ∩ τ ⁻¹' Iio 0) ?_ hopen ⟨hN.2 hx, ?_⟩
  · rintro y ⟨hy, hy0⟩
    exact ⟨interior_subset hy, (hτ.mem y).1, le_of_lt hy0⟩
  · show τ x < (0 : ℝ)
    rw [show τ x = -1 from h1]
    norm_num

/-- The parts of an isolated invariant set in the top and bottom levels form an attractor–repeller
pair. -/
theorem isAttractorRepellerPair {S : Set α} (hS : IsIsolatedInvariantSet ϕ S) :
    IsAttractorRepellerPair ϕ S (S ∩ τ ⁻¹' {1}) (S ∩ τ ⁻¹' {-1}) := by
  obtain ⟨N, hN, rfl⟩ := hS
  refine
    { isolated := ⟨N, hN, rfl⟩
      isolated_A := ⟨_, (hτ.isIsolatingNbhd_top hN).1, (hτ.isIsolatingNbhd_top hN).2⟩
      isolated_R := ⟨_, (hτ.isIsolatingNbhd_bot hN).1, (hτ.isIsolatingNbhd_bot hN).2⟩
      subset_A := inter_subset_left
      subset_R := inter_subset_left
      disjoint := disjoint_left.2 fun x h1 h2 => by
        have e1 : τ x = 1 := h1.2
        have e2 : τ x = -1 := h2.2
        linarith
      connecting := fun x hx hA hR => ?_ }
  have h1 : τ x ≠ 1 := fun h => hA ⟨hx, h⟩
  have h2 : τ x ≠ -1 := fun h => hR ⟨hx, h⟩
  have hlow : -1 < τ x := lt_of_le_of_ne (hτ.mem x).1 (Ne.symm h2)
  have hhigh : τ x < 1 := lt_of_le_of_ne (hτ.mem x).2 h1
  have hScl := (isCompact_Inv (ϕ := ϕ) hN.1).isClosed
  have hSi := isInvariantSet_Inv (ϕ := ϕ) N
  have hcl : closure ((fun t => ϕ.toFun t x) '' Ici 0) ⊆ Inv ϕ N := closure_minimal
    (by rintro _ ⟨t, -, rfl⟩; exact hSi t x hx) hScl
  have hcl' : closure ((fun t => ϕ.toFun t x) '' Iic 0) ⊆ Inv ϕ N := closure_minimal
    (by rintro _ ⟨t, -, rfl⟩; exact hSi t x hx) hScl
  exact ⟨fun z hz => ⟨hcl (mem_closure_of_mem_omegaLim hz), hτ.omegaLim_top hlow hz⟩,
    fun z hz => ⟨hcl' (mem_closure_of_mem_alphaLim hz), hτ.alphaLim_bot hhigh hz⟩⟩

end IsHeight

end ConleyCheck.Conley
