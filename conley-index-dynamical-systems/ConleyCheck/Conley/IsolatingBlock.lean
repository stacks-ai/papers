import ConleyCheck.Conley.Index

/-!
# Isolating blocks

A compact set `N` with a closed set `L ⊆ N` of strict exit points, all other boundary points being
strict entrance points, is an isolating neighborhood, and `(N, L)` is an index pair of `Inv(N)`.
-/

namespace ConleyCheck.Conley

open Set Filter Topology

variable {α : Type*} [TopologicalSpace α] {ϕ : Flow ℝ α}

/-- `N` is an isolating block with exit set `L`: points of `L` leave `N` immediately, and every
other boundary point of `N` enters `N` immediately and is outside `N` just before. -/
structure IsBlock (ϕ : Flow ℝ α) (N L : Set α) : Prop where
  isCompact : IsCompact N
  isClosed_L : IsClosed L
  subset : L ⊆ N
  exit : ∀ x ∈ L, ∃ ε > 0, ∀ t ∈ Ioo 0 ε, ϕ t x ∉ N
  entrance : ∀ x ∈ N, x ∉ interior N → x ∉ L → ∃ ε > 0,
    (∀ t ∈ Ioo (-ε) 0, ϕ t x ∉ N) ∧ ∀ t ∈ Ioo 0 ε, ϕ t x ∈ N

namespace IsBlock

variable {N L : Set α} (h : IsBlock ϕ N L)
include h

theorem Inv_subset_interior_diff : Inv ϕ N ⊆ interior N \ L := by
  intro x hx
  have hxN : x ∈ N := Inv_subset N hx
  refine ⟨?_, fun hL => ?_⟩
  · by_contra hint
    by_cases hL : x ∈ L
    · obtain ⟨ε, hε, hout⟩ := h.exit x hL
      exact hout (ε / 2) ⟨by linarith, by linarith⟩ (hx _)
    · obtain ⟨ε, hε, hout, -⟩ := h.entrance x hxN hint hL
      exact hout (-(ε / 2)) ⟨by linarith, by linarith⟩ (hx _)
  · obtain ⟨ε, hε, hout⟩ := h.exit x hL
    exact hout (ε / 2) ⟨by linarith, by linarith⟩ (hx _)

theorem interior_diff_subset : interior N \ L ⊆ interior (N \ L) :=
  interior_maximal (sdiff_subset_sdiff_left interior_subset) (isOpen_interior.sdiff h.isClosed_L)

theorem isIsolatingNbhd : IsIsolatingNbhd ϕ N :=
  ⟨h.isCompact, fun _ hx => (h.Inv_subset_interior_diff hx).1⟩

variable [T2Space α]

theorem isIndexPair : IsIndexPair ϕ (Inv ϕ N) N L := by
  have hNc : IsClosed N := h.isCompact.isClosed
  have hcl : closure (N \ L) ⊆ N := closure_minimal sdiff_subset hNc
  have hInv : Inv ϕ (closure (N \ L)) = Inv ϕ N := by
    refine Subset.antisymm (fun x hx t => hcl (hx t)) fun x hx t => subset_closure ?_
    have hxt : ϕ t x ∈ Inv ϕ N := fun s => by rw [← Flow.map_add]; exact hx _
    exact sdiff_subset_sdiff_left interior_subset (h.Inv_subset_interior_diff hxt)
  refine
    { isCompact_N := h.isCompact
      isCompact_L := h.isCompact.of_isClosed_subset h.isClosed_L h.subset
      subset := h.subset
      isolating := ⟨h.isCompact.of_isClosed_subset isClosed_closure hcl, ?_⟩
      inv_eq := hInv
      nhds := fun x hx => h.interior_diff_subset (h.Inv_subset_interior_diff hx)
      posInv := ?_
      exit := ?_ }
  · rw [hInv]
    exact fun x hx => interior_mono subset_closure
      (h.interior_diff_subset (h.Inv_subset_interior_diff hx))
  · intro x hx t ht hN
    rcases ht.eq_or_lt with rfl | ht
    · rwa [Flow.map_zero_apply]
    obtain ⟨ε, hε, hout⟩ := h.exit x hx
    exact absurd (hN (min (ε / 2) t) ⟨le_min (by linarith) ht.le, min_le_right _ _⟩)
      (hout _ ⟨lt_min (by linarith) ht, (min_le_left _ _).trans_lt (by linarith)⟩)
  · intro x hx t ht hout
    have hc : Continuous fun r => ϕ r x := ϕ.continuous continuous_id continuous_const
    set C := {s | s ∈ Icc 0 t ∧ ϕ s x ∉ N}
    have hCne : C.Nonempty := ⟨t, ⟨ht, le_rfl⟩, hout⟩
    have hCbdd : BddBelow C := ⟨0, fun s hs => hs.1.1⟩
    set s₀ := sInf C
    have hs₀0 : 0 ≤ s₀ := le_csInf hCne fun s hs => hs.1.1
    have hs₀t : s₀ ≤ t := csInf_le hCbdd ⟨⟨ht, le_rfl⟩, hout⟩
    have hbefore : ∀ r ∈ Icc 0 t, r < s₀ → ϕ r x ∈ N := fun r hr hrs => by
      by_contra hn
      exact absurd (csInf_le hCbdd ⟨hr, hn⟩) (not_le.2 hrs)
    have hs₀N : ϕ s₀ x ∈ N := by
      rcases hs₀0.eq_or_lt with h0 | h0
      · rw [← h0, Flow.map_zero_apply]; exact hx
      · refine hNc.mem_of_tendsto
          (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds : Tendsto _ (𝓝[<] s₀) _) ?_
        filter_upwards [Ioo_mem_nhdsLT h0] with r hr
        exact hbefore r ⟨hr.1.le, hr.2.le.trans hs₀t⟩ hr.2
    have hafter : ∀ ε > 0, ∃ c ∈ C, s₀ < c ∧ c < s₀ + ε := fun ε hε => by
      obtain ⟨c, hcC, hcl⟩ := exists_lt_of_csInf_lt hCne (by linarith : s₀ < s₀ + ε)
      refine ⟨c, hcC, lt_of_le_of_ne (csInf_le hCbdd hcC) ?_, hcl⟩
      rintro rfl
      exact hcC.2 hs₀N
    refine ⟨s₀, ⟨hs₀0, hs₀t⟩, fun r hr => ?_, ?_⟩
    · rcases hr.2.lt_or_eq with hr' | hr'
      · exact hbefore r ⟨hr.1, hr.2.trans hs₀t⟩ hr'
      · rw [hr']; exact hs₀N
    · by_contra hL
      have hint : ϕ s₀ x ∉ interior N := fun hi => by
        have hU : (fun r => ϕ r x) ⁻¹' interior N ∈ 𝓝 s₀ :=
          hc.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hi)
        obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
        obtain ⟨c, hcC, hc1, hc2⟩ := hafter δ hδ
        refine hcC.2 (interior_subset (hball ?_))
        rw [Real.ball_eq_Ioo]
        exact ⟨by linarith, hc2⟩
      obtain ⟨ε, hε, -, hfwd⟩ := h.entrance _ hs₀N hint hL
      obtain ⟨c, hcC, hc1, hc2⟩ := hafter ε hε
      have := hfwd (c - s₀) ⟨by linarith, by linarith⟩
      rw [← Flow.map_add, sub_add_cancel] at this
      exact hcC.2 this

end IsBlock

end ConleyCheck.Conley
