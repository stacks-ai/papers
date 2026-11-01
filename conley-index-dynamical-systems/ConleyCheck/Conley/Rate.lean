import ConleyCheck.Conley.Double
import ConleyCheck.Conley.IsolatingBlock
import ConleyCheck.Conley.Deform

/-!
# Common strict entrance/exit blocks and rate independence

Theorem `thm:rate`. A compact `N ⊆ X` with a closed exit set `L_out ⊆ N` that is an isolating block
for every frozen system, with the same entrance/exit decomposition for every `τ` (a common block,
`IsUniformBlock`), gives

* (i) `S = Inv(N × [-1, 1])` is isolated, `(N, L_out)` is an index pair of `K_±` for `f_±`, and
  `CH_*(K_±; f_±) ≅ H̃_*(N/L_out)`, which is `H_*(N, L_out)` when `L_out` has a collar
  (`rate_index`, `rate_index_collared`);
* (ii) `CH_*(S♮) = 0` and `Ψ` is an isomorphism (`rate_transport`);
* (iii) if `H̃_*(N/L_out) ≠ 0`, there is an orbit of `S` with `-1 < τ < 1`, running from
  `K_- × {-1}` to `K_+ × {1}` (`rate_connection`).

The block condition is stated for the flow, i.e. strict exit through `L_out` and strict entrance
through the rest of the boundary of `N`, for every `τ`.

For `L_out = ∅` the block is forward invariant for the non-autonomous system, so no solution that
enters `N` leaves it, at any rate (`IsUniformBlock.forward_of_exit_empty`, the discussion after
Theorem `thm:rate`).
-/

namespace ConleyCheck.Conley

open Set Function Filter Topology
open scoped unitInterval

universe u

/-- A continuous path at `0` stays in an open set for short times. -/
theorem exists_Ioo_of_continuousAt {Y : Type*} [TopologicalSpace Y] {f : ℝ → Y}
    (hf : ContinuousAt f 0) {U : Set Y} (hU : IsOpen U) (h0 : f 0 ∈ U) :
    ∃ ε > 0, ∀ t ∈ Ioo (-ε) ε, f t ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hf.preimage_mem_nhds (hU.mem_nhds h0))
  refine ⟨ε, hε, fun t ht => hball ?_⟩
  rw [Real.ball_eq_Ioo]
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

section Base

variable {θ : Flow ℝ Tau} (hθ : IsHeight θ (fun b => (b : ℝ)))

/-- On the lower sheet near the IR point, the lifted base flow moves backward to the left. -/
theorem dblFlow_lt_of_neg {u : Dbl} (h1 : -1 < (u : ℝ)) (h0 : (u : ℝ) < 0) {t : ℝ} (ht : t < 0) :
    (dblFlow hθ t u : ℝ) < u := by
  have hτ : tent u = 1 + 2 * u := tent_of_le_zero h0.le
  have hb1 : (θ t (tentT u) : ℝ) < 1 :=
    base_lt_one hθ (show tent u < 1 by linarith) t
  have hb2 : -1 < (θ t (tentT u) : ℝ) :=
    neg_one_lt_base hθ (show -1 < tent u by linarith) t
  have h3 : (θ t (tentT u) : ℝ) < (θ (-t) (θ t (tentT u)) : ℝ) :=
    hθ.strict _ hb2 hb1 (-t) (by linarith)
  rw [base_cancel hθ] at h3
  have h4 : (θ t (tentT u) : ℝ) < tent u := h3
  rw [dblFlow_le0 hθ h0.le]
  unfold br₀
  linarith

/-- The arc `[-1/2, 3/2]` of the double. -/
def blockJ : Set Dbl := {u | (u : ℝ) ∈ Icc (-1 / 2 : ℝ) (3 / 2)}

/-- Its exit point `3/2`. -/
def blockE : Set Dbl := {u | (u : ℝ) = 3 / 2}

theorem blockH_mem {s r : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (-1 / 2 : ℝ) (3 / 2)) :
    r + s * (3 / 2 - r) ∈ Icc (-1 / 2 : ℝ) (3 / 2) := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hr0, hr1⟩ := hr
  constructor <;> nlinarith

/-- The deformation `u ↦ u + s (3/2 - u)` of `[-1/2, 3/2]` onto its exit point. -/
noncomputable def blockH : C(I × blockJ, blockJ) where
  toFun q :=
    have h := blockH_mem q.1.2 q.2.2
    ⟨⟨((q.2 : Dbl) : ℝ) + (q.1 : ℝ) * (3 / 2 - ((q.2 : Dbl) : ℝ)), by linarith [h.1],
      by linarith [h.2]⟩, h⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    have hb : Continuous fun q : I × blockJ => ((q.2 : Dbl) : ℝ) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    exact hb.add ((continuous_subtype_val.comp continuous_fst).mul (continuous_const.sub hb))

end Base

section Rate

variable {X : Type u} [TopologicalSpace X] {Φ : Flow ℝ (X × Tau)} {θ : Flow ℝ Tau}
  (hΦ : IsSkew Φ θ) (hθ : IsHeight θ (fun b => (b : ℝ)))

/-- `N` is a common strict entrance/exit block with exit set `L_out` for the frozen systems: for
every `τ`, points of `L_out` leave `N` immediately, and the other boundary points of `N` enter `N`
immediately and are outside `N` just before. -/
structure IsUniformBlock (Φ : Flow ℝ (X × Tau)) (N Lo : Set X) : Prop where
  isCompact : IsCompact N
  isClosed_out : IsClosed Lo
  out_subset : Lo ⊆ N
  exit : ∀ x ∈ Lo, ∀ τ, ∃ ε > 0, ∀ t ∈ Ioo 0 ε, (Φ t (x, τ)).1 ∉ N
  entrance : ∀ x ∈ N, x ∉ interior N → x ∉ Lo → ∀ τ, ∃ ε > 0,
    (∀ t ∈ Ioo (-ε) 0, (Φ t (x, τ)).1 ∉ N) ∧ ∀ t ∈ Ioo 0 ε, (Φ t (x, τ)).1 ∈ N

variable {N Lo : Set X}

/-- A common block is a block for the fiber flow over a fixed point of the base. -/
theorem IsUniformBlock.fiber (hB : IsUniformBlock Φ N Lo) (b₀ : Tau) (hfix : ∀ t, θ t b₀ = b₀) :
    IsBlock (fiberFlow hΦ b₀ hfix) N Lo :=
  ⟨hB.isCompact, hB.isClosed_out, hB.out_subset, fun x hx => hB.exit x hx b₀,
    fun x hx hi hL => hB.entrance x hx hi hL b₀⟩

/-- A common block gives the block `(N × [-1, 1], L_out × [-1, 1])` of the slab. -/
theorem IsUniformBlock.slab (hB : IsUniformBlock Φ N Lo) :
    IsBlock Φ (N ×ˢ univ) (Lo ×ˢ univ) where
  isCompact := hB.isCompact.prod isCompact_univ
  isClosed_L := hB.isClosed_out.prod isClosed_univ
  subset := prod_mono hB.out_subset subset_rfl
  exit p hp := by
    obtain ⟨ε, hε, h⟩ := hB.exit p.1 hp.1 p.2
    exact ⟨ε, hε, fun t ht hN => h t ht hN.1⟩
  entrance p hp hi hL := by
    rw [interior_prod_eq, interior_univ] at hi
    obtain ⟨ε, hε, h1, h2⟩ := hB.entrance p.1 hp.1 (fun h => hi ⟨h, mem_univ _⟩)
      (fun h => hL ⟨h, mem_univ _⟩) p.2
    exact ⟨ε, hε, fun t ht hN => h1 t ht hN.1, fun t ht => ⟨h2 t ht, mem_univ _⟩⟩

theorem Inv_fiber_block (b₀ : Tau) (hfix : ∀ t, θ t b₀ = b₀) :
    Inv (fiberFlow hΦ b₀ hfix) N = {x | (x, b₀) ∈ Inv Φ (N ×ˢ univ)} := by
  ext x
  exact forall_congr' fun t => ⟨fun h => ⟨h, mem_univ _⟩, fun h => h.1⟩

variable [T2Space X]

/-- A common block with `L_out = ∅` is forward invariant for the non-autonomous system: an orbit
that starts in `N` stays in `N` for all `t ≥ 0`, at every rate. This excludes escape from `N`, but
not motion between Morse sets inside `N`. -/
theorem IsUniformBlock.forward_of_exit_empty (hB : IsUniformBlock Φ N ∅) {p : X × Tau}
    (hp : p.1 ∈ N) {t : ℝ} (ht : 0 ≤ t) : (Φ t p).1 ∈ N := by
  by_contra h
  obtain ⟨s, -, -, hs⟩ :=
    (IsUniformBlock.slab hB).isIndexPair.exit p ⟨hp, mem_univ _⟩ t ht fun hN => h hN.1
  simp at hs

/-- A common block gives the block `(N × [-1/2, 3/2], L_out × [-1/2, 3/2] ∪ N × {3/2})` of the
double. -/
theorem IsUniformBlock.dbl (hB : IsUniformBlock Φ N Lo) :
    IsBlock (dblΦ hΦ hθ) (N ×ˢ blockJ) (Lo ×ˢ blockJ ∪ N ×ˢ blockE) := by
  have hJc : IsClosed blockJ := isClosed_Icc.preimage continuous_subtype_val
  have hEc : IsClosed blockE := isClosed_eq continuous_subtype_val continuous_const
  have hEJ : blockE ⊆ blockJ := fun u (hu : (u : ℝ) = 3 / 2) =>
    show (u : ℝ) ∈ Icc (-1 / 2 : ℝ) (3 / 2) by rw [hu]; norm_num
  refine ⟨hB.isCompact.prod hJc.isCompact,
    (hB.isClosed_out.prod hJc).union (hB.isCompact.isClosed.prod hEc),
    union_subset (prod_mono hB.out_subset subset_rfl) (prod_mono subset_rfl hEJ), ?_, ?_⟩
  · rintro ⟨x, u⟩ (⟨hx, -⟩ | ⟨-, hu⟩)
    · obtain ⟨ε, hε, h⟩ := hB.exit x hx (tentT u)
      exact ⟨ε, hε, fun t ht hN => h t ht hN.1⟩
    · refine ⟨1, one_pos, fun t ht hN => ?_⟩
      have hu' : (u : ℝ) = 3 / 2 := hu
      have h1 := lt_dblFlow_of_gt1 hθ (u := u) (by rw [hu']; norm_num) (by rw [hu']; norm_num) ht.1
      have h2 : (dblFlow hθ t u : ℝ) ≤ 3 / 2 := hN.2.2
      linarith
  · rintro ⟨x, u⟩ ⟨hx, hu⟩ hint hL
    have hu' : (u : ℝ) ∈ Icc (-1 / 2 : ℝ) (3 / 2) := hu
    have hxL : x ∉ Lo := fun h => hL (Or.inl ⟨h, hu⟩)
    have hu3 : (u : ℝ) < 3 / 2 := lt_of_le_of_ne hu'.2 fun h => hL (Or.inr ⟨hx, h⟩)
    obtain ⟨ε₁, hε₁, hfx⟩ : ∃ ε > 0, ∀ t ∈ Ioo 0 ε, (Φ t (x, tentT u)).1 ∈ N := by
      by_cases hxi : x ∈ interior N
      · obtain ⟨ε, hε, h⟩ := exists_Ioo_of_continuousAt (f := fun t => (Φ t (x, tentT u)).1)
          (continuous_fst.comp (Φ.continuous continuous_id continuous_const)).continuousAt
          isOpen_interior (by simpa using hxi)
        exact ⟨ε, hε, fun t ht => interior_subset (h t ⟨by linarith [ht.1], ht.2⟩)⟩
      · obtain ⟨ε, hε, -, h⟩ := hB.entrance x hx hxi hxL (tentT u)
        exact ⟨ε, hε, h⟩
    obtain ⟨ε₂, hε₂, hfu⟩ :
        ∃ ε > 0, ∀ t ∈ Ioo 0 ε, (dblFlow hθ t u : ℝ) ∈ Icc (-1 / 2 : ℝ) (3 / 2) := by
      by_cases h1 : (u : ℝ) ≤ 1
      · refine ⟨1, one_pos, fun t ht => ?_⟩
        by_cases h0 : (u : ℝ) ≤ 0
        · have a := dblFlow_mono_nonpos hθ h0 (s := 0) ht.1.le
          rw [Flow.map_zero_apply] at a
          have b := dblFlow_nonpos hθ h0 t
          exact ⟨by linarith [hu'.1], by linarith⟩
        · have a := dblFlow_mem_01 hθ (not_le.1 h0).le h1 t
          exact ⟨by linarith [a.1], by linarith [a.2]⟩
      · obtain ⟨ε, hε, h⟩ := exists_Ioo_of_continuousAt (f := fun t => (dblFlow hθ t u : ℝ))
          (continuous_dblFlow_time hθ u).continuousAt isOpen_Iio
          (show (dblFlow hθ 0 u : ℝ) ∈ Iio (3 / 2) by rw [Flow.map_zero_apply]; exact hu3)
        refine ⟨ε, hε, fun t ht => ⟨?_, (h t ⟨by linarith [ht.1], ht.2⟩).le⟩⟩
        have := one_le_dblFlow hθ (not_le.1 h1).le t
        linarith
    obtain ⟨ε₃, hε₃, hb⟩ :
        ∃ ε > 0, ∀ t ∈ Ioo (-ε) 0, dblΦ hΦ hθ t (x, u) ∉ N ×ˢ blockJ := by
      by_cases hxi : x ∈ interior N
      · have hu0 : (u : ℝ) = -1 / 2 := by
          by_contra hne
          apply hint
          have hO : IsOpen (interior N ×ˢ {v : Dbl | (v : ℝ) ∈ Ioo (-1 / 2 : ℝ) (3 / 2)}) :=
            isOpen_interior.prod (isOpen_Ioo.preimage continuous_subtype_val)
          have hmem : (x, u) ∈ interior N ×ˢ {v : Dbl | (v : ℝ) ∈ Ioo (-1 / 2 : ℝ) (3 / 2)} :=
            ⟨hxi, show (u : ℝ) ∈ Ioo (-1 / 2 : ℝ) (3 / 2) from
              ⟨lt_of_le_of_ne hu'.1 (Ne.symm hne), hu3⟩⟩
          have hsub : interior N ×ˢ {v : Dbl | (v : ℝ) ∈ Ioo (-1 / 2 : ℝ) (3 / 2)} ⊆
              N ×ˢ blockJ := Set.prod_mono interior_subset
            fun v (hv : (v : ℝ) ∈ Ioo (-1 / 2 : ℝ) (3 / 2)) => (Ioo_subset_Icc_self hv : _)
          exact interior_maximal hsub hO hmem
        refine ⟨1, one_pos, fun t ht hN => ?_⟩
        have h1 := dblFlow_lt_of_neg hθ (u := u) (by rw [hu0]; norm_num) (by rw [hu0]; norm_num)
          ht.2
        have h2 : -1 / 2 ≤ (dblFlow hθ t u : ℝ) := hN.2.1
        linarith
      · obtain ⟨ε, hε, h, -⟩ := hB.entrance x hx hxi hxL (tentT u)
        exact ⟨ε, hε, fun t ht hN => h t ht hN.1⟩
    refine ⟨min ε₃ (min ε₁ ε₂), lt_min hε₃ (lt_min hε₁ hε₂), fun t ht => hb t
      ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) ht.1, ht.2⟩, fun t ht =>
      ⟨hfx t ⟨ht.1, ht.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩,
        hfu t ⟨ht.1, ht.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩⟩⟩

variable [TopologicalSpace.MetrizableSpace X] (K : Type u) [Ring K]

omit [TopologicalSpace.MetrizableSpace X] in
/-- Theorem `thm:rate`(i). `S = Inv(N × [-1, 1])` is isolated, `(N, L_out)` is an index pair of
`K_±` for `f_±`, and `CH_*(K_±; f_±) ≅ H̃_*(N/L_out)`. -/
theorem rate_index (hB : IsUniformBlock Φ N Lo) :
    IsIsolatingNbhd Φ (N ×ˢ univ) ∧
      ∃ (hKp : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ))
          {x | (x, Tau.top) ∈ Inv Φ (N ×ˢ univ)})
        (hKm : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ))
          {x | (x, Tau.bot) ∈ Inv Φ (N ×ˢ univ)}),
        IsIndexPair (fiberFlow hΦ Tau.top (base_top hθ))
          {x | (x, Tau.top) ∈ Inv Φ (N ×ˢ univ)} N Lo ∧
        IsIndexPair (fiberFlow hΦ Tau.bot (base_bot hθ))
          {x | (x, Tau.bot) ∈ Inv Φ (N ×ˢ univ)} N Lo ∧
        ∀ n, Nonempty (homologyIndex K _ hKp n ≃ₗ[K]
            redH K (IndexSpace N Lo) (IndexSpace.pt N Lo) n) ∧
          Nonempty (homologyIndex K _ hKm n ≃ₗ[K]
            redH K (IndexSpace N Lo) (IndexSpace.pt N Lo) n) := by
  have hBT := IsUniformBlock.fiber hΦ hB Tau.top (base_top hθ)
  have hBB := IsUniformBlock.fiber hΦ hB Tau.bot (base_bot hθ)
  have hPT := hBT.isIndexPair
  have hPB := hBB.isIndexPair
  rw [Inv_fiber_block] at hPT hPB
  have hKp : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ))
      {x | (x, Tau.top) ∈ Inv Φ (N ×ˢ univ)} :=
    ⟨N, hBT.isIsolatingNbhd, Inv_fiber_block hΦ _ _⟩
  have hKm : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ))
      {x | (x, Tau.bot) ∈ Inv Φ (N ×ˢ univ)} :=
    ⟨N, hBB.isIsolatingNbhd, Inv_fiber_block hΦ _ _⟩
  exact ⟨(IsUniformBlock.slab hB).isIsolatingNbhd, hKp, hKm, hPT, hPB, fun n =>
    ⟨⟨(homologyIndexIso K hKp hPT n).some.toLinearEquiv⟩,
      ⟨(homologyIndexIso K hKm hPB n).some.toLinearEquiv⟩⟩⟩

omit [TopologicalSpace.MetrizableSpace X] in
/-- Theorem `thm:rate`(i) with a collar of `L_out`: `CH_*(K_±; f_±) ≅ H_*(N, L_out)`. -/
theorem rate_index_collared (hB : IsUniformBlock Φ N Lo) (hc : IsDeformCollared N Lo)
    (hKp : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ))
      {x | (x, Tau.top) ∈ Inv Φ (N ×ˢ univ)})
    (hKm : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ))
      {x | (x, Tau.bot) ∈ Inv Φ (N ×ˢ univ)}) (n : ℕ) :
    Nonempty (homologyIndex K _ hKp n ≃ₗ[K] singH K X (Int.ofNat n) N Lo) ∧
      Nonempty (homologyIndex K _ hKm n ≃ₗ[K] singH K X (Int.ofNat n) N Lo) := by
  obtain ⟨-, -, -, hPT, hPB, -⟩ := rate_index hΦ hθ K hB
  exact ⟨homologyIndex_equiv_of_deformCollared K hKp hPT hc n,
    homologyIndex_equiv_of_deformCollared K hKm hPB hc n⟩

omit [TopologicalSpace.MetrizableSpace X] in
/-- `CH_*(S♮) = 0` for a common block. -/
theorem rate_snat_trivial (hB : IsUniformBlock Φ N Lo)
    (hSn : IsIsolatedInvariantSet (dblΦ hΦ hθ) (snat (Inv Φ (N ×ˢ univ)))) (k : ℕ) :
    Subsingleton (homologyIndex K _ hSn k) := by
  have hP := (IsUniformBlock.dbl hΦ hθ hB).isIndexPair
  have hInv : Inv (dblΦ hΦ hθ) (N ×ˢ blockJ) = snat (Inv Φ (N ×ˢ univ)) := by
    have e : nnat (N ×ˢ (univ : Set Tau)) = N ×ˢ blockJ := by
      ext p
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, mem_univ _⟩, h.2⟩⟩
    rw [← e]
    exact (snat_isolated hΦ hθ (IsUniformBlock.slab hB).isIsolatingNbhd).2
  rw [hInv] at hP
  obtain ⟨iso⟩ := homologyIndexIso K hSn hP k
  have := redH_subsingleton K (IndexSpace.prod_pointedContractible (N₁ := N) (L₁ := Lo)
    (N₂ := blockJ) (L₂ := blockE) blockH
    (fun b => Subtype.ext (Subtype.ext (by
      show _ + ((0 : I) : ℝ) * _ = _
      simp)))
    (fun b => show ((b : Dbl) : ℝ) + ((1 : I) : ℝ) * (3 / 2 - ((b : Dbl) : ℝ)) = 3 / 2 by
      simp only [Set.Icc.coe_one, one_mul]; ring)
    (fun s b (hb : ((b : Dbl) : ℝ) = 3 / 2) =>
      show ((b : Dbl) : ℝ) + (s : ℝ) * (3 / 2 - ((b : Dbl) : ℝ)) = 3 / 2 by rw [hb]; ring)) k
  exact iso.toLinearEquiv.toEquiv.subsingleton

/-- Theorem `thm:rate`(ii): for a common block, `CH_*(S♮) = 0` and `Ψ` is an isomorphism. -/
theorem rate_transport (hB : IsUniformBlock Φ N Lo) :
    ∃ (hSn : IsIsolatedInvariantSet (dblΦ hΦ hθ) (snat (Inv Φ (N ×ˢ univ))))
      (hKp : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ))
        {x | (x, Tau.top) ∈ Inv Φ (N ×ˢ univ)})
      (hKm : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ))
        {x | (x, Tau.bot) ∈ Inv Φ (N ×ˢ univ)})
      (Ψ : ∀ k, homologyIndex K _ hKm k →ₗ[K] homologyIndex K _ hKp k)
      (i : ∀ k, homologyIndex K _ hKp k →ₗ[K] homologyIndex K _ hSn k)
      (p : ∀ k, homologyIndex K _ hSn (k + 1) →ₗ[K] homologyIndex K _ hKm k),
      (∀ k, Exact (Ψ k) (i k)) ∧ (∀ k, Exact (i (k + 1)) (p k)) ∧
        (∀ k, Exact (p k) (Ψ k)) ∧ (∀ k, Subsingleton (homologyIndex K _ hSn k)) ∧
        ∀ k, Bijective (Ψ k) := by
  have hS : IsIsolatedInvariantSet Φ (Inv Φ (N ×ˢ univ)) :=
    ⟨_, (IsUniformBlock.slab hB).isIsolatingNbhd, rfl⟩
  obtain ⟨hSn, hKp, hKm, Ψ, i, p, h1, h2, h3, -⟩ := transport hΦ hθ K hS
  have hz := rate_snat_trivial hΦ hθ K hB hSn
  refine ⟨hSn, hKp, hKm, Ψ, i, p, h1, h2, h3, hz, fun k => ⟨?_, ?_⟩⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨y, rfl⟩ := ((h3 k) x).1 hx
    have := hz (k + 1)
    rw [Subsingleton.elim y 0, map_zero]
  · intro y
    have := hz k
    exact ((h1 k) y).1 (Subsingleton.elim _ _)

include hΦ hθ in
/-- Theorem `thm:rate`(iii): for a common block with `H̃_*(N/L_out) ≠ 0`, the non-autonomous system
has, for every rate, a solution in `N` running from `K_-` to `K_+`, namely an orbit of `S` with
`-1 < τ < 1` whose `α`- and `ω`-limit sets lie in `K_- × {-1}` and `K_+ × {1}`. -/
theorem rate_connection (hB : IsUniformBlock Φ N Lo)
    (hnt : ∃ k, Nontrivial (redH K (IndexSpace N Lo) (IndexSpace.pt N Lo) k)) :
    ∃ p ∈ Inv Φ (N ×ˢ univ), (p.2 : ℝ) ∈ Ioo (-1) 1 ∧
      omegaLim Φ p ⊆ Inv Φ (N ×ˢ univ) ∩ (fun q => (q.2 : ℝ)) ⁻¹' {1} ∧
      alphaLim Φ p ⊆ Inv Φ (N ×ˢ univ) ∩ (fun q => (q.2 : ℝ)) ⁻¹' {-1} := by
  have hS : IsIsolatedInvariantSet Φ (Inv Φ (N ×ˢ univ)) :=
    ⟨_, (IsUniformBlock.slab hB).isIsolatingNbhd, rfl⟩
  have hARs := (hΦ.isHeight hθ).isAttractorRepellerPair hS
  suffices h : ∃ p ∈ Inv Φ (N ×ˢ univ), (p.2 : ℝ) ∈ Ioo (-1) 1 by
    obtain ⟨p, hp, hτ⟩ := h
    exact ⟨p, hp, hτ, hARs.connecting p hp (fun h => hτ.2.ne h.2) (fun h => hτ.1.ne' h.2)⟩
  by_contra hno
  push Not at hno
  obtain ⟨k, hk⟩ := hnt
  obtain ⟨hSn, hAR⟩ := snat_attractorRepeller hΦ hθ hS
  have hcover : ∀ q ∈ snat (Inv Φ (N ×ˢ univ)),
      q ∈ {x | (x, Tau.top) ∈ Inv Φ (N ×ˢ univ)} ×ˢ {Dbl.zero} ∨
        q ∈ {x | (x, Tau.bot) ∈ Inv Φ (N ×ˢ univ)} ×ˢ {Dbl.one} := by
    intro q hq
    have h : tent q.2 ∉ Ioo (-1 : ℝ) 1 := hno _ hq.1
    have ht : tent q.2 = 1 - 2 * q.2 := tent_of_mem hq.2.1 hq.2.2
    rw [ht, mem_Ioo, not_and_or, not_lt, not_lt] at h
    rcases h with h | h
    · right
      rw [← snat_inter_bot]
      refine ⟨hq, show tent q.2 = -1 by rw [ht]; linarith [hq.2.2]⟩
    · left
      rw [← snat_inter_top]
      refine ⟨hq, show tent q.2 = 1 by rw [ht]; linarith [hq.2.1]⟩
  have hRA : IsAttractorRepellerPair (dblΦ hΦ hθ) (snat (Inv Φ (N ×ˢ univ)))
      ({x | (x, Tau.bot) ∈ Inv Φ (N ×ˢ univ)} ×ˢ {Dbl.one})
      ({x | (x, Tau.top) ∈ Inv Φ (N ×ˢ univ)} ×ˢ {Dbl.zero}) :=
    { isolated := hAR.isolated
      isolated_A := hAR.isolated_R
      isolated_R := hAR.isolated_A
      subset_A := hAR.subset_R
      subset_R := hAR.subset_A
      disjoint := hAR.disjoint.symm
      connecting := fun q hq h1 h2 =>
        (hcover q hq).elim (fun h => absurd h h2) (fun h => absurd h h1) }
  obtain ⟨-, pR, d, -, h2, -, h0⟩ := homologyIndex_attractor_repeller_of_pair K hAR
  obtain ⟨-, pA, d', -, h2', -, h0'⟩ := homologyIndex_attractor_repeller_of_pair K hRA
  have hz := rate_snat_trivial hΦ hθ K hB hAR.isolated
  have hA0 := (ConleyCheck.subsingleton_of_two_les
    (A := fun k => (homologyIndex K (dblΦ hΦ hθ) hAR.isolated_A k : Type u))
    (Rr := fun k => (homologyIndex K (dblΦ hΦ hθ) hAR.isolated_R k : Type u))
    (S := fun k => (homologyIndex K (dblΦ hΦ hθ) hAR.isolated k : Type u))
    hz pR d h2 h0 pA d' h2' h0' k).1
  obtain ⟨-, hKp, _hKm, -, -, hiso⟩ := rate_index hΦ hθ K hB
  obtain ⟨e₁⟩ := snat_attractor_index hΦ hθ K hS hAR.isolated_A hKp k
  obtain ⟨⟨e₂⟩, -⟩ := hiso k
  exact not_subsingleton _ ((e₁.trans e₂).symm.toEquiv.subsingleton)

end Rate

end ConleyCheck.Conley
