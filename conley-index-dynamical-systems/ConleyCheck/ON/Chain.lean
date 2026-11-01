import ConleyCheck.ON.Limits

/-!
# The chain-recurrent set of `B_N`: Proposition `prop:ON`(b)

The chain-recurrent set of the flow restricted to `B_N` consists of the fixed points. A non-fixed
point `x` is not chain recurrent: pick an interval `[a, b]` below `V(x)` containing no value of `V`
at a fixed point. On the compact part of `B_N` where `V ∈ [a, b]` the dissipation is bounded below,
so after a long time every point with `V ≤ b` has `V < a`. Small jumps raise `V` by less than
`b - a`, so a chain starting at `x` never returns to the level `V(x)`.
-/

open Set Filter Topology Metric

namespace ConleyCheck.Conley

variable {α : Type*} [PseudoMetricSpace α]

/-- `x` is chain recurrent for the flow restricted to `S`: for all `ε, T > 0` there is an
`(ε, T)`-chain in `S` from `x` to `x`. -/
def IsChainRecurrentIn (ϕ : Flow ℝ α) (S : Set α) (x : α) : Prop :=
  ∀ ε > 0, ∀ T > 0, ∃ (n : ℕ) (xs : ℕ → α) (ts : ℕ → ℝ), xs 0 = x ∧ xs (n + 1) = x ∧
    ∀ i ≤ n, xs i ∈ S ∧ T ≤ ts i ∧ dist (ϕ (ts i) (xs i)) (xs (i + 1)) < ε

end ConleyCheck.Conley

namespace ConleyCheck.ON

open ConleyCheck.Conley ConleyCheck.ODE

variable {N : ℝ}

theorem exists_gap {F : Set ℝ} (hF : F.Finite) {a₀ c : ℝ} (h : a₀ < c) :
    ∃ a b, a₀ < a ∧ a < b ∧ b < c ∧ ∀ v ∈ F, v < a ∨ b < v := by
  obtain ⟨m, ⟨hm1, hm2⟩, hmF⟩ := ((Set.Ioo_infinite h).diff hF).nonempty
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < m - a₀ ∧ δ < c - m ∧ ∀ v ∈ F, δ < |v - m| := by
    refine nhdsWithin_le_nhds ?_
    refine (eventually_lt_nhds (sub_pos.2 hm1)).and ((eventually_lt_nhds (sub_pos.2 hm2)).and
      ((eventually_all_finite hF).2 fun v hv => eventually_lt_nhds ?_))
    exact abs_pos.2 (sub_ne_zero.2 fun e => hmF (e ▸ hv))
  obtain ⟨δ, ⟨h1, h2, h3⟩, hδ⟩ := (hev.and self_mem_nhdsWithin).exists
  have hδ' : 0 < δ := hδ
  refine ⟨m - δ / 2, m + δ / 2, by linarith, by linarith, by linarith, fun v hv => ?_⟩
  rcases le_or_gt v m with hvm | hvm
  · left
    have := h3 v hv
    rw [abs_of_nonpos (by linarith)] at this
    linarith
  · right
    have := h3 v hv
    rw [abs_of_pos (by linarith)] at this
    linarith

theorem Vp_drop (hN : 1 < N) {a b d : ℝ} (hab : a ≤ b) (hd0 : 0 < d)
    (hd : ∀ z ∈ Inv (flowON N) blockR, a ≤ Vp N z → Vp N z ≤ b → d ≤ diss N z)
    {y : ℝ × ℝ} (hy : y ∈ Inv (flowON N) blockR) (hyb : Vp N y ≤ b) {t : ℝ}
    (ht : (b - a) / d + 1 ≤ t) : Vp N (flowON N t y) < a := by
  by_contra hge
  push Not at hge
  have ht0 : 0 ≤ t := le_trans (by have := div_nonneg (sub_nonneg.2 hab) hd0.le; linarith) ht
  have hanti := antitone_Vp_flow hN hy
  have hdiss : ∀ s ∈ Icc 0 t, d ≤ diss N (flowON N s y) := fun s hs =>
    hd _ (flow_mem_Inv hy s) (hge.trans (hanti hs.2))
      ((hanti hs.1).trans (by show Vp N (flowON N 0 y) ≤ b; rw [Flow.map_zero_apply]; exact hyb))
  have hlin : ∀ s, HasDerivAt (fun s => Vp N y - d * s) (-d) s := fun s => by
    simpa using ((hasDerivAt_id s).const_mul d).const_sub (Vp N y)
  have := image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := t)
    (f := fun s => Vp N (flowON N s y)) (f' := fun s => -diss N (flowON N s y))
    (B := fun s => Vp N y - d * s) (B' := fun _ => -d)
    (fun s _ => (hasDerivAt_Vp_flow hy s).continuousAt.continuousWithinAt)
    (fun s _ => (hasDerivAt_Vp_flow hy s).hasDerivWithinAt)
    (by simp [Flow.map_zero_apply])
    (fun s _ => (hlin s).continuousAt.continuousWithinAt)
    (fun s _ => (hlin s).hasDerivWithinAt)
    (fun s hs => by linarith [hdiss s (Ico_subset_Icc_self hs)]) ⟨ht0, le_rfl⟩
  have h1 : (b - a) / d * d = b - a := div_mul_cancel₀ _ hd0.ne'
  nlinarith

/-- Non-fixed points of `B_N` are not chain recurrent. -/
theorem not_chainRecurrent (hN : 1 < N) {x : ℝ × ℝ} (hx : x ∈ Inv (flowON N) blockR)
    (hz : ¬ IsZero N x) : ¬ IsChainRecurrentIn (flowON N) (Inv (flowON N) blockR) x := by
  set S := Inv (flowON N) blockR
  have hanti := antitone_Vp_flow hN hx
  have hd : -diss N (flowON N 0 x) < 0 := by
    rw [Flow.map_zero_apply]
    have : diss N x ≠ 0 := fun h => hz (isZero_of_diss_eq_zero hN h)
    have : 0 < diss N x := lt_of_le_of_ne (diss_nonneg hN x) (Ne.symm this)
    linarith
  obtain ⟨s₀, hs₀, hs₀0⟩ := (((eventually_sign (hasDerivAt_Vp_flow hx 0) hd).1).and
    self_mem_nhdsWithin).exists
  simp only [Flow.map_zero_apply] at hs₀
  have hs₀0' : 0 < s₀ := hs₀0
  -- the gap `[a, b]`
  have hF : (Vp N '' {p | IsZero N p}).Finite := (finite_zeros hN).image _
  obtain ⟨a, b, ha₀, hab, hbc, hgap⟩ := exists_gap hF hs₀
  -- the dissipation bound on `S ∩ V⁻¹[a, b]`
  have hSab : IsCompact (S ∩ Vp N ⁻¹' Icc a b) :=
    isCompact_Inv_R.inter_right (isClosed_Icc.preimage (continuous_Vp N))
  have hcontd : Continuous (diss N) := by unfold diss f₁ f₂; fun_prop
  obtain ⟨d, hd0, hdb⟩ : ∃ d > 0, ∀ z ∈ S, a ≤ Vp N z → Vp N z ≤ b → d ≤ diss N z := by
    rcases (S ∩ Vp N ⁻¹' Icc a b).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun z hzS h1 h2 => absurd (show z ∈ (∅ : Set (ℝ × ℝ)) from
        he ▸ ⟨hzS, h1, h2⟩) (notMem_empty z)⟩
    · obtain ⟨z₀, hz₀, hmin⟩ := hSab.exists_isMinOn hne hcontd.continuousOn
      have hz₀z : ¬ IsZero N z₀ := fun h => by
        rcases hgap _ ⟨z₀, h, rfl⟩ with h' | h'
        · exact absurd hz₀.2.1 (not_le.2 h')
        · exact absurd hz₀.2.2 (not_le.2 h')
      have : diss N z₀ ≠ 0 := fun h => hz₀z (isZero_of_diss_eq_zero hN h)
      exact ⟨diss N z₀, lt_of_le_of_ne (diss_nonneg hN z₀) (Ne.symm this),
        fun z hzS h1 h2 => hmin ⟨hzS, h1, h2⟩⟩
  -- uniform continuity of `V` on `S`
  obtain ⟨ε, hε, huc⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Inv_R.uniformContinuousOn_of_continuous (continuous_Vp N).continuousOn)
    (b - a) (sub_pos.2 hab)
  set T₀ := (b - a) / d + 1
  intro hcr
  obtain ⟨n, xs, ts, h0, hn, hch⟩ := hcr ε hε (max T₀ s₀) (lt_max_of_lt_right hs₀0')
  have hmem : ∀ i ≤ n + 1, xs i ∈ S := fun i hi => by
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · exact (hch i (Nat.lt_succ_iff.1 h)).1
    · rw [le_antisymm hi h, hn]; exact hx
  have hjump : ∀ i ≤ n, Vp N (flowON N (ts i) (xs i)) < a → Vp N (xs (i + 1)) < b := by
    intro i hi hlt
    have h := huc _ (flow_mem_Inv (hch i hi).1 (ts i)) _ (hmem (i + 1) (by omega))
      (hch i hi).2.2
    rw [Real.dist_eq] at h
    linarith [le_abs_self (Vp N (flowON N (ts i) (xs i)) - Vp N (xs (i + 1))),
      neg_abs_le (Vp N (flowON N (ts i) (xs i)) - Vp N (xs (i + 1)))]
  have hall : ∀ i, 1 ≤ i → i ≤ n + 1 → Vp N (xs i) < b := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base =>
      intro _
      refine hjump 0 (Nat.zero_le _) ?_
      rw [h0]
      exact lt_of_le_of_lt (hanti ((le_max_right _ _).trans (hch 0 (Nat.zero_le _)).2.1)) ha₀
    | succ i hi ih =>
      intro hi'
      have hin : i ≤ n := by omega
      refine hjump i hin (Vp_drop hN hab.le hd0 hdb (hch i hin).1 (ih (by omega)).le ?_)
      exact (le_max_left _ _).trans (hch i hin).2.1
  have := hall (n + 1) (by omega) le_rfl
  rw [hn] at this
  linarith

/-- Proposition `prop:ON`(b): the chain-recurrent set of `B_N` consists of the fixed points. -/
theorem prop_ON_b_chain (hN : 1 < N) :
    {x ∈ boundedOrbits N | IsChainRecurrentIn (flowON N) (boundedOrbits N) x} =
      {x | IsZero N x} := by
  ext x
  constructor
  · rintro ⟨hx, hcr⟩
    by_contra hz
    rw [← Inv_R_eq hN] at hx hcr
    exact not_chainRecurrent hN hx hz hcr
  · intro hz
    have hxB := zero_mem_B hN hz
    have hxR : x ∈ blockR := by
      rw [← Inv_R_eq hN] at hxB; exact Inv_subset _ hxB
    refine ⟨hxB, fun ε hε T _ => ⟨0, fun _ => x, fun _ => T, rfl, rfl, fun i _ => ⟨hxB, le_rfl,
      ?_⟩⟩⟩
    rw [flowON_fixed hxR hz, dist_self]
    exact hε

end ConleyCheck.ON
