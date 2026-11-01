import ConleyCheck.ON.Flow
import ConleyCheck.Conley.Morse

/-!
# Limit sets of the `O(N)`-type model: Proposition `prop:ON`(b)

* `tendsto_of_mapClusterPt_finite`: a continuous curve in a compact set, all of whose cluster points
  at `+∞` lie in a finite set, converges to one of them.
* `prop_ON_b_tendsto`: every orbit in `B_N` converges to fixed points in both time directions.
  The cluster points are zeros of the field because `V` is a strict Lyapunov function, which is
  proved directly with the continuity of the flow (no invariance of limit sets is needed).
* `prop_ON_b_morse`: for `N ≠ 4` the four fixed points, ordered by the value of `V`, form a Morse
  decomposition of `B_N`. Each fixed point is isolated, because a full orbit near a fixed point
  `p` converges to `p` in both directions, so `V` is constant on it.
-/

open Set Filter Topology Metric

namespace ConleyCheck.Conley

variable {α : Type*} [TopologicalSpace α]

/-- A Morse decomposition of `S`, indexed by `ι` with the strict order `r`: every point of `S`
outside the Morse sets has its `ω`-limit in some `M i` and its `α`-limit in some `M j` with
`r i j`. -/
structure IsMorseDecomp (ϕ : Flow ℝ α) (S : Set α) {ι : Type*} (M : ι → Set α)
    (r : ι → ι → Prop) : Prop where
  isolated : IsIsolatedInvariantSet ϕ S
  isolated_M : ∀ i, IsIsolatedInvariantSet ϕ (M i)
  subset : ∀ i, M i ⊆ S
  disjoint : Pairwise fun i j => Disjoint (M i) (M j)
  irrefl : ∀ i, ¬ r i i
  trans : ∀ i j k, r i j → r j k → r i k
  connecting : ∀ x ∈ S, (∀ i, x ∉ M i) →
    ∃ i j, r i j ∧ omegaLim ϕ x ⊆ M i ∧ alphaLim ϕ x ⊆ M j

end ConleyCheck.Conley

namespace ConleyCheck.ON

open ConleyCheck.Conley ConleyCheck.ODE

/-! ## Convergence from finitely many cluster points -/

theorem eventually_near_of_mapClusterPt {X : Type*} [MetricSpace X] {γ : ℝ → X} {Z : Set X}
    {K : Set X} (hK : IsCompact K) (hγK : ∀ t, γ t ∈ K)
    (hcl : ∀ p, MapClusterPt p atTop γ → p ∈ Z) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, ∃ z ∈ Z, dist (γ t) z < ε := by
  by_contra h
  rw [not_eventually] at h
  set K' := K ∩ ⋂ z ∈ Z, {q | ε ≤ dist q z}
  have hK'c : IsCompact K' := hK.inter_right (isClosed_biInter fun z _ =>
    isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hfr : ∃ᶠ q in map γ atTop, q ∈ K' := frequently_map.2 (h.mono fun t ht =>
    ⟨hγK t, mem_iInter₂.2 fun z hz => le_of_not_gt fun hlt => ht ⟨z, hz, hlt⟩⟩)
  have := frequently_mem_iff_neBot.1 hfr
  obtain ⟨q, hqK', hq⟩ := hK'c (f := map γ atTop ⊓ 𝓟 K') inf_le_right
  have hqZ := hcl q (hq.mono inf_le_left)
  have := mem_iInter₂.1 hqK'.2 q hqZ
  simp only [mem_ofPred_eq, dist_self] at this
  linarith

theorem exists_sep {X : Type*} [MetricSpace X] {Z : Set X} (hZ : Z.Finite) :
    ∃ ε > 0, ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → 3 * ε ≤ dist z z' := by
  have h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → 3 * ε ≤ dist z z' := by
    refine (eventually_all_finite hZ).2 fun z _ => (eventually_all_finite hZ).2 fun z' _ => ?_
    by_cases hzz : z = z'
    · exact Eventually.of_forall fun _ h => absurd hzz h
    · have hd : 0 < dist z z' / 3 := div_pos (dist_pos.2 hzz) (by norm_num)
      filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hd)] with ε hε _
      linarith
  obtain ⟨ε, hε, hε0⟩ := (h.and self_mem_nhdsWithin).exists
  exact ⟨ε, hε0, hε⟩

/-- A continuous curve in a compact set whose cluster points at `+∞` lie in a finite set converges
to a point of that set. -/
theorem tendsto_of_mapClusterPt_finite {X : Type*} [MetricSpace X] {γ : ℝ → X}
    (hγ : Continuous γ) {Z : Set X} (hZ : Z.Finite) {K : Set X} (hK : IsCompact K)
    (hγK : ∀ t, γ t ∈ K) (hcl : ∀ p, MapClusterPt p atTop γ → p ∈ Z) :
    ∃ z ∈ Z, Tendsto γ atTop (𝓝 z) := by
  obtain ⟨ε₀, hε₀, hsep⟩ := exists_sep hZ
  obtain ⟨T, hT⟩ := eventually_atTop.1 (eventually_near_of_mapClusterPt hK hγK hcl hε₀)
  obtain ⟨z₀, hz₀, hTz₀⟩ := hT T le_rfl
  have hfar : ∀ t, ∀ z ∈ Z, z ≠ z₀ → dist (γ t) z < ε₀ → 2 * ε₀ ≤ dist (γ t) z₀ :=
    fun t z hz hne hlt => by
      have := hsep z hz z₀ hz₀ hne
      have := dist_triangle_left z z₀ (γ t)
      linarith
  have hstay : ∀ t, T ≤ t → dist (γ t) z₀ < ε₀ := by
    intro t₁ ht₁
    by_contra hge
    push Not at hge
    have hd : Continuous fun t => dist (γ t) z₀ := hγ.dist continuous_const
    have h2 : 2 * ε₀ ≤ dist (γ t₁) z₀ := by
      obtain ⟨z₁, hz₁, hz₁t⟩ := hT t₁ ht₁
      by_cases h : z₁ = z₀
      · subst h; linarith
      · exact hfar t₁ z₁ hz₁ h hz₁t
    obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc ht₁ hd.continuousOn
      (⟨by linarith, by linarith⟩ : 3 / 2 * ε₀ ∈ Icc (dist (γ T) z₀) (dist (γ t₁) z₀))
    obtain ⟨z, hz, hzt⟩ := hT t ht.1
    by_cases hzz : z = z₀
    · subst hzz
      simp only at hteq
      linarith
    · have := hfar t z hz hzz hzt
      simp only at hteq
      linarith
  refine ⟨z₀, hz₀, Metric.tendsto_nhds.2 fun ε hε => ?_⟩
  filter_upwards [eventually_near_of_mapClusterPt hK hγK hcl (lt_min hε hε₀),
    eventually_ge_atTop T] with t ⟨z, hz, hzt⟩ ht
  by_cases hzz : z = z₀
  · subst hzz
    exact hzt.trans_le (min_le_left _ _)
  · have := hfar t z hz hzz (hzt.trans_le (min_le_right _ _))
    linarith [hstay t ht]

/-! ## The Lyapunov function along the flow -/

variable {N : ℝ}

/-- The dissipation `f₁² + (N-1)/3 f₂²`, so that `dV/ds = -diss`. -/
noncomputable def diss (N : ℝ) (p : ℝ × ℝ) : ℝ := f₁ N p.1 p.2 ^ 2 + (N - 1) / 3 * f₂ N p.1 p.2 ^ 2

/-- `V` as a function on `ℝ × ℝ`. -/
noncomputable def Vp (N : ℝ) (p : ℝ × ℝ) : ℝ := V N p.1 p.2

theorem continuous_Vp (N : ℝ) : Continuous (Vp N) := by
  unfold Vp V
  fun_prop

theorem diss_nonneg (hN : 1 < N) (p : ℝ × ℝ) : 0 ≤ diss N p := by
  have := (dV_neg (a := f₁ N p.1 p.2) (b := f₂ N p.1 p.2) hN).1
  simp only [diss]
  linarith

theorem isZero_of_diss_eq_zero (hN : 1 < N) {p : ℝ × ℝ} (h : diss N p = 0) : IsZero N p := by
  have := (dV_neg (a := f₁ N p.1 p.2) (b := f₂ N p.1 p.2) hN).2.1
  exact this (by simp only [diss] at h; linarith)

/-- The set of zeros of `eq:ONy` is finite. -/
theorem finite_zeros (hN : 1 < N) : {p : ℝ × ℝ | IsZero N p}.Finite := by
  refine (Set.toFinite ({ptG, ptI, ptC N, ptH N} : Set (ℝ × ℝ))).subset fun p hp => ?_
  have := zeros_complete (y₁ := p.1) (y₂ := p.2) (by linarith) hp
  simp only [Prod.mk.eta] at this
  rcases this with h | h | h | h <;> simp [h]

theorem mem_R_of_Inv {x : ℝ × ℝ} (hx : x ∈ Inv (flowON N) blockR) (t : ℝ) :
    flowON N t x ∈ blockR := hx t

theorem hasDerivAt_Vp_flow {x : ℝ × ℝ} (hx : x ∈ Inv (flowON N) blockR) (t : ℝ) :
    HasDerivAt (fun s => Vp N (flowON N s x)) (-diss N (flowON N t x)) t := by
  have hd := hasDerivAt_flowON N x t
  rw [cutField_eq_on_R (hx t)] at hd
  have h1 : HasDerivAt (fun s => (flowON N s x).1) (f₁ N (flowON N t x).1 (flowON N t x).2) t := by
    have h := (hasFDerivAt_fst (𝕜 := ℝ) (p := flowON N t x)).comp_hasDerivAt t hd
    exact h
  have h2 : HasDerivAt (fun s => (flowON N s x).2) (f₂ N (flowON N t x).1 (flowON N t x).2) t := by
    have h := (hasFDerivAt_snd (𝕜 := ℝ) (p := flowON N t x)).comp_hasDerivAt t hd
    exact h
  exact hasDerivAt_V_along h1 h2

theorem antitone_Vp_flow (hN : 1 < N) {x : ℝ × ℝ} (hx : x ∈ Inv (flowON N) blockR) :
    Antitone fun s => Vp N (flowON N s x) :=
  antitone_of_deriv_nonpos (fun t => (hasDerivAt_Vp_flow hx t).differentiableAt) fun t => by
    rw [(hasDerivAt_Vp_flow hx t).deriv]
    linarith [diss_nonneg hN (flowON N t x)]

theorem isClosed_Inv_R : IsClosed (Inv (flowON N) blockR) :=
  isClosed_Inv ((isCompact_Icc.prod isCompact_Icc).isClosed)

theorem isCompact_Inv_R : IsCompact (Inv (flowON N) blockR) :=
  isCompact_Inv (isCompact_Icc.prod isCompact_Icc)

/-- Cluster points at `+∞` of orbits in `Inv(R)` are zeros. -/
theorem isZero_of_mapClusterPt_atTop (hN : 1 < N) {x : ℝ × ℝ}
    (hx : x ∈ Inv (flowON N) blockR) {p : ℝ × ℝ}
    (hp : MapClusterPt p atTop fun t => flowON N t x) : IsZero N p := by
  have hpR : p ∈ Inv (flowON N) blockR :=
    isClosed_Inv_R.mem_of_mapClusterPt hp (Eventually.of_forall fun t => flow_mem_Inv hx t)
  have hV : ∀ t, Vp N p ≤ Vp N (flowON N t x) := fun t =>
    (isClosed_le (continuous_Vp N) continuous_const).mem_of_mapClusterPt hp
      ((eventually_ge_atTop t).mono fun s hs => antitone_Vp_flow hN hx hs)
  by_contra hz
  have hd : -diss N (flowON N 0 p) < 0 := by
    rw [Flow.map_zero_apply]
    have := diss_nonneg hN p
    have : diss N p ≠ 0 := fun h => hz (isZero_of_diss_eq_zero hN h)
    have : 0 < diss N p := lt_of_le_of_ne (diss_nonneg hN p) (Ne.symm this)
    linarith
  obtain ⟨s₀, hs₀, -⟩ := (((eventually_sign (hasDerivAt_Vp_flow hpR 0) hd).1).and
    self_mem_nhdsWithin).exists
  simp only [Flow.map_zero_apply] at hs₀
  have hcont : Continuous fun q => Vp N (flowON N s₀ q) :=
    (continuous_Vp N).comp ((flowON N).continuous_toFun s₀)
  obtain ⟨t, ht⟩ := (hp.frequently ((hcont.continuousAt).eventually
    (Iio_mem_nhds hs₀))).exists
  have h1 := hV (s₀ + t)
  rw [← Flow.map_add] at ht
  exact absurd ht (not_lt.2 h1)

/-- Cluster points at `-∞` of orbits in `Inv(R)` are zeros. -/
theorem isZero_of_mapClusterPt_atBot (hN : 1 < N) {x : ℝ × ℝ}
    (hx : x ∈ Inv (flowON N) blockR) {p : ℝ × ℝ}
    (hp : MapClusterPt p atBot fun t => flowON N t x) : IsZero N p := by
  have hpR : p ∈ Inv (flowON N) blockR :=
    isClosed_Inv_R.mem_of_mapClusterPt hp (Eventually.of_forall fun t => flow_mem_Inv hx t)
  have hV : ∀ t, Vp N (flowON N t x) ≤ Vp N p := fun t =>
    (isClosed_le continuous_const (continuous_Vp N)).mem_of_mapClusterPt hp
      ((eventually_le_atBot t).mono fun s hs => antitone_Vp_flow hN hx hs)
  by_contra hz
  have hd : -diss N (flowON N 0 p) < 0 := by
    rw [Flow.map_zero_apply]
    have : diss N p ≠ 0 := fun h => hz (isZero_of_diss_eq_zero hN h)
    have : 0 < diss N p := lt_of_le_of_ne (diss_nonneg hN p) (Ne.symm this)
    linarith
  obtain ⟨s₀, hs₀, -⟩ := (((eventually_sign (hasDerivAt_Vp_flow hpR 0) hd).2).and
    self_mem_nhdsWithin).exists
  simp only [Flow.map_zero_apply] at hs₀
  have hcont : Continuous fun q => Vp N (flowON N s₀ q) :=
    (continuous_Vp N).comp ((flowON N).continuous_toFun s₀)
  obtain ⟨t, ht⟩ := (hp.frequently ((hcont.continuousAt).eventually
    (Ioi_mem_nhds hs₀))).exists
  have h1 := hV (s₀ + t)
  rw [← Flow.map_add] at ht
  exact absurd ht (not_lt.2 h1)

theorem continuous_orbit (x : ℝ × ℝ) : Continuous fun t => flowON N t x :=
  (flowON N).continuous continuous_id continuous_const

/-- Proposition `prop:ON`(b), first statement, for orbits of the flow in `Inv(R) = B_N`. -/
theorem tendsto_of_mem_Inv (hN : 1 < N) {x : ℝ × ℝ} (hx : x ∈ Inv (flowON N) blockR) :
    ∃ p q, IsZero N p ∧ IsZero N q ∧ Tendsto (fun t => flowON N t x) atTop (𝓝 p) ∧
      Tendsto (fun t => flowON N t x) atBot (𝓝 q) := by
  have hK : ∀ t, flowON N t x ∈ Inv (flowON N) blockR := fun t => flow_mem_Inv hx t
  obtain ⟨p, hp, hpT⟩ := tendsto_of_mapClusterPt_finite (continuous_orbit x) (finite_zeros hN)
    isCompact_Inv_R hK fun p hp => isZero_of_mapClusterPt_atTop hN hx hp
  obtain ⟨q, hq, hqT⟩ := tendsto_of_mapClusterPt_finite (γ := fun t => flowON N (-t) x)
    ((continuous_orbit x).comp continuous_neg) (finite_zeros hN) isCompact_Inv_R
    (fun t => hK (-t)) fun q hq =>
      isZero_of_mapClusterPt_atBot hN hx (hq.of_comp tendsto_neg_atTop_atBot)
  refine ⟨p, q, hp, hq, hpT, ?_⟩
  have := hqT.comp tendsto_neg_atBot_atTop
  simpa [Function.comp_def] using this

/-- Proposition `prop:ON`(b), first statement: every bounded full solution of `eq:ONy` converges
to fixed points in both time directions. -/
theorem prop_ON_b_tendsto (hN : 1 < N) {γ : ℝ → ℝ × ℝ} (hγ : IsSol (field N) γ)
    (hb : Bornology.IsBounded (range γ)) :
    ∃ p q, IsZero N p ∧ IsZero N q ∧ Tendsto γ atTop (𝓝 p) ∧ Tendsto γ atBot (𝓝 q) := by
  have hx : γ 0 ∈ Inv (flowON N) blockR := by
    rw [Inv_R_eq hN]; exact ⟨γ, hγ, hb, 0, rfl⟩
  have hin : ∀ s, γ s ∈ blockR := fun s =>
    interior_subset (inner_subset_R hN (bounded_sol_mem hN hγ hb s))
  have hγ' : IsSol (cutField N) γ := fun s => by
    rw [cutField_eq_on_R (hin s)]; exact hγ s
  have he : (fun t => flowON N t (γ 0)) = γ := funext fun t => by
    rw [flowON_eq_of_isSol N hγ' 0 t, add_zero]
  obtain ⟨p, q, hp, hq, h1, h2⟩ := tendsto_of_mem_Inv hN hx
  rw [he] at h1 h2
  exact ⟨p, q, hp, hq, h1, h2⟩

/-! ## Rigidity: orbits with `V(α) ≤ V(ω)` are fixed points -/

theorem isZero_of_V_le (hN : 1 < N) {x : ℝ × ℝ} (hx : x ∈ Inv (flowON N) blockR) {p q : ℝ × ℝ}
    (hp : Tendsto (fun t => flowON N t x) atTop (𝓝 p))
    (hq : Tendsto (fun t => flowON N t x) atBot (𝓝 q)) (hle : Vp N q ≤ Vp N p) : IsZero N x := by
  have hVp : Tendsto (fun t => Vp N (flowON N t x)) atTop (𝓝 (Vp N p)) :=
    ((continuous_Vp N).tendsto p).comp hp
  have hVq : Tendsto (fun t => Vp N (flowON N t x)) atBot (𝓝 (Vp N q)) :=
    ((continuous_Vp N).tendsto q).comp hq
  have hanti := antitone_Vp_flow hN hx
  have hup : ∀ t, Vp N (flowON N t x) ≤ Vp N q := fun t =>
    ge_of_tendsto hVq ((eventually_le_atBot t).mono fun s hs => hanti hs)
  have hlow : ∀ t, Vp N p ≤ Vp N (flowON N t x) := fun t =>
    le_of_tendsto hVp ((eventually_ge_atTop t).mono fun s hs => hanti hs)
  have hconst : (fun s => Vp N (flowON N s x)) = fun _ => Vp N p := funext fun s =>
    le_antisymm ((hup s).trans hle) (hlow s)
  have hd := hasDerivAt_Vp_flow hx 0
  rw [hconst, Flow.map_zero_apply] at hd
  have h0 := hd.unique (hasDerivAt_const 0 (Vp N p))
  exact isZero_of_diss_eq_zero hN (by linarith)

theorem eq_of_tendsto_of_mem_omegaLim {x p z : ℝ × ℝ}
    (hp : Tendsto (fun t => flowON N t x) atTop (𝓝 p)) (hz : z ∈ omegaLim (flowON N) x) :
    z = p := by
  have hc := (mem_omegaLimit_singleton_iff_mapClusterPt (f := atTop) (ϕ := (flowON N).toFun)
    x z).1 hz
  exact eq_of_nhds_neBot (hc.clusterPt.mono hp)

theorem eq_of_tendsto_of_mem_alphaLim {x q z : ℝ × ℝ}
    (hq : Tendsto (fun t => flowON N t x) atBot (𝓝 q)) (hz : z ∈ alphaLim (flowON N) x) :
    z = q := by
  have hc := (mem_omegaLimit_singleton_iff_mapClusterPt (f := atBot) (ϕ := (flowON N).toFun)
    x z).1 hz
  exact eq_of_nhds_neBot (hc.clusterPt.mono hq)

/-! ## Isolation of the fixed points -/

theorem flowON_fixed {p : ℝ × ℝ} (hpR : p ∈ blockR) (hp : IsZero N p) (t : ℝ) :
    flowON N t p = p := by
  have hs : IsSol (cutField N) fun _ => p := fun s => by
    rw [cutField_eq_on_R hpR]
    have : field N p = 0 := Prod.ext hp.1 hp.2
    rw [this]
    exact hasDerivAt_const s p
  exact flowON_eq_of_isSol N hs 0 t

theorem zero_mem_inner (hN : 1 < N) {p : ℝ × ℝ} (hp : IsZero N p) :
    p ∈ Icc (-1 / 9 : ℝ) 0 ×ˢ Icc (-1 / (N + 2)) 0 := by
  have hs : IsSol (field N) fun _ => p := fun s => by
    have : field N p = 0 := Prod.ext hp.1 hp.2
    rw [this]
    exact hasDerivAt_const s p
  exact bounded_sol_mem hN hs (by rw [range_const]; exact Bornology.isBounded_singleton) 0

/-- Every fixed point is an isolated invariant set of `flowON N`. -/
theorem isIsolated_zero (hN : 1 < N) {p : ℝ × ℝ} (hp : IsZero N p) :
    IsIsolatedInvariantSet (flowON N) {p} := by
  have hpint : p ∈ interior blockR := inner_subset_R hN (zero_mem_inner hN hp)
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), closedBall p r ⊆ blockR ∧
      ∀ q, IsZero N q → q ≠ p → r < dist q p := by
    refine Eventually.and ?_ ?_
    · obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hpint)
      filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hρ)] with r hr
      exact (closedBall_subset_ball hr).trans (hball.trans interior_subset)
    · have hfin := finite_zeros (N := N) hN
      have := (eventually_all_finite hfin (l := 𝓝[>] (0 : ℝ))
        (p := fun q r => q ≠ p → r < dist q p)).2 fun q _ => by
          by_cases hqp : q = p
          · exact Eventually.of_forall fun _ h => absurd hqp h
          · exact nhdsWithin_le_nhds ((eventually_lt_nhds (dist_pos.2 hqp)).mono
              fun _ h _ => h)
      exact this.mono fun r hr q hq => hr q hq
  obtain ⟨r, ⟨hrR, hrZ⟩, hr0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hr0' : 0 < r := hr0
  have hpR : p ∈ blockR := interior_subset hpint
  have heq : ∀ a, IsZero N a → a ∈ closedBall p r → a = p := fun a ha haU => by
    by_contra hne
    exact absurd (mem_closedBall.1 haU) (not_le.2 (hrZ a ha hne))
  have hInv : Inv (flowON N) (closedBall p r) = {p} := by
    ext x
    constructor
    · intro hx
      have hxR : x ∈ Inv (flowON N) blockR := Inv_mono hrR hx
      obtain ⟨a, b, ha, hb, hta, htb⟩ := tendsto_of_mem_Inv hN hxR
      have ha' := heq a ha (isClosed_closedBall.mem_of_tendsto hta (Eventually.of_forall hx))
      have hb' := heq b hb (isClosed_closedBall.mem_of_tendsto htb (Eventually.of_forall hx))
      have hz := isZero_of_V_le hN hxR hta htb (by rw [ha', hb'])
      exact heq x hz (Inv_subset _ hx)
    · rintro rfl t
      rw [flowON_fixed hpR hp t]
      exact mem_closedBall_self hr0'.le
  refine ⟨closedBall p r, ⟨isCompact_closedBall p r, ?_⟩, hInv⟩
  rw [hInv]
  exact singleton_subset_iff.2 (mem_interior_iff_mem_nhds.2 (closedBall_mem_nhds _ hr0'))

/-! ## The Morse decomposition for `N ≠ 4` -/

/-- The four fixed points `(Σ_G, Σ_I, Σ_C, Σ_H)`. -/
noncomputable def pts (N : ℝ) : Fin 4 → ℝ × ℝ := ![ptG, ptI, ptC N, ptH N]

theorem isZero_pts (hN : 1 < N) (i : Fin 4) : IsZero N (pts N i) := by
  fin_cases i
  · exact isZero_G N
  · exact isZero_I N
  · exact isZero_C (by linarith)
  · exact isZero_H (by linarith)

theorem exists_pts_eq (hN : 1 < N) {p : ℝ × ℝ} (hp : IsZero N p) : ∃ i, pts N i = p := by
  have := zeros_complete (y₁ := p.1) (y₂ := p.2) (by linarith) hp
  simp only [Prod.mk.eta] at this
  rcases this with h | h | h | h
  · exact ⟨0, h.symm⟩
  · exact ⟨1, h.symm⟩
  · exact ⟨2, h.symm⟩
  · exact ⟨3, h.symm⟩

theorem pts_injective (hN : 1 < N) (h4 : N ≠ 4) : Function.Injective (pts N) := by
  have hN0 : 0 < N := by linarith
  have hC2 : (ptC N).2 ≠ 0 := by simp only [ptC]; exact div_ne_zero (by norm_num) (by positivity)
  have hH1 : (ptH N).1 ≠ 0 := by simp only [ptH]; exact div_ne_zero (by norm_num) (by positivity)
  have hH2 : (ptH N).2 ≠ 0 := by simp only [ptH]; exact div_ne_zero (by norm_num) (by positivity)
  have hGI : ptG ≠ ptI := fun h => by
    have := congrArg Prod.fst h; simp only [ptG, ptI] at this; norm_num at this
  have hGC : ptG ≠ ptC N := fun h => hC2 (by rw [← h]; rfl)
  have hGH : ptG ≠ ptH N := fun h => hH1 (by rw [← h]; rfl)
  have hIC : ptI ≠ ptC N := fun h => hC2 (by rw [← h]; rfl)
  have hIH : ptI ≠ ptH N := fun h => hH2 (by rw [← h]; rfl)
  have hCH : ptC N ≠ ptH N := fun h => h4 ((ptC_eq_ptH_iff hN0).1 h)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp only [pts] at hij <;> first
    | rfl
    | exact absurd hij hGI | exact absurd hij.symm hGI
    | exact absurd hij hGC | exact absurd hij.symm hGC
    | exact absurd hij hGH | exact absurd hij.symm hGH
    | exact absurd hij hIC | exact absurd hij.symm hIC
    | exact absurd hij hIH | exact absurd hij.symm hIH
    | exact absurd hij hCH | exact absurd hij.symm hCH

theorem zero_mem_B (hN : 1 < N) {p : ℝ × ℝ} (hp : IsZero N p) : p ∈ boundedOrbits N := by
  refine ⟨fun _ => p, fun s => ?_, by rw [range_const]; exact Bornology.isBounded_singleton,
    0, rfl⟩
  have : field N p = 0 := Prod.ext hp.1 hp.2
  rw [this]
  exact hasDerivAt_const s p

/-- Proposition `prop:ON`(b), second statement: for `N ≠ 4` the four fixed points, ordered by the
value of `V`, form a Morse decomposition of `B_N`. -/
theorem prop_ON_b_morse (hN : 1 < N) (h4 : N ≠ 4) :
    IsMorseDecomp (flowON N) (boundedOrbits N) (fun i => {pts N i})
      (fun i j => Vp N (pts N i) < Vp N (pts N j)) where
  isolated := isIsolatedInvariantSet_B hN
  isolated_M i := isIsolated_zero hN (isZero_pts hN i)
  subset i := singleton_subset_iff.2 (zero_mem_B hN (isZero_pts hN i))
  disjoint i j hij := disjoint_singleton.2 fun h => hij (pts_injective hN h4 h)
  irrefl _ := lt_irrefl _
  trans _ _ _ := lt_trans
  connecting x hx hM := by
    have hxR : x ∈ Inv (flowON N) blockR := by rw [Inv_R_eq hN]; exact hx
    obtain ⟨p, q, hp, hq, hpT, hqT⟩ := tendsto_of_mem_Inv hN hxR
    obtain ⟨i, rfl⟩ := exists_pts_eq hN hp
    obtain ⟨j, rfl⟩ := exists_pts_eq hN hq
    refine ⟨i, j, ?_, fun z hz => eq_of_tendsto_of_mem_omegaLim hpT hz,
      fun z hz => eq_of_tendsto_of_mem_alphaLim hqT hz⟩
    by_contra hle
    push Not at hle
    obtain ⟨k, hk⟩ := exists_pts_eq hN (isZero_of_V_le hN hxR hpT hqT hle)
    exact hM k hk.symm

/-- Proposition `prop:ON`(b), third statement: `B_N` consists of the fixed points and of orbits
running from one fixed point to another one with a strictly larger value of `V`. -/
theorem prop_ON_b_connecting (hN : 1 < N) {x : ℝ × ℝ} (hx : x ∈ boundedOrbits N) :
    IsZero N x ∨ ∃ p q, IsZero N p ∧ IsZero N q ∧ Vp N p < Vp N q ∧
      Tendsto (fun t => flowON N t x) atTop (𝓝 p) ∧
      Tendsto (fun t => flowON N t x) atBot (𝓝 q) := by
  have hxR : x ∈ Inv (flowON N) blockR := by rw [Inv_R_eq hN]; exact hx
  obtain ⟨p, q, hp, hq, hpT, hqT⟩ := tendsto_of_mem_Inv hN hxR
  by_cases hle : Vp N q ≤ Vp N p
  · exact Or.inl (isZero_of_V_le hN hxR hpT hqT hle)
  · exact Or.inr ⟨p, q, hp, hq, not_le.1 hle, hpT, hqT⟩

end ConleyCheck.ON
