import ConleyCheck.ON.Ramp
import ConleyCheck.ON.Connection

/-!
# Limit sets of the parameter shift

Every orbit of `S = Inv(R × [-1, 1])` with `-1 < τ` converges, as `s → ∞`, to a fixed point of the
frozen IR system `f_+` in the level `τ = 1`, and every orbit with `τ < 1` converges, as `s → -∞`,
to a fixed point of `f_-` in the level `τ = -1` (`tendsto_atTop`, `tendsto_atBot`).

Along a solution, `d/ds V_{N_+}(y) = -diss_{N_+}(y) + e(s)` with `e(s) → 0`, since `N(σ(s)) → N_+`.
At a level `m` of `V_{N_+}` that is not a critical value, the dissipation on `R ∩ {V_{N_+} = m}`
is bounded below by some `d > 0`, so once `|e| < d`, the solution cannot cross the level `m`
upward (`not_frequently_both`). Hence `V_{N_+}` is constant on the `ω`-limit set. This set is
invariant under `f_+`, so `V_{N_+}` is constant along `f_+`-orbits in it, and its points are fixed
points. Since there are finitely many, the orbit converges.
-/

open Set Filter Topology Metric Function
open scoped NNReal

namespace ConleyCheck.ON

open ConleyCheck.Conley ConleyCheck.ODE

/-- Along a solution of `eq:ONy` with parameter `n`, the derivative of `V` at parameter `N`. -/
theorem hasDerivAt_V_mixed {N n : ℝ} {y₁ y₂ : ℝ → ℝ} {s : ℝ}
    (h1 : HasDerivAt y₁ (f₁ n (y₁ s) (y₂ s)) s) (h2 : HasDerivAt y₂ (f₂ n (y₁ s) (y₂ s)) s) :
    HasDerivAt (fun t => V N (y₁ t) (y₂ t))
      (-diss N (y₁ s, y₂ s) + (n - N) * (y₂ s ^ 2 *
        (f₁ N (y₁ s) (y₂ s) + (N - 1) / 3 * f₂ N (y₁ s) (y₂ s)))) s := by
  have h := (((((h1.pow 2).const_mul (1 / 2 : ℝ)).add ((h2.pow 2).const_mul ((N - 1) / 6))).add
    ((h1.pow 3).const_mul (3 : ℝ))).add ((h1.mul (h2.pow 2)).const_mul (N - 1))).add
    ((h2.pow 3).const_mul ((N - 1) * (N + 2) / 9))
  convert h using 1
  · funext t; simp only [V, Pi.add_apply, Pi.pow_apply, Pi.mul_apply]; ring
  · simp only [diss, f₁, f₂, Pi.pow_apply]; push_cast; ring

/-- A function with `w' = -D + e`, `e → 0`, and `D ≥ d > 0` on the level `w = m`, cannot be
frequently below and frequently above `m` as `s → ∞`. -/
theorem not_frequently_both {w D e : ℝ → ℝ} (hw : ∀ s, HasDerivAt w (-D s + e s) s)
    (he : Tendsto e atTop (𝓝 0)) {m d : ℝ} (hd : 0 < d) (hD : ∀ s, w s = m → d ≤ D s)
    (h1 : ∃ᶠ s in atTop, w s < m) (h2 : ∃ᶠ s in atTop, m < w s) : False := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 he) d hd)
  obtain ⟨s₀, hs₀, hTs₀⟩ := (h1.and_eventually (eventually_ge_atTop T)).exists
  have hle : ∀ s, s₀ ≤ s → w s ≤ m := fun s hs => by
    have hb : ∀ x ∈ Ico s₀ s, w x = m → -D x + e x < 0 := fun x hx hwx => by
      have h1 := hD x hwx
      have h2 := hT x (hTs₀.trans hx.1)
      rw [Real.dist_eq, sub_zero] at h2
      linarith [le_abs_self (e x)]
    exact image_le_of_deriv_right_lt_deriv_boundary (f := w) (B := fun _ => m) (B' := fun _ => 0)
      (fun x _ => (hw x).continuousAt.continuousWithinAt) (fun x _ => (hw x).hasDerivWithinAt)
      hs₀.le (fun x => hasDerivAt_const x m) hb ⟨hs, le_rfl⟩
  obtain ⟨s, hs, hss⟩ := (h2.and_eventually (eventually_ge_atTop s₀)).exists
  exact absurd (hle s hss) (not_le.2 hs)

/-- Away from critical values, the dissipation is bounded below on a level set of `V` in `R`. -/
theorem exists_diss_lower {N : ℝ} (hN : 1 < N) {m : ℝ} (hm : ∀ p, IsZero N p → Vp N p ≠ m) :
    ∃ d > 0, ∀ y ∈ blockR, Vp N y = m → d ≤ diss N y := by
  have hc : IsCompact (blockR ∩ Vp N ⁻¹' {m}) :=
    (isCompact_Icc.prod isCompact_Icc).inter_right (isClosed_singleton.preimage (continuous_Vp N))
  have hcontd : Continuous (diss N) := by unfold diss f₁ f₂; fun_prop
  rcases (blockR ∩ Vp N ⁻¹' {m}).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun y hy hm' =>
      absurd (show y ∈ (∅ : Set (ℝ × ℝ)) from he ▸ ⟨hy, hm'⟩) (notMem_empty y)⟩
  · obtain ⟨z, hz, hmin⟩ := hc.exists_isMinOn hne hcontd.continuousOn
    have hz0 : diss N z ≠ 0 := fun h => hm z (isZero_of_diss_eq_zero hN h) hz.2
    exact ⟨diss N z, lt_of_le_of_ne (diss_nonneg hN z) (Ne.symm hz0),
      fun y hy hm' => hmin ⟨hy, hm'⟩⟩

/-- A value strictly between two reals avoiding the critical values of `V`. -/
theorem exists_regular_value {N : ℝ} (hN : 1 < N) {a b : ℝ} (hab : a < b) :
    ∃ m, a < m ∧ m < b ∧ ∀ p, IsZero N p → Vp N p ≠ m := by
  obtain ⟨m, ⟨hm1, hm2⟩, hmF⟩ :=
    ((Set.Ioo_infinite hab).sdiff ((finite_zeros hN).image (Vp N))).nonempty
  exact ⟨m, hm1, hm2, fun p hp he => hmF ⟨p, hp, he⟩⟩

namespace Ramp

variable (P : Ramp) {p : (ℝ × ℝ) × Tau}

/-- The parameter `N(σ(s))` along the orbit of `p`. -/
noncomputable def nn (p : (ℝ × ℝ) × Tau) (t : ℝ) : ℝ := P.Nc (P.β t p.2)

theorem mem_R (hp : p ∈ P.S) (t : ℝ) : (P.Φ t p).1 ∈ blockR := (hp t).1

theorem isCompact_S : IsCompact P.S :=
  isCompact_Inv ((isCompact_Icc.prod isCompact_Icc).prod isCompact_univ)

theorem isClosed_S : IsClosed P.S := P.isCompact_S.isClosed

theorem hasDerivAt_y (hp : p ∈ P.S) (t : ℝ) :
    HasDerivAt (fun s => (P.Φ s p).1) (field (P.nn p t) (P.Φ t p).1) t := by
  have h := P.hasDerivAt_Φ_fst p t
  rwa [cutField_eq (norm_le_one_of_mem_R (P.mem_R hp t))] at h

theorem hasDerivAt_y₁ (hp : p ∈ P.S) (t : ℝ) :
    HasDerivAt (fun s => ((P.Φ s p).1).1)
      (f₁ (P.nn p t) ((P.Φ t p).1).1 ((P.Φ t p).1).2) t := by
  have h := hasFDerivAt_fst.comp_hasDerivAt t (P.hasDerivAt_y hp t)
  exact h

theorem hasDerivAt_y₂ (hp : p ∈ P.S) (t : ℝ) :
    HasDerivAt (fun s => ((P.Φ s p).1).2)
      (f₂ (P.nn p t) ((P.Φ t p).1).1 ((P.Φ t p).1).2) t := by
  have h := hasFDerivAt_snd.comp_hasDerivAt t (P.hasDerivAt_y hp t)
  exact h

/-- The error term `y₂² (f₁ + (M-1)/3 f₂)` of `hasDerivAt_V_mixed`, at parameter `M`. -/
noncomputable def errG (M : ℝ) (q : ℝ × ℝ) : ℝ :=
  q.2 ^ 2 * (f₁ M q.1 q.2 + (M - 1) / 3 * f₂ M q.1 q.2)

theorem continuous_errG (M : ℝ) : Continuous (errG M) := by unfold errG f₁ f₂; fun_prop

theorem hasDerivAt_Vy (hp : p ∈ P.S) (M t : ℝ) :
    HasDerivAt (fun s => Vp M (P.Φ s p).1)
      (-diss M (P.Φ t p).1 + (P.nn p t - M) * errG M (P.Φ t p).1) t :=
  hasDerivAt_V_mixed (P.hasDerivAt_y₁ hp t) (P.hasDerivAt_y₂ hp t)

theorem tendsto_β_atTop {b : Tau} (hb : -1 < (b : ℝ)) :
    Tendsto (fun t => P.β t b) atTop (𝓝 1) :=
  Metric.tendsto_atTop.2 fun ε hε => by
    obtain ⟨a₀, ha⟩ := base_tendsto_top P.isHeight_θ hb hε
    refine ⟨a₀, fun a ha' => ?_⟩
    have h1 : 1 - ε < P.β a b := ha a ha'
    have h2 := (P.β_mem b.2 a).2
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith

theorem tendsto_β_atBot {b : Tau} (hb : (b : ℝ) < 1) :
    Tendsto (fun t => P.β t b) atBot (𝓝 (-1)) :=
  Metric.tendsto_nhds.2 fun ε hε => by
    obtain ⟨a₀, ha⟩ := base_tendsto_bot P.isHeight_θ hb hε
    refine eventually_atBot.2 ⟨a₀, fun a ha' => ?_⟩
    have h1 : P.β a b < -1 + ε := ha a ha'
    have h2 := (P.β_mem b.2 a).1
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith

theorem tendsto_nn_atTop (hb : -1 < (p.2 : ℝ)) : Tendsto (P.nn p) atTop (𝓝 (P.N 1)) := by
  have h := (P.lipschitz_Nc.continuous.tendsto 1).comp (P.tendsto_β_atTop hb)
  rwa [Nc, clamp_of_mem (by norm_num)] at h

theorem tendsto_nn_atBot (hb : (p.2 : ℝ) < 1) : Tendsto (P.nn p) atBot (𝓝 (P.N (-1))) := by
  have h := (P.lipschitz_Nc.continuous.tendsto (-1)).comp (P.tendsto_β_atBot hb)
  rwa [Nc, clamp_of_mem (by norm_num)] at h

theorem exists_bound_errG (M : ℝ) : ∃ C, ∀ q ∈ blockR, ‖errG M q‖ ≤ C :=
  (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn (continuous_errG M).continuousOn

theorem tendsto_err {l : Filter ℝ} (hp : p ∈ P.S) {M : ℝ} (hn : Tendsto (P.nn p) l (𝓝 M)) :
    Tendsto (fun t => (P.nn p t - M) * errG M (P.Φ t p).1) l (𝓝 0) := by
  obtain ⟨C, hC⟩ := exists_bound_errG M
  have h0 : Tendsto (fun t => |P.nn p t - M| * C) l (𝓝 0) := by
    have h1 : Tendsto (fun t => P.nn p t - M) l (𝓝 0) := by simpa using hn.sub_const M
    have := ((continuous_abs.tendsto 0).comp h1).mul_const C
    simpa using this
  refine squeeze_zero_norm (fun t => ?_) h0
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hC _ (P.mem_R hp t)) (abs_nonneg _)

theorem one_lt_top : 1 < P.N 1 := P.one_lt 1 (by norm_num)

theorem one_lt_bot : 1 < P.N (-1) := P.one_lt (-1) (by norm_num)

theorem flow_top (q : ℝ × ℝ) (t : ℝ) : P.Φ t (q, Tau.top) = (flowON (P.N 1) t q, Tau.top) := by
  refine Prod.ext ?_ (Subtype.ext (P.β_one t))
  rw [← P.fiber_top]
  rfl

theorem flow_bot (q : ℝ × ℝ) (t : ℝ) :
    P.Φ t (q, Tau.bot) = (flowON (P.N (-1)) t q, Tau.bot) := by
  refine Prod.ext ?_ (Subtype.ext (P.β_neg_one t))
  rw [← P.fiber_bot]
  rfl

theorem mem_Inv_top {q : ℝ × ℝ} (h : (q, Tau.top) ∈ P.S) : q ∈ Inv (flowON (P.N 1)) blockR := by
  rw [Inv_R_eq P.one_lt_top, ← P.Kp_eq]; exact h

theorem mem_Inv_bot {q : ℝ × ℝ} (h : (q, Tau.bot) ∈ P.S) :
    q ∈ Inv (flowON (P.N (-1))) blockR := by
  rw [Inv_R_eq P.one_lt_bot, ← P.Km_eq]; exact h

theorem isZero_of_const {M : ℝ} (hM : 1 < M) {q : ℝ × ℝ} (hq : q ∈ Inv (flowON M) blockR)
    (h : ∀ t, Vp M (flowON M t q) = Vp M q) : IsZero M q := by
  have hd := hasDerivAt_Vp_flow hq 0
  rw [show (fun s => Vp M (flowON M s q)) = fun _ => Vp M q from funext h,
    Flow.map_zero_apply] at hd
  have := hd.unique (hasDerivAt_const 0 _)
  exact isZero_of_diss_eq_zero hM (by linarith)

/-- Forward limits: an orbit of `S` with `-1 < τ` converges to a fixed point of `f_+` in the
level `τ = 1`. -/
theorem tendsto_atTop (hp : p ∈ P.S) (hb : -1 < (p.2 : ℝ)) :
    ∃ q, IsZero (P.N 1) q ∧ Tendsto (fun s => P.Φ s p) atTop (𝓝 (q, Tau.top)) := by
  set M := P.N 1
  have hM : 1 < M := P.one_lt_top
  have hΩS : omegaLim P.Φ p ⊆ P.S :=
    omegaLim_subset_of_invariant P.Φ P.isClosed_S (fun z hz t => flow_mem_Inv hz t) hp
  have hΩtop : ∀ z ∈ omegaLim P.Φ p, z.2 = Tau.top := fun z hz =>
    Subtype.ext ((P.isSkew_Φ.isHeight P.isHeight_θ).omegaLim_top hb hz)
  have hlevel : ∀ z₁ ∈ omegaLim P.Φ p, ∀ z₂ ∈ omegaLim P.Φ p, ¬ Vp M z₁.1 < Vp M z₂.1 := by
    intro z₁ h₁ z₂ h₂ hlt
    obtain ⟨m, hm1, hm2, hmF⟩ := exists_regular_value hM hlt
    obtain ⟨d, hd, hdD⟩ := exists_diss_lower hM hmF
    have hO : ∀ c : ℝ, IsOpen {z : (ℝ × ℝ) × Tau | Vp M z.1 < c} := fun c =>
      isOpen_lt ((continuous_Vp M).comp continuous_fst) continuous_const
    have hO' : ∀ c : ℝ, IsOpen {z : (ℝ × ℝ) × Tau | c < Vp M z.1} := fun c =>
      isOpen_lt continuous_const ((continuous_Vp M).comp continuous_fst)
    exact not_frequently_both (w := fun s => Vp M (P.Φ s p).1)
      (D := fun s => diss M (P.Φ s p).1) (e := fun s => (P.nn p s - M) * errG M (P.Φ s p).1)
      (fun s => P.hasDerivAt_Vy hp M s) (P.tendsto_err hp (P.tendsto_nn_atTop hb)) hd
      (fun s hs => hdD _ (P.mem_R hp s) hs)
      (frequently_of_mem_omegaLim P.Φ h₁ ((hO m).mem_nhds hm1))
      (frequently_of_mem_omegaLim P.Φ h₂ ((hO' m).mem_nhds hm2))
  have hzero : ∀ z ∈ omegaLim P.Φ p, IsZero M z.1 := by
    intro z hz
    have hz2 := hΩtop z hz
    have hze : z = (z.1, Tau.top) := Prod.ext rfl hz2
    have hq := P.mem_Inv_top (hze ▸ hΩS hz)
    refine isZero_of_const hM hq fun t => ?_
    have h := omegaLim_invariant P.Φ hz t
    rw [hze, P.flow_top] at h
    have hz' : (z.1, Tau.top) ∈ omegaLim P.Φ p := hze ▸ hz
    exact le_antisymm (not_lt.1 (hlevel _ hz' _ h)) (not_lt.1 (hlevel _ h (z.1, Tau.top) hz'))
  obtain ⟨_, ⟨q, hq, rfl⟩, ht⟩ := tendsto_of_mapClusterPt_finite (γ := fun s => P.Φ s p)
    (P.Φ.continuous continuous_id continuous_const) ((finite_zeros hM).image
      (fun q => (q, Tau.top))) P.isCompact_S (fun t => flow_mem_Inv hp t) fun z hz => by
      have hzΩ : z ∈ omegaLim P.Φ p :=
        (mem_omegaLimit_singleton_iff_mapClusterPt (f := atTop) (ϕ := P.Φ.toFun) p z).2 hz
      exact ⟨z.1, hzero z hzΩ, Prod.ext rfl (hΩtop z hzΩ).symm⟩
  exact ⟨q, hq, ht⟩

theorem frequently_neg {Q : ℝ → Prop} (h : ∃ᶠ t in atBot, Q t) : ∃ᶠ s in atTop, Q (-s) :=
  tendsto_neg_atBot_atTop.frequently (by simpa using h)

/-- Backward limits: an orbit of `S` with `τ < 1` converges to a fixed point of `f_-` in the
level `τ = -1`. -/
theorem tendsto_atBot (hp : p ∈ P.S) (hb : (p.2 : ℝ) < 1) :
    ∃ q, IsZero (P.N (-1)) q ∧ Tendsto (fun s => P.Φ s p) atBot (𝓝 (q, Tau.bot)) := by
  set M := P.N (-1)
  have hM : 1 < M := P.one_lt_bot
  have hAS : alphaLim P.Φ p ⊆ P.S :=
    alphaLim_subset_of_invariant P.Φ P.isClosed_S (fun z hz t => flow_mem_Inv hz t) hp
  have hAbot : ∀ z ∈ alphaLim P.Φ p, z.2 = Tau.bot := fun z hz =>
    Subtype.ext ((P.isSkew_Φ.isHeight P.isHeight_θ).alphaLim_bot hb hz)
  have hlevel : ∀ z₁ ∈ alphaLim P.Φ p, ∀ z₂ ∈ alphaLim P.Φ p, ¬ Vp M z₁.1 < Vp M z₂.1 := by
    intro z₁ h₁ z₂ h₂ hlt
    obtain ⟨m, hm1, hm2, hmF⟩ := exists_regular_value hM hlt
    obtain ⟨d, hd, hdD⟩ := exists_diss_lower hM hmF
    have hO : ∀ c : ℝ, IsOpen {z : (ℝ × ℝ) × Tau | Vp M z.1 < c} := fun c =>
      isOpen_lt ((continuous_Vp M).comp continuous_fst) continuous_const
    have hO' : ∀ c : ℝ, IsOpen {z : (ℝ × ℝ) × Tau | c < Vp M z.1} := fun c =>
      isOpen_lt continuous_const ((continuous_Vp M).comp continuous_fst)
    have hw : ∀ s, HasDerivAt (fun s => -Vp M (P.Φ (-s) p).1)
        (-diss M (P.Φ (-s) p).1 + (P.nn p (-s) - M) * errG M (P.Φ (-s) p).1) s := fun s => by
      have h := ((P.hasDerivAt_Vy hp M (-s)).comp s (hasDerivAt_neg s)).neg
      convert h using 1
      · funext x; simp [Function.comp_def]
      · ring
    have he : Tendsto (fun s => (P.nn p (-s) - M) * errG M (P.Φ (-s) p).1) atTop (𝓝 0) :=
      (P.tendsto_err hp (P.tendsto_nn_atBot hb)).comp tendsto_neg_atTop_atBot
    exact not_frequently_both (w := fun s => -Vp M (P.Φ (-s) p).1)
      (D := fun s => diss M (P.Φ (-s) p).1) hw he (m := -m) hd
      (fun s hs => hdD _ (P.mem_R hp (-s)) (by linarith))
      ((frequently_neg (frequently_of_mem_alphaLim P.Φ h₂ ((hO' m).mem_nhds hm2))).mono
        fun s hs => by have hs' : m < Vp M (P.Φ (-s) p).1 := hs; linarith)
      ((frequently_neg (frequently_of_mem_alphaLim P.Φ h₁ ((hO m).mem_nhds hm1))).mono
        fun s hs => by have hs' : Vp M (P.Φ (-s) p).1 < m := hs; linarith)
  have hzero : ∀ z ∈ alphaLim P.Φ p, IsZero M z.1 := by
    intro z hz
    have hz2 := hAbot z hz
    have hze : z = (z.1, Tau.bot) := Prod.ext rfl hz2
    have hq := P.mem_Inv_bot (hze ▸ hAS hz)
    refine isZero_of_const hM hq fun t => ?_
    have h := alphaLim_invariant P.Φ hz t
    rw [hze, P.flow_bot] at h
    have hz' : (z.1, Tau.bot) ∈ alphaLim P.Φ p := hze ▸ hz
    exact le_antisymm (not_lt.1 (hlevel _ hz' _ h)) (not_lt.1 (hlevel _ h (z.1, Tau.bot) hz'))
  obtain ⟨_, ⟨q, hq, rfl⟩, ht⟩ := tendsto_of_mapClusterPt_finite (γ := fun s => P.Φ (-s) p)
    ((P.Φ.continuous continuous_id continuous_const).comp continuous_neg) ((finite_zeros hM).image
      (fun q => (q, Tau.bot))) P.isCompact_S (fun t => flow_mem_Inv hp (-t)) fun z hz => by
      have hzA : z ∈ alphaLim P.Φ p :=
        (mem_omegaLimit_singleton_iff_mapClusterPt (f := atBot) (ϕ := P.Φ.toFun) p z).2
          (hz.of_comp tendsto_neg_atTop_atBot)
      exact ⟨z.1, hzero z hzA, Prod.ext rfl (hAbot z hzA).symm⟩
  refine ⟨q, hq, ?_⟩
  have := ht.comp tendsto_neg_atBot_atTop
  simpa [Function.comp_def] using this

/-! ## Orbits leaving `Σ_G` and `Σ_I` -/

theorem Ψ_eq_of_isSol {γ : ℝ → (ℝ × ℝ) × ℝ} (hγ : IsSol P.V γ) (t₀ t : ℝ) :
    P.Ψ t (γ t₀) = γ (t + t₀) :=
  flowOf_eq_of_isSol _ _ hγ t₀ t

/-- `y ≡ 0` is a solution of the shifted system. -/
theorem Φ_zero (b : Tau) (t : ℝ) : (P.Φ t (0, b)).1 = 0 := by
  have hγ : IsSol P.V (fun s => ((0 : ℝ × ℝ), P.β s b)) := fun s => by
    have : P.V ((0 : ℝ × ℝ), P.β s b) = (0, P.gc (P.β s b)) := by
      simp [V, fieldA, field, f₁, f₂]
    rw [this]
    exact (hasDerivAt_const s (0 : ℝ × ℝ)).prodMk (P.hasDerivAt_β b s)
  have h := P.Ψ_eq_of_isSol hγ 0 t
  rw [add_zero] at h
  have e : ((0 : ℝ × ℝ), (b : ℝ)) = ((0 : ℝ × ℝ), P.β 0 b) := by rw [Flow.map_zero_apply]
  show (P.Ψ t ((0 : ℝ × ℝ), (b : ℝ))).1 = 0
  rw [e, h]

theorem nn_gt (p : (ℝ × ℝ) × Tau) (t : ℝ) : 1 < P.nn p t := P.one_lt _ (clamp_mem _)

theorem nn_le (p : (ℝ × ℝ) × Tau) (t : ℝ) : P.nn p t ≤ P.bN :=
  (le_abs_self _).trans (P.abs_Nc_le _)

/-- If `h' ≤ 0` on `(-∞, T]` and `h → 0` as `s → -∞`, then `h ≤ 0` on `(-∞, T]`. -/
theorem nonpos_of_deriv_nonpos {h h' : ℝ → ℝ} (hd : ∀ s, HasDerivAt h (h' s) s) {T : ℝ}
    (hneg : ∀ s ≤ T, h' s ≤ 0) (hlim : Tendsto h atBot (𝓝 0)) {s : ℝ} (hs : s ≤ T) : h s ≤ 0 := by
  have hmono : ∀ s', s' ≤ s → h s ≤ h s' := fun s' hs' =>
    image_le_of_deriv_right_le_deriv_boundary (f := h) (B := fun _ => h s') (B' := fun _ => 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => (hd x).hasDerivWithinAt)
      le_rfl continuousOn_const (fun x _ => hasDerivWithinAt_const x _ _)
      (fun x hx => hneg x (hx.2.le.trans hs)) ⟨hs', le_rfl⟩
  exact ge_of_tendsto hlim (eventually_atBot.2 ⟨s, hmono⟩)

/-- An orbit of `S` whose `y`-component tends to `Σ_G = 0` as `s → -∞` is the constant
solution `y ≡ 0`: near `0`, `|y|²` decreases along every frozen system. -/
theorem eq_zero_of_tendsto_atBot (hp : p ∈ P.S)
    (h : Tendsto (fun s => (P.Φ s p).1) atBot (𝓝 0)) (t : ℝ) : (P.Φ t p).1 = 0 := by
  set c := 1 / (9 * (P.bN + 7))
  have hb := P.bN_nonneg
  have hc : 0 < c := by positivity
  have hc9 : 9 * c ≤ 1 := by
    simp only [c]; rw [← mul_div_assoc, mul_one, div_le_one (by positivity)]; linarith
  have hcN : (2 * P.bN + 7) * c ≤ 1 := by
    simp only [c]; rw [← mul_div_assoc, mul_one, div_le_one (by positivity)]; linarith
  obtain ⟨T, hT⟩ := eventually_atBot.1 (h.eventually (closedBall_mem_nhds (0 : ℝ × ℝ) hc))
  set hf : ℝ → ℝ := fun s => ((P.Φ s p).1).1 ^ 2 + ((P.Φ s p).1).2 ^ 2
  have hd : ∀ s, HasDerivAt hf (2 * ((P.Φ s p).1).1 *
      f₁ (P.nn p s) ((P.Φ s p).1).1 ((P.Φ s p).1).2 + 2 * ((P.Φ s p).1).2 *
      f₂ (P.nn p s) ((P.Φ s p).1).1 ((P.Φ s p).1).2) s := fun s => by
    have := ((P.hasDerivAt_y₁ hp s).pow 2).add ((P.hasDerivAt_y₂ hp s).pow 2)
    convert this using 1
    simp only [Nat.cast_ofNat]; ring
  have hneg : ∀ s ≤ T, 2 * ((P.Φ s p).1).1 * f₁ (P.nn p s) ((P.Φ s p).1).1 ((P.Φ s p).1).2 +
      2 * ((P.Φ s p).1).2 * f₂ (P.nn p s) ((P.Φ s p).1).1 ((P.Φ s p).1).2 ≤ 0 := by
    intro s hs
    have hn1 := P.nn_gt p s
    have hn2 := P.nn_le p s
    have hball := hT s hs
    rw [dist_zero_right] at hball
    obtain ⟨h1, h2⟩ := norm_prod_le_iff.1 hball
    rw [Real.norm_eq_abs, abs_le] at h1 h2
    set a := ((P.Φ s p).1).1
    set b := ((P.Φ s p).1).2
    set n := P.nn p s
    have e : 2 * a * f₁ n a b + 2 * b * f₂ n a b =
        -2 * (a ^ 2 * (1 + 9 * a) + b ^ 2 * (1 + (n + 5) * a + (n + 2) * b)) := by
      simp only [f₁, f₂]; ring
    have f1 : 0 ≤ 1 + 9 * a := by nlinarith
    have f2 : 0 ≤ 1 + (n + 5) * a + (n + 2) * b := by nlinarith
    rw [e]
    have := mul_nonneg (sq_nonneg a) f1
    have := mul_nonneg (sq_nonneg b) f2
    linarith
  have hlim : Tendsto hf atBot (𝓝 0) := by
    have hc : Continuous fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2 := by fun_prop
    have := (hc.tendsto 0).comp h
    rw [show (0 : ℝ × ℝ).1 ^ 2 + (0 : ℝ × ℝ).2 ^ 2 = 0 by simp] at this
    exact this
  have hzero : ∀ s ≤ T, (P.Φ s p).1 = 0 := fun s hs => by
    have h0 : ((P.Φ s p).1).1 ^ 2 + ((P.Φ s p).1).2 ^ 2 ≤ 0 :=
      nonpos_of_deriv_nonpos hd hneg hlim hs
    set u := ((P.Φ s p).1).1
    set v := ((P.Φ s p).1).2
    have hu : u = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have hv : v = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    exact Prod.ext hu hv
  have e : P.Φ t p = P.Φ (t - T) (0, (P.Φ T p).2) := by
    rw [← hzero T le_rfl, ← Flow.map_add, sub_add_cancel]
  rw [e, Φ_zero]

/-- An orbit of `S` whose `y`-component tends to `Σ_I` as `s → -∞` lies on the invariant axis
`y₂ = 0`. -/
theorem snd_eq_zero_of_tendsto_atBot (hp : p ∈ P.S)
    (h : Tendsto (fun s => (P.Φ s p).1) atBot (𝓝 ptI)) (t : ℝ) : ((P.Φ t p).1).2 = 0 := by
  set c := 1 / (10 * (P.bN + 2))
  have hb := P.bN_nonneg
  have hc : 0 < c := by positivity
  have hcN : (P.bN + 2) * c = 1 / 10 := by
    simp only [c]; field_simp
  have hr : 0 < min (1 / 100 : ℝ) c := lt_min (by norm_num) hc
  obtain ⟨T, hT⟩ := eventually_atBot.1 (h.eventually (closedBall_mem_nhds ptI hr))
  set z : ℝ → ℝ := fun s => ((P.Φ s p).1).2
  have hd : ∀ s, HasDerivAt (fun s => z s ^ 2) (2 * z s *
      f₂ (P.nn p s) ((P.Φ s p).1).1 (z s)) s := fun s => by
    have := (P.hasDerivAt_y₂ hp s).pow 2
    convert this using 1
    simp only [Nat.cast_ofNat, z]; ring
  have hneg : ∀ s ≤ T, 2 * z s * f₂ (P.nn p s) ((P.Φ s p).1).1 (z s) ≤ 0 := by
    intro s hs
    have hn1 := P.nn_gt p s
    have hn2 := P.nn_le p s
    have hball := hT s hs
    rw [Prod.dist_eq, max_le_iff] at hball
    obtain ⟨h1, h2⟩ := hball
    rw [Real.dist_eq, abs_le] at h1 h2
    simp only [ptI] at h1 h2
    have hm1 := min_le_left (1 / 100 : ℝ) c
    have hm2 := min_le_right (1 / 100 : ℝ) c
    set a := ((P.Φ s p).1).1
    set b := z s
    set n := P.nn p s
    have e : 2 * b * f₂ n a b = -2 * (b ^ 2 * (1 + 6 * a + (n + 2) * b)) := by
      simp only [f₂]; ring
    have hb' : (n + 2) * b ≥ -(1 / 10) := by
      have : (n + 2) * b ≥ -((P.bN + 2) * c) := by nlinarith
      linarith
    have f2 : 0 ≤ 1 + 6 * a + (n + 2) * b := by nlinarith
    rw [e]
    have := mul_nonneg (sq_nonneg b) f2
    linarith
  have hlim : Tendsto (fun s => z s ^ 2) atBot (𝓝 0) := by
    have hc : Continuous fun q : ℝ × ℝ => q.2 ^ 2 := by fun_prop
    have := (hc.tendsto ptI).comp h
    rw [show ptI.2 ^ 2 = 0 by simp [ptI]] at this
    exact this
  have hT0 : z T = 0 := by
    have := nonpos_of_deriv_nonpos hd hneg hlim le_rfl
    nlinarith [sq_nonneg (z T)]
  -- `z' = a z` with a bounded coefficient, so `z ≡ 0`
  set a : ℝ → ℝ := fun s => -(1 + 6 * ((P.Φ s p).1).1 + (P.nn p s + 2) * z s)
  have hA : ∀ s, |a s| ≤ 9 + P.bN := fun s => by
    have hR := P.mem_R hp s
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hR
    simp only [δ] at h2 h4
    have hn1 := P.nn_gt p s
    have hn2 := P.nn_le p s
    have : |(P.nn p s + 2) * z s| ≤ P.bN + 2 := by
      rw [abs_mul, abs_of_pos (by linarith)]
      have : |z s| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      nlinarith [abs_nonneg (z s)]
    simp only [a]
    rw [abs_neg]
    have h6 : |6 * ((P.Φ s p).1).1| ≤ 6 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
      have : |((P.Φ s p).1).1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      linarith
    calc |1 + 6 * ((P.Φ s p).1).1 + (P.nn p s + 2) * z s|
        ≤ |1 + 6 * ((P.Φ s p).1).1| + |(P.nn p s + 2) * z s| := abs_add_le _ _
      _ ≤ (|(1 : ℝ)| + |6 * ((P.Φ s p).1).1|) + |(P.nn p s + 2) * z s| := by
          gcongr; exact abs_add_le _ _
      _ ≤ 9 + P.bN := by rw [abs_one]; linarith
  have hK : 0 ≤ 9 + P.bN := by linarith
  have hlip : ∀ s, LipschitzWith (⟨9 + P.bN, hK⟩ : ℝ≥0) (fun x => a s * x) := fun s =>
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
      show _ ≤ (9 + P.bN) * _
      exact mul_le_mul_of_nonneg_right (hA s) (abs_nonneg _)
  have hzsol : ∀ s, HasDerivAt z (a s * z s) s := fun s => by
    have := P.hasDerivAt_y₂ hp s
    convert this using 1
    simp only [a, f₂, z]; ring
  have heq := ODE_solution_unique_univ (v := fun s x => a s * x) (s := fun _ => univ)
    (f := z) (g := fun _ => 0) (t₀ := T) (fun s => (hlip s).lipschitzOnWith)
    (fun s => ⟨hzsol s, trivial⟩)
    (fun s => ⟨by simpa using hasDerivAt_const s (0 : ℝ), trivial⟩) hT0
  exact congrFun heq t

end Ramp

end ConleyCheck.ON
