import ConleyCheck.ON.RampLimits

/-!
# The Morse decomposition of `S♮` for the parameter shift

For `N_- > 4` and `1 < N_+ < 4`, the eight fixed points of the double, namely the four fixed
points of `f_+` in the IR row `u = 0` and the four fixed points of `f_-` in the UV row `u = 1`,
form a Morse decomposition of `S♮` (`isMorseDecomp`). The order is the one of Corollary `cor:ON`
in each row, and an IR point lies below a UV point unless the UV point is `Σ_G^-` and the IR point
is not `Σ_G^+`, or the UV point is `Σ_I^-` and the IR point is `Σ_C^+` or `Σ_H^+`.

The two exclusions are rigidity statements. An orbit with `α`-limit `Σ_G^-` is `y ≡ 0`, and an
orbit with `α`-limit `Σ_I^-` stays on the axis `y_2 = 0` (`eq_zero_of_tendsto_atBot`,
`snd_eq_zero_of_tendsto_atBot`).
-/

open Set Filter Topology Metric Function

namespace ConleyCheck.ON

open ConleyCheck.Conley ConleyCheck.ODE

theorem omegaLim_eq_of_tendsto {α : Type*} [TopologicalSpace α] [T2Space α] {ϕ : Flow ℝ α}
    {x z : α} (h : Tendsto (fun t => ϕ t x) atTop (𝓝 z)) : omegaLim ϕ x = {z} := by
  ext y
  show y ∈ omegaLimit atTop ϕ.toFun {x} ↔ y ∈ ({z} : Set α)
  rw [mem_omegaLimit_singleton_iff_mapClusterPt, mem_singleton_iff]
  exact ⟨fun hy => eq_of_nhds_neBot (hy.neBot.mono (inf_le_inf_left _ h)),
    by rintro rfl; exact h.mapClusterPt⟩

theorem alphaLim_eq_of_tendsto {α : Type*} [TopologicalSpace α] [T2Space α] {ϕ : Flow ℝ α}
    {x z : α} (h : Tendsto (fun t => ϕ t x) atBot (𝓝 z)) : alphaLim ϕ x = {z} := by
  ext y
  show y ∈ omegaLimit atBot ϕ.toFun {x} ↔ y ∈ ({z} : Set α)
  rw [mem_omegaLimit_singleton_iff_mapClusterPt, mem_singleton_iff]
  exact ⟨fun hy => eq_of_nhds_neBot (hy.neBot.mono (inf_le_inf_left _ h)),
    by rintro rfl; exact h.mapClusterPt⟩

theorem pts_fixed {N : ℝ} (hN : 1 < N) (i : Fin 4) (t : ℝ) : flowON N t (pts N i) = pts N i :=
  flowON_fixed (interior_subset (inner_subset_R hN (zero_mem_inner hN (isZero_pts hN i))))
    (isZero_pts hN i) t

/-- In a row with a Morse decomposition by the fixed points, every orbit of `B_N` converges to
fixed points `i, j` with `i` below `j`, or is the fixed point `i = j`. -/
theorem row_limits {N : ℝ} (hN : 1 < N) {σ : Fin 4 → Fin 4}
    (hM : IsMorseDecomp (flowON N) (boundedOrbits N) (fun i => {pts N (σ i)}) diamond)
    {y : ℝ × ℝ} (hy : y ∈ boundedOrbits N) :
    ∃ i j, Tendsto (fun t => flowON N t y) atTop (𝓝 (pts N (σ i))) ∧
      Tendsto (fun t => flowON N t y) atBot (𝓝 (pts N (σ j))) ∧
      (diamond i j ∨ y = pts N (σ i) ∧ i = j) := by
  by_cases hfix : ∃ i, y = pts N (σ i)
  · obtain ⟨i, rfl⟩ := hfix
    have hc : (fun t => flowON N t (pts N (σ i))) = fun _ => pts N (σ i) :=
      funext fun t => pts_fixed hN _ t
    rw [hc]
    exact ⟨i, i, tendsto_const_nhds, tendsto_const_nhds, Or.inr ⟨rfl, rfl⟩⟩
  · simp only [not_exists] at hfix
    obtain ⟨i, j, hij, hω, hα⟩ := hM.connecting y hy fun i h => hfix i (mem_singleton_iff.1 h)
    obtain ⟨p, q, -, -, hp, hq⟩ := tendsto_of_mem_Inv hN (by rwa [Inv_R_eq hN])
    have e1 : p = pts N (σ i) := hω (by rw [omegaLim_eq_of_tendsto hp]; exact mem_singleton _)
    have e2 : q = pts N (σ j) := hα (by rw [alphaLim_eq_of_tendsto hq]; exact mem_singleton _)
    exact ⟨i, j, e1 ▸ hp, e2 ▸ hq, Or.inl hij⟩

theorem σgt_σgt : ∀ i, σgt (σgt i) = i := by decide

namespace Ramp

variable (P : Ramp)

/-! ## The eight fixed points and their order -/

/-- The labels of the fixed points of the double, `(false, i)` in the IR row and `(true, j)` in
the UV row, with the indices `0, 1, 2, 3` for `G, I, C, H`. -/
abbrev Lab : Type := Bool × Fin 4

/-- The fixed points of the double. -/
noncomputable def pt : Lab → (ℝ × ℝ) × Dbl
  | (false, i) => (pts (P.N 1) i, Dbl.zero)
  | (true, j) => (pts (P.N (-1)) j, Dbl.one)

/-- `diamond` as a Boolean function. -/
def dmd (i j : Fin 4) : Bool := (i == 0 && j != 0) || (j == 3 && i != 3)

theorem dmd_of_diamond {i j : Fin 4} (h : diamond i j) : dmd i j = true := by
  revert i j; unfold dmd diamond; decide

/-- The order on the labels. -/
def relb : Lab → Lab → Bool
  | (false, i), (false, j) => dmd i j
  | (true, i), (true, j) => dmd (σgt i) (σgt j)
  | (false, i), (true, j) => j == 2 || j == 3 || i == 0 || (j == 1 && i == 1)
  | (true, _), (false, _) => false

/-- The order on the labels. -/
def rel (a b : Lab) : Prop := relb a b = true

theorem rel_irrefl : ∀ a, ¬ rel a a := by unfold rel; decide

theorem rel_trans : ∀ a b c, rel a b → rel b c → rel a c := by unfold rel; decide

theorem rel_cross {i j : Fin 4} (h0 : j = 0 → i = 0) (h1 : j = 1 → i = 0 ∨ i = 1) :
    rel (false, i) (true, j) := by
  revert i j; unfold rel; decide

/-! ## Orbits of the double -/

theorem D_zero (y : ℝ × ℝ) (t : ℝ) : P.D t (y, Dbl.zero) = (flowON (P.N 1) t y, Dbl.zero) := by
  simp only [dblΦ_apply, dblQ_apply, tentT_zero, flow_top, dblFlow_zero]

theorem D_one (y : ℝ × ℝ) (t : ℝ) : P.D t (y, Dbl.one) = (flowON (P.N (-1)) t y, Dbl.one) := by
  simp only [dblΦ_apply, dblQ_apply, tentT_one, flow_bot, dblFlow_one]

theorem D_pt (a : Lab) (t : ℝ) : P.D t (P.pt a) = P.pt a := by
  rcases a with ⟨_ | _, i⟩
  · show P.D t (pts (P.N 1) i, Dbl.zero) = (pts (P.N 1) i, Dbl.zero)
    rw [D_zero, pts_fixed P.one_lt_top]
  · show P.D t (pts (P.N (-1)) i, Dbl.one) = (pts (P.N (-1)) i, Dbl.one)
    rw [D_one, pts_fixed P.one_lt_bot]

theorem tendsto_dbl_zero {u : Dbl} (h0 : 0 < (u : ℝ)) (h1 : (u : ℝ) < 1) :
    Tendsto (fun t => dblFlow P.isHeight_θ t u) atTop (𝓝 Dbl.zero) := by
  rw [tendsto_subtype_rng]
  refine Metric.tendsto_nhds.2 fun ε hε => eventually_atTop.2 ?_
  obtain ⟨T1, hT1⟩ := dblFlow_tendsto0_upper P.isHeight_θ (by linarith) h1 hε
  obtain ⟨T2, hT2⟩ := dblFlow_tendsto0_lower P.isHeight_θ (by linarith) h1 hε
  refine ⟨max T1 T2, fun t ht => ?_⟩
  have a := hT1 t (le_of_max_le_left ht)
  have b := hT2 t (le_of_max_le_right ht)
  rw [Real.dist_eq, abs_lt]
  show -ε < (dblFlow P.isHeight_θ t u : ℝ) - 0 ∧ (dblFlow P.isHeight_θ t u : ℝ) - 0 < ε
  constructor <;> linarith

theorem tendsto_dbl_one {u : Dbl} (h0 : 0 < (u : ℝ)) (h1 : (u : ℝ) < 1) :
    Tendsto (fun t => dblFlow P.isHeight_θ t u) atBot (𝓝 Dbl.one) := by
  rw [tendsto_subtype_rng]
  refine Metric.tendsto_nhds.2 fun ε hε => eventually_atBot.2 ?_
  obtain ⟨T1, hT1⟩ := dblFlow_tendsto1_upper P.isHeight_θ h0 (by linarith) hε
  obtain ⟨T2, hT2⟩ := dblFlow_tendsto1_lower P.isHeight_θ h0 (by linarith) hε
  refine ⟨min T1 T2, fun t ht => ?_⟩
  have a := hT1 t (le_of_le_min_left ht)
  have b := hT2 t (le_of_le_min_right ht)
  rw [Real.dist_eq, abs_lt]
  show -ε < (dblFlow P.isHeight_θ t u : ℝ) - 1 ∧ (dblFlow P.isHeight_θ t u : ℝ) - 1 < ε
  constructor <;> linarith

theorem snd_pts_ne {N : ℝ} (hN : 1 < N) {i : Fin 4} (h : (pts N i).2 = 0) : i = 0 ∨ i = 1 := by
  have hN0 : 0 < N := by linarith
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd h (show (ptC N).2 ≠ 0 by
      simp only [ptC]; exact div_ne_zero (by norm_num) (by positivity))
  · exact absurd h (show (ptH N).2 ≠ 0 by
      simp only [ptH]; exact div_ne_zero (by norm_num) (by positivity))

/-- Every orbit of `S♮` converges to fixed points `a, b` of the double with `a` below `b`, or is
the fixed point `a = b`. -/
theorem limits (h4m : 4 < P.N (-1)) (h4p : P.N 1 < 4) {x : (ℝ × ℝ) × Dbl} (hx : x ∈ snat P.S) :
    ∃ a b, Tendsto (fun t => P.D t x) atTop (𝓝 (P.pt a)) ∧
      Tendsto (fun t => P.D t x) atBot (𝓝 (P.pt b)) ∧ (rel a b ∨ x = P.pt a ∧ a = b) := by
  obtain ⟨y, u⟩ := x
  obtain ⟨hS, h0, h1⟩ := hx
  rcases h0.eq_or_lt with h0 | h0
  · have hu : u = Dbl.zero := Subtype.ext h0.symm
    subst hu
    have hy : y ∈ boundedOrbits (P.N 1) := by
      rw [← P.Kp_eq]
      show (y, Tau.top) ∈ P.S
      rw [← tentT_zero]; exact hS
    obtain ⟨i, j, hi, hj, hij⟩ := row_limits P.one_lt_top (isMorseDecomp_lt P.one_lt_top h4p) hy
    refine ⟨(false, i), (false, j), ?_, ?_, ?_⟩
    · simp only [D_zero]; exact hi.prodMk_nhds tendsto_const_nhds
    · simp only [D_zero]; exact hj.prodMk_nhds tendsto_const_nhds
    · rcases hij with h | ⟨e, rfl⟩
      · exact Or.inl (dmd_of_diamond h)
      · exact Or.inr ⟨by rw [e]; rfl, rfl⟩
  rcases h1.eq_or_lt with h1 | h1
  · have hu : u = Dbl.one := Subtype.ext h1
    subst hu
    have hy : y ∈ boundedOrbits (P.N (-1)) := by
      rw [← P.Km_eq]
      show (y, Tau.bot) ∈ P.S
      rw [← tentT_one]; exact hS
    obtain ⟨i, j, hi, hj, hij⟩ := row_limits P.one_lt_bot (isMorseDecomp_gt h4m) hy
    refine ⟨(true, σgt i), (true, σgt j), ?_, ?_, ?_⟩
    · simp only [D_one]; exact hi.prodMk_nhds tendsto_const_nhds
    · simp only [D_one]; exact hj.prodMk_nhds tendsto_const_nhds
    · rcases hij with h | ⟨e, rfl⟩
      · left
        show dmd (σgt (σgt i)) (σgt (σgt j)) = true
        rw [σgt_σgt, σgt_σgt]; exact dmd_of_diamond h
      · exact Or.inr ⟨by rw [e]; rfl, rfl⟩
  set p := dblQ (y, u) with hpdef
  have hb1 : -1 < (p.2 : ℝ) := neg_one_lt_tent (by linarith) h1
  have hb2 : (p.2 : ℝ) < 1 := tent_lt_one_of_pos h0 (by linarith)
  obtain ⟨qp, hqp, hT⟩ := P.tendsto_atTop hS hb1
  obtain ⟨qm, hqm, hB⟩ := P.tendsto_atBot hS hb2
  obtain ⟨i, rfl⟩ := exists_pts_eq P.one_lt_top hqp
  obtain ⟨j, rfl⟩ := exists_pts_eq P.one_lt_bot hqm
  have hTf : Tendsto (fun s => (P.Φ s p).1) atTop (𝓝 (pts (P.N 1) i)) :=
    (continuous_fst.tendsto _).comp hT
  have hBf : Tendsto (fun s => (P.Φ s p).1) atBot (𝓝 (pts (P.N (-1)) j)) :=
    (continuous_fst.tendsto _).comp hB
  refine ⟨(false, i), (true, j), ?_, ?_, Or.inl (rel_cross ?_ ?_)⟩
  · show Tendsto (fun t => ((P.Φ t p).1, dblFlow P.isHeight_θ t u)) atTop
      (𝓝 (pts (P.N 1) i, Dbl.zero))
    exact hTf.prodMk_nhds (P.tendsto_dbl_zero h0 h1)
  · show Tendsto (fun t => ((P.Φ t p).1, dblFlow P.isHeight_θ t u)) atBot
      (𝓝 (pts (P.N (-1)) j, Dbl.one))
    exact hBf.prodMk_nhds (P.tendsto_dbl_one h0 h1)
  · rintro rfl
    have hz := P.eq_zero_of_tendsto_atBot hS hBf
    have hf0 : Tendsto (fun s => (P.Φ s p).1) atTop (𝓝 0) := by
      simp only [hz]; exact tendsto_const_nhds
    exact pts_injective P.one_lt_top h4p.ne (tendsto_nhds_unique hTf hf0)
  · rintro rfl
    have hz := P.snd_eq_zero_of_tendsto_atBot hS hBf
    have hT2 : Tendsto (fun s => ((P.Φ s p).1).2) atTop (𝓝 (pts (P.N 1) i).2) :=
      (continuous_snd.tendsto _).comp hTf
    have hf0 : Tendsto (fun s => ((P.Φ s p).1).2) atTop (𝓝 0) := by
      simp only [hz]; exact tendsto_const_nhds
    exact snd_pts_ne P.one_lt_top (tendsto_nhds_unique hT2 hf0)

/-! ## The Morse decomposition -/

theorem isIsolated_S : IsIsolatedInvariantSet P.Φ P.S :=
  ⟨_, (IsUniformBlock.slab P.isUniformBlock_R).isIsolatingNbhd, rfl⟩

theorem isIsolated_snat : IsIsolatedInvariantSet P.D (snat P.S) :=
  (snat_attractorRepeller P.isSkew_Φ P.isHeight_θ P.isIsolated_S).1

theorem pt_mem (a : Lab) : P.pt a ∈ snat P.S := by
  rcases a with ⟨_ | _, i⟩
  · have h : pts (P.N 1) i ∈ {x | (x, Tau.top) ∈ P.S} :=
      P.Kp_eq ▸ zero_mem_B P.one_lt_top (isZero_pts P.one_lt_top i)
    refine ⟨?_, ?_⟩
    · show (pts (P.N 1) i, tentT Dbl.zero) ∈ P.S
      rw [tentT_zero]; exact h
    · show (0 : ℝ) ∈ Icc (0 : ℝ) 1
      exact ⟨le_rfl, zero_le_one⟩
  · have h : pts (P.N (-1)) i ∈ {x | (x, Tau.bot) ∈ P.S} :=
      P.Km_eq ▸ zero_mem_B P.one_lt_bot (isZero_pts P.one_lt_bot i)
    refine ⟨?_, ?_⟩
    · show (pts (P.N (-1)) i, tentT Dbl.one) ∈ P.S
      rw [tentT_one]; exact h
    · show (1 : ℝ) ∈ Icc (0 : ℝ) 1
      exact ⟨zero_le_one, le_rfl⟩

theorem pt_injective (h4m : 4 < P.N (-1)) (h4p : P.N 1 < 4) : Injective P.pt := by
  rintro ⟨_ | _, i⟩ ⟨_ | _, j⟩ h
  · obtain rfl := pts_injective P.one_lt_top h4p.ne (congrArg Prod.fst h); rfl
  · have := congrArg (fun z => ((z.2 : Dbl) : ℝ)) h
    change (0 : ℝ) = 1 at this; norm_num at this
  · have := congrArg (fun z => ((z.2 : Dbl) : ℝ)) h
    change (1 : ℝ) = 0 at this; norm_num at this
  · obtain rfl := pts_injective P.one_lt_bot h4m.ne' (congrArg Prod.fst h); rfl

/-- Proposition `prop:ONramp`(i), second half: for `N_- > 4` and `1 < N_+ < 4`, the eight fixed
points of the double form a Morse decomposition of `S♮` for the order `rel`. -/
theorem isMorseDecomp (h4m : 4 < P.N (-1)) (h4p : P.N 1 < 4) :
    IsMorseDecomp P.D (snat P.S) (fun a => {P.pt a}) rel where
  isolated := P.isIsolated_snat
  isolated_M a := by
    refine isIsolated_of_limits (D := P.pt '' {b | b ≠ a}) P.isIsolated_snat
      (singleton_subset_iff.2 (P.pt_mem a)) isClosed_singleton ?_
      ((toFinite _).image _).isClosed ?_ ?_ ?_
    · intro t x hx
      rw [mem_singleton_iff.1 hx, P.D_pt]
      exact mem_singleton _
    · rintro _ ⟨b, -, rfl⟩; exact P.pt_mem b
    · rw [disjoint_singleton_left]
      rintro ⟨b, hb, e⟩
      exact hb (P.pt_injective h4m h4p e)
    · intro x hx hxa
      obtain ⟨a', b', hT, hB, hr⟩ := P.limits h4m h4p hx
      have hω : P.pt a' ∈ omegaLim P.D x := by
        rw [omegaLim_eq_of_tendsto hT]; exact mem_singleton _
      have hα : P.pt b' ∈ alphaLim P.D x := by
        rw [alphaLim_eq_of_tendsto hB]; exact mem_singleton _
      by_cases ha : a' = a
      · subst ha
        rcases hr with hr | ⟨e, -⟩
        · refine Or.inl ⟨_, hα, b', fun h => ?_, rfl⟩
          rw [show b' = a' from h] at hr
          exact rel_irrefl _ hr
        · exact absurd (mem_singleton_iff.2 e) hxa
      · exact Or.inr ⟨_, hω, a', ha, rfl⟩
  subset a := singleton_subset_iff.2 (P.pt_mem a)
  disjoint a b hab := disjoint_singleton.2 fun h => hab (P.pt_injective h4m h4p h)
  irrefl := rel_irrefl
  trans := rel_trans
  connecting x hx hM := by
    obtain ⟨a, b, hT, hB, hr⟩ := P.limits h4m h4p hx
    rcases hr with hr | ⟨e, -⟩
    · exact ⟨a, b, hr, (omegaLim_eq_of_tendsto hT).subset, (alphaLim_eq_of_tendsto hB).subset⟩
    · exact absurd (mem_singleton_iff.2 e) (hM a)

end Ramp

end ConleyCheck.ON
