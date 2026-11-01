import ConleyCheck.Bjorken
import ConleyCheck.ODE.SkewODE
import ConleyCheck.ODE.Triangular
import ConleyCheck.Conley.FaceUniform
import ConleyCheck.Conley.PointIndex
import ConleyCheck.Conley.SphereHomology
import ConleyCheck.Conley.OrbitTools
import ConleyCheck.Conley.Rate

/-!
# The Bjorken attractor solution as a connecting orbit

The compactified Bjorken equation `c' = -num k u c/(1 - c/20)`, with `u = (1 + τ)/2`, over a base
flow `τ' = g(τ)` on `[-1, 1]` (any rate: `g` Lipschitz, `g(±1) = 0`, `g > 0` inside), is cut off
away from the interval `N = [c_L, c_R]`, `c_L < c^-`, `0 < c_R < c^+`.

* `isUniformBlock_bj`: `N` is a common block with empty exit set.
* `Kbot_eq`, `Ktop_eq`: the ends are `K_- = {c^-}` and `K_+ = {0}`.
* `prop_bjorken_index`: `CH_*(K_±) ≅ Λ[0]`, `CH_*(S♮) = 0`, and the transport is an isomorphism.
* `prop_bjorken_exists`: an orbit with `-1 < τ < 1` runs from `(c^-, -1)` to `(0, 1)`.
* `prop_bjorken_unique`: it is the only orbit over a given base orbit with `c → c^-` as `τ → -1`.
* `prop_bjorken_ker`: the linearization along it has no nonzero bounded solution.

The invertibility of the linearized operator, via Proposition `prop:palmer`(ii)–(iii), is
`prop_bjorken_invertible` in `ConleyCheck.Palmer.BjorkenApp`.
-/

namespace ConleyCheck.Bjorken.Flow

open Set Function Filter Topology ConleyCheck.ODE ConleyCheck.Conley
open scoped NNReal

/-! ### Limits of orbits in a compact set -/

section Limits

variable {X : Type*} [TopologicalSpace X] [T2Space X] (ϕ : Flow ℝ X)

theorem tendsto_atBot_of_alphaLim_subset {x e : X} {C : Set X} (hC : IsCompact C)
    (hx : ∀ t, ϕ t x ∈ C) (h : alphaLim ϕ x ⊆ {e}) : Tendsto (fun t => ϕ t x) atBot (𝓝 e) := by
  intro U hU
  obtain ⟨V, hVU, hV, heV⟩ := mem_nhds_iff.1 hU
  have := eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset atBot ϕ.toFun
    {x} hC (Eventually.of_forall fun t y hy => by rw [mem_singleton_iff.1 hy]; exact hx t) hV
    (h.trans (singleton_subset_iff.2 heV))
  exact mem_map.2 (this.mono fun t ht => hVU (ht rfl))

theorem tendsto_atTop_of_omegaLim_subset {x e : X} {C : Set X} (hC : IsCompact C)
    (hx : ∀ t, ϕ t x ∈ C) (h : omegaLim ϕ x ⊆ {e}) : Tendsto (fun t => ϕ t x) atTop (𝓝 e) := by
  intro U hU
  obtain ⟨V, hVU, hV, heV⟩ := mem_nhds_iff.1 hU
  have := eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset atTop ϕ.toFun
    {x} hC (Eventually.of_forall fun t y hy => by rw [mem_singleton_iff.1 hy]; exact hx t) hV
    (h.trans (singleton_subset_iff.2 heV))
  exact mem_map.2 (this.mono fun t ht => hVU (ht rfl))

end Limits

/-! ### Rest points of a skew-product ODE on the boundary fibers -/

theorem Φ_rest (Q : SkewODE ℝ) {c₀ : ℝ} {b : Tau} (hb : (b : ℝ) = 1 ∨ (b : ℝ) = -1)
    (hF : Q.F (c₀, b) = 0) (t : ℝ) : Q.Φ t (c₀, b) = (c₀, b) := by
  have hβ : ∀ s, Q.β s b = b := fun s => by
    rcases hb with h | h <;> rw [h]
    · exact Q.β_one s
    · exact Q.β_neg_one s
  have hg : Q.g b = 0 := by rcases hb with h | h <;> rw [h]; exacts [Q.g_one, Q.g_neg_one]
  have hγ : IsSol Q.V fun _ => (c₀, (b : ℝ)) := fun s => by
    have := hasDerivAt_const s ((c₀, (b : ℝ)) : ℝ × ℝ)
    convert this using 1
    simp [SkewODE.V, hF, hg]
  have h := flowOf_eq_of_isSol Q.exists_lipschitz_V.choose_spec Q.exists_bound_V.choose_spec hγ 0 t
  refine Prod.ext ?_ (Subtype.ext (hβ t))
  have h1 := congrArg Prod.fst h
  exact h1

/-! ### The data and the cut-off field -/

/-- `k = 3/(2θ₀) > 0`, the interval `[c_L, c_R]`, and a rate `g`. -/
structure Data where
  k : ℝ
  cL : ℝ
  cR : ℝ
  g : ℝ → ℝ
  Kg : ℝ≥0
  hk : 0 < k
  hL : cL < cminus
  hR0 : 0 < cR
  hR : cR < cplus
  hg : LipschitzOnWith Kg g (Icc (-1) 1)
  g1 : g 1 = 0
  gm1 : g (-1) = 0
  gpos : ∀ τ ∈ Ioo (-1 : ℝ) 1, 0 < g τ

/-- The compactified Bjorken field at `τ`. -/
noncomputable def Fb (k c τ : ℝ) : ℝ := -num k ((1 + τ) / 2) c / (1 - c / 20)

variable (D : Data)

theorem cL_lt_cR : D.cL < D.cR := by linarith [D.hL, cminus_neg, D.hR0]

theorem cR_lt_20 : D.cR < 20 := D.hR.trans cplus_lt_20

theorem cL_lt_cm : D.cL < cminus := D.hL

theorem cm_lt_cR : cminus < D.cR := cminus_neg.trans D.hR0

/-- The interval `N = [c_L, c_R]`. -/
def N : Set ℝ := Icc D.cL D.cR

theorem den_pos {c : ℝ} (hc : c ∈ N D) : 0 < 1 - c / 20 := by
  have := hc.2; have := cR_lt_20 D; linarith

noncomputable def mC : ℝ := (D.cL + D.cR) / 2

noncomputable def bumpC : ContDiffBump (mC D) :=
  ⟨(D.cR - D.cL) / 2, (D.cR - D.cL) / 2 + (20 - D.cR) / 2, by linarith [cL_lt_cR D],
    by linarith [cR_lt_20 D]⟩

noncomputable def bumpT : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

theorem bumpC_eq_one {c : ℝ} (hc : c ∈ N D) : bumpC D c = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  show dist c (mC D) ≤ (D.cR - D.cL) / 2
  rw [Real.dist_eq, abs_le]; unfold mC; constructor <;> linarith [hc.1, hc.2]

theorem bumpC_eq_zero {c : ℝ} (hc : (20 + D.cR) / 2 ≤ c) : bumpC D c = 0 := by
  rw [← notMem_support, (bumpC D).support_eq]
  show ¬ dist c (mC D) < (D.cR - D.cL) / 2 + (20 - D.cR) / 2
  rw [Real.dist_eq]; unfold mC; intro h; have := (abs_lt.1 h).2; linarith

/-- The cut-off factor `bump(c)/(1 - c/20)`, smooth because the bump vanishes before `c = 20`. -/
noncomputable def ρ (c : ℝ) : ℝ := bumpC D c / (1 - c / 20)

theorem contDiff_ρ : ContDiff ℝ 1 (ρ D) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x < 20
  · exact (bumpC D).contDiff.contDiffAt.div (contDiffAt_const.sub (contDiffAt_id.div_const 20))
      (by show (1:ℝ) - x / 20 ≠ 0; intro h; linarith)
  · have : ρ D =ᶠ[𝓝 x] fun _ => 0 := by
      have : Ioi ((20 + D.cR) / 2) ∈ 𝓝 x := Ioi_mem_nhds (by linarith [cR_lt_20 D])
      filter_upwards [this] with c hc
      simp [ρ, bumpC_eq_zero D (le_of_lt hc)]
    exact contDiffAt_const.congr_of_eventuallyEq this

/-- The cut-off fiber field. -/
noncomputable def A (q : ℝ × ℝ) : ℝ := ρ D q.1 * bumpT q.2 * -num D.k ((1 + q.2) / 2) q.1

theorem contDiff_A : ContDiff ℝ 1 (A D) := by
  have h1 : ContDiff ℝ 1 fun q : ℝ × ℝ => ρ D q.1 := (contDiff_ρ D).comp contDiff_fst
  have h2 : ContDiff ℝ 1 fun q : ℝ × ℝ => bumpT q.2 := bumpT.contDiff.comp contDiff_snd
  have h3 : ContDiff ℝ 1 fun q : ℝ × ℝ => -num D.k ((1 + q.2) / 2) q.1 := by
    unfold num P; fun_prop
  exact (h1.mul h2).mul h3

theorem hasCompactSupport_A : HasCompactSupport (A D) := by
  refine HasCompactSupport.intro ((isCompact_closedBall (mC D)
    ((D.cR - D.cL) / 2 + (20 - D.cR) / 2)).prod (isCompact_closedBall (0 : ℝ) 2)) fun q hq => ?_
  by_contra hA
  apply hq
  have hC : bumpC D q.1 ≠ 0 := fun h => hA (by simp [A, ρ, h])
  have hT : bumpT q.2 ≠ 0 := fun h => hA (by simp [A, h])
  rw [← mem_support, (bumpC D).support_eq] at hC
  rw [← mem_support, bumpT.support_eq] at hT
  exact ⟨Metric.ball_subset_closedBall hC, Metric.ball_subset_closedBall hT⟩

/-- The cut-off compactified Bjorken system. -/
noncomputable def Pb : SkewODE ℝ :=
  SkewODE.ofSmooth (A D) (contDiff_A D) (hasCompactSupport_A D) D.g D.Kg D.hg D.g1 D.gm1 D.gpos

/-- On `N × [-1, 1]` the cut-off field is the compactified Bjorken field. -/
theorem Pb_F {c : ℝ} (hc : c ∈ N D) (τ : Tau) : (Pb D).F (c, τ) = Fb D.k c τ := by
  show A D (c, clamp τ) = _
  rw [clamp_of_mem τ.2]
  simp only [A, ρ]
  rw [bumpC_eq_one D hc, bumpT.one_of_mem_closedBall]
  · unfold Fb; ring
  · show dist (τ : ℝ) 0 ≤ 1
    rw [dist_zero_right, Real.norm_eq_abs]
    exact abs_le.2 ⟨τ.2.1, τ.2.2⟩

/-! ### The block -/

def gF : Fin 2 → ℝ → ℝ := ![fun c => D.cL - c, fun c => c - D.cR]

theorem N_eq : {c | ∀ j, gF D j c ≤ 0} = N D := by
  ext c
  simp only [mem_ofPred_eq, Fin.forall_fin_two, gF, Matrix.cons_val_zero, Matrix.cons_val_one,
    N, mem_Icc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem Lo_eq : {c | (∀ j, gF D j c ≤ 0) ∧ ∃ j ∈ (∅ : Set (Fin 2)), gF D j c = 0} = ∅ := by
  ext c; simp

noncomputable def DF : Fin 2 → ℝ → Tau → ℝ :=
  ![fun c τ => -(Pb D).F (c, τ), fun c τ => (Pb D).F (c, τ)]

theorem isUniformBlock_bj : IsUniformBlock (Pb D).Φ (N D) ∅ := by
  have h := isUniformBlock_of_faces (Φ := (Pb D).Φ) (g := gF D) (D := DF D) (E := ∅)
    (fun j => by fin_cases j <;> simp [gF] <;> fun_prop)
    (by rw [N_eq]; exact isCompact_Icc) ?_ (fun j hj => absurd hj (notMem_empty j)) ?_
  · rwa [N_eq, Lo_eq] at h
  · intro j c τ _
    have hd := (Pb D).hasDerivAt_Φ_fst (c, τ) 0
    simp only [Flow.map_zero_apply] at hd
    fin_cases j
    · exact hd.const_sub D.cL
    · exact hd.sub_const D.cR
  · intro j _ c τ hc h0
    have hcN : c ∈ N D := by rw [← N_eq]; exact hc
    have hu0 : 0 ≤ (1 + (τ : ℝ)) / 2 := by linarith [τ.2.1]
    have hu1 : (1 + (τ : ℝ)) / 2 ≤ 1 := by linarith [τ.2.2]
    have hf := faces D.hk D.hL D.hR0 D.hR hu0 hu1
    fin_cases j
    · have h1 : c = D.cL := by simp [gF] at h0; linarith
      show -(Pb D).F (c, τ) < 0
      rw [Pb_F D hcN, h1]; unfold Fb; linarith [hf.1]
    · have h1 : c = D.cR := by simp [gF] at h0; linarith
      show (Pb D).F (c, τ) < 0
      rw [Pb_F D hcN, h1]; unfold Fb; linarith [hf.2]

/-! ### The ends -/

/-- The invariant set of `N × [-1, 1]`. -/
def S : Set (ℝ × Tau) := Inv (Pb D).Φ (N D ×ˢ univ)

theorem mem_N_of_S {p : ℝ × Tau} (hp : p ∈ S D) (t : ℝ) : ((Pb D).Φ t p).1 ∈ N D := (hp t).1

theorem Fb_bot (k c : ℝ) : Fb k c (-1) = 1 / 5 * (c - cplus) * (c - cminus) / (1 - c / 20) := by
  unfold Fb num; rw [P_factor]; ring_nf

theorem Fb_top (k c : ℝ) : Fb k c 1 = -k * c / (1 - c / 20) := by
  unfold Fb num; ring_nf

theorem coef_le {n d dm α : ℝ} (hn : n ≤ -α) (hα : 0 < α) (hd : 0 < d) (hdm : d ≤ dm) :
    n / d ≤ -(α / dm) := by
  have h1 : n / d ≤ -α / d := div_le_div_of_nonneg_right hn hd.le
  have h2 : α / dm ≤ α / d := div_le_div_of_nonneg_left hα.le hd hdm
  rw [neg_div] at h1
  linarith

theorem dm_pos : 0 < 1 - D.cL / 20 := by
  have := cL_lt_cR D; have := cR_lt_20 D; linarith

/-- `K_- = {c^-}`. -/
theorem Kbot_eq : {x | (x, Tau.bot) ∈ S D} = {cminus} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · intro hx
    set c := fun t => ((Pb D).Φ t (x, Tau.bot)).1 with hc
    have hN : ∀ t, c t ∈ N D := fun t => mem_N_of_S D hx t
    have hθ : ∀ t, (Pb D).θ t Tau.bot = Tau.bot := fun t => Subtype.ext ((Pb D).β_neg_one t)
    set h := fun t => 1 / 5 * (c t - cplus) / (1 - c t / 20) with hh
    have hd : ∀ t, HasDerivAt (fun s => c s - cminus) (h t * (c t - cminus)) t := fun t => by
      have := ((Pb D).hasDerivAt_Φ_fst (x, Tau.bot) t).sub_const cminus
      convert this using 1
      rw [hθ, Pb_F D (hN t)]
      show _ = Fb D.k (c t) (-1)
      rw [Fb_bot, hh]
      field_simp [(den_pos D (hN t)).ne']
    have hcont : Continuous h := by
      have hc' : Continuous c := (Pb D).continuous_Φ_fst _
      exact Continuous.div (by fun_prop) (by fun_prop) fun t => (den_pos D (hN t)).ne'
    have hle : ∀ t, h t ≤ -((cplus - D.cR) / 5 / (1 - D.cL / 20)) := fun t => by
      have h1 := hN t
      show 1 / 5 * (c t - cplus) / (1 - c t / 20) ≤ _
      exact coef_le (by linarith [h1.2]) (by linarith [D.hR]) (den_pos D h1)
        (by linarith [h1.1])
    have hb : ∀ t, |c t - cminus| ≤ D.cR - D.cL := fun t => by
      have h1 := hN t
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, cL_lt_cm D, cm_lt_cR D]
    have := lin_zero_of_le (div_pos (div_pos (by linarith [D.hR] : (0:ℝ) < cplus - D.cR)
      (by norm_num)) (dm_pos D)) hd hcont hb hle 0
    have h0 : c 0 = x := by simp [hc]
    linarith
  · rintro rfl t
    refine ⟨?_, mem_univ _⟩
    have hcN : cminus ∈ N D := ⟨(cL_lt_cm D).le, (cm_lt_cR D).le⟩
    rw [Φ_rest (Pb D) (Or.inr rfl)]
    · exact hcN
    · rw [Pb_F D hcN]; show Fb D.k cminus (-1) = 0; rw [Fb_bot]; simp

/-- `K_+ = {0}`. -/
theorem Ktop_eq : {x | (x, Tau.top) ∈ S D} = {0} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · intro hx
    set c := fun t => ((Pb D).Φ t (x, Tau.top)).1 with hc
    have hN : ∀ t, c t ∈ N D := fun t => mem_N_of_S D hx t
    have hθ : ∀ t, (Pb D).θ t Tau.top = Tau.top := fun t => Subtype.ext ((Pb D).β_one t)
    set h := fun t => -D.k / (1 - c t / 20) with hh
    have hd : ∀ t, HasDerivAt c (h t * c t) t := fun t => by
      have := (Pb D).hasDerivAt_Φ_fst (x, Tau.top) t
      convert this using 1
      rw [hθ, Pb_F D (hN t)]
      show _ = Fb D.k (c t) 1
      rw [Fb_top, hh]
      ring
    have hcont : Continuous h := by
      have hc' : Continuous c := (Pb D).continuous_Φ_fst _
      exact continuous_const.div (by fun_prop) fun t => (den_pos D (hN t)).ne'
    have hle : ∀ t, h t ≤ -(D.k / (1 - D.cL / 20)) := fun t => by
      have h1 := hN t
      exact coef_le le_rfl D.hk (den_pos D h1) (by linarith [h1.1])
    have hb : ∀ t, |c t| ≤ |D.cL| + |D.cR| := fun t => by
      have h1 := hN t
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, le_abs_self D.cL, neg_abs_le D.cL, le_abs_self D.cR,
        neg_abs_le D.cR]
    have := lin_zero_of_le (div_pos D.hk (dm_pos D)) hd hcont hb hle 0
    simpa [hc] using this
  · rintro rfl t
    refine ⟨?_, mem_univ _⟩
    have hcN : (0 : ℝ) ∈ N D := ⟨by linarith [cL_lt_cm D, cminus_neg], D.hR0.le⟩
    rw [Φ_rest (Pb D) (Or.inl rfl)]
    · exact hcN
    · rw [Pb_F D hcN]; show Fb D.k 0 1 = 0; rw [Fb_top]; simp

/-- Proposition `prop:bjorken`, index part. For every `k > 0` and every rate, `N × [-1, 1]`
isolates `S`, the ends are `K_- = {c^-}` and `K_+ = {0}` with `CH_*(K_±) ≅ Λ[0]`, the double
`S♮` has trivial index and the transport `Ψ : CH_*(K_-) → CH_*(K_+)` is an isomorphism. -/
theorem prop_bjorken_index (K : Type) [Ring K] :
    IsIsolatingNbhd (Pb D).Φ (N D ×ˢ univ) ∧
      {x | (x, Tau.bot) ∈ S D} = {cminus} ∧ {x | (x, Tau.top) ∈ S D} = {0} ∧
      ∃ (hSn : IsIsolatedInvariantSet (dblΦ (Pb D).isSkew_Φ (Pb D).isHeight_θ) (snat (S D)))
        (hKp : IsIsolatedInvariantSet (fiberFlow (Pb D).isSkew_Φ Tau.top
          (base_top (Pb D).isHeight_θ)) {x | (x, Tau.top) ∈ S D})
        (hKm : IsIsolatedInvariantSet (fiberFlow (Pb D).isSkew_Φ Tau.bot
          (base_bot (Pb D).isHeight_θ)) {x | (x, Tau.bot) ∈ S D})
        (Ψ : ∀ k, homologyIndex K _ hKm k →ₗ[K] homologyIndex K _ hKp k)
        (i : ∀ k, homologyIndex K _ hKp k →ₗ[K] homologyIndex K _ hSn k)
        (p : ∀ k, homologyIndex K _ hSn (k + 1) →ₗ[K] homologyIndex K _ hKm k),
        (∀ k, Exact (Ψ k) (i k)) ∧ (∀ k, Exact (i (k + 1)) (p k)) ∧
        (∀ k, Exact (p k) (Ψ k)) ∧ (∀ k, Subsingleton (homologyIndex K _ hSn k)) ∧
        (∀ k, Bijective (Ψ k)) ∧
        Nonempty (homologyIndex K _ hKp 0 ≃ₗ[K] K) ∧
        (∀ n, n ≠ 0 → Subsingleton (homologyIndex K _ hKp n)) ∧
        Nonempty (homologyIndex K _ hKm 0 ≃ₗ[K] K) ∧
        (∀ n, n ≠ 0 → Subsingleton (homologyIndex K _ hKm n)) := by
  have hB := isUniformBlock_bj D
  obtain ⟨hN, -, -, hPT, hPB, -⟩ := rate_index (Pb D).isSkew_Φ (Pb D).isHeight_θ K hB
  have hx₀ : D.cL ∈ N D := ⟨le_rfl, (cL_lt_cR D).le⟩
  have hp := (hasIndex_sphere_zero_of_convex hx₀ (convex_Icc _ _) hPT).homologyIndex_sphere' K
  have hm := (hasIndex_sphere_zero_of_convex hx₀ (convex_Icc _ _) hPB).homologyIndex_sphere' K
  obtain ⟨hSn, hKp, hKm, Ψ, i, p, h1, h2, h3, h4, h5⟩ :=
    rate_transport (Pb D).isSkew_Φ (Pb D).isHeight_θ K hB
  exact ⟨hN, Kbot_eq D, Ktop_eq D, hSn, hKp, hKm, Ψ, i, p, h1, h2, h3, h4, h5, hp.1, hp.2, hm.1,
    hm.2⟩

/-! ### Existence and limits -/

theorem isCompact_NU : IsCompact (N D ×ˢ (univ : Set Tau)) := isCompact_Icc.prod isCompact_univ

/-- Proposition `prop:bjorken`, existence. Some orbit of `S` with `-1 < τ < 1` tends to
`(c^-, -1)` as `t → -∞` and to `(0, 1)` as `t → ∞`. -/
theorem prop_bjorken_exists :
    ∃ p ∈ S D, (p.2 : ℝ) ∈ Ioo (-1) 1 ∧
      Tendsto (fun t => (Pb D).Φ t p) atBot (𝓝 (cminus, Tau.bot)) ∧
      Tendsto (fun t => (Pb D).Φ t p) atTop (𝓝 (0, Tau.top)) := by
  have hB := isUniformBlock_bj D
  obtain ⟨-, -, -, -, hKp, -, -, -, -, -, -, -, -, -, ⟨e⟩, -, -, -⟩ := prop_bjorken_index D ℤ
  obtain ⟨-, hKp', hKm', -, -, hiso⟩ := rate_index (Pb D).isSkew_Φ (Pb D).isHeight_θ ℤ hB
  have hnt : ∃ k, Nontrivial (redH ℤ (IndexSpace (N D) ∅) (IndexSpace.pt (N D) ∅) k) :=
    ⟨0, ((hiso 0).1.some.symm.trans e).toEquiv.nontrivial⟩
  obtain ⟨p, hp, hτ, hω, hα⟩ := rate_connection (Pb D).isSkew_Φ (Pb D).isHeight_θ ℤ hB hnt
  refine ⟨p, hp, hτ, tendsto_atBot_of_alphaLim_subset _ (isCompact_NU D) hp ?_,
    tendsto_atTop_of_omegaLim_subset _ (isCompact_NU D) hp ?_⟩
  · intro q hq
    obtain ⟨hqS, hq2⟩ := hα hq
    have h2 : q.2 = Tau.bot := Subtype.ext hq2
    have h1 : q.1 ∈ {x | (x, Tau.bot) ∈ S D} := by
      show (q.1, Tau.bot) ∈ S D; rw [← h2]; exact hqS
    rw [Kbot_eq] at h1
    exact Prod.ext h1 h2
  · intro q hq
    obtain ⟨hqS, hq2⟩ := hω hq
    have h2 : q.2 = Tau.top := Subtype.ext hq2
    have h1 : q.1 ∈ {x | (x, Tau.top) ∈ S D} := by
      show (q.1, Tau.top) ∈ S D; rw [← h2]; exact hqS
    rw [Ktop_eq] at h1
    exact Prod.ext h1 h2

/-! ### The linearization -/

/-- `∂F/∂c` for the compactified Bjorken field. -/
noncomputable def Fc (k c τ : ℝ) : ℝ :=
  -((k * ((1 + τ) / 2) + (1 - (1 + τ) / 2) * (5 / 7 - 2 / 5 * c)) * (1 - c / 20) +
    num k ((1 + τ) / 2) c / 20) / (1 - c / 20) ^ 2

theorem hasDerivAt_Fb (k τ : ℝ) {c : ℝ} (hc : 1 - c / 20 ≠ 0) :
    HasDerivAt (fun x => Fb k x τ) (Fc k c τ) c := by
  set u := (1 + τ) / 2
  have hn : HasDerivAt (fun x => num k u x) (k * u + (1 - u) * (5 / 7 - 2 / 5 * c)) c :=
    hasDerivAt_of_cubic 0 (-(1 - u) / 5) (k * u + (1 - u) * (5 / 7)) (4 * (1 - u)) c _
      (fun y => by unfold num P; ring) (by ring)
  have hd : HasDerivAt (fun x : ℝ => 1 - x / 20) (-1 / 20) c :=
    hasDerivAt_of_cubic 0 0 (-1 / 20) 1 c _ (fun y => by ring) (by ring)
  have := hn.neg.div hd hc
  convert this using 1
  · funext x; rfl
  · simp only [Pi.neg_apply, u]; unfold Fc; ring

/-- On the interior of `N`, `Fc` is the derivative of the cut-off field in `c`. -/
theorem hasDerivAt_Pb_F {c : ℝ} (hc : c ∈ Ioo D.cL D.cR) (τ : Tau) :
    HasDerivAt (fun x => (Pb D).F (x, τ)) (Fc D.k c τ) c := by
  refine (hasDerivAt_Fb D.k τ (den_pos D (Ioo_subset_Icc_self hc)).ne').congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hc.1 hc.2] with x hx
  exact Pb_F D (Ioo_subset_Icc_self hx) τ

theorem Fc_cm (k : ℝ) : Fc k cminus (-1) = -(5 / 7 - 2 / 5 * cminus) / (1 - cminus / 20) := by
  have hq : 1 - cminus / 20 ≠ 0 := by intro h; linarith [cminus_neg]
  unfold Fc num
  rw [show (1 + (-1 : ℝ)) / 2 = 0 by norm_num, P_cminus, pow_two,
    div_eq_div_iff (mul_ne_zero hq hq) hq]
  ring

theorem Fc_cm_lt (k : ℝ) : Fc k cminus (-1) < -1 := by
  rw [Fc_cm, eig_cminus]; linarith [eig_signs.2.2.2]

theorem Fc_cont (k : ℝ) : ContinuousAt (fun q : ℝ × ℝ => Fc k q.1 q.2) (cminus, -1) := by
  unfold Fc num P
  exact ContinuousAt.div (by fun_prop) (by fun_prop)
    (by show (1 - cminus / 20) ^ 2 ≠ 0; exact pow_ne_zero 2 (by intro h; linarith [cminus_neg]))

theorem Fc_nbhd (k : ℝ) : ∃ r > 0, ∀ c τ, |c - cminus| < r → |τ + 1| < r → Fc k c τ < -1 / 2 := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 (Fc_cont k) (1 / 2) (by norm_num)
  refine ⟨δ, hδ, fun c τ hc hτ => ?_⟩
  have h1 := h (x := (c, τ)) (by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_neg_eq_add]
    exact max_lt hc hτ)
  rw [Real.dist_eq] at h1
  have := (abs_lt.1 h1).2
  linarith [Fc_cm_lt k]

/-- Product of increments of an antitone function. -/
theorem mul_sub_nonpos {f f' : ℝ → ℝ} {U : Set ℝ} (hU : Convex ℝ U)
    (hf : ∀ x ∈ U, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ U, f' x ≤ 0) {x y : ℝ} (hx : x ∈ U)
    (hy : y ∈ U) : (x - y) * (f x - f y) ≤ 0 := by
  have ha : AntitoneOn f U := antitoneOn_of_deriv_nonpos hU
    (fun z hz => (hf z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hf z (interior_subset hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(hf z (interior_subset hz)).deriv]; exact hf' z (interior_subset hz))
  rcases le_total x y with h | h
  · have := ha hx hy h; nlinarith
  · have := ha hy hx h; nlinarith

/-- Near `(c^-, -1)` every orbit over a base orbit with `τ → -1` is eventually in `N` with
`∂F/∂c < -1/2`. -/
theorem eventually_near {p : ℝ × Tau} (hb : (p.2 : ℝ) < 1)
    (hc : Tendsto (fun t => ((Pb D).Φ t p).1) atBot (𝓝 cminus)) {r : ℝ} (hr : 0 < r) :
    ∃ T, ∀ t ≤ T, |((Pb D).Φ t p).1 - cminus| < r ∧ |((Pb D).θ t p.2 : ℝ) + 1| < r := by
  obtain ⟨T₁, hT₁⟩ := base_tendsto_bot (Pb D).isHeight_θ hb hr
  obtain ⟨T₂, hT₂⟩ := eventually_atBot.1 (hc.eventually (Metric.ball_mem_nhds _ hr))
  refine ⟨min T₁ T₂, fun t ht => ⟨?_, ?_⟩⟩
  · have := hT₂ t (ht.trans (min_le_right _ _))
    simpa only [Metric.mem_ball, Real.dist_eq] using this
  · have h1 := hT₁ t (ht.trans (min_le_left _ _))
    have h2 := ((Pb D).θ t p.2).2.1
    rw [abs_lt]; constructor <;> linarith

/-- Proposition `prop:bjorken`, uniqueness. Two orbits over the same base point with `τ < 1`
whose fiber components tend to `c^-` as `t → -∞` coincide. -/
theorem prop_bjorken_unique {p p' : ℝ × Tau} (hpp : p.2 = p'.2) (hb : (p.2 : ℝ) < 1)
    (hc : Tendsto (fun t => ((Pb D).Φ t p).1) atBot (𝓝 cminus))
    (hc' : Tendsto (fun t => ((Pb D).Φ t p').1) atBot (𝓝 cminus)) : p = p' := by
  obtain ⟨r₀, hr₀, hFc⟩ := Fc_nbhd D.k
  set r := min r₀ (min (cminus - D.cL) (D.cR - cminus))
  have hr : 0 < r := lt_min hr₀ (lt_min (by linarith [cL_lt_cm D]) (by linarith [cm_lt_cR D]))
  have hrN : ∀ x, |x - cminus| < r → x ∈ N D := fun x hx => by
    have h1 := abs_lt.1 hx
    have h2 : r ≤ cminus - D.cL := (min_le_right _ _).trans (min_le_left _ _)
    have h3 : r ≤ D.cR - cminus := (min_le_right _ _).trans (min_le_right _ _)
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  obtain ⟨T₁, hT₁⟩ := eventually_near D hb hc hr
  obtain ⟨T₂, hT₂⟩ := eventually_near D (hpp ▸ hb) hc' hr
  set T := min T₁ T₂
  set c₁ := fun t => ((Pb D).Φ t p).1
  set c₂ := fun t => ((Pb D).Φ t p').1
  set z := fun t => (c₁ t - c₂ t) ^ 2
  have hθ : ∀ t, (Pb D).θ t p'.2 = (Pb D).θ t p.2 := fun t => by rw [hpp]
  have hz : ∀ t, HasDerivAt z (2 * (c₁ t - c₂ t) * ((Pb D).F (c₁ t, (Pb D).θ t p.2) -
      (Pb D).F (c₂ t, (Pb D).θ t p.2))) t := fun t => by
    have h1 := (Pb D).hasDerivAt_Φ_fst p t
    have h2 := (Pb D).hasDerivAt_Φ_fst p' t
    rw [hθ] at h2
    have := (h1.sub h2).pow 2
    convert this using 1
    simp only [c₁, c₂, Pi.sub_apply]
    push_cast; ring
  have hneg : ∀ t ≤ T, 2 * (c₁ t - c₂ t) * ((Pb D).F (c₁ t, (Pb D).θ t p.2) -
      (Pb D).F (c₂ t, (Pb D).θ t p.2)) ≤ 0 := fun t ht => by
    obtain ⟨h1, hτ⟩ := hT₁ t (ht.trans (min_le_left _ _))
    obtain ⟨h2, -⟩ := hT₂ t (ht.trans (min_le_right _ _))
    have hU : ∀ x ∈ Metric.ball cminus r, x ∈ N D := fun x hx => hrN x (by
      rwa [Metric.mem_ball, Real.dist_eq] at hx)
    have key := mul_sub_nonpos (f := fun x => Fb D.k x ((Pb D).θ t p.2))
      (f' := fun x => Fc D.k x ((Pb D).θ t p.2)) (convex_ball cminus r)
      (fun x hx => hasDerivAt_Fb D.k _ (den_pos D (hU x hx)).ne')
      (fun x hx => by
        rw [Metric.mem_ball, Real.dist_eq] at hx
        have := hFc x _ (hx.trans_le (min_le_left _ _)) (hτ.trans_le (min_le_left _ _))
        linarith)
      (x := c₁ t) (y := c₂ t) (by rwa [Metric.mem_ball, Real.dist_eq])
      (by rwa [Metric.mem_ball, Real.dist_eq])
    have e1 := Pb_F D (hrN _ h1) ((Pb D).θ t p.2)
    have e2 := Pb_F D (hrN _ h2) ((Pb D).θ t p.2)
    rw [e1, e2]
    nlinarith
  have hanti : AntitoneOn z (Iic T) := antitoneOn_of_deriv_nonpos (convex_Iic T)
    (fun t _ => (hz t).continuousAt.continuousWithinAt)
    (fun t _ => (hz t).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [(hz t).deriv]
      rw [interior_Iic] at ht
      exact hneg t (le_of_lt ht))
  have htend : Tendsto z atBot (𝓝 0) := by
    have := (hc.sub hc').pow 2
    simpa using this
  have hzT : z T ≤ 0 := ge_of_tendsto htend (eventually_atBot.2 ⟨T, fun t ht =>
    hanti (mem_Iic.2 ht) (mem_Iic.2 le_rfl) ht⟩)
  have heq1 : c₁ T = c₂ T := by
    have : (c₁ T - c₂ T) ^ 2 = 0 := le_antisymm hzT (sq_nonneg _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  have heq : (Pb D).Φ T p = (Pb D).Φ T p' :=
    Prod.ext heq1 (by rw [SkewODE.Φ_snd, SkewODE.Φ_snd, hpp])
  have := congrArg ((Pb D).Φ (-T)) heq
  rwa [← Flow.map_add, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply,
    Flow.map_zero_apply] at this

/-- Proposition `prop:bjorken`, hyperbolicity. Along an orbit of `S` with `τ < 1` and
`c → c^-` as `t → -∞`, the linearized equation `y' = (∂F/∂c) y` has no nonzero bounded
solution. -/
theorem prop_bjorken_ker {p : ℝ × Tau} (hp : p ∈ S D) (hb : (p.2 : ℝ) < 1)
    (hc : Tendsto (fun t => ((Pb D).Φ t p).1) atBot (𝓝 cminus)) {y : ℝ → ℝ}
    (hy : ∀ t, HasDerivAt y (Fc D.k ((Pb D).Φ t p).1 ((Pb D).θ t p.2) * y t) t) {B : ℝ}
    (hB : ∀ t, |y t| ≤ B) (t : ℝ) : y t = 0 := by
  obtain ⟨r, hr, hFc⟩ := Fc_nbhd D.k
  obtain ⟨T, hT⟩ := eventually_near D hb hc hr
  have hcc : Continuous fun s => ((Pb D).Φ s p).1 := (Pb D).continuous_Φ_fst p
  have hτc : Continuous fun s => ((Pb D).θ s p.2 : ℝ) := (Pb D).continuous_θ p.2
  have hcont : Continuous fun s => Fc D.k ((Pb D).Φ s p).1 ((Pb D).θ s p.2) := by
    unfold Fc num P
    exact Continuous.div (by fun_prop) (by fun_prop)
      fun s => pow_ne_zero 2 (den_pos D (mem_N_of_S D hp s)).ne'
  exact lin_zero_of_le_back (c := 1 / 2) (T := T) (by norm_num) hy hcont hB
    (fun s hs => by have := hFc _ _ (hT s hs).1 (hT s hs).2; linarith) t

end ConleyCheck.Bjorken.Flow
