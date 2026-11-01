import ConleyCheck.ON.RampLimits
import ConleyCheck.ON.Diagonal

/-!
# Proposition `prop:ONramp`(ii): rigidity of the diagonal

Along every solution of the parameter shift, the off-diagonal coordinate `w = y₁ - y₂` solves
`w' = -k w` with `k = 1 + 9 y₁ + 3 y₂` (times the cut-off), since
`f₁ - f₂ = -(1 + 9 y₁ + 3 y₂)(y₁ - y₂)` for every `N` (`f₁_sub_f₂`). At `Σ_H(N)` the coefficient is
`k = (N - 4)/(N + 8)`.

* `eq_diagonal_of_tendsto_atTop`: for `N₊ < 4`, `k < 0` near `Σ_H^+`, so `w` grows forward, and a
  solution converging to `Σ_H^+` as `s → ∞` lies on the diagonal. On the diagonal `p = -1/y₁` solves
  `p' = p - (N(σ(s)) + 8)` and is bounded, so it is `p_*`: the solution is the diagonal solution
  `eq:ONdiag`.
* `diag_of_tendsto_atBot`: for `N₋ > 4`, `k > 0` near `Σ_H^-`, so `w` grows backward, and a solution
  converging to `Σ_H^-` as `s → -∞` lies on the diagonal.
* `not_tendsto_I_or_C`: hence no solution runs from `Σ_H^-` to `Σ_I^+`, nor, if `N₊ ≠ 4`, to `Σ_C^+`,
  which do not lie on the diagonal.

These are statements about all orbits of the shifted flow `Φ`, not only those in `S`.
-/

open Real Set Filter Topology Metric
open scoped NNReal

namespace ConleyCheck.ON

open ConleyCheck.Conley ConleyCheck.ODE

theorem f₁_sub_f₂ (N a b : ℝ) : f₁ N a b - f₂ N a b = -((1 + 9 * a + 3 * b) * (a - b)) := by
  simp only [f₁, f₂]; ring

theorem f₁_diag (N a : ℝ) : f₁ N a a = -a * (1 + (N + 8) * a) := by
  simp only [f₁]; ring

/-- Near `Σ_H(N)`, the coefficient `1 + 9 y₁ + 3 y₂` is close to `(N - 4)/(N + 8)`, the
square `[-1, 1]²` is not left, and `y₁ < 0`. -/
theorem near_H {N r : ℝ} (hN : 1 < N) (hr : r ≤ 1 / (N + 8) / 8) {y : ℝ × ℝ}
    (hy : y ∈ closedBall (ptH N) r) :
    ‖y‖ ≤ 1 ∧ |1 + 9 * y.1 + 3 * y.2 - (1 - 12 * (1 / (N + 8)))| ≤ 12 * r ∧
      y.1 ≤ -(1 / (N + 8)) / 2 ∧ -(2 * (1 / (N + 8))) ≤ y.1 := by
  set u := 1 / (N + 8) with hu
  have hu0 : 0 < u := by positivity
  have hu9 : u < 1 / 9 := by rw [hu]; exact one_div_lt_one_div_of_lt (by norm_num) (by linarith)
  rw [mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq] at hy
  have e : (ptH N).1 = -u ∧ (ptH N).2 = -u := by simp [ptH, hu, neg_div]
  rw [e.1, e.2, sub_neg_eq_add, sub_neg_eq_add, abs_le, abs_le] at hy
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hy
  refine ⟨norm_prod_le_iff.2 ⟨?_, ?_⟩, ?_, by linarith, by linarith⟩
  · rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  · rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

namespace Ramp

variable (P : Ramp)

/-- The off-diagonal coordinate `y₁ - y₂` along the orbit of `p`. -/
noncomputable def offDiag (p : (ℝ × ℝ) × Tau) (s : ℝ) : ℝ := ((P.Φ s p).1).1 - ((P.Φ s p).1).2

/-- Its growth rate, `β(y) (1 + 9 y₁ + 3 y₂)` with the cut-off `β`. -/
noncomputable def kDiag (p : (ℝ × ℝ) × Tau) (s : ℝ) : ℝ :=
  bump (P.Φ s p).1 * (1 + 9 * ((P.Φ s p).1).1 + 3 * ((P.Φ s p).1).2)

theorem hasDerivAt_offDiag (p : (ℝ × ℝ) × Tau) (s : ℝ) :
    HasDerivAt (P.offDiag p) (-(P.kDiag p s * P.offDiag p s)) s := by
  have h := P.hasDerivAt_Φ_fst p s
  have h1 := (hasFDerivAt_fst (𝕜 := ℝ) (p := (P.Φ s p).1)).comp_hasDerivAt s h
  have h2 := (hasFDerivAt_snd (𝕜 := ℝ) (p := (P.Φ s p).1)).comp_hasDerivAt s h
  have e : (cutField (P.Nc (P.β s p.2)) (P.Φ s p).1).1 -
      (cutField (P.Nc (P.β s p.2)) (P.Φ s p).1).2 = -(P.kDiag p s * P.offDiag p s) := by
    simp only [cutField, field, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, kDiag, offDiag]
    rw [← mul_sub, f₁_sub_f₂]; ring
  rw [← e]
  exact h1.sub h2

theorem kDiag_eq (p : (ℝ × ℝ) × Tau) {s : ℝ} (h : ‖(P.Φ s p).1‖ ≤ 1) :
    P.kDiag p s = 1 + 9 * ((P.Φ s p).1).1 + 3 * ((P.Φ s p).1).2 := by
  rw [kDiag, bump.one_of_mem_closedBall (mem_closedBall_zero_iff.2 h), one_mul]

theorem abs_kDiag_le (p : (ℝ × ℝ) × Tau) (s : ℝ) : |P.kDiag p s| ≤ 25 := by
  set y := (P.Φ s p).1
  by_cases hb : bump y = 0
  · simp [kDiag, y, hb]
  have hy : y ∈ ball (0 : ℝ × ℝ) 2 := by
    have : y ∈ Function.support bump := hb
    rwa [bump.support_eq] at this
  rw [mem_ball_zero_iff] at hy
  obtain ⟨h1, h2⟩ := norm_prod_le_iff.1 hy.le
  rw [Real.norm_eq_abs, abs_le] at h1 h2
  rw [kDiag, abs_mul, abs_of_nonneg (bump.nonneg)]
  have hk : |1 + 9 * y.1 + 3 * y.2| ≤ 25 := by rw [abs_le]; constructor <;> linarith
  calc bump y * |1 + 9 * y.1 + 3 * y.2| ≤ 1 * 25 :=
        mul_le_mul bump.le_one hk (abs_nonneg _) zero_le_one
    _ = 25 := one_mul _

/-- If the orbit meets the diagonal once, it lies on it. -/
theorem offDiag_eq_zero (p : (ℝ × ℝ) × Tau) {T : ℝ} (hT : P.offDiag p T = 0) (t : ℝ) :
    P.offDiag p t = 0 := by
  have hlip : ∀ s, LipschitzWith (25 : ℝ≥0) (fun x => -(P.kDiag p s * x)) :=
    fun s => LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, Real.dist_eq, NNReal.coe_ofNat]
      calc |-(P.kDiag p s * x) - -(P.kDiag p s * y)| = |P.kDiag p s| * |x - y| := by
            rw [show -(P.kDiag p s * x) - -(P.kDiag p s * y) = -(P.kDiag p s * (x - y)) by ring,
              abs_neg, abs_mul]
        _ ≤ 25 * |x - y| := mul_le_mul_of_nonneg_right (P.abs_kDiag_le p s) (abs_nonneg _)
  have heq := ODE_solution_unique_univ (v := fun s x => -(P.kDiag p s * x)) (s := fun _ => univ)
    (f := P.offDiag p) (g := fun _ => 0) (t₀ := T) (fun s => (hlip s).lipschitzOnWith)
    (fun s => ⟨P.hasDerivAt_offDiag p s, trivial⟩)
    (fun s => ⟨by simpa using hasDerivAt_const s (0 : ℝ), trivial⟩) hT
  exact congrFun heq t

theorem tendsto_offDiag {l : Filter ℝ} {p : (ℝ × ℝ) × Tau} {N : ℝ}
    (h : Tendsto (fun s => (P.Φ s p).1) l (𝓝 (ptH N))) : Tendsto (P.offDiag p) l (𝓝 0) := by
  have hc : Continuous fun q : ℝ × ℝ => q.1 - q.2 := by fun_prop
  have := (hc.tendsto (ptH N)).comp h
  rwa [show (ptH N).1 - (ptH N).2 = 0 by simp [ptH]] at this

/-- A solution converging to `Σ_H^-` as `s → -∞` lies on the diagonal, if `N₋ > 4`. -/
theorem diag_of_tendsto_atBot (h4 : 4 < P.N (-1)) {p : (ℝ × ℝ) × Tau}
    (h : Tendsto (fun s => (P.Φ s p).1) atBot (𝓝 (ptH (P.N (-1))))) (t : ℝ) :
    ((P.Φ t p).1).1 = ((P.Φ t p).1).2 := by
  set N := P.N (-1)
  set u := 1 / (N + 8) with hu
  have hu0 : 0 < u := by positivity
  have hu12 : u < 1 / 12 := by rw [hu]; exact one_div_lt_one_div_of_lt (by norm_num) (by linarith)
  set r := min (u / 8) ((1 / 12 - u) / 2)
  have hr : 0 < r := lt_min (by positivity) (by linarith)
  obtain ⟨T, hT⟩ := eventually_atBot.1 (h.eventually (closedBall_mem_nhds _ hr))
  have hk : ∀ s ≤ T, 0 ≤ P.kDiag p s := fun s hs => by
    obtain ⟨hn, hk, -, -⟩ := near_H (by linarith) (min_le_left _ _) (hT s hs)
    rw [P.kDiag_eq p hn]
    have := min_le_right (u / 8) ((1 / 12 - u) / 2)
    rw [abs_le] at hk
    linarith [hk.1]
  have hd : ∀ s, HasDerivAt (fun s => P.offDiag p s ^ 2)
      (-(2 * P.kDiag p s * P.offDiag p s ^ 2)) s := fun s => by
    have := (P.hasDerivAt_offDiag p s).pow 2
    convert this using 1; simp only [Nat.cast_ofNat]; ring
  have hlim : Tendsto (fun s => P.offDiag p s ^ 2) atBot (𝓝 0) := by
    simpa using (P.tendsto_offDiag h).pow 2
  have hT0 : P.offDiag p T = 0 := by
    have := nonpos_of_deriv_nonpos hd (fun s hs => by
      have := hk s hs
      have := sq_nonneg (P.offDiag p s)
      nlinarith) hlim le_rfl
    nlinarith [sq_nonneg (P.offDiag p T)]
  have := P.offDiag_eq_zero p hT0 t
  simp only [offDiag] at this
  linarith

/-- No solution runs from `Σ_H^-` to `Σ_I^+`, and none from `Σ_H^-` to `Σ_C^+` if `N₊ ≠ 4`
(Proposition `prop:ONramp`(ii)). -/
theorem not_tendsto_I_or_C (h4 : 4 < P.N (-1)) (hp4 : P.N 1 ≠ 4) {p : (ℝ × ℝ) × Tau}
    (h : Tendsto (fun s => (P.Φ s p).1) atBot (𝓝 (ptH (P.N (-1))))) :
    ¬ Tendsto (fun s => (P.Φ s p).1) atTop (𝓝 ptI) ∧
      ¬ Tendsto (fun s => (P.Φ s p).1) atTop (𝓝 (ptC (P.N 1))) := by
  have hdiag : ∀ {q : ℝ × ℝ}, Tendsto (fun s => (P.Φ s p).1) atTop (𝓝 q) → q.1 = q.2 :=
    fun {q} hq => by
      have hcl : IsClosed {y : ℝ × ℝ | y.1 = y.2} := isClosed_eq continuous_fst continuous_snd
      exact hcl.mem_of_tendsto hq (Eventually.of_forall fun t => P.diag_of_tendsto_atBot h4 h t)
  refine ⟨fun hI => ?_, fun hC => ?_⟩
  · have := hdiag hI
    simp [ptI] at this
  · have := hdiag hC
    have hN : 1 < P.N 1 := P.one_lt_top
    simp only [ptC] at this
    field_simp at this
    exact hp4 (by nlinarith)

/-- If `q' = q - h` on `[T, ∞)` and `q` is bounded there, then `q(T) = p_*(T)`. -/
theorem eq_pstar_of_Ici {h : ℝ → ℝ} {B : ℝ} (hc : Continuous h) (hb : ∀ r, |h r| ≤ B)
    {q : ℝ → ℝ} {T C : ℝ} (hq : ∀ s, T ≤ s → HasDerivAt q (q s - h s) s)
    (hqb : ∀ s, T ≤ s → |q s| ≤ C) : q T = pstar h T := by
  set d : ℝ → ℝ := fun s => q s - pstar h s
  have hd : ∀ s, T ≤ s → HasDerivAt d (d s) s := fun s hs => by
    have := (hq s hs).sub (hasDerivAt_pstar hc hb s)
    convert this using 1; simp only [d]; ring
  have he : ∀ s, T ≤ s → HasDerivAt (fun s => exp (-s) * d s) 0 s := fun s hs => by
    have := ((hasDerivAt_neg s).exp).mul (hd s hs)
    convert this using 1; ring
  have hconst : ∀ s, T ≤ s → exp (-s) * d s = exp (-T) * d T := fun s hs =>
    constant_of_has_deriv_right_zero (f := fun s => exp (-s) * d s) (a := T) (b := s)
      (fun x hx => (he x hx.1).continuousAt.continuousWithinAt)
      (fun x hx => (he x hx.1).hasDerivWithinAt) s ⟨hs, le_rfl⟩
  have hds : ∀ s, T ≤ s → d s = exp (s - T) * d T := fun s hs => by
    have h1 := hconst s hs
    have : exp s * exp (-s) = 1 := by rw [← exp_add]; simp
    calc d s = exp s * (exp (-s) * d s) := by rw [← mul_assoc, this, one_mul]
      _ = exp s * (exp (-T) * d T) := by rw [h1]
      _ = exp (s - T) * d T := by rw [← mul_assoc, ← exp_add, sub_eq_add_neg]
  by_contra hne
  have hpos : 0 < |d T| := abs_pos.2 (sub_ne_zero.2 hne)
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hqb T le_rfl)
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hb 0)
  set s := T + (C + B) / |d T|
  have hs0 : T ≤ s := le_add_of_nonneg_right (div_nonneg (by linarith) hpos.le)
  have hbound : |d s| ≤ C + B :=
    (abs_sub _ _).trans (add_le_add (hqb s hs0) (abs_pstar_le hc hb s))
  rw [hds s hs0, abs_mul, abs_of_pos (exp_pos _)] at hbound
  have h2 : (s - T + 1) * |d T| ≤ exp (s - T) * |d T| :=
    mul_le_mul_of_nonneg_right (add_one_le_exp _) hpos.le
  have h3 : (s - T) * |d T| = C + B := by simp only [s, add_sub_cancel_left]; field_simp
  nlinarith

/-- `h(s) = N(σ(s)) + 8` along the orbit of `p`. -/
noncomputable def hDiag (p : (ℝ × ℝ) × Tau) (s : ℝ) : ℝ := P.nn p s + 8

theorem continuous_hDiag (p : (ℝ × ℝ) × Tau) : Continuous (P.hDiag p) :=
  (P.lipschitz_Nc.continuous.comp (P.β.continuous continuous_id continuous_const)).add
    continuous_const

theorem abs_hDiag_le (p : (ℝ × ℝ) × Tau) (s : ℝ) : |P.hDiag p s| ≤ P.bN + 8 := by
  have h1 := P.nn_gt p s
  have h2 := P.nn_le p s
  rw [hDiag, abs_le]; constructor <;> linarith

theorem exists_hDiag_ge (p : (ℝ × ℝ) × Tau) : ∃ m, 9 < m ∧ ∀ s, m ≤ P.hDiag p s := by
  obtain ⟨τ₀, hτ₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (by norm_num : (-1 : ℝ) ≤ 1))
    P.lipschitz_Nc.continuous.continuousOn
  refine ⟨P.Nc τ₀ + 8, by linarith [P.one_lt _ (clamp_mem τ₀), show P.Nc τ₀ = P.N (clamp τ₀) from rfl],
    fun s => ?_⟩
  have hc : P.nn p s = P.Nc (clamp (P.β s p.2)) := by
    simp only [nn, Nc, clamp_of_mem (clamp_mem _)]
  have := hmin (clamp_mem (P.β s p.2))
  simp only [Set.mem_ofPred_eq] at this
  rw [hDiag, hc]; linarith

/-- The diagonal solution `eq:ONdiag` is an orbit of the shifted flow. -/
theorem Φ_diagonal (p : (ℝ × ℝ) × Tau) (T t : ℝ)
    (hT : (P.Φ T p).1 = (-1 / pstar (P.hDiag p) T, -1 / pstar (P.hDiag p) T)) :
    (P.Φ t p).1 = (-1 / pstar (P.hDiag p) t, -1 / pstar (P.hDiag p) t) := by
  obtain ⟨m, hm9, hm⟩ := P.exists_hDiag_ge p
  have hc := P.continuous_hDiag p
  have hb := P.abs_hDiag_le p
  set b : ℝ := (p.2 : ℝ)
  set γ : ℝ → (ℝ × ℝ) × ℝ := fun s => ((-1 / pstar (P.hDiag p) s, -1 / pstar (P.hDiag p) s), P.β s b)
  have hγ : IsSol P.V γ := fun s => by
    obtain ⟨d1, d2, -, h1, h2⟩ := diagonal_solution hc hb hm9 hm s
    have hn : ‖((-1 / pstar (P.hDiag p) s, -1 / pstar (P.hDiag p) s) : ℝ × ℝ)‖ ≤ 1 := by
      refine norm_prod_le_iff.2 ⟨?_, ?_⟩ <;> rw [Real.norm_eq_abs, abs_le] <;> constructor <;>
        linarith
    have e : P.V (γ s) = (field (P.hDiag p s - 8) (γ s).1, P.gc (P.β s b)) := by
      simp only [V, γ]
      rw [P.fieldA_eq hn]
      simp [hDiag, nn, b]
    rw [e]
    exact (d1.prodMk d2).prodMk (P.hasDerivAt_β b s)
  have hγT : P.Ψ T (p.1, b) = γ T := by
    refine Prod.ext ?_ (P.Ψ_snd T _)
    exact hT
  have h := P.Ψ_eq_of_isSol hγ T (t - T)
  rw [sub_add_cancel, ← hγT, ← Flow.map_add, sub_add_cancel] at h
  rw [Φ_fst]
  exact congrArg Prod.fst h

/-- Proposition `prop:ONramp`(ii): for `N₊ < 4`, the only solution that converges to `Σ_H^+` as
`s → ∞` is the diagonal solution `y₁ = y₂ = -1/p_*` of `eq:ONdiag`. -/
theorem eq_diagonal_of_tendsto_atTop (h4 : P.N 1 < 4) {p : (ℝ × ℝ) × Tau}
    (h : Tendsto (fun s => (P.Φ s p).1) atTop (𝓝 (ptH (P.N 1)))) (t : ℝ) :
    (P.Φ t p).1 = (-1 / pstar (P.hDiag p) t, -1 / pstar (P.hDiag p) t) := by
  set N := P.N 1
  have hN : 1 < N := P.one_lt_top
  set u := 1 / (N + 8) with hu
  have hu0 : 0 < u := by positivity
  have hu12 : 1 / 12 < u := by rw [hu]; exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  set r := min (u / 8) ((u - 1 / 12) / 2)
  have hr : 0 < r := lt_min (by positivity) (by linarith)
  obtain ⟨T, hT⟩ := eventually_atTop.1 (h.eventually (closedBall_mem_nhds _ hr))
  have hnear := fun s (hs : T ≤ s) => near_H hN (min_le_left _ _) (hT s hs)
  -- the solution is on the diagonal
  have hk : ∀ s ≥ T, P.kDiag p s ≤ 0 := fun s hs => by
    obtain ⟨hn, hk, -, -⟩ := hnear s hs
    rw [P.kDiag_eq p hn]
    have := min_le_right (u / 8) ((u - 1 / 12) / 2)
    rw [abs_le] at hk
    linarith [hk.2]
  have hd : ∀ s, HasDerivAt (fun s => P.offDiag p (-s) ^ 2)
      (2 * P.kDiag p (-s) * P.offDiag p (-s) ^ 2) s := fun s => by
    have := ((P.hasDerivAt_offDiag p (-s)).pow 2).comp s (hasDerivAt_neg s)
    convert this using 1
    · rfl
    · simp only [Nat.cast_ofNat]; ring
  have hlim : Tendsto (fun s => P.offDiag p (-s) ^ 2) atBot (𝓝 0) := by
    have := ((P.tendsto_offDiag h).pow 2).comp tendsto_neg_atBot_atTop
    rw [zero_pow two_ne_zero] at this
    exact this
  have hT0 : P.offDiag p T = 0 := by
    have := nonpos_of_deriv_nonpos hd (T := -T) (fun s hs => by
      have := hk (-s) (by linarith)
      have := sq_nonneg (P.offDiag p (-s))
      nlinarith) hlim le_rfl
    rw [neg_neg] at this
    nlinarith [sq_nonneg (P.offDiag p T)]
  have hw : ∀ s, ((P.Φ s p).1).1 = ((P.Φ s p).1).2 := fun s => by
    have := P.offDiag_eq_zero p hT0 s
    simp only [offDiag] at this; linarith
  -- on the diagonal, `-1/y₁` is bounded and solves `p' = p - h`
  set ς : ℝ → ℝ := fun s => ((P.Φ s p).1).1
  have hς : ∀ s, T ≤ s → ς s < 0 := fun s hs => by
    obtain ⟨-, -, h1, -⟩ := hnear s hs
    simp only [ς]; linarith
  have hq : ∀ s, T ≤ s → HasDerivAt (fun t => -1 / ς t) (-1 / ς s - P.hDiag p s) s :=
    fun s hs => by
      refine riccati ?_ (hς s hs).ne
      obtain ⟨hn, -, -, -⟩ := hnear s hs
      have := P.hasDerivAt_Φ_fst p s
      rw [cutField_eq hn] at this
      have h1 := (hasFDerivAt_fst (𝕜 := ℝ) (p := (P.Φ s p).1)).comp_hasDerivAt s this
      have e : (ContinuousLinearMap.fst ℝ ℝ ℝ) (field (P.Nc (P.β s p.2)) (P.Φ s p).1) =
          -ς s * (1 + P.hDiag p s * ς s) := by
        show f₁ _ ((P.Φ s p).1).1 ((P.Φ s p).1).2 = _
        rw [← hw s, f₁_diag]; simp only [ς, hDiag, nn]
      rw [e] at h1
      exact h1
  have hqb : ∀ s, T ≤ s → |-1 / ς s| ≤ 2 * (N + 8) := fun s hs => by
    obtain ⟨-, -, h1, h2⟩ := hnear s hs
    have hs0 := hς s hs
    rw [abs_div, abs_neg, abs_one, abs_of_neg hs0, div_le_iff₀ (by linarith)]
    have : u * (N + 8) = 1 := by rw [hu]; field_simp
    simp only [ς] at hs0 ⊢
    nlinarith
  have hpT := eq_pstar_of_Ici (P.continuous_hDiag p) (P.abs_hDiag_le p) hq hqb
  refine P.Φ_diagonal p T t ?_
  have e : ς T = -1 / pstar (P.hDiag p) T := by
    rw [← hpT]; field_simp [(hς T le_rfl).ne]
  exact Prod.ext e ((hw T).symm.trans e)

end Ramp

end ConleyCheck.ON
