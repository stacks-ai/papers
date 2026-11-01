import ConleyCheck.ON.Model

/-!
# The diagonal solution of the parameter shift (Proposition `prop:ONramp`(ii))

On the invariant diagonal `y₁ = y₂ = ς` the shifted flow is `ς' = -ς (1 + h(s) ς)` with
`h(s) = N(σ(s)) + 8`. We verify that `p = -1/ς` solves `p' = p - h`, that
`p_*(s) = ∫_s^∞ e^{s-r} h(r) dr` is a solution, that it is the only solution bounded as
`s → ∞`, that it is a weighted average of `h` (so `p_* > 9` and `-1/p_* ∈ (-1/9, 0)`), and that
`p_*(s) → lim h` as `s → ±∞`.

Throughout, `h` is continuous and bounded. In the paper `h = N ∘ σ + 8` with `N` continuous on
`[-1, 1]` with values in `(1, ∞)`, so `h` is bounded and `inf h > 9`.
-/

open Real MeasureTheory Set Filter Topology

namespace ConleyCheck.ON

/-- `p_*(s) = ∫_s^∞ e^{s-r} h(r) dr`, eq. `eq:ONdiag`. -/
noncomputable def pstar (h : ℝ → ℝ) (s : ℝ) : ℝ := ∫ r in Ioi s, exp (s - r) * h r

variable {h : ℝ → ℝ} {B : ℝ}

theorem integrableOn_exp_sub_mul (hc : Continuous h) (hb : ∀ r, |h r| ≤ B) (a c : ℝ) :
    IntegrableOn (fun r => exp (c - r) * h r) (Ioi a) := by
  have hg : IntegrableOn (fun r => B * exp c * exp (-1 * r)) (Ioi a) :=
    (exp_neg_integrableOn_Ioi a one_pos).const_mul (B * exp c)
  refine Integrable.mono' hg ?_ ?_
  · exact (by fun_prop : Continuous fun r => exp (c - r) * h r).aestronglyMeasurable
  · filter_upwards with r
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (exp_pos _), Real.norm_eq_abs]
    calc exp (c - r) * |h r| ≤ exp (c - r) * B :=
          mul_le_mul_of_nonneg_left (hb r) (exp_pos _).le
      _ = B * exp c * exp (-1 * r) := by rw [neg_one_mul, sub_eq_add_neg, exp_add]; ring

theorem integral_exp_sub (s : ℝ) : ∫ r in Ioi s, exp (s - r) = 1 := by
  have : (fun r => exp (s - r)) = fun r => exp s * exp (-r) := by
    funext r; rw [sub_eq_add_neg, exp_add]
  rw [this, integral_const_mul, integral_exp_neg_Ioi, ← exp_add]; simp

/-- `p_*(s)` is a weighted average of `h` over `(s, ∞)`. -/
theorem pstar_bounds (hc : Continuous h) (hb : ∀ r, |h r| ≤ B) {s m M : ℝ}
    (hm : ∀ r, s < r → m ≤ h r) (hM : ∀ r, s < r → h r ≤ M) :
    m ≤ pstar h s ∧ pstar h s ≤ M := by
  have hI := integrableOn_exp_sub_mul hc hb s s
  have hE : IntegrableOn (fun r => exp (s - r)) (Ioi s) := by
    simpa using integrableOn_exp_sub_mul (h := fun _ => 1) continuous_const
      (fun _ => by simp : ∀ _ : ℝ, |(1 : ℝ)| ≤ 1) s s
  constructor
  · calc m = ∫ r in Ioi s, exp (s - r) * m := by rw [integral_mul_const, integral_exp_sub, one_mul]
      _ ≤ pstar h s := setIntegral_mono_on (hE.mul_const m) hI measurableSet_Ioi
          (fun r hr => mul_le_mul_of_nonneg_left (hm r hr) (exp_pos _).le)
  · calc pstar h s ≤ ∫ r in Ioi s, exp (s - r) * M := setIntegral_mono_on hI (hE.mul_const M)
          measurableSet_Ioi (fun r hr => mul_le_mul_of_nonneg_left (hM r hr) (exp_pos _).le)
      _ = M := by rw [integral_mul_const, integral_exp_sub, one_mul]

theorem abs_pstar_le (hc : Continuous h) (hb : ∀ r, |h r| ≤ B) (s : ℝ) : |pstar h s| ≤ B := by
  obtain ⟨h1, h2⟩ := pstar_bounds hc hb (s := s) (m := -B) (M := B)
    (fun r _ => (abs_le.1 (hb r)).1) (fun r _ => (abs_le.1 (hb r)).2)
  exact abs_le.2 ⟨h1, h2⟩

/-- `p_*` solves the linear equation `p' = p - h`. -/
theorem hasDerivAt_pstar (hc : Continuous h) (hb : ∀ r, |h r| ≤ B) (s : ℝ) :
    HasDerivAt (pstar h) (pstar h s - h s) s := by
  set φ : ℝ → ℝ := fun r => exp (-r) * h r with hφ
  have hφI : ∀ a, IntegrableOn φ (Ioi a) := fun a => by
    simpa [φ] using integrableOn_exp_sub_mul hc hb a 0
  have hF : ∀ t, ∫ r in Ioi t, φ r = (∫ r in t..0, φ r) + ∫ r in Ioi 0, φ r := fun t =>
    (intervalIntegral.integral_interval_add_Ioi (hφI t) (hφI 0)).symm
  have hp : pstar h = fun t => exp t * ∫ r in Ioi t, φ r := by
    funext t
    simp only [pstar, φ]
    rw [← integral_const_mul]
    congr 1; funext r; rw [sub_eq_add_neg, exp_add]; ring
  have hφc : Continuous φ := by fun_prop
  have hd1 : HasDerivAt (fun t => ∫ r in t..0, φ r) (-φ s) s :=
    intervalIntegral.integral_hasDerivAt_left (hφc.intervalIntegrable _ _)
      (hφc.stronglyMeasurableAtFilter _ _) hφc.continuousAt
  have hd2 : HasDerivAt (fun t => ∫ r in Ioi t, φ r) (-φ s) s := by
    have := hd1.add_const (∫ r in Ioi 0, φ r)
    convert this using 1
    funext t; exact hF t
  have key := (hasDerivAt_exp s).mul hd2
  rw [hp]
  convert key using 1
  have he : exp s * exp (-s) = 1 := by rw [← exp_add]; simp
  simp only [φ]
  linear_combination (h s) * he

/-- `p_*` is the only solution of `p' = p - h` that is bounded as `s → ∞`. -/
theorem pstar_unique (hc : Continuous h) (hb : ∀ r, |h r| ≤ B) {q : ℝ → ℝ}
    (hq : ∀ s, HasDerivAt q (q s - h s) s) {C : ℝ} (hqb : ∀ s, 0 ≤ s → |q s| ≤ C) :
    q = pstar h := by
  set d : ℝ → ℝ := fun s => q s - pstar h s with hd_def
  have hd : ∀ s, HasDerivAt d (d s) s := fun s => by
    have := (hq s).sub (hasDerivAt_pstar hc hb s)
    convert this using 1; simp only [d]; ring
  have he : ∀ s, HasDerivAt (fun s => exp (-s) * d s) 0 s := fun s => by
    have := ((hasDerivAt_neg s).exp).mul (hd s)
    convert this using 1; ring
  have hconst : ∀ s, exp (-s) * d s = exp (-0) * d 0 := fun s =>
    is_const_of_deriv_eq_zero (fun t => (he t).differentiableAt) (fun t => (he t).deriv) s 0
  have hds : ∀ s, d s = exp s * d 0 := fun s => by
    have h1 := hconst s
    simp only [neg_zero, exp_zero, one_mul] at h1
    have : exp s * exp (-s) = 1 := by rw [← exp_add]; simp
    calc d s = exp s * (exp (-s) * d s) := by rw [← mul_assoc, this, one_mul]
      _ = exp s * d 0 := by rw [h1]
  have hd0 : d 0 = 0 := by
    by_contra hne
    have hpos : 0 < |d 0| := abs_pos.2 hne
    have hC : 0 ≤ C := le_trans (abs_nonneg _) (hqb 0 le_rfl)
    have hB : 0 ≤ B := le_trans (abs_nonneg _) (hb 0)
    set s := (C + B) / |d 0| with hs
    have hs0 : 0 ≤ s := div_nonneg (by linarith) hpos.le
    have hbound : |d s| ≤ C + B := by
      calc |d s| = |q s - pstar h s| := rfl
        _ ≤ |q s| + |pstar h s| := abs_sub _ _
        _ ≤ C + B := add_le_add (hqb s hs0) (abs_pstar_le hc hb s)
    rw [hds s, abs_mul, abs_of_pos (exp_pos s)] at hbound
    have := add_one_le_exp s
    have h2 : (s + 1) * |d 0| ≤ exp s * |d 0| := mul_le_mul_of_nonneg_right this hpos.le
    have h3 : s * |d 0| = C + B := by rw [hs]; field_simp
    nlinarith
  funext s
  have := hds s
  rw [hd0, mul_zero] at this
  simp only [d] at this
  linarith

/-- The Riccati substitution: if `ς' = -ς (1 + h ς)` and `ς ≠ 0`, then `p = -1/ς` satisfies
`p' = p - h`. -/
theorem riccati {ς : ℝ → ℝ} {s : ℝ} (hς : HasDerivAt ς (-ς s * (1 + h s * ς s)) s)
    (h0 : ς s ≠ 0) : HasDerivAt (fun t => -1 / ς t) (-1 / ς s - h s) s := by
  have := (hς.inv h0).neg
  convert this using 1
  · funext t; simp only [Pi.neg_apply, Pi.inv_apply]; ring
  · field_simp; ring

/-- The diagonal solution `y₁ = y₂ = -1/p_*` solves the shifted `O(N)` flow with
`N(s) = h(s) - 8`, and it lies in `(-1/9, 0)²`. -/
theorem diagonal_solution (hc : Continuous h) (hb : ∀ r, |h r| ≤ B) {m : ℝ} (hm9 : 9 < m)
    (hm : ∀ r, m ≤ h r) (s : ℝ) :
    HasDerivAt (fun t => -1 / pstar h t) (f₁ (h s - 8) (-1 / pstar h s) (-1 / pstar h s)) s ∧
    HasDerivAt (fun t => -1 / pstar h t) (f₂ (h s - 8) (-1 / pstar h s) (-1 / pstar h s)) s ∧
    9 < pstar h s ∧ -1 / 9 < -1 / pstar h s ∧ -1 / pstar h s < 0 := by
  have hp9 : 9 < pstar h s :=
    lt_of_lt_of_le hm9 (pstar_bounds hc hb (M := B) (fun r _ => hm r)
      (fun r _ => (abs_le.1 (hb r)).2)).1
  have hp0 : pstar h s ≠ 0 := by linarith
  have hD := ((hasDerivAt_pstar hc hb s).inv hp0).neg
  have hD' : HasDerivAt (fun t => -1 / pstar h t) ((pstar h s - h s) / pstar h s ^ 2) s := by
    convert hD using 1
    · funext t; simp only [Pi.neg_apply, Pi.inv_apply]; ring
    · ring
  refine ⟨?_, ?_, hp9, ?_, ?_⟩
  · convert hD' using 1; simp only [f₁]; field_simp; ring
  · convert hD' using 1; simp only [f₂]; field_simp; ring
  · have := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 9) hp9
    have e1 : -1 / pstar h s = -(1 / pstar h s) := by ring
    have e2 : (-1 : ℝ) / 9 = -(1 / 9) := by ring
    rw [e1, e2]; linarith
  · exact div_neg_of_neg_of_pos (by norm_num) (by linarith)

/-- `p_*(s) → L` as `s → ∞` if `h → L`. -/
theorem tendsto_pstar_atTop (hc : Continuous h) (hb : ∀ r, |h r| ≤ B) {L : ℝ}
    (hL : Tendsto h atTop (𝓝 L)) : Tendsto (pstar h) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at hL ⊢
  intro ε hε
  obtain ⟨S, hS⟩ := hL (ε / 2) (by linarith)
  refine ⟨S, fun s hs => ?_⟩
  have hr : ∀ r, s < r → |h r - L| < ε / 2 := fun r hr => hS r (by linarith)
  obtain ⟨h1, h2⟩ := pstar_bounds hc hb (s := s) (m := L - ε / 2) (M := L + ε / 2)
    (fun r hr' => by linarith [(abs_lt.1 (hr r hr')).1])
    (fun r hr' => by linarith [(abs_lt.1 (hr r hr')).2])
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith

/-- `p_*(s) → L` as `s → -∞` if `h → L`. -/
theorem tendsto_pstar_atBot (hc : Continuous h) (hb : ∀ r, |h r| ≤ B) {L : ℝ}
    (hL : Tendsto h atBot (𝓝 L)) : Tendsto (pstar h) atBot (𝓝 L) := by
  rw [Metric.tendsto_nhds] at hL ⊢
  intro ε hε
  obtain ⟨S, hS'⟩ := Filter.eventually_atBot.1 (hL (ε / 4) (by linarith))
  have hS : ∀ r, r ≤ S → |h r - L| < ε / 4 := fun r hr => by
    have := hS' r hr; rwa [Real.dist_eq] at this
  set e : ℝ → ℝ := fun s => pstar h s - L with he_def
  have hde : ∀ s, HasDerivAt e (e s - (h s - L)) s := fun s => by
    have := (hasDerivAt_pstar hc hb s).sub_const L
    convert this using 1; simp only [e]; ring
  -- `g = (e - ε/4) e^{-s}` is monotone and `k = (e + ε/4) e^{-s}` is antitone on `(-∞, S]`.
  have hg : ∀ c : ℝ, ∀ s, HasDerivAt (fun t => (e t + c) * exp (-t))
      ((-c - (h s - L)) * exp (-s)) s := fun c s => by
    have := ((hde s).add_const c).mul (hasDerivAt_neg s).exp
    convert this using 1; ring
  have hcont : ∀ c : ℝ, Continuous fun t => (e t + c) * exp (-t) := fun c =>
    continuous_iff_continuousAt.2 fun t => (hg c t).continuousAt
  have hmono : MonotoneOn (fun t => (e t + -(ε / 4)) * exp (-t)) (Iic S) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic S) (hcont _).continuousOn
      (fun x _ => (hg _ x).hasDerivWithinAt)
    intro x hx
    rw [interior_Iic] at hx
    have := (abs_lt.1 (hS x (le_of_lt hx))).2
    exact mul_nonneg (by linarith) (exp_pos _).le
  have hanti : AntitoneOn (fun t => (e t + ε / 4) * exp (-t)) (Iic S) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic S) (hcont _).continuousOn
      (fun x _ => (hg _ x).hasDerivWithinAt)
    intro x hx
    rw [interior_Iic] at hx
    have := (abs_lt.1 (hS x (le_of_lt hx))).1
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (exp_pos _).le
  set A := |e S| + ε / 4 with hA
  have hA0 : 0 < A := by positivity
  refine Filter.eventually_atBot.2 ⟨S + Real.log (ε / 4 / A), fun s hs => ?_⟩
  have hlog : Real.log (ε / 4 / A) ≤ 0 := by
    apply Real.log_nonpos (by positivity)
    rw [div_le_one hA0]; linarith [abs_nonneg (e S)]
  have hsS : s ≤ S := by linarith
  have hexp : exp (s - S) * A ≤ ε / 4 := by
    have : exp (s - S) ≤ ε / 4 / A := by
      calc exp (s - S) ≤ exp (Real.log (ε / 4 / A)) := exp_le_exp.2 (by linarith)
        _ = ε / 4 / A := exp_log (by positivity)
    calc exp (s - S) * A ≤ ε / 4 / A * A := mul_le_mul_of_nonneg_right this hA0.le
      _ = ε / 4 := by field_simp
  have hup := hmono (mem_Iic.2 hsS) (mem_Iic.2 le_rfl) hsS
  have hlo := hanti (mem_Iic.2 hsS) (mem_Iic.2 le_rfl) hsS
  simp only at hup hlo
  have hes : exp (-s) * exp (s - S) = exp (-S) := by rw [← exp_add]; ring_nf
  have hpos : 0 < exp (-s) := exp_pos _
  -- Multiply the two inequalities by `e^{s}`.
  have hup' : e s - ε / 4 ≤ exp (s - S) * (e S - ε / 4) := by
    have : (e s - ε / 4) * exp (-s) ≤ (exp (s - S) * (e S - ε / 4)) * exp (-s) := by
      calc (e s - ε / 4) * exp (-s) = (e s + -(ε / 4)) * exp (-s) := by ring
        _ ≤ (e S + -(ε / 4)) * exp (-S) := hup
        _ = (exp (s - S) * (e S - ε / 4)) * exp (-s) := by rw [← hes]; ring
    exact le_of_mul_le_mul_right this hpos
  have hlo' : exp (s - S) * (e S + ε / 4) ≤ e s + ε / 4 := by
    have : (exp (s - S) * (e S + ε / 4)) * exp (-s) ≤ (e s + ε / 4) * exp (-s) := by
      calc (exp (s - S) * (e S + ε / 4)) * exp (-s) = (e S + ε / 4) * exp (-S) := by
            rw [← hes]; ring
        _ ≤ (e s + ε / 4) * exp (-s) := hlo
    exact le_of_mul_le_mul_right this hpos
  have hE : 0 < exp (s - S) := exp_pos _
  have h1 : exp (s - S) * (e S - ε / 4) ≤ exp (s - S) * A := by
    apply mul_le_mul_of_nonneg_left _ hE.le; linarith [le_abs_self (e S)]
  have h2 : -(exp (s - S) * A) ≤ exp (s - S) * (e S + ε / 4) := by
    have : -A ≤ e S + ε / 4 := by linarith [neg_abs_le (e S)]
    nlinarith
  rw [Real.dist_eq, abs_lt]
  simp only [e] at hup' hlo' h1 h2
  constructor <;> linarith

end ConleyCheck.ON
