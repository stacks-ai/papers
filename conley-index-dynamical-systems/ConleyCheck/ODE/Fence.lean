import ConleyCheck.ODE.Flow

/-!
# Fencing and growth lemmas for scalar differential inequalities

* `growth_fwd`, `no_growth_fwd`, `no_growth_bwd`: a quantity that grows at a fixed rate once above
  its initial value is unbounded.
* `nonpos_of_fence`, `fence_affine`: if `g' < C g` wherever `g > 0` (for instance
  `g' = -m + k g` with `m ≥ 0`), then `g(0) ≤ 0` implies `g ≤ 0`.
* `pos_of_linear`: solutions of `T' = k(t) T` keep the sign of `T(0)`.
* `arc_orbit`, `arc_orbit_neg`: for a Lipschitz field `F` on `ℝ` with consecutive zeros `α < β`
  and a fixed sign on `(α, β)`, every orbit starting in `(α, β)` stays there and runs from one
  endpoint to the other.
-/

open Set Filter Topology Real
open scoped NNReal

namespace ConleyCheck.ODE

/-! ## Growth lemmas -/

theorem growth_fwd {g g' : ℝ → ℝ} (hg : ∀ t, HasDerivAt g (g' t) t) {t₀ c : ℝ} (hc : 0 < c)
    (h : ∀ t, t₀ ≤ t → g t₀ ≤ g t → c ≤ g' t) :
    ∀ t, t₀ ≤ t → g t₀ + c / 2 * (t - t₀) ≤ g t := by
  intro t ht
  have hl : ∀ s, HasDerivAt (fun s => g t₀ + c / 2 * (s - t₀)) (c / 2) s := fun s => by
    simpa using (((hasDerivAt_id s).sub_const t₀).const_mul (c / 2)).const_add (g t₀)
  refine image_le_of_deriv_right_lt_deriv_boundary (f' := fun _ => c / 2) (B' := g')
    (fun s _ => (hl s).continuousAt.continuousWithinAt) (fun s _ => (hl s).hasDerivWithinAt)
    (by simp) hg (fun s hs hfs => ?_) ⟨ht, le_rfl⟩
  have : g t₀ ≤ g s := by
    rw [← hfs]; nlinarith [hs.1]
  linarith [h s hs.1 this]

/-- A coordinate that grows at a fixed rate once above its initial value is unbounded. -/
theorem no_growth_fwd {g g' : ℝ → ℝ} (hg : ∀ t, HasDerivAt g (g' t) t) {t₀ c M : ℝ}
    (hc : 0 < c) (h : ∀ t, t₀ ≤ t → g t₀ ≤ g t → c ≤ g' t) (hM : ∀ t, g t ≤ M) : False := by
  set T := 2 * (|M - g t₀| + 1) / c
  have hT : 0 ≤ T := by positivity
  have h1 := growth_fwd hg hc h (t₀ + T) (by linarith)
  have h2 : c / 2 * (t₀ + T - t₀) = |M - g t₀| + 1 := by
    simp only [T, add_sub_cancel_left]; field_simp
  linarith [hM (t₀ + T), le_abs_self (M - g t₀)]

theorem no_growth_bwd {g g' : ℝ → ℝ} (hg : ∀ t, HasDerivAt g (g' t) t) {t₀ c M : ℝ}
    (hc : 0 < c) (h : ∀ t, t ≤ t₀ → g t₀ ≤ g t → g' t ≤ -c) (hM : ∀ t, g t ≤ M) : False := by
  have hG : ∀ s, HasDerivAt (fun s => g (-s)) (-g' (-s)) s := fun s => by
    have := (hg (-s)).comp s (hasDerivAt_neg s)
    simp only [mul_neg, mul_one] at this
    exact this
  refine no_growth_fwd hG (t₀ := -t₀) hc (fun s hs hgs => ?_) (fun s => hM (-s))
  have := h (-s) (by linarith) (by simpa using hgs)
  linarith


/-- If `g' < C g` wherever `g > 0` and `g(0) ≤ 0`, then `g ≤ 0`. -/
theorem nonpos_of_fence {g g' : ℝ → ℝ} {t C : ℝ} (ht : 0 ≤ t)
    (hg : ∀ s ∈ Icc 0 t, HasDerivAt g (g' s) s) (h0 : g 0 ≤ 0)
    (hb : ∀ s ∈ Ico 0 t, 0 < g s → g' s < C * g s) : g t ≤ 0 := by
  have key : ∀ ε > 0, g t ≤ ε * exp (C * t) := by
    intro ε hε
    have hB : ∀ s, HasDerivAt (fun s => ε * exp (C * s)) (C * (ε * exp (C * s))) s := fun s =>
      (((hasDerivAt_id s).const_mul C).exp.const_mul ε).congr_deriv (by simp; ring)
    refine image_le_of_deriv_right_lt_deriv_boundary (a := 0) (b := t)
      (fun s hs => (hg s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hg s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (by simp; linarith) hB (fun s hs hgs => ?_) ⟨ht, le_rfl⟩
    have hpos : 0 < g s := by rw [hgs]; positivity
    have := hb s hs hpos
    rw [hgs] at this
    exact this
  by_contra hpos
  push Not at hpos
  have he := exp_pos (C * t)
  have := key (g t / (2 * exp (C * t))) (by positivity)
  rw [div_mul_eq_mul_div, mul_div_assoc, div_mul_cancel_right₀ he.ne'] at this
  linarith


theorem fence_affine {g g' m k : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hg : ∀ s ∈ Icc 0 t, HasDerivAt g (g' s) s) (h0 : g 0 ≤ 0)
    (hid : ∀ s ∈ Icc 0 t, g' s = -m s + k s * g s) (hm : ∀ s ∈ Icc 0 t, 0 ≤ m s)
    (hk : ContinuousOn k (Icc 0 t)) : g t ≤ 0 := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hk
  refine nonpos_of_fence (C := K + 1) ht hg h0 fun s hs hpos => ?_
  have hs' := Ico_subset_Icc_self hs
  have hks : k s ≤ K := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hK s hs')
  rw [hid s hs']
  nlinarith [hm s hs', mul_le_mul_of_nonneg_right hks hpos.le]

/-- Solutions of the linear equation `T' = k(t) T` keep the sign of `T(0) > 0`. -/
theorem pos_of_linear {T k : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hT : ∀ s ∈ Icc 0 t, HasDerivAt T (k s * T s) s) (hk : ContinuousOn k (Icc 0 t))
    (h0 : 0 < T 0) : 0 < T t := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hk
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, ht⟩)
  set M := K + 1
  have hh : ∀ s, HasDerivAt (fun s => T 0 * exp (-M * s)) (-M * (T 0 * exp (-M * s))) s :=
    fun s => (((hasDerivAt_id s).const_mul (-M)).exp.const_mul (T 0)).congr_deriv (by simp; ring)
  have hg := nonpos_of_fence (g := fun s => T 0 * exp (-M * s) - T s)
    (g' := fun s => -M * (T 0 * exp (-M * s)) - k s * T s) (C := M) ht
    (fun s hs => (hh s).sub (hT s hs)) (by simp) fun s hs hpos => by
      have hs' := Ico_subset_Icc_self hs
      have hks : |k s| ≤ K := by simpa [Real.norm_eq_abs] using hK s hs'
      have hkT : -(k s * T s) ≤ K * |T s| :=
        (neg_le_abs _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hks (abs_nonneg _))
      have hpe : 0 < T 0 * exp (-M * s) := mul_pos h0 (exp_pos _)
      rcases le_or_gt 0 (T s) with hT0 | hT0
      · rw [abs_of_nonneg hT0] at hkT
        nlinarith
      · rw [abs_of_neg hT0] at hkT
        nlinarith
  have := mul_pos h0 (exp_pos (-M * t))
  linarith

theorem eventually_sign {g : ℝ → ℝ} {d t : ℝ} (hg : HasDerivAt g d t) (hd : d < 0) :
    (∀ᶠ s in 𝓝[>] t, g s < g t) ∧ ∀ᶠ s in 𝓝[<] t, g t < g s := by
  have h' : ∀ᶠ s in 𝓝[≠] t, slope g t s < 0 :=
    (hasDerivAt_iff_tendsto_slope.1 hg).eventually (Iio_mem_nhds hd)
  constructor
  · filter_upwards [nhdsWithin_mono t (fun s (hs : t < s) => ne_of_gt hs) h',
      self_mem_nhdsWithin] with s hs (hst : t < s)
    rw [slope_def_field] at hs
    have := (div_lt_iff₀ (sub_pos.2 hst)).1 hs
    linarith
  · filter_upwards [nhdsWithin_mono t (fun s (hs : s < t) => ne_of_lt hs) h',
      self_mem_nhdsWithin] with s hs (hst : s < t)
    rw [slope_def_field] at hs
    have := (div_lt_iff_of_neg (sub_neg.2 hst)).1 hs
    linarith

theorem eventually_mem_Icc {g : ℝ → ℝ} {d a b : ℝ} (hg : HasDerivAt g d 0) (ha : a < g 0)
    (hb : g 0 ≤ b) (hd : g 0 = b → d < 0) : ∀ᶠ s in 𝓝[>] (0 : ℝ), g s ∈ Icc a b := by
  have hlow : ∀ᶠ s in 𝓝[>] (0 : ℝ), a < g s :=
    nhdsWithin_le_nhds (hg.continuousAt.eventually (Ioi_mem_nhds ha))
  have hup : ∀ᶠ s in 𝓝[>] (0 : ℝ), g s ≤ b := by
    rcases hb.lt_or_eq with hb | hb
    · exact nhdsWithin_le_nhds ((hg.continuousAt.eventually (Iio_mem_nhds hb)).mono
        fun _ h => le_of_lt h)
    · exact (eventually_sign hg (hd hb)).1.mono fun _ h => by rw [← hb]; exact h.le
  filter_upwards [hlow, hup] with s h1 h2 using ⟨h1.le, h2⟩

theorem exists_eps {P Q : ℝ → Prop} (hP : ∀ᶠ s in 𝓝[<] (0 : ℝ), P s)
    (hQ : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q s) :
    ∃ ε > 0, (∀ t ∈ Ioo (-ε) 0, P t) ∧ ∀ t ∈ Ioo 0 ε, Q t := by
  obtain ⟨l, hl, hlP⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hP
  obtain ⟨u, hu, huQ⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hQ
  have hl' : l < 0 := hl
  have hu' : 0 < u := hu
  refine ⟨min (-l) u, lt_min (by linarith) hu', fun t ht => hlP ⟨?_, ht.2⟩,
    fun t ht => huQ ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩⟩
  linarith [ht.1, min_le_left (-l) u]

/-- If `g(0) ≤ b` and `g' < 0` where `g(0) = b`, then `g ≤ b` just after `0`. -/
theorem eventually_le_right {g : ℝ → ℝ} {d b : ℝ} (hg : HasDerivAt g d 0) (hb : g 0 ≤ b)
    (hd : g 0 = b → d < 0) : ∀ᶠ s in 𝓝[>] (0 : ℝ), g s ≤ b := by
  rcases hb.lt_or_eq with hb | hb
  · exact nhdsWithin_le_nhds ((hg.continuousAt.eventually (Iio_mem_nhds hb)).mono
      fun _ h => le_of_lt h)
  · exact (eventually_sign hg (hd hb)).1.mono fun _ h => by rw [← hb]; exact h.le

/-- If `g(0) ≤ b` and `g' > 0` where `g(0) = b`, then `g ≤ b` just before `0`. -/
theorem eventually_le_left {g : ℝ → ℝ} {d b : ℝ} (hg : HasDerivAt g d 0) (hb : g 0 ≤ b)
    (hd : g 0 = b → 0 < d) : ∀ᶠ s in 𝓝[<] (0 : ℝ), g s ≤ b := by
  rcases hb.lt_or_eq with hb | hb
  · exact nhdsWithin_le_nhds ((hg.continuousAt.eventually (Iio_mem_nhds hb)).mono
      fun _ h => le_of_lt h)
  · have := (eventually_sign hg.neg (neg_lt_zero.2 (hd hb))).2
    exact this.mono fun _ h => by simp only [Pi.neg_apply] at h; rw [← hb]; linarith

/-- Solutions of `T' = k(t) T` defined for all time keep the sign of `T(s₀) > 0`, forward and
backward. -/
theorem pos_of_linear_all {T k : ℝ → ℝ} (hT : ∀ s, HasDerivAt T (k s * T s) s)
    (hk : Continuous k) {s₀ : ℝ} (h0 : 0 < T s₀) (s : ℝ) : 0 < T s := by
  rcases le_total s₀ s with h | h
  · have := pos_of_linear (T := fun r => T (s₀ + r)) (k := fun r => k (s₀ + r)) (t := s - s₀)
      (by linarith) (fun r _ => HasDerivAt.comp_const_add s₀ r (hT (s₀ + r)))
      (by fun_prop) (by simpa using h0)
    simpa using this
  · have := pos_of_linear (T := fun r => T (s₀ - r)) (k := fun r => -k (s₀ - r)) (t := s₀ - s)
      (by linarith) (fun r _ => by
        have := HasDerivAt.comp_const_sub s₀ r (hT (s₀ - r))
        rw [neg_mul_eq_neg_mul] at this
        exact this)
      (by fun_prop) (by simpa using h0)
    simpa using this

/-- Solutions of `T' = k(t) T` that vanish once vanish identically. -/
theorem eq_zero_of_linear_all {T k : ℝ → ℝ} (hT : ∀ s, HasDerivAt T (k s * T s) s)
    (hk : Continuous k) {s₀ : ℝ} (h0 : T s₀ = 0) (s : ℝ) : T s = 0 := by
  by_contra hs
  rcases lt_or_gt_of_ne hs with h | h
  · have := pos_of_linear_all (T := fun r => -T r) (k := k)
      (fun r => by
        have := (hT r).neg
        rw [← mul_neg] at this
        exact this) hk (s₀ := s) (by linarith) s₀
    simp [h0] at this
  · have := pos_of_linear_all hT hk h s₀
    simp [h0] at this

/-- If `g > 0` satisfies `g' ≤ -κ g` on `(-∞, s₀]`, then `g` grows exponentially backward in
time, so it is unbounded there. -/
theorem exp_growth_bwd {g g' : ℝ → ℝ} {s₀ κ M : ℝ} (hg : ∀ s ≤ s₀, HasDerivAt g (g' s) s)
    (hκ : 0 < κ) (h : ∀ s ≤ s₀, g' s ≤ -κ * g s) (h0 : 0 < g s₀) (hM : ∀ s ≤ s₀, g s ≤ M) :
    False := by
  set p : ℝ → ℝ := fun r => g (s₀ - r) * exp (-κ * r)
  have hp : ∀ r, 0 ≤ r → HasDerivAt p (-(g' (s₀ - r) + κ * g (s₀ - r)) * exp (-κ * r)) r :=
    fun r hr => by
      have h1 := HasDerivAt.comp_const_sub s₀ r (hg (s₀ - r) (by linarith))
      have h2 := ((hasDerivAt_id r).const_mul (-κ)).exp
      have h3 := h1.mul h2
      simp only [id] at h3
      convert h3 using 1
      ring
  have hmono : MonotoneOn p (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun r hr => (hp r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hp r (interior_subset hr)).differentiableAt.differentiableWithinAt)
      fun r hr => ?_
    have hr0 : 0 ≤ r := interior_subset hr
    rw [(hp r hr0).deriv]
    have := h (s₀ - r) (by linarith)
    exact mul_nonneg (by linarith) (exp_pos _).le
  set r := |M| / (g s₀ * κ)
  have hr : 0 ≤ r := by positivity
  have h1 : p 0 ≤ p r := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hr) hr
  have h2 : g s₀ * (1 + κ * r) ≤ g (s₀ - r) := by
    have he : 1 + κ * r ≤ exp (κ * r) := by linarith [add_one_le_exp (κ * r)]
    have h1' : g s₀ ≤ g (s₀ - r) * exp (-κ * r) := by simpa [p] using h1
    have hgr : 0 ≤ g (s₀ - r) := by
      by_contra hneg; push Not at hneg
      nlinarith [exp_pos (-κ * r)]
    calc g s₀ * (1 + κ * r) ≤ g s₀ * exp (κ * r) := mul_le_mul_of_nonneg_left he h0.le
      _ ≤ g (s₀ - r) * exp (-κ * r) * exp (κ * r) := mul_le_mul_of_nonneg_right h1' (exp_pos _).le
      _ = g (s₀ - r) := by rw [mul_assoc, ← exp_add]; simp
  have h3 : g s₀ * (1 + κ * r) = g s₀ + |M| := by
    simp only [r]; field_simp
  have := hM (s₀ - r) (by linarith)
  linarith [le_abs_self M]

/-- A forward barrier: if `g(a) ≤ 0` and `g' < 0` wherever `g = 0`, then `g(b) ≤ 0` for `b ≥ a`. -/
theorem nonpos_forward {g g' : ℝ → ℝ} (hg : ∀ s, HasDerivAt g (g' s) s) {a b : ℝ} (hab : a ≤ b)
    (h0 : g a ≤ 0) (h : ∀ s ∈ Ico a b, g s = 0 → g' s < 0) : g b ≤ 0 :=
  image_le_of_deriv_right_lt_deriv_boundary' (f := g) (B := fun _ => 0) (B' := fun _ => 0)
    (fun s _ => (hg s).continuousAt.continuousWithinAt) (fun s _ => (hg s).hasDerivWithinAt) h0
    continuousOn_const (fun s _ => hasDerivWithinAt_const _ _ _) h ⟨hab, le_rfl⟩

/-- An orbit of a Lipschitz field on `ℝ` between consecutive zeros `α < β`, with `F > 0` on
`(α, β)`, stays in `(α, β)`, is increasing, and runs from `α` to `β`. -/
theorem arc_orbit {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) {α β : ℝ}
    (hα : F α = 0) (hβ : F β = 0) (hpos : ∀ x ∈ Ioo α β, 0 < F x) {φ : ℝ → ℝ}
    (hφ : ∀ t, HasDerivAt φ (F (φ t)) t) (h0 : φ 0 ∈ Ioo α β) :
    (∀ t, φ t ∈ Ioo α β) ∧ StrictMono φ ∧ Tendsto φ atBot (𝓝 α) ∧ Tendsto φ atTop (𝓝 β) := by
  have hsol : IsSol F φ := hφ
  have hconst : ∀ p, F p = 0 → IsSol F fun _ => p := fun p hp t => by
    rw [hp]; exact hasDerivAt_const t p
  have hnot : ∀ p, F p = 0 → ∀ t, φ t ≠ p := fun p hp t ht => by
    have := IsSol.unique hF hsol (hconst p hp) (t₀ := t) ht
    have h := congrFun this 0
    rcases h0 with ⟨h1, h2⟩
    rw [h] at h1 h2
    have hp' : p ≠ α ∨ p ≠ β := by
      by_contra hc; push Not at hc; linarith [hc.1, hc.2]
    rcases lt_or_ge p β with hpb | hpb
    · rcases lt_or_ge α p with hap | hap
      · exact absurd (hpos p ⟨hap, hpb⟩) (by rw [hp]; exact lt_irrefl 0)
      · linarith
    · linarith
  have hcont : Continuous φ := continuous_iff_continuousAt.2 fun t => (hφ t).continuousAt
  have hin : ∀ t, φ t ∈ Ioo α β := by
    intro t
    by_contra hout
    simp only [mem_Ioo, not_and_or, not_lt] at hout
    rcases hout with h | h
    · obtain ⟨s, -, hs⟩ := intermediate_value_uIcc (a := 0) (b := t) hcont.continuousOn
        (show α ∈ uIcc (φ 0) (φ t) from mem_uIcc.2 (Or.inr ⟨h, h0.1.le⟩))
      exact hnot α hα s hs
    · obtain ⟨s, -, hs⟩ := intermediate_value_uIcc (a := 0) (b := t) hcont.continuousOn
        (show β ∈ uIcc (φ 0) (φ t) from mem_uIcc.2 (Or.inl ⟨h0.2.le, h⟩))
      exact hnot β hβ s hs
  have hmono : StrictMono φ := strictMono_of_deriv_pos fun t => by
    rw [(hφ t).deriv]; exact hpos _ (hin t)
  have hFc : Continuous F := hF.continuous
  refine ⟨hin, hmono, ?_, ?_⟩
  · have hbdd : BddBelow (range φ) := ⟨α, by rintro _ ⟨t, rfl⟩; exact (hin t).1.le⟩
    have hT := tendsto_atBot_ciInf hmono.monotone hbdd
    set L := ⨅ t, φ t
    have hL1 : α ≤ L := le_ciInf fun t => (hin t).1.le
    have hL2 : L < β := (ciInf_le hbdd 0).trans_lt h0.2
    rcases hL1.lt_or_eq with hL | hL
    · exfalso
      have hFL := hpos L ⟨hL, hL2⟩
      have hev : ∀ᶠ t in atBot, F L / 2 < F (φ t) :=
        ((hFc.tendsto L).comp hT).eventually (lt_mem_nhds (by linarith))
      obtain ⟨t₀, ht₀⟩ := eventually_atBot.1 hev
      have hG : ∀ s, HasDerivAt (fun s => -φ s) (-F (φ s)) s := fun s => (hφ s).neg
      refine no_growth_bwd hG (t₀ := t₀) (c := F L / 2) (M := -α) (by linarith)
        (fun s hs _ => by linarith [ht₀ s hs]) fun s => by linarith [(hin s).1]
    · rw [← hL] at hT; exact hT
  · have hbdd : BddAbove (range φ) := ⟨β, by rintro _ ⟨t, rfl⟩; exact (hin t).2.le⟩
    have hT := tendsto_atTop_ciSup hmono.monotone hbdd
    set L := ⨆ t, φ t
    have hL1 : L ≤ β := ciSup_le fun t => (hin t).2.le
    have hL2 : α < L := h0.1.trans_le (le_ciSup hbdd 0)
    rcases hL1.lt_or_eq with hL | hL
    · exfalso
      have hFL := hpos L ⟨hL2, hL⟩
      have hev : ∀ᶠ t in atTop, F L / 2 < F (φ t) :=
        ((hFc.tendsto L).comp hT).eventually (lt_mem_nhds (by linarith))
      obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 hev
      refine no_growth_fwd hφ (t₀ := t₀) (c := F L / 2) (M := β) (by linarith)
        (fun s hs _ => by linarith [ht₀ s hs]) fun s => (hin s).2.le
    · rw [hL] at hT; exact hT

/-- The decreasing case: with `F < 0` on `(α, β)` orbits run from `β` to `α`. -/
theorem arc_orbit_neg {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) {α β : ℝ}
    (hα : F α = 0) (hβ : F β = 0) (hneg : ∀ x ∈ Ioo α β, F x < 0) {φ : ℝ → ℝ}
    (hφ : ∀ t, HasDerivAt φ (F (φ t)) t) (h0 : φ 0 ∈ Ioo α β) :
    (∀ t, φ t ∈ Ioo α β) ∧ StrictAnti φ ∧ Tendsto φ atBot (𝓝 β) ∧ Tendsto φ atTop (𝓝 α) := by
  have hG : LipschitzWith K fun x => -F (-x) := by
    have := (LipschitzWith.id.neg.comp (hF.comp LipschitzWith.id.neg))
    simp only [one_mul, mul_one] at this
    exact this
  have hψ : ∀ t, HasDerivAt (fun t => -φ t) ((fun x => -F (-x)) ((fun t => -φ t) t)) t :=
    fun t => by
      show HasDerivAt (fun t => -φ t) (-F (- -φ t)) t
      rw [neg_neg]; exact (hφ t).neg
  obtain ⟨hin, hmono, hbot, htop⟩ := arc_orbit hG (α := -β) (β := -α) (by simp [hβ])
    (by simp [hα]) (fun x hx => by
      have := hneg (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
      linarith) hψ ⟨by linarith [h0.2], by linarith [h0.1]⟩
  refine ⟨fun t => ⟨by linarith [(hin t).2], by linarith [(hin t).1]⟩,
    fun a b hab => by linarith [hmono hab], ?_, ?_⟩
  · simpa using hbot.neg
  · simpa using htop.neg

end ConleyCheck.ODE
