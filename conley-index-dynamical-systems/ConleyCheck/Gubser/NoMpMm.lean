import ConleyCheck.Gubser.MorseG

/-!
# No connection from `M⁺` to `M⁻` inside `{y₁ > 0}`

An orbit with `y₁ > 0` that leaves `K⁺` keeps `B₁ > 0`, so near `M⁻` it stays in
`{-a < π̄ ≤ -(a - η)}` with `y₃ > 0`. Its `ω`-limit set lies in `{τ = ±1}`.

* If `τ ≡ -1`, then `T = y₁ / y₃` increases and is bounded by `a / δ`, so the `ω`-limit set lies on
  a level `{T = L}` with `L > 0`, which no orbit with `T' > 0` can stay on.
* If `τ → 1`, then `π̄` increases and is bounded by `0`, so the `ω`-limit set lies on a level
  `{π̄ = L}` with `-a < L ≤ 0`, where `β_π > 0`.
-/

open Set Filter Topology
open ConleyCheck.Conley ConleyCheck.ODE

namespace ConleyCheck.Gubser

variable {c a η δ : ℝ}

theorem gy3_le_one (q : OmG) : gy3 q ≤ 1 := by
  nlinarith [sphere_G q, sq_nonneg (gy1 q), sq_nonneg (gy2 q), gy3_nonneg q]

theorem gB1_pos (ha : a ^ 2 = 1 / 5) (ha0 : 0 < a) (hc : 0 < c) {p : OmG} (hy : 0 ≤ gy1 p)
    {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁) (h0 : 0 < gB1 a (ϕG c t₀ p)) : 0 < gB1 a (ϕG c t₁ p) :=
  affine_pos (g := fun s => gB1 a (ϕG c s p)) (hasDerivAt_gB1 c p ha)
    (continuous_k c p _ (continuous_kB1 c a)) h01
    (fun s _ => div_nonneg (mul_nonneg (mul_nonneg ha0.le (gy1_nonneg_all c hy s))
      (gy3_nonneg _)) hc.le) h0

/-- A function with positive derivative on `[T₁, ∞)` and bounded above converges to a limit
larger than its value at `T₁`. -/
theorem exists_limit_of_deriv_pos {g d : ℝ → ℝ} {T₁ B : ℝ}
    (hg : ∀ t, T₁ ≤ t → HasDerivAt g (d t) t) (hd : ∀ t, T₁ ≤ t → 0 < d t)
    (hB : ∀ t, T₁ ≤ t → g t ≤ B) : ∃ L, g T₁ < L ∧ Tendsto g atTop (𝓝 L) := by
  have hmono : StrictMonoOn g (Ici T₁) := strictMonoOn_of_deriv_pos (convex_Ici T₁)
    (fun t ht => (hg t ht).continuousAt.continuousWithinAt) fun t ht => by
      rw [interior_Ici] at ht
      rw [(hg t (le_of_lt ht)).deriv]
      exact hd t (le_of_lt ht)
  set h := fun s => g (max s T₁) with hh
  have hm : Monotone h := fun s s' hss => hmono.monotoneOn
    (show max s T₁ ∈ Ici T₁ from le_max_right s T₁) (show max s' T₁ ∈ Ici T₁ from le_max_right s' T₁)
    (max_le_max hss le_rfl)
  have hbdd : BddAbove (range h) := ⟨B, by rintro _ ⟨s, rfl⟩; exact hB _ (le_max_right _ _)⟩
  refine ⟨⨆ s, h s, ?_, (tendsto_atTop_ciSup hm hbdd).congr' ?_⟩
  · calc g T₁ < g (T₁ + 1) := hmono (show T₁ ∈ Ici T₁ from le_refl T₁) (show T₁ + 1 ∈ Ici T₁ from by simp only [mem_Ici]; linarith) (by linarith)
      _ = h (T₁ + 1) := by simp only [hh, max_eq_left (show T₁ ≤ T₁ + 1 by linarith)]
      _ ≤ ⨆ s, h s := le_ciSup hbdd _
  · filter_upwards [eventually_ge_atTop T₁] with s hs
    simp only [hh, max_eq_left hs]

/-- If a ratio `f / y₃` converges along an orbit with `y₃ > 0`, the `ω`-limit set lies on the
corresponding level. -/
theorem omegaLim_subset_ratio {x : OmG} {f : OmG → ℝ} (hf : Continuous f) {T₁ L : ℝ}
    (h3 : ∀ t, T₁ ≤ t → 0 < gy3 (ϕG c t x))
    (hL : Tendsto (fun t => f (ϕG c t x) / gy3 (ϕG c t x)) atTop (𝓝 L)) :
    omegaLim (ϕG c) x ⊆ {q | f q - L * gy3 q = 0} := by
  refine omegaLim_subset_level (ϕG c) (hf.sub (continuous_const.mul continuous_gy3)) ?_
  have h0 : Tendsto (fun t => f (ϕG c t x) / gy3 (ϕG c t x) - L) atTop (𝓝 0) := by
    simpa using hL.sub_const L
  refine squeeze_zero_norm' ?_ (by simpa using h0.norm)
  filter_upwards [eventually_ge_atTop T₁] with t ht
  have hy := h3 t ht
  have e : f (ϕG c t x) - L * gy3 (ϕG c t x) =
      gy3 (ϕG c t x) * (f (ϕG c t x) / gy3 (ϕG c t x) - L) := by field_simp
  show |f (ϕG c t x) - L * gy3 (ϕG c t x)| ≤ _
  rw [e, abs_mul, abs_of_pos hy]
  exact mul_le_of_le_one_left (abs_nonneg _) (gy3_le_one _)

/-- A ratio that is constant along a full orbit with `y₃ > 0` has zero derivative. -/
theorem ratio_const {z : OmG} {f : OmG → ℝ} {L : ℝ} (h3 : ∀ s, 0 < gy3 (ϕG c s z))
    (hf : ∀ s, f (ϕG c s z) - L * gy3 (ϕG c s z) = 0) (s : ℝ) :
    f (ϕG c s z) / gy3 (ϕG c s z) = L := by
  rw [div_eq_iff (h3 s).ne']; linarith [hf s]

section Hyp

variable (H : KHyp c a η δ)
include H

theorem no_conn_Bp_Bm {x : OmG} (hy : 0 < gy1 x)
    (hα : (alphaLim (ϕG c) x ∩ Inv (ϕG c) (Kp a η δ)).Nonempty)
    (hω : (omegaLim (ϕG c) x ∩ Inv (ϕG c) (Km a η δ)).Nonempty) : False := by
  have hc := H.hc
  have ha0 := H.ha0
  have hd := H.hδ
  obtain ⟨T₀, hT₀⟩ := eventually_atBot.1 (H.isConvexNbhd_Kp.eventually_of_meets_alpha hα)
  have hB : ∀ t, T₀ ≤ t → 0 < gB1 a (ϕG c t x) := fun t ht =>
    gB1_pos H.ha H.ha0 H.hc hy.le ht (B1_pos_of_Kp H (hT₀ T₀ le_rfl))
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1
    ((H.isConvexNbhd_Km.eventually_of_meets hω).and (eventually_ge_atTop T₀))
  have hK : ∀ t, T₁ ≤ t → ϕG c t x ∈ Km a η δ := fun t ht => (hT₁ t ht).1
  have hB' : ∀ t, T₁ ≤ t → 0 < gB1 a (ϕG c t x) := fun t ht => hB t (hT₁ t ht).2
  have hy2 : ∀ t, T₁ ≤ t → gy2 (ϕG c t x) < 0 := fun t ht => gy2_neg_of_Km H (hK t ht)
  have h3 : ∀ t, T₁ ≤ t → 0 < gy3 (ϕG c t x) := fun t ht => by
    have := hy2 t ht
    have := hB' t ht
    unfold gB1 at this
    nlinarith [gy3_nonneg (ϕG c t x)]
  have hy1 : ∀ t, 0 < gy1 (ϕG c t x) := gy1_pos c x hy
  -- the `ω`-limit set
  have hωK := H.isConvexNbhd_Km.omegaLim_subset_of_meets hω
  have hωB : omegaLim (ϕG c) x ⊆ {q | 0 ≤ gB1 a q} :=
    omegaLim_subset_of_eventually (ϕG c)
      (isClosed_le continuous_const (continuous_gy2.add (continuous_const.mul continuous_gy3)))
      (eventually_atTop.2 ⟨T₁, fun t ht => (hB' t ht).le⟩)
  have hω1 : omegaLim (ϕG c) x ⊆ {q | 0 ≤ gy1 q} :=
    omegaLim_subset_of_eventually (ϕG c) (isClosed_le continuous_const continuous_gy1)
      (Eventually.of_forall fun t => (hy1 t).le)
  have hω3 : ∀ z ∈ omegaLim (ϕG c) x, 0 < gy3 z := fun z hz => by
    have := gy2_neg_of_Km H (Inv_subset _ (hωK hz))
    have hb : 0 ≤ gB1 a z := hωB hz
    unfold gB1 at hb
    nlinarith [gy3_nonneg z]
  obtain ⟨z, hz, -⟩ := hω
  have hzs : ∀ s, ϕG c s z ∈ omegaLim (ϕG c) x := fun s => omegaLim_invariant (ϕG c) hz s
  have hz3 : ∀ s, 0 < gy3 (ϕG c s z) := fun s => hω3 _ (hzs s)
  have hz2 : gy2 z < 0 := gy2_neg_of_Km H (Inv_subset _ (hωK hz))
  have hz3' := hω3 z hz
  have hzπ : gπ z < 0 := div_neg_of_neg_of_pos hz2 hz3'
  have hzT : 0 ≤ gT z := div_nonneg (hω1 hz) hz3'.le
  obtain ⟨τL, hτL⟩ := tendsto_gw1 c x
  have hzτ : gw1 z = τL := omegaLim_subset_level (ϕG c) continuous_gw1 hτL hz
  have hτ2 : (τL - 1) * (τL + 1) = 0 := by
    have := deriv_zero_of_const (hasDerivAt_gw1 c z 0) fun s => by
      rw [(w_const_of_omegaLim hz s).1, (w_const_of_omegaLim hz 0).1]
    rw [Flow.map_zero_apply] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hz3'.ne'
    · rw [hzτ] at h; linear_combination -h
  have hmono := monotone_gw1 c x
  rcases mul_eq_zero.1 hτ2 with hτ1 | hτ1
  · -- `τ → 1`: the slope `π̄` increases to a limit in `(-a, 0]`
    have hτ1 : τL = 1 := by linarith
    obtain ⟨T₂, hT₂⟩ := eventually_atTop.1 ((hτL.eventually (lt_mem_nhds
      (show (0 : ℝ) < τL by rw [hτ1]; norm_num))).and (eventually_ge_atTop T₁))
    have hπa : ∀ t, T₁ ≤ t → -a < gπ (ϕG c t x) := fun t ht => by
      rw [gπ, lt_div_iff₀ (h3 t ht)]
      have := hB' t ht
      unfold gB1 at this
      linarith
    have hπ0 : ∀ t, T₁ ≤ t → gπ (ϕG c t x) < 0 := fun t ht =>
      div_neg_of_neg_of_pos (hy2 t ht) (h3 t ht)
    obtain ⟨L, hL1, hL⟩ := exists_limit_of_deriv_pos (g := fun t => gπ (ϕG c t x)) (T₁ := T₂)
      (B := 0) (fun t ht => hasDerivAt_gπ c x (h3 t ((hT₂ T₂ le_rfl).2.trans ht)))
      (fun t ht => by
        have ht1 : T₁ ≤ t := (hT₂ T₂ le_rfl).2.trans ht
        have hτp : 0 < gw1 (ϕG c t x) := (hT₂ T₂ le_rfl).1.trans_le (hmono ht)
        have hTp : 0 < gT (ϕG c t x) := div_pos (hy1 t) (h3 t ht1)
        have hπ1 := hπa t ht1
        have hπ2 := hπ0 t ht1
        have hsq : gπ (ϕG c t x) ^ 2 < 1 / 5 := by rw [← H.ha]; nlinarith
        refine mul_pos (h3 t ht1) ?_
        unfold βπ
        have e1 : 0 < (1 / 5 - gπ (ϕG c t x) ^ 2) * gw1 (ϕG c t x) := mul_pos (by linarith) hτp
        have e2 : 0 < -(gT (ϕG c t x) * gπ (ϕG c t x)) / c := div_pos (by nlinarith) hc
        rw [neg_div] at e2
        linarith)
      fun t ht => (hπ0 t ((hT₂ T₂ le_rfl).2.trans ht)).le
    have hL0 : L ≤ 0 := le_of_tendsto hL (eventually_atTop.2 ⟨T₁, fun t ht => (hπ0 t ht).le⟩)
    have hLa : -a < L := (hπa T₂ (hT₂ T₂ le_rfl).2).trans hL1
    have hωL := omegaLim_subset_ratio (f := gy2) continuous_gy2 h3 hL
    have hconst : ∀ s, gπ (ϕG c s z) = L := ratio_const hz3 fun s => hωL (hzs s)
    have := deriv_zero_of_const (hasDerivAt_gπ c z (t := 0) (hz3 0))
      fun s => by rw [hconst s, hconst 0]
    have h0 := hconst 0
    rw [Flow.map_zero_apply] at this h0
    rw [h0, hzτ, hτ1] at this
    have hsq : L ^ 2 < 1 / 5 := by rw [← H.ha]; nlinarith
    have hβ : 0 < βπ c (gT z) L 1 := by
      unfold βπ
      have e2 : 0 ≤ -(gT z * L) / c := div_nonneg (by nlinarith) hc.le
      rw [neg_div] at e2
      nlinarith
    exact (mul_pos hz3' hβ).ne' this
  · -- `τ ≡ -1`: the slope `T` increases to a positive limit
    have hτ1 : τL = -1 := by linarith
    have hτx : ∀ t, gw1 (ϕG c t x) = -1 := fun t =>
      le_antisymm (hτ1 ▸ hmono.ge_of_tendsto hτL t) (gw1_mem _).1
    obtain ⟨L, hL1, hL⟩ := exists_limit_of_deriv_pos (g := fun t => gT (ϕG c t x)) (T₁ := T₁)
      (B := a / δ) (fun t ht => hasDerivAt_gT c x (h3 t ht))
      (fun t ht => by
        have hTp : 0 < gT (ϕG c t x) := div_pos (hy1 t) (h3 t ht)
        have hπ : gπ (ϕG c t x) < 0 := div_neg_of_neg_of_pos (hy2 t ht) (h3 t ht)
        refine mul_pos (h3 t ht) ?_
        rw [hτx]
        unfold βT
        nlinarith [mul_pos hTp (show 0 < 2 - gπ (ϕG c t x) by linarith)])
      fun t ht => by
        show gy1 (ϕG c t x) / gy3 (ϕG c t x) ≤ a / δ
        rw [div_le_div_iff₀ (h3 t ht) hd]
        have := (Km_coords (hK t ht)).2.1
        have := hB' t ht
        unfold gB1 at this
        linarith
    have hL0 : 0 < L := (div_pos (hy1 T₁) (h3 T₁ le_rfl)).trans hL1
    have hωL := omegaLim_subset_ratio (f := gy1) continuous_gy1 h3 hL
    have hconst : ∀ s, gT (ϕG c s z) = L := ratio_const hz3 fun s => hωL (hzs s)
    have := deriv_zero_of_const (hasDerivAt_gT c z (t := 0) (hz3 0))
      fun s => by rw [hconst s, hconst 0]
    have h0 := hconst 0
    rw [Flow.map_zero_apply] at this h0
    rw [h0, hzτ, hτ1] at this
    have hβ : 0 < βT L (gπ z) (-1) := by
      unfold βT
      nlinarith [mul_pos hL0 (show 0 < 2 - gπ z by linarith)]
    exact (mul_pos hz3' hβ).ne' this

end Hyp

end ConleyCheck.Gubser
