import Mathlib

/-!
# Linear nonautonomous equations on the line

Let `A : ℝ → E →L[ℝ] E` be continuous with `‖A t‖ ≤ M`, and `h : ℝ → E` continuous and bounded.
The equation `y' = A(t) y + h(t)` has exactly one solution on `ℝ` through each `(t₀, ξ)`
(`exists_isLinSol`, `IsLinSol.eq_of_eq`). Existence is the Banach fixed point theorem for the
Volterra operator in the weighted norm `sup_t ‖y t‖ / cosh (2m (t - t₀))`, `m = max M 0 + 1`.
`IsLinSol.norm_le_back` is the backward Grönwall estimate.
-/

namespace ConleyCheck.Palmer

open Set Filter Topology MeasureTheory BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `y` solves `y' = A(t) y + h(t)` on `ℝ`. -/
def IsLinSol (A : ℝ → E →L[ℝ] E) (h : ℝ → E) (y : ℝ → E) : Prop :=
  ∀ t, HasDerivAt y (A t (y t) + h t) t

variable {A : ℝ → E →L[ℝ] E} {h h' : ℝ → E} {y z : ℝ → E} {M H : ℝ}

theorem IsLinSol.continuous (hy : IsLinSol A h y) : Continuous y :=
  continuous_iff_continuousAt.2 fun t => (hy t).continuousAt

theorem IsLinSol.add (hy : IsLinSol A h y) (hz : IsLinSol A h' z) :
    IsLinSol A (h + h') (y + z) := fun t =>
  ((hy t).add (hz t)).congr_deriv (by simp only [Pi.add_apply, map_add]; abel)

theorem IsLinSol.sub (hy : IsLinSol A h y) (hz : IsLinSol A h' z) :
    IsLinSol A (h - h') (y - z) := fun t =>
  ((hy t).sub (hz t)).congr_deriv (by simp only [Pi.sub_apply, map_sub]; abel)

theorem IsLinSol.smul (hy : IsLinSol A h y) (c : ℝ) : IsLinSol A (c • h) (c • y) := fun t =>
  ((hy t).const_smul c).congr_deriv (by simp only [Pi.smul_apply, map_smul, smul_add])

theorem IsLinSol.neg (hy : IsLinSol A h y) : IsLinSol A (-h) (-y) := fun t =>
  ((hy t).neg).congr_deriv (by simp only [Pi.neg_apply, map_neg, neg_add])

theorem isLinSol_zero : IsLinSol A 0 (0 : ℝ → E) := fun t => by
  simp only [Pi.zero_apply, map_zero, add_zero]
  exact hasDerivAt_const t (0 : E)

/-- Uniqueness of solutions through a point. -/
theorem IsLinSol.eq_of_eq (hM : ∀ t, ‖A t‖ ≤ M) (hy : IsLinSol A h y) (hz : IsLinSol A h z)
    {t₀ : ℝ} (h0 : y t₀ = z t₀) : y = z := by
  set K : NNReal := ⟨max M 0, le_max_right _ _⟩
  have hv : ∀ t, LipschitzOnWith K (fun x => A t x + h t) univ := fun t => by
    refine LipschitzWith.lipschitzOnWith ?_
    refine LipschitzWith.of_dist_le_mul fun x x' => ?_
    rw [dist_add_right, dist_eq_norm, dist_eq_norm, ← map_sub]
    refine ((A t).le_opNorm _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact (hM t).trans (le_max_left _ _)
  exact ODE_solution_unique_univ (s := fun _ => univ) (t₀ := t₀) hv
    (fun t => ⟨hy t, trivial⟩) (fun t => ⟨hz t, trivial⟩) h0

/-- A solution agrees on `[T, ∞)` with any function that solves the same equation there and
agrees with it at `T`. -/
theorem IsLinSol.eq_of_Ici (hM : ∀ t, ‖A t‖ ≤ M) (hy : IsLinSol A h y) {T : ℝ}
    (hz : ∀ t, T ≤ t → HasDerivAt z (A t (z t) + h t) t) (h0 : y T = z T) :
    ∀ t, T ≤ t → y t = z t := by
  intro t ht
  set K : NNReal := ⟨max M 0, le_max_right _ _⟩
  have hv : ∀ s ∈ Ico T t, LipschitzOnWith K (fun x => A s x + h s) univ := fun s _ => by
    refine LipschitzWith.lipschitzOnWith ?_
    refine LipschitzWith.of_dist_le_mul fun x x' => ?_
    rw [dist_add_right, dist_eq_norm, dist_eq_norm, ← map_sub]
    refine ((A s).le_opNorm _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact (hM s).trans (le_max_left _ _)
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ) hv
    hy.continuous.continuousOn (fun s _ => (hy s).hasDerivWithinAt) (fun _ _ => trivial)
    (HasDerivAt.continuousOn fun s hs => hz s hs.1) (fun s hs => (hz s hs.1).hasDerivWithinAt)
    (fun _ _ => trivial) h0 ⟨ht, le_rfl⟩

/-- A solution of the homogeneous equation that vanishes somewhere vanishes identically. -/
theorem IsLinSol.eq_zero (hM : ∀ t, ‖A t‖ ≤ M) (hy : IsLinSol A 0 y) {t₀ : ℝ} (h0 : y t₀ = 0) :
    y = 0 :=
  hy.eq_of_eq hM isLinSol_zero (t₀ := t₀) h0

theorem abs_le_cosh (x : ℝ) : |x| ≤ Real.cosh x := by
  rw [← Real.cosh_abs]
  exact (Real.self_le_sinh_iff.2 (abs_nonneg x)).trans (Real.sinh_lt_cosh _).le

theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  refine abs_le.2 ⟨?_, (Real.sinh_lt_cosh _).le⟩
  have := Real.cosh_add_sinh x
  linarith [Real.exp_pos x]

theorem hasDerivAt_sinh_div {m t₀ : ℝ} (hm : m ≠ 0) (s : ℝ) :
    HasDerivAt (fun s => Real.sinh (2 * m * (s - t₀)) / (2 * m))
      (Real.cosh (2 * m * (s - t₀))) s := by
  have h1 : HasDerivAt (fun s => 2 * m * (s - t₀)) (2 * m) s := by
    simpa using ((hasDerivAt_id s).sub_const t₀).const_mul (2 * m)
  have h2 := (Real.hasDerivAt_sinh _).comp s h1
  convert h2.div_const (2 * m) using 1
  · rfl
  · field_simp

theorem integral_cosh {m t₀ : ℝ} (hm : m ≠ 0) (t : ℝ) :
    ∫ s in t₀..t, Real.cosh (2 * m * (s - t₀)) = Real.sinh (2 * m * (t - t₀)) / (2 * m) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_sinh_div hm s)
    ((by fun_prop : Continuous fun s => Real.cosh (2 * m * (s - t₀))).intervalIntegrable _ _)]
  simp

/-- The weighted Volterra estimate: if `‖u s‖ ≤ c cosh (2m (s - t₀))` and `‖A s‖ ≤ m`, then
`‖∫_{t₀}^t A s (u s) ds‖ ≤ (c / 2) cosh (2m (t - t₀))`. -/
theorem norm_integral_weighted_le {m c t₀ : ℝ} (hm : 0 < m)
    (hAm : ∀ t, ‖A t‖ ≤ m) {u : ℝ → E}
    (huc : ∀ s, ‖u s‖ ≤ c * Real.cosh (2 * m * (s - t₀))) (t : ℝ) :
    ‖∫ s in t₀..t, A s (u s)‖ ≤ c / 2 * Real.cosh (2 * m * (t - t₀)) := by
  have hc : 0 ≤ c := by
    have := (norm_nonneg _).trans (huc t₀)
    simpa using this
  have hb : ∀ s, ‖A s (u s)‖ ≤ m * c * Real.cosh (2 * m * (s - t₀)) := fun s => by
    calc ‖A s (u s)‖ ≤ ‖A s‖ * ‖u s‖ := (A s).le_opNorm _
      _ ≤ m * (c * Real.cosh (2 * m * (s - t₀))) :=
        mul_le_mul (hAm s) (huc s) (norm_nonneg _) hm.le
      _ = _ := by ring
  have h := intervalIntegral.norm_integral_le_abs_of_norm_le (μ := volume) (a := t₀) (b := t)
    (Eventually.of_forall hb)
    ((by fun_prop : Continuous fun s => m * c * Real.cosh (2 * m * (s - t₀))).intervalIntegrable
      _ _)
  rw [intervalIntegral.integral_const_mul, integral_cosh hm.ne'] at h
  refine h.trans ?_
  rw [abs_mul, abs_of_nonneg (by positivity), abs_div, abs_of_pos (by positivity : 0 < 2 * m)]
  calc m * c * (|Real.sinh (2 * m * (t - t₀))| / (2 * m))
      = c / 2 * |Real.sinh (2 * m * (t - t₀))| := by field_simp
    _ ≤ c / 2 * Real.cosh (2 * m * (t - t₀)) := by
      gcongr
      exact abs_sinh_le_cosh _

section Exist

variable [CompleteSpace E]

/-- Global existence for `y' = A(t) y + h(t)`. -/
theorem exists_isLinSol (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M) (hh : Continuous h)
    (hH : ∀ t, ‖h t‖ ≤ H) (t₀ : ℝ) (ξ : E) : ∃ y, IsLinSol A h y ∧ y t₀ = ξ := by
  set m := max M 0 + 1 with hm_def
  have hm : 0 < m := by positivity
  have hAm : ∀ t, ‖A t‖ ≤ m := fun t => (hM t).trans (by rw [hm_def]; linarith [le_max_left M 0])
  set w : ℝ → ℝ := fun t => Real.cosh (2 * m * (t - t₀)) with hw
  have hw1 : ∀ t, 1 ≤ w t := fun t => Real.one_le_cosh _
  have hw0 : ∀ t, 0 < w t := fun t => lt_of_lt_of_le one_pos (hw1 t)
  have hwc : Continuous w := by fun_prop
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0)
  -- the integrand of the Volterra operator
  set F : (ℝ →ᵇ E) → ℝ → E := fun z s => A s (w s • z s) + h s with hF
  have hFc : ∀ z, Continuous (F z) := fun z => by
    simp only [hF]
    exact (hA.clm_apply (hwc.smul z.continuous)).add hh
  set Φ0 : (ℝ →ᵇ E) → ℝ → E := fun z t => (w t)⁻¹ • (ξ + ∫ s in t₀..t, F z s) with hΦ0
  have hint : ∀ z t, ∫ s in t₀..t, F z s =
      (∫ s in t₀..t, A s (w s • z s)) + ∫ s in t₀..t, h s := fun z t => by
    apply intervalIntegral.integral_add
    · exact ((hA.clm_apply (hwc.smul z.continuous))).intervalIntegrable _ _
    · exact hh.intervalIntegrable _ _
  have hvol : ∀ (z : ℝ →ᵇ E) t, ‖∫ s in t₀..t, A s (w s • z s)‖ ≤ ‖z‖ / 2 * w t := fun z t =>
    norm_integral_weighted_le hm hAm (fun s => by
      show ‖w s • z s‖ ≤ _
      rw [norm_smul, Real.norm_of_nonneg (hw0 s).le, mul_comm]
      exact mul_le_mul_of_nonneg_right (z.norm_coe_le_norm s) (hw0 s).le) t
  have hhint : ∀ t, (w t)⁻¹ * ‖∫ s in t₀..t, h s‖ ≤ H / (2 * m) := fun t => by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := t₀) (b := t)
      (fun s _ => hH s)
    have h2 : 2 * m * |t - t₀| ≤ w t := by
      have := abs_le_cosh (2 * m * (t - t₀))
      rwa [abs_mul, abs_of_pos (by positivity : 0 < 2 * m)] at this
    rw [inv_mul_le_iff₀ (hw0 t)]
    calc ‖∫ s in t₀..t, h s‖ ≤ H * |t - t₀| := h1
      _ = H / (2 * m) * (2 * m * |t - t₀|) := by field_simp
      _ ≤ H / (2 * m) * w t := by gcongr
      _ = w t * (H / (2 * m)) := mul_comm _ _
  have hΦ0b : ∀ z t, ‖Φ0 z t‖ ≤ ‖ξ‖ + ‖z‖ / 2 + H / (2 * m) := fun z t => by
    simp only [hΦ0]
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 (hw0 t)).le, hint]
    have hwi : (w t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hw1 t)
    calc (w t)⁻¹ * ‖ξ + ((∫ s in t₀..t, A s (w s • z s)) + ∫ s in t₀..t, h s)‖
        ≤ (w t)⁻¹ * (‖ξ‖ + (‖z‖ / 2 * w t + ‖∫ s in t₀..t, h s‖)) := by
          gcongr
          have := norm_add_le ξ ((∫ s in t₀..t, A s (w s • z s)) + ∫ s in t₀..t, h s)
          have := norm_add_le (∫ s in t₀..t, A s (w s • z s)) (∫ s in t₀..t, h s)
          have := hvol z t
          linarith
      _ = (w t)⁻¹ * ‖ξ‖ + ‖z‖ / 2 + (w t)⁻¹ * ‖∫ s in t₀..t, h s‖ := by
          field_simp [(hw0 t).ne']
          ring
      _ ≤ 1 * ‖ξ‖ + ‖z‖ / 2 + H / (2 * m) := by
          gcongr
          exact hhint t
      _ = _ := by ring
  have hΦ0c : ∀ z, Continuous (Φ0 z) := fun z => by
    simp only [hΦ0]
    refine (hwc.inv₀ fun t => (hw0 t).ne').smul (continuous_const.add ?_)
    exact intervalIntegral.continuous_primitive (fun a b => (hFc z).intervalIntegrable a b) t₀
  set Φ : (ℝ →ᵇ E) → (ℝ →ᵇ E) := fun z =>
    BoundedContinuousFunction.ofNormedAddCommGroup (Φ0 z) (hΦ0c z) _ (hΦ0b z) with hΦ
  have hcontr : ContractingWith (1 / 2) Φ := by
    refine ⟨by norm_num, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun z₁ z₂ => ?_
    rw [BoundedContinuousFunction.dist_le (by positivity)]
    intro t
    simp only [hΦ, BoundedContinuousFunction.coe_ofNormedAddCommGroup, hΦ0, dist_eq_norm]
    have hc1 : Continuous fun s => A s (w s • z₁ s) := hA.clm_apply (hwc.smul z₁.continuous)
    have hc2 : Continuous fun s => A s (w s • z₂ s) := hA.clm_apply (hwc.smul z₂.continuous)
    rw [← smul_sub, hint, hint, add_sub_add_comm, add_sub_add_right_eq_sub, sub_self, zero_add,
      ← intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
    have hd : ∀ s, A s (w s • z₁ s) - A s (w s • z₂ s) = A s (w s • (z₁ - z₂) s) := fun s => by
      simp [smul_sub]
    simp_rw [hd]
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 (hw0 t)).le, inv_mul_le_iff₀ (hw0 t)]
    calc ‖∫ s in t₀..t, A s (w s • (z₁ - z₂) s)‖ ≤ ‖z₁ - z₂‖ / 2 * w t := hvol _ t
      _ = w t * (↑(1 / 2 : NNReal) * ‖z₁ - z₂‖) := by push_cast; ring
  set z := ContractingWith.fixedPoint Φ hcontr
  have hz : ∀ t, z t = Φ0 z t := fun t => by
    have := hcontr.fixedPoint_isFixedPt
    exact (congrArg (fun f : ℝ →ᵇ E => f t) this).symm
  refine ⟨fun t => w t • z t, fun t => ?_, ?_⟩
  · have heq : (fun t => w t • z t) = fun t => ξ + ∫ s in t₀..t, F z s := by
      funext t
      rw [hz t]
      simp only [hΦ0, smul_smul, mul_inv_cancel₀ (hw0 t).ne', one_smul]
    rw [heq]
    have hd := intervalIntegral.integral_hasDerivAt_right ((hFc z).intervalIntegrable t₀ t)
      ((hFc z).stronglyMeasurableAtFilter _ _) (hFc z).continuousAt
    refine (hd.const_add ξ).congr_deriv ?_
    rw [← heq]
  · show w t₀ • z t₀ = ξ
    rw [hz t₀]
    simp [hΦ0, hw]

/-- The solution through `(t₀, ξ)`. -/
noncomputable def linSol (A : ℝ → E →L[ℝ] E) (h : ℝ → E) (t₀ : ℝ) (ξ : E) : ℝ → E := by
  classical
  exact if hs : ∃ y, IsLinSol A h y ∧ y t₀ = ξ then hs.choose else 0

theorem linSol_spec (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M) (hh : Continuous h)
    (hH : ∀ t, ‖h t‖ ≤ H) (t₀ : ℝ) (ξ : E) :
    IsLinSol A h (linSol A h t₀ ξ) ∧ linSol A h t₀ ξ t₀ = ξ := by
  have hs := exists_isLinSol hA hM hh hH t₀ ξ
  simp only [linSol, hs, ↓reduceDIte]
  exact hs.choose_spec

theorem eq_linSol (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M) (hh : Continuous h)
    (hH : ∀ t, ‖h t‖ ≤ H) (hy : IsLinSol A h y) (t₀ : ℝ) : y = linSol A h t₀ (y t₀) :=
  hy.eq_of_eq hM (linSol_spec hA hM hh hH t₀ (y t₀)).1 (t₀ := t₀)
    (linSol_spec hA hM hh hH t₀ (y t₀)).2.symm

theorem linSol_add (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M) (hh : Continuous h)
    (hH : ∀ t, ‖h t‖ ≤ H) (hh' : Continuous h') (hH' : ∀ t, ‖h' t‖ ≤ H) (t₀ : ℝ) (ξ η : E) :
    linSol A (h + h') t₀ (ξ + η) = linSol A h t₀ ξ + linSol A h' t₀ η := by
  have h1 := linSol_spec hA hM hh hH t₀ ξ
  have h2 := linSol_spec hA hM hh' hH' t₀ η
  have h3 := linSol_spec (h := h + h') (H := H + H) hA hM (hh.add hh')
    (fun t => (norm_add_le _ _).trans (add_le_add (hH t) (hH' t))) t₀ (ξ + η)
  exact h3.1.eq_of_eq hM (h1.1.add h2.1) (t₀ := t₀) (by simp [h1.2, h2.2, h3.2])

theorem linSol_smul (hA : Continuous A) (hM : ∀ t, ‖A t‖ ≤ M) (hh : Continuous h)
    (hH : ∀ t, ‖h t‖ ≤ H) (c : ℝ) (t₀ : ℝ) (ξ : E) :
    linSol A (c • h) t₀ (c • ξ) = c • linSol A h t₀ ξ := by
  have h1 := linSol_spec hA hM hh hH t₀ ξ
  have hH3 : ∀ t, ‖(c • h) t‖ ≤ ‖c‖ * H := fun t => by
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hH t) (norm_nonneg _)
  have h3 := linSol_spec hA hM (hh.const_smul c) hH3 t₀ (c • ξ)
  exact h3.1.eq_of_eq hM (h1.1.smul c) (t₀ := t₀) (by simp [h1.2, h3.2])

end Exist

/-- The backward Grönwall estimate: `‖y a‖ ≤ gronwallBound ‖y b‖ M H (b - a)` for `a ≤ b`. -/
theorem IsLinSol.norm_le_back (hM : ∀ t, ‖A t‖ ≤ M) (hH : ∀ t, ‖h t‖ ≤ H) (hy : IsLinSol A h y)
    {a b : ℝ} (hab : a ≤ b) : ‖y a‖ ≤ gronwallBound ‖y b‖ M H (b - a) := by
  set u : ℝ → E := fun s => y (-s)
  have hu : ∀ s, HasDerivAt u (-(A (-s) (u s) + h (-s))) s := fun s => by
    exact ((hy (-s)).scomp s (hasDerivAt_neg s)).congr_deriv (by simp only [u, neg_smul, one_smul])
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (f := u) (a := -b) (b := -a)
    (δ := ‖y b‖) (K := M) (ε := H)
    (HasDerivAt.continuousOn fun s _ => hu s) (fun s _ => (hu s).hasDerivWithinAt)
    (by simp [u]) (fun s _ => by
      rw [norm_neg]
      refine (norm_add_le _ _).trans (add_le_add ((A (-s)).le_opNorm _ |>.trans ?_) (hH _))
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)) (-a) ⟨by linarith, le_rfl⟩
  simpa [u, sub_eq_add_neg, add_comm] using hg

end ConleyCheck.Palmer
