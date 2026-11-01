import ConleyCheck.Palmer.GubserApp
import ConleyCheck.Analysis.CoshBeta

/-!
# Remark `rem:gap`: the slopes of `E^u` and `E^s`

For `τ = tanh`, the linearization `eq:linB` has the explicit solutions
`w = (0, cosh^{8a/3})`, unbounded in both directions, and
`u = (cosh^{-k}, cosh^{8a/3} · (a/c) ∫_{-∞}^ρ cosh^{-ν})`, bounded on `(-∞, 0]`,
with `k = (2 + a)/3` and `ν = 8a/3 + k`. Then `s = u - Δ w` is bounded on `[0, ∞)`, where
`Δ(c) = (a/c) ∫_ℝ cosh^{-ν}`. Hence `E^u = ⟨(1, Δ/2)⟩` and `E^s = ⟨(1, -Δ/2)⟩`
(`rem_gap`), and `Δ(c) = (a/c) √π Γ(ν/2) / Γ((ν + 1)/2)` by `integral_cosh_rpow_neg`.
-/

namespace ConleyCheck.Gubser.Sep

open Real MeasureTheory Set Filter Topology ConleyCheck.Palmer

/-- `ν = 8a/3 + k`, `k = (2 + a)/3`. -/
noncomputable def nuGap : ℝ := 8 * a / 3 + (2 + a) / 3

theorem nuGap_pos : 0 < nuGap := by have := a_pos; unfold nuGap; positivity

/-- Eq. `eq:gap`: `Δ(c) = (a/c) ∫_ℝ cosh^{-ν}`. -/
noncomputable def gap (c : ℝ) : ℝ := a / c * ∫ ρ, cosh ρ ^ (-nuGap)

variable {c : ℝ}

theorem hasDerivAt_cosh_rpow (p t : ℝ) :
    HasDerivAt (fun s => cosh s ^ p) (p * tanh t * cosh t ^ p) t := by
  have hc := cosh_pos t
  convert (hasDerivAt_cosh t).rpow_const (p := p) (Or.inl hc.ne') using 1
  rw [tanh_eq_sinh_div_cosh, Real.rpow_sub_one hc.ne']
  ring

theorem isLinSol_linB_iff {τ : ℝ → ℝ} {y : ℝ → Fin 2 → ℝ} :
    IsLinSol (linB c τ) 0 y ↔ ∀ t,
      HasDerivAt (fun s => y s 0) (-((2 + a) / 3) * τ t * y t 0) t ∧
        HasDerivAt (fun s => y s 1) (8 * a / 3 * τ t * y t 1 + a / c * y t 0) t := by
  unfold IsLinSol
  refine forall_congr' fun t => ?_
  rw [Pi.zero_apply, add_zero, hasDerivAt_pi, Fin.forall_fin_two, linB_apply_zero,
    linB_apply_one]

theorem norm_linB_tanh_le (t : ℝ) : ‖linB c tanh t‖ ≤ ‖linB₁‖ + ‖linB₂ c‖ := by
  have h1 : ‖tanh t • linB₁‖ ≤ ‖linB₁‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_tanh_lt_one t).le
  show ‖tanh t • linB₁ + linB₂ c‖ ≤ _
  exact (norm_add_le _ _).trans (by linarith)

/-- `∫_{-∞}^t cosh^{-ν}`. -/
noncomputable def Fm (t : ℝ) : ℝ := ∫ r in Iic t, cosh r ^ (-nuGap)

theorem continuous_cosh_rpow (p : ℝ) : Continuous fun r => cosh r ^ p :=
  continuous_cosh.rpow_const fun r => Or.inl (cosh_pos r).ne'

theorem hasDerivAt_Fm (t : ℝ) : HasDerivAt Fm (cosh t ^ (-nuGap)) t := by
  have hi := integrable_cosh_rpow_neg nuGap_pos
  have e : Fm = fun u => Fm 0 + ∫ r in (0 : ℝ)..u, cosh r ^ (-nuGap) := by
    funext u
    rw [← intervalIntegral.integral_Iic_sub_Iic (a := 0) (b := u) hi.integrableOn
      hi.integrableOn, Fm, Fm]
    ring
  rw [e]
  exact (((continuous_cosh_rpow _).integral_hasStrictDerivAt 0 t).hasDerivAt).const_add _

theorem Fm_neg (t : ℝ) : Fm (-t) = (∫ r, cosh r ^ (-nuGap)) - Fm t := by
  have hi := integrable_cosh_rpow_neg nuGap_pos
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := t) hi.integrableOn hi.integrableOn, Fm, Fm,
    add_sub_cancel_left, ← integral_comp_neg_Ioi]
  simp only [cosh_neg]

theorem Fm_zero : Fm 0 = (∫ r, cosh r ^ (-nuGap)) / 2 := by
  have := Fm_neg 0
  rw [neg_zero] at this
  linarith

theorem Fm_nonneg (t : ℝ) : 0 ≤ Fm t :=
  setIntegral_nonneg measurableSet_Iic fun r _ => (rpow_pos_of_pos (cosh_pos r) _).le

/-- For `t ≤ 0`, `cosh^{8a/3} t · ∫_{-∞}^t cosh^{-ν} ≤ ∫_ℝ cosh^{-k}`. -/
theorem coshm_mul_Fm_le {t : ℝ} (ht : t ≤ 0) :
    cosh t ^ (8 * a / 3) * Fm t ≤ ∫ r, cosh r ^ (-((2 + a) / 3)) := by
  have ha := a_pos
  have hk : 0 < (2 + a) / 3 := by positivity
  have hik := integrable_cosh_rpow_neg hk
  have hct := cosh_pos t
  have h1 : Fm t ≤ ∫ r in Iic t, cosh t ^ (-(8 * a / 3)) * cosh r ^ (-((2 + a) / 3)) := by
    refine setIntegral_mono_on (integrable_cosh_rpow_neg nuGap_pos).integrableOn
      (hik.integrableOn.const_mul _) measurableSet_Iic fun r hr => ?_
    have hr' : r ≤ t := hr
    have hcr := cosh_pos r
    have hle : cosh t ≤ cosh r :=
      cosh_le_cosh.2 (by rw [abs_of_nonpos ht, abs_of_nonpos (hr'.trans ht)]; linarith)
    rw [nuGap, neg_add, rpow_add hcr]
    exact mul_le_mul_of_nonneg_right (rpow_le_rpow_of_nonpos hct hle (by linarith))
      (rpow_nonneg hcr.le _)
  rw [integral_const_mul] at h1
  have h2 : ∫ r in Iic t, cosh r ^ (-((2 + a) / 3)) ≤ ∫ r, cosh r ^ (-((2 + a) / 3)) :=
    setIntegral_le_integral hik (Eventually.of_forall fun r => (rpow_pos_of_pos (cosh_pos r) _).le)
  have h3 : cosh t ^ (8 * a / 3) * cosh t ^ (-(8 * a / 3)) = 1 := by
    rw [← rpow_add hct]; simp
  calc cosh t ^ (8 * a / 3) * Fm t
      ≤ cosh t ^ (8 * a / 3) *
          (cosh t ^ (-(8 * a / 3)) * ∫ r in Iic t, cosh r ^ (-((2 + a) / 3))) :=
        mul_le_mul_of_nonneg_left h1 (rpow_nonneg hct.le _)
    _ = ∫ r in Iic t, cosh r ^ (-((2 + a) / 3)) := by rw [← mul_assoc, h3, one_mul]
    _ ≤ _ := h2

/-- The homogeneous `δπ`-mode `(0, cosh^{8a/3})`. -/
noncomputable def solW (t : ℝ) : Fin 2 → ℝ := ![0, cosh t ^ (8 * a / 3)]

/-- The solution bounded on `(-∞, 0]`. -/
noncomputable def solU (c t : ℝ) : Fin 2 → ℝ :=
  ![cosh t ^ (-((2 + a) / 3)), cosh t ^ (8 * a / 3) * (a / c * Fm t)]

theorem isLinSol_solW : IsLinSol (linB c tanh) 0 solW := isLinSol_linB_iff.2 fun t => by
  refine ⟨?_, ?_⟩
  · show HasDerivAt (fun _ => (0 : ℝ)) (-((2 + a) / 3) * tanh t * 0) t
    rw [mul_zero]; exact hasDerivAt_const _ _
  · show HasDerivAt (fun s => cosh s ^ (8 * a / 3))
      (8 * a / 3 * tanh t * cosh t ^ (8 * a / 3) + a / c * 0) t
    rw [mul_zero, add_zero]; exact hasDerivAt_cosh_rpow _ t

theorem isLinSol_solU : IsLinSol (linB c tanh) 0 (solU c) := isLinSol_linB_iff.2 fun t => by
  refine ⟨hasDerivAt_cosh_rpow _ t, ?_⟩
  show HasDerivAt (fun s => cosh s ^ (8 * a / 3) * (a / c * Fm s))
    (8 * a / 3 * tanh t * (cosh t ^ (8 * a / 3) * (a / c * Fm t)) +
      a / c * cosh t ^ (-((2 + a) / 3))) t
  have := (hasDerivAt_cosh_rpow (8 * a / 3) t).mul ((hasDerivAt_Fm t).const_mul (a / c))
  convert this using 1
  have e : cosh t ^ (8 * a / 3) * cosh t ^ (-nuGap) = cosh t ^ (-((2 + a) / 3)) := by
    rw [← rpow_add (cosh_pos t)]; congr 1; unfold nuGap; ring
  rw [← e]; ring

theorem norm_vec2_le {x : Fin 2 → ℝ} {C : ℝ} (hC : 0 ≤ C) (h0 : |x 0| ≤ C) (h1 : |x 1| ≤ C) :
    ‖x‖ ≤ C :=
  (pi_norm_le_iff_of_nonneg hC).2 fun i => by fin_cases i <;> simpa

theorem cosh_rpow_neg_le_one {p : ℝ} (hp : 0 ≤ p) (t : ℝ) : |cosh t ^ (-p)| ≤ 1 := by
  rw [abs_of_pos (rpow_pos_of_pos (cosh_pos t) _)]
  exact rpow_le_one_of_one_le_of_nonpos (one_le_cosh t) (by linarith)

/-- The bound for both half-line solutions. -/
noncomputable def solBound (c : ℝ) : ℝ := max 1 (|a / c| * ∫ r, cosh r ^ (-((2 + a) / 3)))

theorem solU_bdd {t : ℝ} (ht : t ≤ 0) : ‖solU c t‖ ≤ solBound c := by
  have hk : 0 ≤ (2 + a) / 3 := by have := a_pos; positivity
  refine norm_vec2_le (le_max_of_le_left zero_le_one)
    ((cosh_rpow_neg_le_one hk t).trans (le_max_left _ _)) ?_
  show |cosh t ^ (8 * a / 3) * (a / c * Fm t)| ≤ _
  rw [show cosh t ^ (8 * a / 3) * (a / c * Fm t) = a / c * (cosh t ^ (8 * a / 3) * Fm t) by ring,
    abs_mul, abs_of_nonneg (mul_nonneg (rpow_nonneg (cosh_pos t).le _) (Fm_nonneg t))]
  exact (mul_le_mul_of_nonneg_left (coshm_mul_Fm_le ht) (abs_nonneg _)).trans (le_max_right _ _)

theorem solU_zero : solU c 0 = ![1, gap c / 2] := by
  ext i; fin_cases i <;> simp [solU, Fm_zero, gap]; ring

/-- The solution bounded on `[0, ∞)`. -/
noncomputable def solS (c : ℝ) : ℝ → Fin 2 → ℝ := solU c - gap c • solW

theorem isLinSol_solS : IsLinSol (linB c tanh) 0 (solS c) := by
  have := (isLinSol_solU (c := c)).sub ((isLinSol_solW (c := c)).smul (gap c))
  rwa [smul_zero, sub_zero] at this

theorem solS_apply_one (t : ℝ) :
    solS c t 1 = -(cosh (-t) ^ (8 * a / 3) * (a / c * Fm (-t))) := by
  simp only [solS, solU, solW, gap, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Fm_neg, cosh_neg]
  simp; ring

theorem solS_bdd {t : ℝ} (ht : 0 ≤ t) : ‖solS c t‖ ≤ solBound c := by
  have hk : 0 ≤ (2 + a) / 3 := by have := a_pos; positivity
  refine norm_vec2_le (le_max_of_le_left zero_le_one) ?_ ?_
  · have : solS c t 0 = cosh t ^ (-((2 + a) / 3)) := by simp [solS, solU, solW]
    rw [this]; exact (cosh_rpow_neg_le_one hk t).trans (le_max_left _ _)
  · rw [solS_apply_one, abs_neg]
    have := solU_bdd (c := c) (neg_nonpos.2 ht)
    exact (norm_le_pi_norm (solU c (-t)) 1).trans this

theorem solS_zero : solS c 0 = ![1, -(gap c / 2)] := by
  rw [solS, Pi.sub_apply, solU_zero]
  ext i; fin_cases i <;> simp [solW]; ring

theorem tendsto_cosh_rpow_atTop {m : ℝ} (hm : 0 < m) :
    Tendsto (fun t => cosh t ^ m) atTop atTop := by
  have h1 : Tendsto cosh atTop atTop :=
    tendsto_atTop_mono (fun t => by rw [cosh_eq]; linarith [exp_pos (-t)])
      (tendsto_exp_atTop.atTop_div_const two_pos)
  exact (tendsto_rpow_atTop hm).comp h1

theorem exists_Ici_gt (C : ℝ) : ∃ t ∈ Ici (0 : ℝ), C < cosh t ^ (8 * a / 3) := by
  obtain ⟨t, h1, h2⟩ := (((tendsto_cosh_rpow_atTop (m := 8 * a / 3) (by have := a_pos; positivity)).eventually_gt_atTop
    C).and (eventually_ge_atTop 0)).exists
  exact ⟨t, h2, h1⟩

theorem exists_Iic_gt (C : ℝ) : ∃ t ∈ Iic (0 : ℝ), C < cosh t ^ (8 * a / 3) := by
  obtain ⟨t, h1, h2⟩ := exists_Ici_gt C
  exact ⟨-t, show -t ≤ 0 from neg_nonpos.2 h1, by rwa [cosh_neg]⟩

/-- A half-line bounded subspace of `eq:linB` with `τ = tanh` is spanned by any bounded solution
`v` with `δT(0) = 1`, provided `cosh^{8a/3}` is unbounded on the half line. -/
theorem bddSub_linB_tanh {S : Set ℝ} {v : ℝ → Fin 2 → ℝ} (hv : IsLinSol (linB c tanh) 0 v)
    (hv0 : v 0 0 = 1) (hvb : ∃ C, ∀ t ∈ S, ‖v t‖ ≤ C)
    (hS : ∀ C, ∃ t ∈ S, C < cosh t ^ (8 * a / 3)) :
    bddSub (linB c tanh) S = Submodule.span ℝ {v 0} := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl, C, hC⟩
    obtain ⟨Cv, hCv⟩ := hvb
    set β := y 0 1 - y 0 0 * v 0 1 with hβdef
    have hz : IsLinSol (linB c tanh) 0 (y 0 0 • v + β • solW) := by
      have := (hv.smul (y 0 0)).add (isLinSol_solW.smul β)
      rwa [smul_zero, smul_zero, add_zero] at this
    have hyz : y = y 0 0 • v + β • solW := hy.eq_of_eq norm_linB_tanh_le hz (t₀ := 0) (by
      funext i; fin_cases i <;> simp [solW, hv0, β])
    have hβ : β = 0 := by
      by_contra hβ
      have hβp : 0 < |β| := abs_pos.2 hβ
      obtain ⟨t, htS, ht⟩ := hS ((C + |y 0 0| * Cv) / |β|)
      have e := congrFun (congrFun hyz t) 1
      have e' : (y 0 0 • v + β • solW) t 1 = y 0 0 * v t 1 + β * cosh t ^ (8 * a / 3) := by
        simp [solW]
      rw [e'] at e
      have hy1 : |y t 1| ≤ C := by
        rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm (y t) 1).trans (hC t htS)
      have hv1 : |v t 1| ≤ Cv := by
        rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm (v t) 1).trans (hCv t htS)
      have h1 : |β| * cosh t ^ (8 * a / 3) ≤ C + |y 0 0| * Cv := by
        calc |β| * cosh t ^ (8 * a / 3) = |β * cosh t ^ (8 * a / 3)| := by
              rw [abs_mul, abs_of_pos (rpow_pos_of_pos (cosh_pos t) _)]
          _ = |y t 1 - y 0 0 * v t 1| := by rw [e]; ring_nf
          _ ≤ |y t 1| + |y 0 0 * v t 1| := abs_sub _ _
          _ ≤ C + |y 0 0| * Cv := by
              rw [abs_mul]; gcongr
      rw [div_lt_iff₀ hβp] at ht
      linarith
    have e := congrFun hyz 0
    rw [hβ, zero_smul, add_zero] at e
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨v, hv, rfl, hvb⟩

/-- Remark `rem:gap`. For `τ = tanh`, `E^u = ⟨(1, Δ/2)⟩` and `E^s = ⟨(1, -Δ/2)⟩` in the
`(δT, δπ)` plane, with `Δ(c) = (a/c) ∫_ℝ cosh^{-ν} = (a/c) √π Γ(ν/2) / Γ((ν + 1)/2)`,
`ν = 8a/3 + k`. For `c > 0`, `Δ(c) > 0`, and `Δ(c) → 0` as `c → ∞`. -/
theorem rem_gap :
    unstableSub (linB c tanh) = Submodule.span ℝ {![1, gap c / 2]} ∧
      stableSub (linB c tanh) = Submodule.span ℝ {![1, -(gap c / 2)]} ∧
      gap c = a / c * (√π * Real.Gamma (nuGap / 2) / Real.Gamma ((nuGap + 1) / 2)) ∧
      (0 < c → 0 < gap c) ∧ Tendsto gap atTop (𝓝 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← solU_zero]
    exact bddSub_linB_tanh isLinSol_solU (by simp [solU]) ⟨_, fun t ht => solU_bdd ht⟩
      exists_Iic_gt
  · rw [← solS_zero]
    exact bddSub_linB_tanh isLinSol_solS (by simp [solS, solU, solW])
      ⟨_, fun t ht => solS_bdd ht⟩ exists_Ici_gt
  · rw [gap, integral_cosh_rpow_neg nuGap_pos]
  · intro hc
    rw [gap, integral_cosh_rpow_neg nuGap_pos]
    have := a_pos
    have := nuGap_pos
    have h1 := Real.Gamma_pos_of_pos (show 0 < nuGap / 2 by positivity)
    have h2 := Real.Gamma_pos_of_pos (show 0 < (nuGap + 1) / 2 by positivity)
    have h3 : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
    positivity
  · have : gap = fun c => (a * ∫ ρ, cosh ρ ^ (-nuGap)) * c⁻¹ := by
      funext c; rw [gap]; ring
    rw [this]
    simpa using tendsto_inv_atTop_zero.const_mul (a * ∫ ρ, cosh ρ ^ (-nuGap))

end ConleyCheck.Gubser.Sep
