import ConleyCheck.Palmer.Green

/-!
# Asymptotically hyperbolic systems on a half-line

Let `A : ℝ → E →L[ℝ] E` be continuous and bounded with `A(t) → A₀` as `t → ∞`, `A₀` hyperbolic.
Fix `T ≥ 0` with `‖A t - A₀‖ ≤ α/(4K)` for `t ≥ T` (`HalfData`). On `X = ℝ →ᵇ E`, with `𝒢` the
Green operator of `A₀` on `[T, ∞)`, `𝓑 z = (A - A₀) z` on `[T, ∞)` and `𝓔 ξ = e^{(t-T)A₀} P ξ`, the
Lyapunov–Perron equation `z = 𝓔 ξ + 𝒢 (𝓑 z + h)` has the unique solution
`z = (1 - 𝒢𝓑)⁻¹ (𝓔 ξ + 𝒢 h)` (Neumann series, `‖𝒢𝓑‖ ≤ 1/2`). Its restriction to `[T, ∞)` solves
`y' = A(t) y + h(t)` (`Y_eq`), and every solution bounded on `[T, ∞)` is of this form
(`eq_sol_of_bdd`). This is the roughness of exponential dichotomies in the form needed here.

Consequences:
* `finrank_stableSub`: `dim E^s = dim range P = n - μ₊`, where `E^s` is the space of initial
  values at `t = 0` of solutions of `y' = A(t) y` bounded on `[0, ∞)`;
* `Splus`: a bounded linear map `C⁰_b → E` such that a solution of `y' = A(t) y + h(t)` is bounded
  on `[0, ∞)` if and only if `y(0) - S₊ h ∈ E^s` (`bdd_iff_mem_stableSub`).
-/

namespace ConleyCheck.Palmer

open NormedSpace Set Filter Topology MeasureTheory BoundedContinuousFunction Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Initial values at `t = 0` of solutions of `y' = A(t) y` that are bounded on `S`. -/
def bddSub (A : ℝ → E →L[ℝ] E) (S : Set ℝ) : Submodule ℝ E where
  carrier := {ξ | ∃ y, IsLinSol A 0 y ∧ y 0 = ξ ∧ ∃ C, ∀ t ∈ S, ‖y t‖ ≤ C}
  add_mem' := by
    rintro _ _ ⟨y, hy, rfl, C, hC⟩ ⟨z, hz, rfl, D, hD⟩
    refine ⟨y + z, by simpa using hy.add hz, rfl, C + D, fun t ht => ?_⟩
    exact (norm_add_le _ _).trans (add_le_add (hC t ht) (hD t ht))
  zero_mem' := ⟨0, isLinSol_zero, rfl, 0, fun t _ => by simp⟩
  smul_mem' := by
    rintro c _ ⟨y, hy, rfl, C, hC⟩
    refine ⟨c • y, by simpa using hy.smul c, rfl, ‖c‖ * C, fun t ht => ?_⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC t ht) (norm_nonneg _)

/-- The stable subspace `E^s` at `t = 0`. -/
abbrev stableSub (A : ℝ → E →L[ℝ] E) : Submodule ℝ E := bddSub A (Ici 0)

/-- The unstable subspace `E^u` at `t = 0`. -/
abbrev unstableSub (A : ℝ → E →L[ℝ] E) : Submodule ℝ E := bddSub A (Iic 0)

variable {A : ℝ → E →L[ℝ] E} {A₀ : E →L[ℝ] E}

/-- Data for the half-line `[T, ∞)`. -/
structure HalfData (A : ℝ → E →L[ℝ] E) (A₀ : E →L[ℝ] E) where
  d : Dichotomy A₀
  T : ℝ
  hT : 0 ≤ T
  hA : Continuous A
  M : ℝ
  hM0 : 0 < M
  hM : ∀ t, ‖A t‖ ≤ M
  hB : ∀ t, T ≤ t → ‖A t - A₀‖ ≤ d.α / (4 * d.K)

omit [CompleteSpace E] in
theorem HalfData.exists_of_tendsto (d : Dichotomy A₀) (hA : Continuous A) {M : ℝ}
    (hM : ∀ t, ‖A t‖ ≤ M) (hlim : Tendsto A atTop (𝓝 A₀)) : ∃ H : HalfData A A₀, H.d = d := by
  have hδ : 0 < d.α / (4 * d.K) := div_pos d.hα (by linarith [d.hK])
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim _ hδ
  refine ⟨⟨d, max N 0, le_max_right _ _, hA, max M 0 + 1, by positivity,
    fun t => (hM t).trans (by linarith [le_max_left M 0]), fun t ht => ?_⟩, rfl⟩
  rw [← dist_eq_norm]
  exact (hN t ((le_max_left _ _).trans ht)).le

namespace HalfData

variable (H : HalfData A A₀)

omit [CompleteSpace E] in
theorem hδ : 0 ≤ H.d.α / (4 * H.d.K) := div_nonneg H.d.hα.le (by linarith [H.d.hK])

/-- `𝓑 z (t) = (A(max t T) - A₀) z(t)`. -/
noncomputable def opB : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) :=
  mkBCF (fun z t => (A (max t H.T) - A₀) (z t))
    (fun z => ((H.hA.comp (continuous_id.max continuous_const)).sub continuous_const).clm_apply
      z.continuous)
    (fun z z' t => by simp; abel) (fun c z t => by simp) (H.d.α / (4 * H.d.K)) (fun z t =>
      ((A (max t H.T) - A₀).le_opNorm _).trans (mul_le_mul (H.hB _ (le_max_right _ _))
        (z.norm_coe_le_norm t) (norm_nonneg _) H.hδ))

/-- `𝒢 g (t) = gr g (max t T)`. -/
noncomputable def opG : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) :=
  mkBCF (fun g t => gr H.d H.T g (max t H.T))
    (fun g => (continuous_gr g).comp (continuous_id.max continuous_const))
    (fun g g' _ => gr_add g g' _) (fun c g _ => gr_smul c g _) (2 * H.d.K / H.d.α)
    (fun g _ => norm_gr_le g (le_max_right _ _))

/-- `𝓔 ξ (t) = e^{(max t T - T) A₀} P ξ`. -/
noncomputable def opE : E →L[ℝ] (ℝ →ᵇ E) :=
  mkBCF (fun ξ t => exp ((max t H.T - H.T) • A₀) (H.d.P ξ))
    (fun ξ => ((continuous_exp_smul A₀).comp
      ((continuous_id.max continuous_const).sub continuous_const)).clm_apply continuous_const)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) H.d.K (fun ξ t =>
      H.d.norm_exp_P_le' (sub_nonneg.2 (le_max_right t H.T)) ξ)

theorem norm_opGB : ‖H.opG ∘L H.opB‖ < 1 := by
  have hK := H.d.hK
  have hα := H.d.hα
  refine ((H.opG.opNorm_comp_le H.opB).trans (mul_le_mul (norm_mkBCF_le (by positivity))
    (norm_mkBCF_le H.hδ) (norm_nonneg _) (by positivity))).trans_lt ?_
  rw [show 2 * H.d.K / H.d.α * (H.d.α / (4 * H.d.K)) = 1 / 2 by field_simp; ring]
  norm_num

/-- The inverse `(1 - 𝒢𝓑)⁻¹`. -/
noncomputable def opN : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) := ↑(Units.oneSub _ H.norm_opGB)⁻¹

theorem opN_spec (w : ℝ →ᵇ E) : H.opN w = H.opG (H.opB (H.opN w)) + w := by
  have h := (Units.oneSub _ H.norm_opGB).mul_inv
  have h2 := congrArg (fun f : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) => f w) h
  simp only [Units.val_oneSub, clm_mul_apply, clm_one_sub_apply] at h2
  rw [opN]
  exact (sub_eq_iff_eq_add.1 h2).trans (by rw [add_comm]; rfl)

theorem opN_unique {z w : ℝ →ᵇ E} (h : z = H.opG (H.opB z) + w) : z = H.opN w := by
  have hu := (Units.oneSub _ H.norm_opGB).inv_mul
  have h2 := congrArg (fun f : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) => f z) hu
  simp only [Units.val_oneSub, clm_mul_apply, clm_one_sub_apply] at h2
  rw [opN]
  have : z - (H.opG ∘L H.opB) z = w := by
    rw [ContinuousLinearMap.comp_apply]; nth_rw 1 [h]; abel
  rw [← this]
  exact h2.symm

/-- The solution `(1 - 𝒢𝓑)⁻¹ (𝓔 ξ + 𝒢 h)` of the Lyapunov–Perron equation. -/
noncomputable def sol (ξ : E) (h : ℝ →ᵇ E) : ℝ →ᵇ E := H.opN (H.opE ξ + H.opG h)

/-- The formula for `sol` on `[T, ∞)`, extended to `ℝ`. -/
noncomputable def u (ξ : E) (h : ℝ →ᵇ E) (τ : ℝ) : E :=
  exp ((τ - H.T) • A₀) (H.d.P ξ) + gr H.d H.T (H.opB (H.sol ξ h) + h) τ

theorem sol_eq (ξ : E) (h : ℝ →ᵇ E) (t : ℝ) : H.sol ξ h t = H.u ξ h (max t H.T) := by
  have := H.opN_spec (H.opE ξ + H.opG h)
  rw [← sol] at this
  have h2 := congrArg (fun f : ℝ →ᵇ E => f t) this
  simp only [coe_add, Pi.add_apply] at h2
  rw [h2, u]
  simp only [opG, opE, mkBCF_apply, gr_add]
  abel

theorem sol_eq_of_le (ξ : E) (h : ℝ →ᵇ E) {t : ℝ} (ht : H.T ≤ t) : H.sol ξ h t = H.u ξ h t := by
  rw [sol_eq, max_eq_left ht]

theorem hasDerivAt_u (ξ : E) (h : ℝ →ᵇ E) {τ : ℝ} (hτ : H.T ≤ τ) :
    HasDerivAt (H.u ξ h) (A τ (H.u ξ h τ) + h τ) τ := by
  have h1 := hasDerivAt_exp_sub_smul_apply A₀ (H.d.P ξ) H.T τ
  have h2 := hasDerivAt_gr (d := H.d) (T := H.T) (H.opB (H.sol ξ h) + h) τ
  refine (h1.add h2).congr_deriv ?_
  have hB : H.opB (H.sol ξ h) τ = (A τ - A₀) (H.u ξ h τ) := by
    simp only [opB, mkBCF_apply, max_eq_left hτ, H.sol_eq_of_le ξ h hτ]
  simp only [coe_add, Pi.add_apply, hB, u, _root_.sub_apply, map_add]
  abel

/-- The global solution of `y' = A(t) y + h(t)` that agrees with `sol ξ h` on `[T, ∞)`. -/
noncomputable def Y (ξ : E) (h : ℝ →ᵇ E) : ℝ → E := linSol A h H.T (H.sol ξ h H.T)

theorem isLinSol_Y (ξ : E) (h : ℝ →ᵇ E) : IsLinSol A h (H.Y ξ h) :=
  (linSol_spec H.hA H.hM h.continuous h.norm_coe_le_norm _ _).1

theorem Y_eq (ξ : E) (h : ℝ →ᵇ E) {t : ℝ} (ht : H.T ≤ t) : H.Y ξ h t = H.sol ξ h t := by
  have h0 := (linSol_spec H.hA H.hM h.continuous h.norm_coe_le_norm H.T (H.sol ξ h H.T)).2
  rw [H.sol_eq_of_le ξ h ht]
  refine (H.isLinSol_Y ξ h).eq_of_Ici H.hM (fun s hs => H.hasDerivAt_u ξ h hs) ?_ t ht
  rw [Y, h0, H.sol_eq_of_le ξ h le_rfl]

theorem Y_T (ξ : E) (h : ℝ →ᵇ E) : H.Y ξ h H.T = H.sol ξ h H.T := H.Y_eq ξ h le_rfl

theorem Y_bdd (ξ : E) (h : ℝ →ᵇ E) : ∃ C, ∀ t, 0 ≤ t → ‖H.Y ξ h t‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := 0) (b := H.T)).exists_bound_of_continuousOn
    (H.isLinSol_Y ξ h).continuous.norm.continuousOn
  refine ⟨max C ‖H.sol ξ h‖, fun t ht => ?_⟩
  rcases le_total t H.T with h1 | h1
  · have := hC t ⟨ht, h1⟩
    rw [norm_norm] at this
    exact this.trans (le_max_left _ _)
  · rw [H.Y_eq ξ h h1]
    exact (norm_coe_le_norm _ t).trans (le_max_right _ _)

/-- A solution that is bounded on `[T, ∞)` solves the Lyapunov–Perron equation. -/
theorem eq_sol_of_bdd {h : ℝ →ᵇ E} {y : ℝ → E} (hy : IsLinSol A h y) {C : ℝ}
    (hC : ∀ t, H.T ≤ t → ‖y t‖ ≤ C) {t : ℝ} (ht : H.T ≤ t) : y t = H.sol (y H.T) h t := by
  set yt : ℝ →ᵇ E := BoundedContinuousFunction.ofNormedAddCommGroup (fun t => y (max t H.T))
    (hy.continuous.comp (continuous_id.max continuous_const)) C
    (fun t => hC _ (le_max_right _ _)) with hyt
  set g : ℝ →ᵇ E := H.opB yt + h with hg
  set v : ℝ → E := fun τ => exp ((τ - H.T) • A₀) (H.d.P (y H.T)) + gr H.d H.T g τ with hv_def
  set w : ℝ → E := fun τ => y τ - v τ with hw_def
  have hgτ : ∀ τ, H.T ≤ τ → g τ = (A τ - A₀) (y τ) + h τ := fun τ hτ => by
    simp [hg, yt, opB, max_eq_left hτ]
  have hv : ∀ τ, H.T ≤ τ → HasDerivAt v (A₀ (v τ) + ((A τ - A₀) (y τ) + h τ)) τ := fun τ hτ => by
    refine ((hasDerivAt_exp_sub_smul_apply A₀ _ H.T τ).add (hasDerivAt_gr g τ)).congr_deriv ?_
    rw [← hgτ τ hτ, hv_def, map_add]; abel
  have hw : ∀ τ, H.T ≤ τ → HasDerivAt w (A₀ (w τ) + (0 : ℝ → E) τ) τ := fun τ hτ => by
    refine ((hy τ).sub (hv τ hτ)).congr_deriv ?_
    simp only [hw_def, Pi.zero_apply, add_zero, map_sub, _root_.sub_apply]; abel
  have hwT : H.d.P (w H.T) = 0 := by
    simp [hw_def, hv_def, H.d.P_apply_P, P_gr_T]
  set C' := C + (H.d.K * ‖y H.T‖ + 2 * H.d.K / H.d.α * ‖g‖)
  have hwb : ∀ τ, H.T ≤ τ → ‖w τ‖ ≤ C' := fun τ hτ => by
    refine (norm_sub_le _ _).trans (add_le_add (hC τ hτ) ((norm_add_le _ _).trans
      (add_le_add (H.d.norm_exp_P_le' (sub_nonneg.2 hτ) _) (norm_gr_le g hτ))))
  have hw_eq : ∀ τ, H.T ≤ τ → exp ((τ - H.T) • A₀) (w H.T) = w τ :=
    (isLinSol_exp_sub A₀ (w H.T) H.T).eq_of_Ici (M := ‖A₀‖) (fun _ => le_rfl) hw (by simp)
  have hw0 : w H.T = 0 := by
    have hb : ∀ s, 0 ≤ s → ‖w H.T‖ ≤ H.d.K * C' * Real.exp (-(H.d.α * s)) := fun s hs => by
      have h1 : w H.T = exp ((-s) • A₀) (w (s + H.T) - H.d.P (w (s + H.T))) := by
        rw [← hw_eq (s + H.T) (by linarith), add_sub_cancel_right, ← H.d.exp_P, hwT, map_zero,
          sub_zero, ← clm_mul_apply, exp_neg_mul_smul]
        rfl
      rw [h1]
      refine (H.d.norm_exp_Q_le hs _).trans ?_
      calc H.d.K * Real.exp (-(H.d.α * s)) * ‖w (s + H.T)‖
          ≤ H.d.K * Real.exp (-(H.d.α * s)) * C' := mul_le_mul_of_nonneg_left
            (hwb _ (by linarith)) (mul_nonneg H.d.hK.le (Real.exp_pos _).le)
        _ = _ := by ring
    have hlim : Tendsto (fun s => H.d.K * C' * Real.exp (-(H.d.α * s))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop H.d.hα)).const_mul (H.d.K * C')
      simpa using this
    exact norm_le_zero_iff.1 (ge_of_tendsto hlim (eventually_atTop.2 ⟨0, fun s hs => hb s hs⟩))
  have hyv : ∀ τ, H.T ≤ τ → y τ = v τ := fun τ hτ => by
    have := hw_eq τ hτ
    rw [hw0, map_zero] at this
    exact sub_eq_zero.1 this.symm
  have hfix : yt = H.opG (H.opB yt) + (H.opE (y H.T) + H.opG h) := by
    ext s
    have h1 : yt s = y (max s H.T) := rfl
    have := hyv (max s H.T) (le_max_right _ _)
    simp only [coe_add, Pi.add_apply, opG, opE, mkBCF_apply, h1, this, hv_def, hg, gr_add]
    abel
  have := H.opN_unique hfix
  rw [sol, ← this]
  show y t = y (max t H.T)
  rw [max_eq_left ht]

/-- The homogeneous solution through `(0, ξ)`. -/
@[nolint unusedArguments]
noncomputable def Z (_H : HalfData A A₀) (ξ : E) : ℝ → E := linSol A 0 0 ξ

theorem Z_spec (ξ : E) : IsLinSol A 0 (H.Z ξ) ∧ H.Z ξ 0 = ξ :=
  linSol_spec H.hA H.hM (h := 0) (H := 0) continuous_const (fun _ => by simp) 0 ξ

theorem eq_Z {y : ℝ → E} (hy : IsLinSol A 0 y) : y = H.Z (y 0) :=
  eq_linSol H.hA H.hM (h := 0) (H := 0) continuous_const (fun _ => by simp) hy 0

theorem Z_add (ξ η : E) : H.Z (ξ + η) = H.Z ξ + H.Z η := by
  have := linSol_add H.hA H.hM (h := 0) (h' := 0) (H := 0) continuous_const
    (fun _ => by simp) continuous_const (fun _ => by simp) 0 ξ η
  rwa [add_zero] at this

theorem Z_smul (c : ℝ) (ξ : E) : H.Z (c • ξ) = c • H.Z ξ := by
  have := linSol_smul H.hA H.hM (h := 0) (H := 0) continuous_const (fun _ => by simp) c 0 ξ
  rwa [smul_zero] at this

omit [NormedSpace ℝ E] [CompleteSpace E] H in
theorem coe_zero_bcf : ⇑(0 : ℝ →ᵇ E) = 0 := rfl

/-- `ξ ↦ P (y_ξ(T))`, an isomorphism `E^s ≅ range P`. -/
noncomputable def stableToRange : stableSub A →ₗ[ℝ] LinearMap.range (H.d.P : E →ₗ[ℝ] E) where
  toFun ξ := ⟨H.d.P (H.Z ξ H.T), LinearMap.mem_range_self _ _⟩
  map_add' ξ η := by ext; simp [H.Z_add]
  map_smul' c ξ := by ext; simp [H.Z_smul]

theorem stableToRange_bijective : Function.Bijective H.stableToRange := by
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro ⟨ξ, y, hy, rfl, C, hC⟩ h0
    have hP : H.d.P (y H.T) = 0 := by
      have := congrArg Subtype.val h0
      simpa [stableToRange, ← H.eq_Z hy] using this
    have hy' : IsLinSol A ⇑(0 : ℝ →ᵇ E) y := by rw [coe_zero_bcf]; exact hy
    have hT := H.eq_sol_of_bdd hy' (fun t ht => hC t (H.hT.trans ht)) le_rfl
    have hE : H.opE (y H.T) = 0 := by ext s; simp [opE, hP]
    have hs : H.sol (y H.T) 0 = 0 := by simp [sol, hE]
    rw [hs] at hT
    have := hy.eq_zero H.hM (t₀ := H.T) hT
    ext; simp [this]
  · rintro ⟨_, x, rfl⟩
    have hY := H.isLinSol_Y x 0
    rw [coe_zero_bcf] at hY
    obtain ⟨C, hC⟩ := H.Y_bdd x 0
    refine ⟨⟨H.Y x 0 0, H.Y x 0, hY, rfl, C, hC⟩, ?_⟩
    ext
    simp only [stableToRange, LinearMap.coe_mk, AddHom.coe_mk, ← H.eq_Z hY]
    rw [H.Y_T, H.sol_eq_of_le x 0 le_rfl, u, map_add, P_gr_T, add_zero, sub_self, zero_smul,
      exp_zero]
    exact H.d.P_apply_P x

/-- `dim E^s = dim range P`. -/
theorem finrank_stableSub :
    finrank ℝ (stableSub A) = finrank ℝ (LinearMap.range (H.d.P : E →ₗ[ℝ] E)) :=
  (LinearEquiv.ofBijective _ H.stableToRange_bijective).finrank_eq

theorem sol_zero_add (h h' : ℝ →ᵇ E) : H.sol 0 (h + h') = H.sol 0 h + H.sol 0 h' := by
  simp only [sol, map_zero, zero_add, map_add]

theorem sol_zero_smul (c : ℝ) (h : ℝ →ᵇ E) : H.sol 0 (c • h) = c • H.sol 0 h := by
  simp only [sol, map_zero, zero_add, map_smul]

theorem Y_zero_add (h h' : ℝ →ᵇ E) : H.Y 0 (h + h') = H.Y 0 h + H.Y 0 h' := by
  have := linSol_add H.hA H.hM h.continuous (H := ‖h‖ + ‖h'‖)
    (fun t => (h.norm_coe_le_norm t).trans (le_add_of_nonneg_right (norm_nonneg _)))
    h'.continuous (fun t => (h'.norm_coe_le_norm t).trans (le_add_of_nonneg_left (norm_nonneg _)))
    H.T (H.sol 0 h H.T) (H.sol 0 h' H.T)
  rw [Y, H.sol_zero_add]
  exact this

theorem Y_zero_smul (c : ℝ) (h : ℝ →ᵇ E) : H.Y 0 (c • h) = c • H.Y 0 h := by
  have := linSol_smul H.hA H.hM h.continuous h.norm_coe_le_norm c H.T (H.sol 0 h H.T)
  rw [Y, H.sol_zero_smul]
  exact this

theorem norm_Y_zero_le (h : ℝ →ᵇ E) :
    ‖H.Y 0 h 0‖ ≤ (‖H.opN‖ * ‖H.opG‖ * Real.exp (H.M * H.T) +
      (Real.exp (H.M * H.T) - 1) / H.M) * ‖h‖ := by
  have hb := (H.isLinSol_Y 0 h).norm_le_back H.hM h.norm_coe_le_norm H.hT
  rw [gronwallBound_of_K_ne_0 H.hM0.ne', sub_zero, H.Y_T] at hb
  have hs : ‖H.sol 0 h H.T‖ ≤ ‖H.opN‖ * ‖H.opG‖ * ‖h‖ := by
    refine (norm_coe_le_norm _ _).trans ?_
    rw [sol, map_zero, zero_add, mul_assoc]
    exact (H.opN.le_opNorm _).trans (mul_le_mul_of_nonneg_left (H.opG.le_opNorm _)
      (norm_nonneg _))
  have he : 0 ≤ Real.exp (H.M * H.T) - 1 := by
    have := Real.one_le_exp (mul_nonneg H.hM0.le H.hT); linarith
  refine hb.trans ?_
  calc ‖H.sol 0 h H.T‖ * Real.exp (H.M * H.T) + ‖h‖ / H.M * (Real.exp (H.M * H.T) - 1)
      ≤ ‖H.opN‖ * ‖H.opG‖ * ‖h‖ * Real.exp (H.M * H.T) +
          ‖h‖ / H.M * (Real.exp (H.M * H.T) - 1) := by gcongr
    _ = _ := by ring

/-- The bounded linear map `S₊ : C⁰_b → E`, `S₊ h = Y(0)` for the solution `Y` of
`y' = A(t) y + h(t)` produced by the Lyapunov–Perron equation, which is bounded on `[0, ∞)`. -/
noncomputable def Splus : (ℝ →ᵇ E) →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun h => H.Y 0 h 0
      map_add' := fun h h' => by rw [H.Y_zero_add]; rfl
      map_smul' := fun c h => by rw [H.Y_zero_smul]; rfl }
    _ H.norm_Y_zero_le

theorem Splus_apply (h : ℝ →ᵇ E) : H.Splus h = H.Y 0 h 0 := rfl

/-- A solution of `y' = A(t) y + h(t)` is bounded on `[0, ∞)` iff `y(0) - S₊ h ∈ E^s`. -/
theorem bdd_iff_mem_stableSub {h : ℝ →ᵇ E} {y : ℝ → E} (hy : IsLinSol A h y) :
    (∃ C, ∀ t, 0 ≤ t → ‖y t‖ ≤ C) ↔ y 0 - H.Splus h ∈ stableSub A := by
  obtain ⟨D, hD⟩ := H.Y_bdd 0 h
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨y - H.Y 0 h, by simpa using hy.sub (H.isLinSol_Y 0 h), rfl, C + D, fun t ht => ?_⟩
    exact (norm_sub_le _ _).trans (add_le_add (hC t ht) (hD t ht))
  · rintro ⟨w, hw, hw0, C, hC⟩
    have hyw : y = H.Y 0 h + w := hy.eq_of_eq H.hM (by simpa using (H.isLinSol_Y 0 h).add hw)
      (t₀ := 0) (by rw [Pi.add_apply, hw0, Splus_apply]; abel)
    refine ⟨D + C, fun t ht => ?_⟩
    rw [hyw]
    exact (norm_add_le _ _).trans (add_le_add (hD t ht) (hC t ht))

end HalfData

end ConleyCheck.Palmer
