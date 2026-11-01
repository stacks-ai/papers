import ConleyCheck.Palmer.Fredholm

/-!
# Planar linear systems

`2 × 2` real matrices act on `ℝ² = Fin 2 → ℝ` (with the sup norm) through `matCLM`.
* `exists_dichotomy_pair`: a dichotomy from two independent eigenvectors with nonzero
  eigenvalues `l, m`, with `μ = [l > 0] + [m > 0]`;
* `exists_dichotomy_tri`: the case of a lower-triangular matrix `[[p, 0], [r, q]]`;
* `exists_bound_of_tendsto`: a continuous coefficient with limits at `±∞` is bounded.
-/

namespace ConleyCheck.Palmer

open Set Filter Topology Module Matrix

theorem exists_bound_of_tendsto {F : Type*} [NormedAddCommGroup F] {f : ℝ → F} {u v : F}
    (hf : Continuous f) (hu : Tendsto f atBot (𝓝 u)) (hv : Tendsto f atTop (𝓝 v)) :
    ∃ M, ∀ t, ‖f t‖ ≤ M := by
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (hv.norm.eventually (gt_mem_nhds (lt_add_one ‖v‖)))
  obtain ⟨T₂, hT₂⟩ := eventually_atBot.1 (hu.norm.eventually (gt_mem_nhds (lt_add_one ‖u‖)))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := T₂) (b := T₁)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max C (max (‖u‖ + 1) (‖v‖ + 1)), fun t => ?_⟩
  by_cases h1 : T₁ ≤ t
  · exact (hT₁ t h1).le.trans ((le_max_right _ _).trans (le_max_right _ _))
  by_cases h2 : t ≤ T₂
  · exact (hT₂ t h2).le.trans ((le_max_left _ _).trans (le_max_right _ _))
  exact (hC t ⟨by linarith, by linarith⟩).trans (le_max_left _ _)

/-- `M ↦ (v ↦ M v)`. -/
noncomputable def matCLM : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ((Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ Matrix.toLin'.toLinearMap)

@[simp]
theorem matCLM_apply (M : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) : matCLM M v = M *ᵥ v :=
  Matrix.toLin'_apply M v

theorem continuous_matCLM_comp {M : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (h : ∀ i j, Continuous fun t => M t i j) : Continuous fun t => matCLM (M t) :=
  matCLM.continuous.comp (continuous_matrix h)

theorem tendsto_matCLM_comp {M : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {M₀ : Matrix (Fin 2) (Fin 2) ℝ}
    {l : Filter ℝ} (h : ∀ i j, Tendsto (fun t => M t i j) l (𝓝 (M₀ i j))) :
    Tendsto (fun t => matCLM (M t)) l (𝓝 (matCLM M₀)) :=
  (matCLM.continuous.tendsto M₀).comp (tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => h i j)

/-- A dichotomy from two independent eigenvectors with nonzero eigenvalues. -/
theorem exists_dichotomy_pair {M : Matrix (Fin 2) (Fin 2) ℝ} {v w : Fin 2 → ℝ} {l m : ℝ}
    (hli : LinearIndependent ℝ ![v, w]) (hv : M *ᵥ v = l • v) (hw : M *ᵥ w = m • w)
    (hl : l ≠ 0) (hm : m ≠ 0) :
    ∃ d : Dichotomy (matCLM M), d.μ = (if 0 < l then 1 else 0) + (if 0 < m then 1 else 0) := by
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : ∀ i, matCLM M (b i) = ![l, m] i • b i := fun i => by
    fin_cases i <;> simp [b, hv, hw]
  refine ⟨Dichotomy.ofBasis hb (fun i => by fin_cases i <;> simp [hl, hm]), ?_⟩
  rw [Dichotomy.ofBasis_μ, Finset.card_filter, Fin.sum_univ_two]
  simp
  split_ifs with h <;> simp [h]

/-- A dichotomy for `[[p, 0], [r, q]]` with `p, q ≠ 0` and `p ≠ q` or `r = 0`, with
eigenvectors `(1, r/(p - q))` and `(0, 1)`. -/
theorem exists_dichotomy_tri {p r q : ℝ} (hpq : p ≠ q ∨ r = 0) (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ d : Dichotomy (matCLM !![p, 0; r, q]),
      d.μ = (if 0 < p then 1 else 0) + (if 0 < q then 1 else 0) := by
  refine exists_dichotomy_pair (v := ![1, r / (p - q)]) (w := ![0, 1]) ?_ ?_ ?_ hp hq
  · rw [LinearIndependent.pair_iff]
    intro s t h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    subst h0
    simpa using h1
  · ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rcases hpq with h | h
      · have : p - q ≠ 0 := sub_ne_zero.2 h
        simp
        field_simp
        ring
      · simp [h]
  · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end ConleyCheck.Palmer
