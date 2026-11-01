import ConleyCheck.Palmer.Fredholm

/-!
# Scalar linear systems

`y' = a(t) y` on `ℝ`, with `a(t) • 1 : ℝ →L[ℝ] ℝ`.
* `exists_dichotomy_scalar`: for `l ≠ 0`, `y' = l y` has an exponential dichotomy with
  `μ = [l > 0]`;
* `continuous_scal`, `tendsto_scal`: continuity and limits of `t ↦ a(t) • 1`.
-/

namespace ConleyCheck.Palmer

open Set Filter Topology Module

/-- The dichotomy of `y' = l y`, `l ≠ 0`, with `μ = 1` if `l > 0` and `μ = 0` if `l < 0`. -/
theorem exists_dichotomy_scalar {l : ℝ} (hl : l ≠ 0) :
    ∃ d : Dichotomy (l • (1 : ℝ →L[ℝ] ℝ)), d.μ = if 0 < l then 1 else 0 := by
  classical
  let b : Basis (Fin 1) ℝ ℝ := Basis.singleton (Fin 1) ℝ
  have hb : ∀ i, (l • (1 : ℝ →L[ℝ] ℝ)) (b i) = (fun _ => l) i • b i := fun i => by simp
  refine ⟨Dichotomy.ofBasis hb (fun _ => hl), ?_⟩
  rw [Dichotomy.ofBasis_μ]
  split_ifs with h <;> simp [h]

theorem continuous_scal {a : ℝ → ℝ} (ha : Continuous a) :
    Continuous fun t => a t • (1 : ℝ →L[ℝ] ℝ) :=
  ha.smul continuous_const

theorem tendsto_scal {a : ℝ → ℝ} {l : Filter ℝ} {a₀ : ℝ} (ha : Tendsto a l (𝓝 a₀)) :
    Tendsto (fun t => a t • (1 : ℝ →L[ℝ] ℝ)) l (𝓝 (a₀ • (1 : ℝ →L[ℝ] ℝ))) :=
  ha.smul_const _

end ConleyCheck.Palmer
