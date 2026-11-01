import ConleyCheck.ODE.Flow
import ConleyCheck.ODE.Fence
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Global flows of cut-off vector fields

For a `C¹` vector field `f` on a finite-dimensional space and a radius `R > 0`, the field
`bumpField f R = β • f`, with `β` a smooth bump equal to `1` on the closed ball of radius `R`,
is bounded and globally Lipschitz, and so generates a global flow `bumpFlow`. It agrees with `f`
on the ball, so `bumpFlow` is the flow of `f` there.
-/

open Set Filter Topology Metric
open scoped NNReal

namespace ConleyCheck.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A smooth bump equal to `1` on `closedBall 0 R`. -/
noncomputable def bumpOf (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : E) := ⟨R, R + 1, hR, by linarith⟩

/-- The cut-off field `β • f`. -/
noncomputable def bumpField (f : E → E) (R : ℝ) (hR : 0 < R) (p : E) : E :=
  (bumpOf (E := E) R hR : E → ℝ) p • f p

variable {f : E → E} {R : ℝ} {hR : 0 < R}

theorem bumpOf_eq_one {p : E} (hp : ‖p‖ ≤ R) : (bumpOf (E := E) R hR : E → ℝ) p = 1 :=
  (bumpOf R hR).one_of_mem_closedBall (mem_closedBall_zero_iff.2 hp)

theorem continuous_bumpOf : Continuous (bumpOf (E := E) R hR : E → ℝ) :=
  (bumpOf R hR).continuous

variable (hf : ContDiff ℝ 1 f)
include hf

theorem exists_lipschitz_bumpField : ∃ K : ℝ≥0, LipschitzWith K (bumpField f R hR) :=
  ContDiff.lipschitzWith_of_hasCompactSupport (bumpOf R hR).hasCompactSupport.smul_right
    ((bumpOf R hR).contDiff.smul hf) one_ne_zero

theorem exists_bound_bumpField : ∃ L : ℝ≥0, ∀ x, ‖bumpField f R hR x‖ ≤ L := by
  obtain ⟨C, hC⟩ := ((bumpOf R hR).hasCompactSupport.smul_right (f' := f)).exists_bound_of_continuous
    ((bumpOf R hR).contDiff.smul hf).continuous
  exact ⟨⟨max C 0, le_max_right _ _⟩, fun x => (hC x).trans (le_max_left C 0)⟩

variable [CompleteSpace E]

/-- The flow of the cut-off field. -/
noncomputable def bumpFlow (R : ℝ) (hR : 0 < R) : Flow ℝ E :=
  flowOf (exists_lipschitz_bumpField (hR := hR) hf).choose_spec
    (exists_bound_bumpField (hR := hR) hf).choose_spec

theorem hasDerivAt_bumpFlow (x : E) (t : ℝ) :
    HasDerivAt (fun s => bumpFlow hf R hR s x)
      ((bumpOf (E := E) R hR : E → ℝ) (bumpFlow hf R hR t x) • f (bumpFlow hf R hR t x)) t :=
  hasDerivAt_flowOf _ _ x t

end ConleyCheck.ODE
