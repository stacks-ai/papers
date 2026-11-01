import ConleyCheck.Conley.SphereHomology
import ConleyCheck.Conley.Continuation

/-!
# The homology index of a hyperbolic equilibrium

A hyperbolic equilibrium with `k` unstable directions has `CH_*(e; K) = K[k]` for every ring `K`
(`IsHyperbolicEquilibrium.homologyIndex`), from `hasIndex_sphere` and `sphere_homology`.
-/

namespace ConleyCheck.Conley

theorem IsHyperbolicEquilibrium.homologyIndex (K : Type) [Ring K] {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {ϕ : Flow ℝ E} {e : E}
    {k : ℕ} (h : IsHyperbolicEquilibrium ϕ e k) :
    Nonempty (homologyIndex K ϕ (hasIndex_sphere h).isIsolated k ≃ₗ[K] K) ∧
      ∀ n : ℕ, n ≠ k → Subsingleton (homologyIndex K ϕ (hasIndex_sphere h).isIsolated n) :=
  (hasIndex_sphere h).homologyIndex_sphere' K

end ConleyCheck.Conley
