import ConleyCheck.Conley.SphereHomology
import ConleyCheck.Gubser.TCMinus

/-!
# The homology indices of `TC^±` (`lem:TC`)

From the homotopy indices of `lem:TC` and `sphere_homology`, for every ring `K`:

* `lem_TC_i_homology`: `CH_*(TC^+; K) = K[1]`.
* `lem_TC_ii_homology`: `CH_*(TC^-; K) = K[2]`.
* `lem_TC_iv_homology`: for the reversed flow, `CH_*(TC^+; K) = K[2]` and `CH_*(TC^-; K) = K[1]`.
-/

open ConleyCheck.Conley

namespace ConleyCheck.Gubser

variable (K : Type) [Ring K] {c δ δ' : ℝ}

theorem lem_TC_i_homology (H : TCHyp c δ δ') :
    Nonempty (homologyIndex K (ϕS c) (lem_TC_i H).isIsolated 1 ≃ₗ[K] K) ∧
      ∀ n : ℕ, n ≠ 1 → Subsingleton (homologyIndex K (ϕS c) (lem_TC_i H).isIsolated n) :=
  (lem_TC_i H).homologyIndex_sphere' K

theorem lem_TC_ii_homology (H : TCHyp c δ δ') :
    Nonempty (homologyIndex K (ϕSm c) (lem_TC_ii_minus H).isIsolated 2 ≃ₗ[K] K) ∧
      ∀ n : ℕ, n ≠ 2 → Subsingleton (homologyIndex K (ϕSm c) (lem_TC_ii_minus H).isIsolated n) :=
  (lem_TC_ii_minus H).homologyIndex_sphere' K

theorem lem_TC_iv_homology (H : TCHyp c δ δ') :
    (Nonempty (homologyIndex K (ϕS c).reverse (lem_TC_ii H).isIsolated 2 ≃ₗ[K] K) ∧
      ∀ n : ℕ, n ≠ 2 → Subsingleton (homologyIndex K (ϕS c).reverse (lem_TC_ii H).isIsolated n)) ∧
    (Nonempty (homologyIndex K (ϕSm c).reverse
        (lem_TC_i_minus_of (modelSm c) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) H).isIsolated
        1 ≃ₗ[K] K) ∧
      ∀ n : ℕ, n ≠ 1 → Subsingleton (homologyIndex K (ϕSm c).reverse
        (lem_TC_i_minus_of (modelSm c) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) H).isIsolated
        n)) :=
  ⟨(lem_TC_ii H).homologyIndex_sphere' K,
    (lem_TC_i_minus_of (modelSm c) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) H).homologyIndex_sphere'
      K⟩

end ConleyCheck.Gubser
