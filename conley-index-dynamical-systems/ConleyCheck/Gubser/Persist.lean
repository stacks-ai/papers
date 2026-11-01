import ConleyCheck.Gubser.Separatrix
import ConleyCheck.Conley.Persist

/-!
# Persistence of the Gubser connection under continuation

The paragraph after Corollary `cor:gubserB`: the UV→IR connection of `S_B` persists under every
deformation along which `S_B♮` and `K_-` continue, with integer coefficients. Indeed
`CH_*(S_B♮) = 0` and `CH_1(K_-) ≅ ℤ` (Corollary `cor:gubserB`(i)) are continuation invariants, and
they force `Ψ_1 ≠ 0` (`transport_persist`).
-/

namespace ConleyCheck.Gubser.Sep

open Set Function ConleyCheck.Conley

variable {c : ℝ} (hc : c ≠ 0)

/-- The UV→IR connection of `S_B` persists along continuations. Let `Φ₁` be a compactified flow
with an isolated invariant set `S₁`, such that `S_B♮` continues to `S₁♮` along a family `D` of
flows on the double and `K_- = {(0, -a)}` continues to `K_-¹` along a family `F` of flows on
`ℝ²`, each with a common isolating neighborhood. Then `S₁` contains a solution with
`-1 < τ < 1` that runs from `K_-¹` to `K_+¹`. -/
theorem gubserB_persist {Φ₁ : Flow ℝ ((ℝ × ℝ) × Tau)} {θ₁ : Flow ℝ Tau} (hΦ₁ : IsSkew Φ₁ θ₁)
    (hθ₁ : IsHeight θ₁ (fun b => (b : ℝ))) {S₁ : Set ((ℝ × ℝ) × Tau)}
    (hS₁ : IsIsolatedInvariantSet Φ₁ S₁)
    (D : FlowFamily ((ℝ × ℝ) × Dbl)) {M : Set ((ℝ × ℝ) × Dbl)} (hM : IsCompact M)
    (hMi : ∀ l, Inv (D.slice l) M ⊆ interior M)
    (hD0 : D.slice 0 = dblΦ (P hc).isSkew_Φ (P hc).isHeight_θ) (hD1 : D.slice 1 = dblΦ hΦ₁ hθ₁)
    (hM0 : Inv (D.slice 0) M = snat SB) (hM1 : Inv (D.slice 1) M = snat S₁)
    (F : FlowFamily (ℝ × ℝ)) {M' : Set (ℝ × ℝ)} (hM' : IsCompact M')
    (hM'i : ∀ l, Inv (F.slice l) M' ⊆ interior M')
    (hF0 : F.slice 0 = fiberFlow (P hc).isSkew_Φ Tau.bot (base_bot (P hc).isHeight_θ))
    (hF1 : F.slice 1 = fiberFlow hΦ₁ Tau.bot (base_bot hθ₁))
    (hF0' : Inv (F.slice 0) M' = {x | (x, Tau.bot) ∈ SB})
    (hF1' : Inv (F.slice 1) M' = {x | (x, Tau.bot) ∈ S₁}) :
    ∃ q ∈ S₁, (q.2 : ℝ) ∈ Ioo (-1) 1 ∧
      omegaLim Φ₁ q ⊆ S₁ ∩ (fun q => (q.2 : ℝ)) ⁻¹' {1} ∧
      alphaLim Φ₁ q ⊆ S₁ ∩ (fun q => (q.2 : ℝ)) ⁻¹' {-1} := by
  obtain ⟨-, -, -, hSn, hKp, hKm, Ψ, i, p, e1, e2, e3, h0, -, -, -, ⟨eM⟩, -⟩ := cor_gubserB_i hc ℤ
  refine transport_persist ℤ (P hc).isSkew_Φ (P hc).isHeight_θ hΦ₁ hθ₁ hS₁ D hM hMi hD0 hD1
    hM0 hM1 F hM' hM'i hF0 hF1 hF0' hF1' (k := 1) (fun h => h0 2) (fun h => ?_)
  exact eM.toEquiv.nontrivial

end ConleyCheck.Gubser.Sep
