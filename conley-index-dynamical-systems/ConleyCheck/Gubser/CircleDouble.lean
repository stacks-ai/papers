import ConleyCheck.Gubser.Separatrix
import ConleyCheck.Conley.CircleSign
import ConleyCheck.Algebra.ExactSplit

/-!
# The `B`-circle in the circle double

The separatrix `S_B` of the Gubser flow has ends `K_± = {(0, -1/√5)}` with
`CH_*(K_±) = ℤ[1]` (`cor_gubserB_i`). In the circle double, `CH_*(K₊ × {0}) = ℤ[1]` is torsion
free, so Theorem `thm:equivariant`(ii) splits the homology sequence of the attractor–repeller pair
`(K₊ × {0}, K₋ × {π})` of the `B`-circle `S̃_B = q⁻¹(S_B)` into short exact sequences, and
`CH_*(S̃_B; ℤ) = ℤ[1] ⊕ ℤ[2]` (`gubserB_circle`).
-/

namespace ConleyCheck.Gubser.Sep

open Set Function ConleyCheck.ODE ConleyCheck.Conley

variable {c : ℝ} (hc : c ≠ 0)

/-- The circle-double index of `S_B` (remark after `cor:gubserB`): over `ℤ`,
`CH_*(S̃_B) = ℤ[1] ⊕ ℤ[2]`. -/
theorem gubserB_circle :
    ∃ hS : IsIsolatedInvariantSet (circΦ (P hc).isSkew_Φ (P hc).isHeight_θ) (cq ⁻¹' SB),
      Nonempty (homologyIndex ℤ _ hS 1 ≃ₗ[ℤ] ℤ) ∧ Nonempty (homologyIndex ℤ _ hS 2 ≃ₗ[ℤ] ℤ) ∧
        ∀ n, n ≠ 1 → n ≠ 2 → Subsingleton (homologyIndex ℤ _ hS n) := by
  obtain ⟨hN, hInv, -, -, hKp, hKm, -, -, -, -, -, -, -, -, ⟨eP⟩, hp2, ⟨eM⟩, hm2⟩ :=
    cor_gubserB_i hc ℤ
  have hS : IsIsolatedInvariantSet (P hc).Φ SB := ⟨_, hN, hInv⟩
  have hΦ := (P hc).isSkew_Φ
  have hθ := (P hc).isHeight_θ
  obtain ⟨-, h⟩ := circ_attractorRepeller hΦ hθ hS
  obtain ⟨i, p, d, hip, -, -, -, -, htor⟩ := equivariant_ii hΦ hθ ℤ hS h
  have hA := circ_index_attractor hΦ hθ ℤ h.isolated_A hKp
  obtain ⟨hR, hR0⟩ := circ_index_repeller hΦ hθ ℤ h.isolated_R hKm
  have hAs : ∀ n, n ≠ 1 → Subsingleton (homologyIndex ℤ _ h.isolated_A n) := fun n hn => by
    have := hp2 n hn
    exact (hA n).some.toEquiv.subsingleton
  have hRs : ∀ n, n ≠ 2 → Subsingleton (homologyIndex ℤ _ h.isolated_R n) := fun n hn => by
    rcases n with _ | k
    · exact hR0
    · have := hm2 k (by omega)
      exact (hR k).some.toEquiv.subsingleton
  obtain ⟨-, hi, hp⟩ := htor fun n a ha => by
    rcases eq_or_ne n 1 with rfl | hn
    · let E := (hA 1).some.trans eP
      have h2 : (2 : ℕ) • E a = 0 := by rw [← map_nsmul, ha, map_zero]
      rw [nsmul_eq_mul] at h2
      have h0 : E a = 0 := by push_cast at h2; omega
      exact E.injective (h0.trans E.map_zero.symm)
    · have := hAs n hn
      exact Subsingleton.elim _ _
  refine ⟨h.isolated, ?_, ?_, fun n h1 h2 => ?_⟩
  · have hb : Bijective (i 1) := ⟨hi 1, fun y => by
      have := hRs 1 (by omega)
      exact (hip 1 y).1 (Subsingleton.elim _ _)⟩
    exact ⟨(LinearEquiv.ofBijective (i 1) hb).symm.trans ((hA 1).some.trans eP)⟩
  · have hb : Bijective (p 2) := ⟨fun y y' hyy' => by
      have := hAs 2 (by omega)
      have hz : p 2 (y - y') = 0 := by rw [map_sub, hyy', sub_self]
      obtain ⟨z, hz⟩ := (hip 2 _).1 hz
      rw [Subsingleton.elim z 0, map_zero] at hz
      exact sub_eq_zero.1 hz.symm, hp 2⟩
    exact ⟨(LinearEquiv.ofBijective (p 2) hb).trans ((hR 1).some.trans eM)⟩
  · have := hAs n h1
    have := hRs n h2
    exact subsingleton_of_exact (hip n)

end ConleyCheck.Gubser.Sep
