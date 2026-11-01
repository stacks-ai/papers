import ConleyCheck.Gubser.NoMpMm
import ConleyCheck.Gubser.MIndex
import ConleyCheck.ON.Limits

/-!
# Theorem `thm:M`

The precise form of Appendix `app:3d`, for `0 < η < a` and `δ` satisfying `(k1)`–`(k3)` of
`eq:kcond` (`KHyp`):

* (i) `M^∓ = Inv(K^∓)` have trivial Conley index (`KHyp.indexTrivial_Mm`, `KHyp.indexTrivial_Mp`).
* (ii) The equilibria with `y₂ < 0` lie in `M⁻` and those with `y₂ > a y₃` lie in `M⁺`
  (`fixed_mem_Mm`, `fixed_mem_Mp`). This covers the points `Σ_U(B)`, `Σ_I(B)`, `Σ_U(C)`,
  `Σ_I(C)` and the complexes `X^∓` listed in part (ii) of the main text.
* (iii) `Σ_I(A) < TC⁺ < M⁻, M⁺ < TC⁻ < Σ_U(A)` is a Morse decomposition of `Ω` (`thmM_morse`),
  and no orbit connects `M⁻` and `M⁺` (`no_conn_Mm_Mp`).
-/

open Set Filter Topology
open ConleyCheck.Conley ConleyCheck.ODE

namespace ConleyCheck.Gubser

variable {c a η δ : ℝ}

section Hyp

variable (H : KHyp c a η δ)
include H

theorem isClosed_MG (i : GM) : IsClosed (MG c a η δ i) := by
  obtain ⟨N, hN⟩ := exists_isConvexNbhd H i
  rw [← hN.inv]
  exact isClosed_Inv hN.isClosed

theorem MG_inv (i : GM) {z : OmG} (hz : z ∈ MG c a η δ i) (t : ℝ) : ϕG c t z ∈ MG c a η δ i := by
  obtain ⟨N, hN⟩ := exists_isConvexNbhd H i
  rw [← hN.inv] at hz ⊢
  exact flow_mem_Inv hz t

theorem conn_rank {x : OmG} (hx : ∀ k, x ∉ MG c a η δ k) {i j : GM}
    (hω : (omegaLim (ϕG c) x ∩ MG c a η δ i).Nonempty)
    (hα : (alphaLim (ϕG c) x ∩ MG c a η δ j).Nonempty) : i.rank < j.rank := by
  have hR := isReversor_revΩ c
  have rα : ∀ {S : Set OmG}, revΩ ⁻¹' S = S → (omegaLim (ϕG c) x ∩ S).Nonempty →
      (alphaLim (ϕG c) (revΩ x) ∩ S).Nonempty := fun hS ⟨z, hz, hzS⟩ =>
    ⟨revΩ z, hR.mem_alphaLim hz, by rw [← hS] at hzS; exact hzS⟩
  have rω : ∀ {S : Set OmG}, revΩ ⁻¹' S = S → (alphaLim (ϕG c) x ∩ S).Nonempty →
      (omegaLim (ϕG c) (revΩ x) ∩ S).Nonempty := fun hS ⟨z, hz, hzS⟩ =>
    ⟨revΩ z, hR.mem_omegaLim hz, by rw [← hS] at hzS; exact hzS⟩
  have rT : (omegaLim (ϕG c) x ∩ revΩ ⁻¹' TCp).Nonempty →
      (alphaLim (ϕG c) (revΩ x) ∩ TCp).Nonempty := fun ⟨z, hz, hzS⟩ =>
    ⟨revΩ z, hR.mem_alphaLim hz, hzS⟩
  have hxT : revΩ x ∉ TCp := fun h => hx .Tm h
  have E3a : (alphaLim (ϕG c) x ∩ Inv (ϕG c) (Km a η δ)).Nonempty →
      (omegaLim (ϕG c) x ∩ Inv (ϕG c) (Kp a η δ)).Nonempty → False := fun hα hω => by
    rcases le_or_gt 0 (gy1 x) with hy | hy
    · exact no_conn_Bm_Bp H hy hα hω
    · exact no_conn_Bp_Bm H (x := revΩ x) (by rw [gy1_rev]; linarith)
        (rα revΩ_preimage_Mp hω) (rω revΩ_preimage_Mm hα)
  have E3b : (alphaLim (ϕG c) x ∩ Inv (ϕG c) (Kp a η δ)).Nonempty →
      (omegaLim (ϕG c) x ∩ Inv (ϕG c) (Km a η δ)).Nonempty → False := fun hα hω => by
    rcases le_or_gt (gy1 x) 0 with hy | hy
    · exact no_conn_Bm_Bp H (x := revΩ x) (by rw [gy1_rev]; linarith)
        (rα revΩ_preimage_Mm hω) (rω revΩ_preimage_Mp hα)
    · exact no_conn_Bp_Bm H hy hα hω
  by_cases hij : i = j
  · subst hij
    obtain ⟨N, hN⟩ := exists_isConvexNbhd H i
    exact absurd (hN.mem_of_limits hω hα) (hx i)
  cases i <;> cases j <;> first
    | decide
    | exact absurd rfl hij
    | exact (no_conn_A H (hx .A) hα).elim
    | exact (no_conn_R H (hx .R) hω).elim
    | exact (no_conn_TCp H (hx .Tp) hα (by decide) hω).elim
    | exact (no_conn_TCp H hxT (rT hω) (i := .Bm) (by decide) (rω revΩ_preimage_Mm hα)).elim
    | exact (no_conn_TCp H hxT (rT hω) (i := .Bp) (by decide) (rω revΩ_preimage_Mp hα)).elim
    | exact (E3a hα hω).elim
    | exact (E3b hα hω).elim

/-- **Theorem `thm:M` (iii).** The six sets, ordered by rank, form a Morse decomposition of `Ω`. -/
theorem thmM_morse :
    IsMorseDecomp (ϕG c) univ (MG c a η δ) fun i j => i.rank < j.rank where
  isolated := isIsolatedInvariantSet_univ (ϕG c)
  isolated_M i := by
    obtain ⟨N, hN⟩ := exists_isConvexNbhd H i
    exact hN.isIsolatedInvariantSet
  subset _ := subset_univ _
  disjoint := disjoint_MG H
  irrefl _ := lt_irrefl _
  trans _ _ _ := lt_trans
  connecting x _ hx := by
    obtain ⟨e, he, hfix⟩ := exists_fixed_omegaLim H.hc x
    obtain ⟨i, hi⟩ := fixed_mem_MG H hfix
    obtain ⟨e', he', hfix'⟩ := exists_fixed_alphaLim H.hc x
    obtain ⟨j, hj⟩ := fixed_mem_MG H hfix'
    obtain ⟨N, hN⟩ := exists_isConvexNbhd H i
    obtain ⟨N', hN'⟩ := exists_isConvexNbhd H j
    exact ⟨i, j, conn_rank H hx ⟨e, he, hi⟩ ⟨e', he', hj⟩,
      hN.omegaLim_subset_of_meets ⟨e, he, hi⟩, hN'.alphaLim_subset_of_meets ⟨e', he', hj⟩⟩

/-- **Theorem `thm:M` (iii), no connection between `M⁻` and `M⁺`.** -/
theorem no_conn_Mm_Mp (x : OmG) {i j : GM} (hij : (i = .Bm ∧ j = .Bp) ∨ (i = .Bp ∧ j = .Bm))
    (hω : (omegaLim (ϕG c) x ∩ MG c a η δ i).Nonempty)
    (hα : (alphaLim (ϕG c) x ∩ MG c a η δ j).Nonempty) : False := by
  by_cases hx : ∀ k, x ∉ MG c a η δ k
  · have := conn_rank H hx hω hα
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact absurd this (by decide)
  · push Not at hx
    obtain ⟨k, hk⟩ := hx
    obtain ⟨z, hz, hzi⟩ := hω
    obtain ⟨z', hz', hzj⟩ := hα
    have h1 := omegaLim_subset_of_invariant (ϕG c) (isClosed_MG H k) (fun _ h t => MG_inv H k h t)
      hk hz
    have h2 := alphaLim_subset_of_invariant (ϕG c) (isClosed_MG H k) (fun _ h t => MG_inv H k h t)
      hk hz'
    have d := disjoint_MG H
    have e1 : k = i := by
      by_contra h
      exact Set.disjoint_left.1 (d h) h1 hzi
    have e2 : k = j := by
      by_contra h
      exact Set.disjoint_left.1 (d h) h2 hzj
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact absurd (e1.symm.trans e2) (by decide)

/-- **Theorem `thm:M` (ii).** Equilibria with `y₂ < 0` lie in `M⁻`. -/
theorem fixed_mem_Mm {e : OmG} (he : ∀ t, ϕG c t e = e) (h2 : gy2 e < 0) :
    e ∈ Inv (ϕG c) (Km a η δ) := by
  obtain ⟨i, hi⟩ := fixed_mem_MG H he
  have ha0 := H.ha0
  cases i
  · obtain ⟨h3, -, h, -⟩ := SIA_coords H hi; nlinarith
  · linarith [(TCp_coords hi).1]
  · exact hi
  · linarith [gy2_pos_of_Kp H (Inv_subset _ hi)]
  · have := (TCp_coords hi).1; rw [gy2_rev] at this; linarith
  · obtain ⟨h3, -, h, -⟩ := SIA_coords H hi
    rw [gy2_rev, gy3_rev] at h; rw [gy3_rev] at h3; nlinarith

/-- **Theorem `thm:M` (ii).** Equilibria with `y₂ > a y₃` lie in `M⁺`. -/
theorem fixed_mem_Mp {e : OmG} (he : ∀ t, ϕG c t e = e) (h2 : a * gy3 e < gy2 e) :
    e ∈ Inv (ϕG c) (Kp a η δ) := by
  obtain ⟨i, hi⟩ := fixed_mem_MG H he
  have ha0 := H.ha0
  cases i
  · obtain ⟨-, -, h, -⟩ := SIA_coords H hi; linarith
  · obtain ⟨h, h'⟩ := TCp_coords hi; rw [h, h'] at h2; linarith
  · linarith [gy2_neg_of_Km H (Inv_subset _ hi), mul_nonneg ha0.le (gy3_nonneg e)]
  · exact hi
  · obtain ⟨h, h'⟩ := TCp_coords hi
    rw [gy2_rev] at h; rw [gy3_rev] at h'; rw [h, h'] at h2; linarith
  · obtain ⟨-, -, h, -⟩ := SIA_coords H hi
    rw [gy2_rev, gy3_rev] at h; linarith

end Hyp

end ConleyCheck.Gubser
