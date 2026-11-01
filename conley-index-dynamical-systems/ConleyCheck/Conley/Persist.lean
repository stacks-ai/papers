import ConleyCheck.Conley.Double

/-!
# Persistence of connections under continuation

If `CH_{k+1}(S♮) = 0` and `CH_k(K_-; f_-) ≠ 0`, then `Ψ_k` is injective and nonzero, so by
Theorem `thm:transport`(ii) `S` contains a UV→IR connection (`transport_connection_of_vanishing`).
If `CH_*(S♮) = 0`, every `Ψ_k` is bijective (`transport_bijective_of_vanishing`). Both
hypotheses are invariant under continuation of `S♮` and `K_-` (`homologyIndex_continuation`), so
the connection persists along every deformation along which `S♮` and `K_-` continue
(`transport_persist`), with integer coefficients.
-/

namespace ConleyCheck.Conley

open Set Function

universe u

section Continuation

variable (K : Type u) [Ring K] {α : Type u} [TopologicalSpace α]
  [TopologicalSpace.MetrizableSpace α]

/-- The homology index is invariant under continuation along a family with a common isolating
neighborhood. -/
theorem homologyIndex_continuation (Ψ : FlowFamily α) {N : Set α} (hN : IsCompact N)
    (hiso : ∀ l, Inv (Ψ.slice l) N ⊆ interior N)
    (h0 : IsIsolatedInvariantSet (Ψ.slice 0) (Inv (Ψ.slice 0) N))
    (h1 : IsIsolatedInvariantSet (Ψ.slice 1) (Inv (Ψ.slice 1) N)) (n : ℕ) :
    Nonempty (homologyIndex K _ h0 n ≃ₗ[K] homologyIndex K _ h1 n) := by
  obtain ⟨N₀, L₀, hP₀, -⟩ := exists_indexPair (ϕ := Ψ.slice 0) ⟨hN, hiso 0⟩
  obtain ⟨N₁, L₁, hP₁, -⟩ := exists_indexPair (ϕ := Ψ.slice 1) ⟨hN, hiso 1⟩
  obtain ⟨e⟩ := continuation Ψ hN hiso hP₀ hP₁
  obtain ⟨i₀⟩ := homologyIndexIso K h0 hP₀ n
  obtain ⟨i₁⟩ := homologyIndexIso K h1 hP₁ n
  exact ⟨i₀.toLinearEquiv.trans ((redIso K e n).toLinearEquiv.trans i₁.symm.toLinearEquiv)⟩

end Continuation

section Transport

variable {X : Type u} [TopologicalSpace X] [T2Space X] [TopologicalSpace.MetrizableSpace X]
  (K : Type u) [Ring K]

/-- If `CH_{k+1}(S♮) = 0` and `CH_k(K_-) ≠ 0`, then `S` contains a UV→IR connection. -/
theorem transport_connection_of_vanishing {Φ : Flow ℝ (X × Tau)} {θ : Flow ℝ Tau}
    (hΦ : IsSkew Φ θ) (hθ : IsHeight θ (fun b => (b : ℝ))) {S : Set (X × Tau)}
    (hS : IsIsolatedInvariantSet Φ S) {k : ℕ}
    (h1 : ∀ h : IsIsolatedInvariantSet (dblΦ hΦ hθ) (snat S),
      Subsingleton (homologyIndex K _ h (k + 1)))
    (h2 : ∀ h : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ))
      {x | (x, Tau.bot) ∈ S}, Nontrivial (homologyIndex K _ h k)) :
    ∃ q ∈ S, (q.2 : ℝ) ∈ Ioo (-1) 1 ∧
      omegaLim Φ q ⊆ S ∩ (fun q => (q.2 : ℝ)) ⁻¹' {1} ∧
      alphaLim Φ q ⊆ S ∩ (fun q => (q.2 : ℝ)) ⁻¹' {-1} := by
  obtain ⟨hSn, hKp, hKm, Ψ, i, p, -, -, h3, -, hconn, -⟩ := transport hΦ hθ K hS
  refine hconn k fun hΨ => ?_
  have := h1 hSn
  have := h2 hKm
  obtain ⟨x, hx⟩ := exists_ne (0 : homologyIndex K _ hKm k)
  obtain ⟨y, hy⟩ := ((h3 k) x).1 (by rw [hΨ, LinearMap.zero_apply])
  rw [Subsingleton.elim y 0, map_zero] at hy
  exact hx hy.symm

/-- If `CH_*(S♮) = 0`, then every `Ψ_k` is an isomorphism. -/
theorem transport_bijective_of_vanishing {Φ : Flow ℝ (X × Tau)} {θ : Flow ℝ Tau}
    (hΦ : IsSkew Φ θ) (hθ : IsHeight θ (fun b => (b : ℝ))) {S : Set (X × Tau)}
    (hS : IsIsolatedInvariantSet Φ S)
    (h0 : ∀ (h : IsIsolatedInvariantSet (dblΦ hΦ hθ) (snat S)) (k : ℕ),
      Subsingleton (homologyIndex K _ h k)) :
    ∃ (hKp : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ)) {x | (x, Tau.top) ∈ S})
      (hKm : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ)) {x | (x, Tau.bot) ∈ S})
      (Ψ : ∀ k, homologyIndex K _ hKm k →ₗ[K] homologyIndex K _ hKp k), ∀ k, Bijective (Ψ k) := by
  obtain ⟨hSn, hKp, hKm, Ψ, i, p, h1, -, h3, -, -⟩ := transport hΦ hθ K hS
  refine ⟨hKp, hKm, Ψ, fun k => ⟨fun x y hxy => ?_, fun y => ?_⟩⟩
  · have := h0 hSn (k + 1)
    have : Ψ k (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := ((h3 k) (x - y)).1 this
    rw [Subsingleton.elim z 0, map_zero] at hz
    exact sub_eq_zero.1 hz.symm
  · have := h0 hSn k
    exact ((h1 k) y).1 (Subsingleton.elim _ _)

/-- Persistence of the transport data under continuation. Let `Φ₀` and `Φ₁` be compactified
flows, with isolated invariant sets `S₀` and `S₁`, such that `S♮₀` continues to `S♮₁` along a
family `D` of flows on the double, and `K_-⁰` continues to `K_-¹` along a family `F` of flows on
`X`, each with a common isolating neighborhood. If `CH_{k+1}(S♮₀) = 0` and `CH_k(K_-⁰) ≠ 0`,
then `S₁` contains a UV→IR connection. -/
theorem transport_persist {Φ₀ : Flow ℝ (X × Tau)} {θ₀ : Flow ℝ Tau} (hΦ₀ : IsSkew Φ₀ θ₀)
    (hθ₀ : IsHeight θ₀ (fun b => (b : ℝ))) {Φ₁ : Flow ℝ (X × Tau)} {θ₁ : Flow ℝ Tau}
    (hΦ₁ : IsSkew Φ₁ θ₁) (hθ₁ : IsHeight θ₁ (fun b => (b : ℝ))) {S₀ S₁ : Set (X × Tau)}
    (hS₁ : IsIsolatedInvariantSet Φ₁ S₁)
    (D : FlowFamily (X × Dbl)) {M : Set (X × Dbl)} (hM : IsCompact M)
    (hMi : ∀ l, Inv (D.slice l) M ⊆ interior M)
    (hD0 : D.slice 0 = dblΦ hΦ₀ hθ₀) (hD1 : D.slice 1 = dblΦ hΦ₁ hθ₁)
    (hM0 : Inv (D.slice 0) M = snat S₀) (hM1 : Inv (D.slice 1) M = snat S₁)
    (F : FlowFamily X) {M' : Set X} (hM' : IsCompact M')
    (hM'i : ∀ l, Inv (F.slice l) M' ⊆ interior M')
    (hF0 : F.slice 0 = fiberFlow hΦ₀ Tau.bot (base_bot hθ₀))
    (hF1 : F.slice 1 = fiberFlow hΦ₁ Tau.bot (base_bot hθ₁))
    (hF0' : Inv (F.slice 0) M' = {x | (x, Tau.bot) ∈ S₀})
    (hF1' : Inv (F.slice 1) M' = {x | (x, Tau.bot) ∈ S₁}) {k : ℕ}
    (h1 : ∀ h : IsIsolatedInvariantSet (dblΦ hΦ₀ hθ₀) (snat S₀),
      Subsingleton (homologyIndex K _ h (k + 1)))
    (h2 : ∀ h : IsIsolatedInvariantSet (fiberFlow hΦ₀ Tau.bot (base_bot hθ₀))
      {x | (x, Tau.bot) ∈ S₀}, Nontrivial (homologyIndex K _ h k)) :
    ∃ q ∈ S₁, (q.2 : ℝ) ∈ Ioo (-1) 1 ∧
      omegaLim Φ₁ q ⊆ S₁ ∩ (fun q => (q.2 : ℝ)) ⁻¹' {1} ∧
      alphaLim Φ₁ q ⊆ S₁ ∩ (fun q => (q.2 : ℝ)) ⁻¹' {-1} := by
  have hD0i : IsIsolatedInvariantSet (D.slice 0) (Inv (D.slice 0) M) := ⟨M, ⟨hM, hMi 0⟩, rfl⟩
  have hD1i : IsIsolatedInvariantSet (D.slice 1) (Inv (D.slice 1) M) := ⟨M, ⟨hM, hMi 1⟩, rfl⟩
  have hF0i : IsIsolatedInvariantSet (F.slice 0) (Inv (F.slice 0) M') := ⟨M', ⟨hM', hM'i 0⟩, rfl⟩
  have hF1i : IsIsolatedInvariantSet (F.slice 1) (Inv (F.slice 1) M') := ⟨M', ⟨hM', hM'i 1⟩, rfl⟩
  have hSn0 : IsIsolatedInvariantSet (dblΦ hΦ₀ hθ₀) (snat S₀) := by
    rw [← hD0, ← hM0]; exact hD0i
  have hKm0 : IsIsolatedInvariantSet (fiberFlow hΦ₀ Tau.bot (base_bot hθ₀))
      {x | (x, Tau.bot) ∈ S₀} := by
    rw [← hF0, ← hF0']; exact hF0i
  refine transport_connection_of_vanishing K hΦ₁ hθ₁ hS₁ (k := k) (fun h => ?_) (fun h => ?_)
  · obtain ⟨e₁⟩ := homologyIndex_congr K hD1.symm hM1.symm h hD1i (k + 1)
    obtain ⟨e₂⟩ := homologyIndex_continuation K D hM hMi hD0i hD1i (k + 1)
    obtain ⟨e₃⟩ := homologyIndex_congr K hD0 hM0 hD0i hSn0 (k + 1)
    have := h1 hSn0
    exact (e₁.trans (e₂.symm.trans e₃)).toEquiv.subsingleton
  · obtain ⟨e₁⟩ := homologyIndex_congr K hF1.symm hF1'.symm h hF1i k
    obtain ⟨e₂⟩ := homologyIndex_continuation K F hM' hM'i hF0i hF1i k
    obtain ⟨e₃⟩ := homologyIndex_congr K hF0 hF0' hF0i hKm0 k
    have := h2 hKm0
    exact (e₁.trans (e₂.symm.trans e₃)).toEquiv.nontrivial

end Transport

end ConleyCheck.Conley
