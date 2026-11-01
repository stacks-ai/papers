import ConleyCheck.Conley.RateConj
import ConleyCheck.Conley.SphereHomology

/-!
# Moving saddle blocks

Corollary `cor:moving`. Let `Φ` be a skew product over a height flow `θ` on `[-1, 1]`, and
`e : X × [-1, 1] ≃ Y × [-1, 1]` a fiberwise homeomorphism such that `(N, L_out)` is a uniform
block for `e Φ e⁻¹` whose index space `N/L_out` is pointed homotopy equivalent to `S^k`. Then
`S = Inv(e⁻¹(N × [-1, 1]))` is isolated, `CH_*(K_±) = Λ[k]`, `CH_*(S♮) = 0`, the transport
`Ψ : CH_*(K_-) → CH_*(K_+)` is an isomorphism, and, over a nontrivial ring, some orbit of `S` with
`-1 < τ < 1` runs from `K_-` to `K_+`.
-/

namespace ConleyCheck.Conley

open Set Function

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace.MetrizableSpace X] [TopologicalSpace.MetrizableSpace Y]
  {Φ : Flow ℝ (X × Tau)} {θ : Flow ℝ Tau} (hΦ : IsSkew Φ θ) (e : X × Tau ≃ₜ Y × Tau)
  (he : ∀ p, (e p).2 = p.2) (hθ : IsHeight θ (fun b => (b : ℝ)))

include he in
theorem moving_saddle (K : Type) [Ring K] {N Lo : Set Y} {k : ℕ}
    (hB : IsUniformBlock (conjFlow Φ e) N Lo)
    (hsph : PointedHomotopyEquiv (IndexSpace N Lo) (Sphere k) (IndexSpace.pt N Lo) (Sphere.pt k)) :
    IsIsolatingNbhd Φ (e ⁻¹' (N ×ˢ univ)) ∧
      ∃ (hSn : IsIsolatedInvariantSet (dblΦ hΦ hθ) (snat (Inv Φ (e ⁻¹' (N ×ˢ univ)))))
        (hKp : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ))
          {x | (x, Tau.top) ∈ Inv Φ (e ⁻¹' (N ×ˢ univ))})
        (hKm : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ))
          {x | (x, Tau.bot) ∈ Inv Φ (e ⁻¹' (N ×ˢ univ))})
        (Ψ : ∀ k, homologyIndex K _ hKm k →ₗ[K] homologyIndex K _ hKp k)
        (i : ∀ k, homologyIndex K _ hKp k →ₗ[K] homologyIndex K _ hSn k)
        (p : ∀ k, homologyIndex K _ hSn (k + 1) →ₗ[K] homologyIndex K _ hKm k),
        (∀ k, Exact (Ψ k) (i k)) ∧ (∀ k, Exact (i (k + 1)) (p k)) ∧
        (∀ k, Exact (p k) (Ψ k)) ∧ (∀ k, Subsingleton (homologyIndex K _ hSn k)) ∧
        (∀ k, Bijective (Ψ k)) ∧
        Nonempty (homologyIndex K _ hKp k ≃ₗ[K] K) ∧
        (∀ n, n ≠ k → Subsingleton (homologyIndex K _ hKp n)) ∧
        Nonempty (homologyIndex K _ hKm k ≃ₗ[K] K) ∧
        (∀ n, n ≠ k → Subsingleton (homologyIndex K _ hKm n)) ∧
        (Nontrivial K → ∃ q ∈ Inv Φ (e ⁻¹' (N ×ˢ univ)), (q.2 : ℝ) ∈ Ioo (-1) 1 ∧
          omegaLim Φ q ⊆ Inv Φ (e ⁻¹' (N ×ˢ univ)) ∩ (fun q => (q.2 : ℝ)) ⁻¹' {1} ∧
          alphaLim Φ q ⊆ Inv Φ (e ⁻¹' (N ×ˢ univ)) ∩ (fun q => (q.2 : ℝ)) ⁻¹' {-1}) := by
  have hci := conj_index hΦ e he hθ hB
  have hsp : ∀ {S : Set X} {b : Tau} (hb : ∀ t, θ t b = b),
      HasIndex (fiberFlow hΦ b hb) S (IndexSpace N Lo) (IndexSpace.pt N Lo) →
      HasIndex (fiberFlow hΦ b hb) S (Sphere k) (Sphere.pt k) := fun _ ⟨N', L', hP, ⟨f⟩⟩ =>
    ⟨N', L', hP, ⟨f.trans hsph⟩⟩
  have hp := (hsp _ hci.2.1).homologyIndex_sphere' K
  have hm := (hsp _ hci.2.2).homologyIndex_sphere' K
  obtain ⟨hSn, hKp, hKm, Ψ, i, p, h1, h2, h3, h4, h5⟩ := rate_transport_conj hΦ e he hθ K hB
  refine ⟨hci.1, hSn, hKp, hKm, Ψ, i, p, h1, h2, h3, h4, h5, hp.1, hp.2, hm.1, hm.2, fun _ => ?_⟩
  refine rate_connection_conj hΦ e he hθ K hB ⟨k, ?_⟩
  obtain ⟨⟨e0⟩, -⟩ := sphere_homology K k
  exact ((redIso K hsph k).toLinearEquiv.trans e0).toEquiv.nontrivial

end ConleyCheck.Conley
