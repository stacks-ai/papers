import ConleyCheck.Conley.OrbitTools
import ConleyCheck.Conley.MorseSets
import ConleyCheck.Conley.Conjugacy
import ConleyCheck.Conley.HomologyIndex
import ConleyCheck.Algebra.ExactSeq

/-!
# Theorem `thm:duality`: reversors and duality

A reversor `𝒮` conjugates a flow `ψ` to its time reversal `ψ⁻¹`. Hence `𝒮(K)` is isolated whenever
`K` is, and `h(𝒮(K), ψ) ≅ h(K, ψ⁻¹)`. McCord duality for `ψ⁻¹` on an `n`-manifold without boundary,
`dim CH_k(K, ψ⁻¹) = dim CH_{n-k}(K, ψ)` over a field, is not formalized and enters as a hypothesis.

* `IsReversor.isIsolated_image`: `𝒮(K)` is an isolated invariant set.
* `IsReversor.homologyIndex_image`: `CH_*(𝒮(K), ψ) ≅ CH_*(K, ψ⁻¹)`.
* `IsReversor.duality`: `dim CH_k(𝒮(K)) = dim CH_{n-k}(K)`, given McCord duality.
* `IsReversor.duality_euler`, `IsReversor.duality_euler_odd`: if `𝒮(K) = K`, then
  `χ̃(h(K)) = (-1)^n χ̃(h(K))`, and `χ̃(h(K)) = 0` for odd `n`.
-/

namespace ConleyCheck.Conley

open Set Finset Module

universe u

variable {α : Type u} [TopologicalSpace α] {ψ : Flow ℝ α} {R : α → α}

namespace IsReversor

variable (hR : IsReversor ψ R)
include hR

/-- A reversor as a homeomorphism. -/
def homeo : α ≃ₜ α where
  toFun := R
  invFun := R
  left_inv := hR.invol
  right_inv := hR.invol
  continuous_toFun := hR.cont
  continuous_invFun := hR.cont

theorem homeo_conj (t : ℝ) (x : α) : hR.homeo (ψ t x) = ψ.reverse t (hR.homeo x) := by
  change R (ψ t x) = ψ (-t) (R x)
  rw [hR.conj, neg_neg]

theorem isIsolated_image {K : Set α} (hK : IsIsolatedInvariantSet ψ K) :
    IsIsolatedInvariantSet ψ (R '' K) := by
  rw [hR.image_eq_preimage]
  obtain ⟨N, hN, hNK⟩ := hK
  refine ⟨R ⁻¹' N, ⟨hR.homeo.isCompact_preimage.2 hN.1, ?_⟩, by rw [hR.Inv_preimage, hNK]⟩
  rw [hR.Inv_preimage]
  exact (preimage_mono hN.2).trans (preimage_interior_subset_interior_preimage hR.cont)

variable [T2Space α]

/-- `CH_*(𝒮(K), ψ) ≅ CH_*(K, ψ⁻¹)`. -/
theorem homologyIndex_image (F : Type u) [Ring F] {K : Set α} (hK : IsIsolatedInvariantSet ψ K)
    (n : ℕ) :
    Nonempty (homologyIndex F ψ (hR.isIsolated_image hK) n ≃ₗ[F]
      homologyIndex F ψ.reverse hK.reverse n) := by
  obtain ⟨N, L, hP⟩ := hK.reverse.hasIndex
  have hP' : IsIndexPair ψ (R '' K) (hR.homeo ⁻¹' N) (hR.homeo ⁻¹' L) := by
    rw [hR.image_eq_preimage]
    exact hP.preimage hR.homeo_conj
  obtain ⟨a⟩ := homologyIndexIso F (hR.isIsolated_image hK) hP' n
  obtain ⟨b⟩ := homologyIndexIso F hK.reverse hP n
  let c := (redIso F (IndexSpace.preimageEquiv hR.homeo N L) n).toLinearEquiv
  exact ⟨a.toLinearEquiv.trans (c.trans b.toLinearEquiv.symm)⟩

/-- Theorem `thm:duality`: given McCord duality `dim CH_k(K, ψ⁻¹) = dim CH_{n-k}(K, ψ)` for
`k ≤ n`, `dim CH_k(𝒮(K)) = dim CH_{n-k}(K)`. -/
theorem duality (F : Type u) [Field F] {K : Set α} (hK : IsIsolatedInvariantSet ψ K) (n : ℕ)
    (hMc : ∀ k ≤ n, finrank F (homologyIndex F ψ.reverse hK.reverse k) =
      finrank F (homologyIndex F ψ hK (n - k)))
    {k : ℕ} (hk : k ≤ n) :
    finrank F (homologyIndex F ψ (hR.isIsolated_image hK) k) =
      finrank F (homologyIndex F ψ hK (n - k)) := by
  obtain ⟨e⟩ := hR.homologyIndex_image F hK k
  rw [e.finrank_eq, hMc k hk]

omit hR in
theorem homologyIndex_set_congr (F : Type u) [Ring F] {S T : Set α} (h : S = T)
    (hS : IsIsolatedInvariantSet ψ S) (hT : IsIsolatedInvariantSet ψ T) (n : ℕ) :
    Nonempty (homologyIndex F ψ hS n ≃ₗ[F] homologyIndex F ψ hT n) := by
  subst h
  exact ⟨LinearEquiv.refl _ _⟩

/-- Theorem `thm:duality`, Euler characteristic: if `𝒮(K) = K`, then `χ̃(h(K)) = (-1)^n χ̃(h(K))`,
given McCord duality. -/
theorem duality_euler (F : Type u) [Field F] {K : Set α} (hK : IsIsolatedInvariantSet ψ K)
    (hRK : R '' K = K) (n : ℕ)
    (hMc : ∀ k ≤ n, finrank F (homologyIndex F ψ.reverse hK.reverse k) =
      finrank F (homologyIndex F ψ hK (n - k))) :
    ∑ k ∈ range (n + 1), (-1) ^ k * (finrank F (homologyIndex F ψ hK k) : ℤ) =
      (-1) ^ n * ∑ k ∈ range (n + 1), (-1) ^ k * (finrank F (homologyIndex F ψ hK k) : ℤ) := by
  refine euler_reflect _ n fun k hk => ?_
  obtain ⟨e⟩ := homologyIndex_set_congr F hRK (hR.isIsolated_image hK) hK k
  rw [← e.finrank_eq, hR.duality F hK n hMc hk]

theorem duality_euler_odd (F : Type u) [Field F] {K : Set α} (hK : IsIsolatedInvariantSet ψ K)
    (hRK : R '' K = K) {n : ℕ} (hn : Odd n)
    (hMc : ∀ k ≤ n, finrank F (homologyIndex F ψ.reverse hK.reverse k) =
      finrank F (homologyIndex F ψ hK (n - k))) :
    ∑ k ∈ range (n + 1), (-1) ^ k * (finrank F (homologyIndex F ψ hK k) : ℤ) = 0 := by
  have h := hR.duality_euler F hK hRK n hMc
  rw [hn.neg_one_pow] at h
  linarith

end IsReversor

end ConleyCheck.Conley
