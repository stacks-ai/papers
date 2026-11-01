import ConleyCheck.Conley.Rate
import ConleyCheck.Conley.FaceBlock

/-!
# Common blocks cut out by finitely many inequalities

The uniform version of `isBlock_of_faces`. A compact set `{p | ∀ k, g k p ≤ 0}` whose faces are
crossed strictly by the fiber component of a skew product, outward on the faces indexed by `E`
and inward on the others, for every value of the base, is a common block.
-/

namespace ConleyCheck.Conley

open Set Filter Topology ConleyCheck.ODE

variable {X : Type*} [TopologicalSpace X] {Φ : Flow ℝ (X × Tau)} {ι : Type*} [Finite ι]

theorem isUniformBlock_of_faces {g : ι → X → ℝ} {D : ι → X → Tau → ℝ} {E : Set ι}
    (hg : ∀ k, Continuous (g k)) (hcpt : IsCompact {p | ∀ k, g k p ≤ 0})
    (hD : ∀ k p τ, (∀ j, g j p ≤ 0) → HasDerivAt (fun t => g k (Φ t (p, τ)).1) (D k p τ) 0)
    (hexit : ∀ k ∈ E, ∀ p τ, (∀ j, g j p ≤ 0) → g k p = 0 → 0 < D k p τ)
    (hent : ∀ k ∉ E, ∀ p τ, (∀ j, g j p ≤ 0) → g k p = 0 → D k p τ < 0) :
    IsUniformBlock Φ {p | ∀ k, g k p ≤ 0} {p | (∀ k, g k p ≤ 0) ∧ ∃ k ∈ E, g k p = 0} where
  isCompact := hcpt
  isClosed_out := by
    have : {p | (∀ k, g k p ≤ 0) ∧ ∃ k ∈ E, g k p = 0} =
        {p | ∀ k, g k p ≤ 0} ∩ ⋃ k ∈ E, {p | g k p = 0} := by
      ext p; simp
    rw [this, ofPred_forall]
    exact (isClosed_iInter fun k => isClosed_le (hg k) continuous_const).inter
      (E.toFinite.isClosed_biUnion fun k _ => isClosed_eq (hg k) continuous_const)
  out_subset _ hp := hp.1
  exit := by
    rintro x ⟨hxB, k, hk, hx0⟩ τ
    have h00 : (Φ 0 (x, τ)).1 = x := by rw [Flow.map_zero_apply]
    have hd := (hD k x τ hxB).neg
    have hout : ∀ᶠ s in 𝓝[>] (0 : ℝ), (Φ s (x, τ)).1 ∉ {p | ∀ k, g k p ≤ 0} :=
      (eventually_sign hd (by linarith [hexit k hk x τ hxB hx0])).1.mono fun s hs hB => by
        have h0 : g k (Φ 0 (x, τ)).1 = 0 := by rw [h00]; exact hx0
        have := hB k
        rw [Pi.neg_apply, Pi.neg_apply] at hs
        linarith
    obtain ⟨ε, hε, -, h⟩ := exists_eps (P := fun _ => True) (Eventually.of_forall fun _ => trivial)
      hout
    exact ⟨ε, hε, h⟩
  entrance := by
    intro x hxB hint hL τ
    have h00 : (Φ 0 (x, τ)).1 = x := by rw [Flow.map_zero_apply]
    have hopen : IsOpen {p | ∀ k, g k p < 0} := by
      rw [ofPred_forall]
      exact isOpen_iInter_of_finite fun k => isOpen_lt (hg k) continuous_const
    obtain ⟨k, hk⟩ : ∃ k, g k x = 0 := by
      by_contra hc
      push Not at hc
      exact hint (interior_maximal (fun p (hp : ∀ k, g k p < 0) k => (hp k).le) hopen fun k =>
        lt_of_le_of_ne (hxB k) (hc k))
    have hnX : ∀ k, g k x = 0 → k ∉ E := fun k hk hkX => hL ⟨hxB, k, hkX, hk⟩
    have hback : ∀ᶠ s in 𝓝[<] (0 : ℝ), (Φ s (x, τ)).1 ∉ {p | ∀ k, g k p ≤ 0} :=
      (eventually_sign (hD k x τ hxB) (hent k (hnX k hk) x τ hxB hk)).2.mono fun s hs hB => by
        simp only [h00, hk] at hs
        have := hB k
        linarith
    have hfwd : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ j, g j (Φ s (x, τ)).1 ≤ 0 := by
      refine eventually_all.2 fun j => ?_
      rcases (hxB j).lt_or_eq with hj | hj
      · have h0 : g j (Φ 0 (x, τ)).1 < 0 := by rw [h00]; exact hj
        exact nhdsWithin_le_nhds (((hD j x τ hxB).continuousAt.eventually (Iio_mem_nhds h0)).mono
          fun _ hs => le_of_lt hs)
      · exact (eventually_sign (hD j x τ hxB) (hent j (hnX j hj) x τ hxB hj)).1.mono fun s hs => by
          simp only [h00, hj] at hs
          exact hs.le
    exact exists_eps hback hfwd

end ConleyCheck.Conley
