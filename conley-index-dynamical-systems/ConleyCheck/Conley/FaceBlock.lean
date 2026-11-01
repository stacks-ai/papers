import ConleyCheck.Conley.IsolatingBlock
import ConleyCheck.ODE.Fence

/-!
# Isolating blocks cut out by finitely many inequalities

A compact set `{p | ∀ k, g k p ≤ 0}` whose faces `g k = 0` are crossed strictly by the flow is an
isolating block. The exit set is the union of the faces crossed outward.
-/

namespace ConleyCheck.Conley

open Set Filter Topology ConleyCheck.ODE

variable {α : Type*} [TopologicalSpace α] {ϕ : Flow ℝ α} {ι : Type*} [Finite ι]

/-- A compact set cut out by finitely many inequalities `g k ≤ 0`, whose faces are crossed strictly,
outward on the faces indexed by `X` and inward on the others, is an isolating block whose exit set
is the union of the faces indexed by `X`. -/
theorem isBlock_of_faces {g D : ι → α → ℝ} {X : Set ι} (hg : ∀ k, Continuous (g k))
    (hcpt : IsCompact {p | ∀ k, g k p ≤ 0})
    (hD : ∀ k, ∀ p, (∀ j, g j p ≤ 0) → HasDerivAt (fun t => g k (ϕ t p)) (D k p) 0)
    (hexit : ∀ k ∈ X, ∀ p, (∀ j, g j p ≤ 0) → g k p = 0 → 0 < D k p)
    (hent : ∀ k ∉ X, ∀ p, (∀ j, g j p ≤ 0) → g k p = 0 → D k p < 0) :
    IsBlock ϕ {p | ∀ k, g k p ≤ 0} {p | (∀ k, g k p ≤ 0) ∧ ∃ k ∈ X, g k p = 0} where
  isCompact := hcpt
  isClosed_L := by
    have : {p | (∀ k, g k p ≤ 0) ∧ ∃ k ∈ X, g k p = 0} =
        {p | ∀ k, g k p ≤ 0} ∩ ⋃ k ∈ X, {p | g k p = 0} := by
      ext p; simp
    rw [this, ofPred_forall]
    exact (isClosed_iInter fun k => isClosed_le (hg k) continuous_const).inter
      (X.toFinite.isClosed_biUnion fun k _ => isClosed_eq (hg k) continuous_const)
  subset _ hp := hp.1
  exit := by
    rintro x ⟨hxB, k, hk, hx0⟩
    have hd := (hD k x hxB).neg
    have hout : ∀ᶠ s in 𝓝[>] (0 : ℝ), ϕ s x ∉ {p | ∀ k, g k p ≤ 0} :=
      (eventually_sign hd (by linarith [hexit k hk x hxB hx0])).1.mono fun s hs hB => by
        have h0 : g k (ϕ 0 x) = 0 := by rw [Flow.map_zero_apply]; exact hx0
        have := hB k
        rw [Pi.neg_apply, Pi.neg_apply] at hs
        linarith
    obtain ⟨ε, hε, -, h⟩ := exists_eps (P := fun _ => True) (Eventually.of_forall fun _ => trivial)
      hout
    exact ⟨ε, hε, h⟩
  entrance := by
    intro x hxB hint hL
    have hopen : IsOpen {p | ∀ k, g k p < 0} := by
      rw [ofPred_forall]
      exact isOpen_iInter_of_finite fun k => isOpen_lt (hg k) continuous_const
    obtain ⟨k, hk⟩ : ∃ k, g k x = 0 := by
      by_contra hc
      push Not at hc
      exact hint (interior_maximal (fun p (hp : ∀ k, g k p < 0) k => (hp k).le) hopen fun k =>
        lt_of_le_of_ne (hxB k) (hc k))
    have hnX : ∀ k, g k x = 0 → k ∉ X := fun k hk hkX => hL ⟨hxB, k, hkX, hk⟩
    have hback : ∀ᶠ s in 𝓝[<] (0 : ℝ), ϕ s x ∉ {p | ∀ k, g k p ≤ 0} :=
      (eventually_sign (hD k x hxB) (hent k (hnX k hk) x hxB hk)).2.mono fun s hs hB => by
        simp only [Flow.map_zero_apply, hk] at hs
        have := hB k
        linarith
    have hfwd : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ j, g j (ϕ s x) ≤ 0 := by
      refine eventually_all.2 fun j => ?_
      rcases (hxB j).lt_or_eq with hj | hj
      · have h0 : g j (ϕ 0 x) < 0 := by rw [Flow.map_zero_apply]; exact hj
        exact nhdsWithin_le_nhds (((hD j x hxB).continuousAt.eventually (Iio_mem_nhds h0)).mono
          fun _ hs => le_of_lt hs)
      · exact (eventually_sign (hD j x hxB) (hent j (hnX j hj) x hxB hj)).1.mono fun s hs => by
          simp only [Flow.map_zero_apply, hj] at hs
          exact hs.le
    exact exists_eps hback hfwd

/-- The case of a block with no exit faces, a positively invariant block. -/
theorem isBlock_of_faces_attr {g D : ι → α → ℝ} (hg : ∀ k, Continuous (g k))
    (hcpt : IsCompact {p | ∀ k, g k p ≤ 0})
    (hD : ∀ k, ∀ p, (∀ j, g j p ≤ 0) → HasDerivAt (fun t => g k (ϕ t p)) (D k p) 0)
    (hent : ∀ k, ∀ p, (∀ j, g j p ≤ 0) → g k p = 0 → D k p < 0) :
    IsBlock ϕ {p | ∀ k, g k p ≤ 0} ∅ := by
  have h := isBlock_of_faces (X := ∅) hg hcpt hD (fun k hk => absurd hk (notMem_empty k))
    (fun k _ => hent k)
  have he : {p | (∀ k, g k p ≤ 0) ∧ ∃ k ∈ (∅ : Set ι), g k p = 0} = ∅ := by
    ext p; simp
  rwa [he] at h

end ConleyCheck.Conley
