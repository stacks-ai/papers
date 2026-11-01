import ConleyCheck.Conley.OrbitTools
import ConleyCheck.Conley.IsolatingBlock

/-!
# Convergence along orbits

* `fixed_of_tendsto`: the limit of a convergent orbit is a fixed point.
* `omegaLim_subset_level`: if `f` converges along an orbit, then `f` is constant on its limit set.
* `IsBlock.exists_exit`: an orbit that leaves an isolating block passes through the exit set.
-/

open Set Filter Topology

namespace ConleyCheck.Conley

variable {X : Type*} [TopologicalSpace X] (ϕ : Flow ℝ X)

theorem mem_omegaLim_of_tendsto {x e : X} (h : Tendsto (fun t => ϕ t x) atTop (𝓝 e)) :
    e ∈ omegaLim ϕ x := by
  rw [omegaLim, mem_omegaLimit_singleton_iff_mapClusterPt]
  exact h.mapClusterPt

theorem mem_alphaLim_of_tendsto {x e : X} (h : Tendsto (fun t => ϕ t x) atBot (𝓝 e)) :
    e ∈ alphaLim ϕ x := by
  rw [alphaLim, mem_omegaLimit_singleton_iff_mapClusterPt]
  exact h.mapClusterPt

theorem fixed_of_tendsto [T2Space X] {x e : X} (h : Tendsto (fun t => ϕ t x) atTop (𝓝 e))
    (s : ℝ) : ϕ s e = e := by
  have h1 : Tendsto (fun t => ϕ s (ϕ t x)) atTop (𝓝 (ϕ s e)) :=
    ((ϕ.continuous continuous_const continuous_id).tendsto e).comp h
  have h2 : Tendsto (fun t => ϕ s (ϕ t x)) atTop (𝓝 e) :=
    (h.comp (tendsto_add_atTop s)).congr fun t => by simp only [Function.comp, Flow.map_add]
  exact tendsto_nhds_unique h1 h2

theorem omegaLim_subset_level {f : X → ℝ} (hf : Continuous f) {x : X} {L : ℝ}
    (h : Tendsto (fun t => f (ϕ t x)) atTop (𝓝 L)) : omegaLim ϕ x ⊆ {z | f z = L} := by
  intro z hz
  rw [omegaLim, mem_omegaLimit_singleton_iff_mapClusterPt] at hz
  have h1 : MapClusterPt (f z) atTop (fun t => f (ϕ t x)) := hz.tendsto_comp (hf.tendsto z)
  exact eq_of_nhds_neBot (ClusterPt.mono h1 h)

theorem alphaLim_subset_level {f : X → ℝ} (hf : Continuous f) {x : X} {L : ℝ}
    (h : Tendsto (fun t => f (ϕ t x)) atBot (𝓝 L)) : alphaLim ϕ x ⊆ {z | f z = L} := by
  intro z hz
  rw [alphaLim, mem_omegaLimit_singleton_iff_mapClusterPt] at hz
  have h1 : MapClusterPt (f z) atBot (fun t => f (ϕ t x)) := hz.tendsto_comp (hf.tendsto z)
  exact eq_of_nhds_neBot (ClusterPt.mono h1 h)

/-- The limit sets of a point of a closed invariant set lie in that set. -/
theorem omegaLim_subset_of_invariant {S : Set X} (hS : IsClosed S) (hinv : ∀ z ∈ S, ∀ t, ϕ t z ∈ S)
    {z : X} (hz : z ∈ S) : omegaLim ϕ z ⊆ S :=
  omegaLim_subset_of_eventually ϕ hS (Eventually.of_forall fun t => hinv z hz t)

theorem alphaLim_subset_of_invariant {S : Set X} (hS : IsClosed S) (hinv : ∀ z ∈ S, ∀ t, ϕ t z ∈ S)
    {z : X} (hz : z ∈ S) : alphaLim ϕ z ⊆ S :=
  alphaLim_subset_of_eventually ϕ hS (Eventually.of_forall fun t => hinv z hz t)

theorem isIsolatedInvariantSet_univ [CompactSpace X] : IsIsolatedInvariantSet ϕ univ :=
  ⟨univ, ⟨isCompact_univ, fun _ _ => by rw [interior_univ]; trivial⟩,
    eq_univ_of_forall fun _ _ => trivial⟩

/-- An orbit that is in an isolating block at time `t₁` and outside it at time `t₂ ≥ t₁` meets the
exit set at some time in `[t₁, t₂)`. -/
theorem IsBlock.exists_exit [T2Space X] {N L : Set X} (hB : IsBlock ϕ N L) {x : X} {t₁ t₂ : ℝ}
    (h12 : t₁ ≤ t₂) (h1 : ϕ t₁ x ∈ N) (h2 : ϕ t₂ x ∉ N) : ∃ s ∈ Ico t₁ t₂, ϕ s x ∈ L := by
  by_contra hno
  push Not at hno
  have hc : Continuous fun r => ϕ r x := ϕ.continuous continuous_id continuous_const
  have hs : IsClosed ({r | ϕ r x ∈ N} ∩ Icc t₁ t₂) :=
    (hB.isCompact.isClosed.preimage hc).inter isClosed_Icc
  refine h2 (hs.Icc_subset_of_forall_mem_nhdsWithin h1 (fun r ⟨hrN, hr⟩ => ?_) ⟨h12, le_rfl⟩)
  by_cases hint : ϕ r x ∈ interior N
  · exact nhdsWithin_le_nhds (Filter.mem_of_superset
      (hc.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hint))
      fun r' (hr' : ϕ r' x ∈ interior N) => (interior_subset hr' : ϕ r' x ∈ N))
  · obtain ⟨ε, hε, -, hfwd⟩ := hB.entrance _ hrN hint (hno r hr)
    filter_upwards [Ioo_mem_nhdsGT (show r < r + ε by linarith)] with r' hr'
    have := hfwd (r' - r) ⟨by linarith [hr'.1], by linarith [hr'.2]⟩
    rwa [← Flow.map_add, sub_add_cancel] at this

end ConleyCheck.Conley
