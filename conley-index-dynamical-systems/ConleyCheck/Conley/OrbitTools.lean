import ConleyCheck.Conley.Morse
import ConleyCheck.ODE.Fence

/-!
# Tools for locating limit sets

* `mem_of_local_fwd`: a closed set that orbits do not leave immediately is forward invariant.
* `omegaLim_invariant`, `omegaLim_subset_of_eventually`, `eventually_of_omegaLim_subset`,
  `tendsto_of_omegaLim_subset`: elementary properties of `ω`- and `α`-limit sets in compact spaces.
* `IsConvexNbhd`: a neighborhood `N` of `M = Inv(N)` such that every orbit meets `N` in an interval
  of times. If `ω(x)` or `α(x)` meets `M`, it lies in `M` (`omegaLim_subset_of_meets`), and if both
  do, then `x ∈ M` (`mem_of_limits`).
* `nonpos_of_deriv_neg`: a function cannot be positive somewhere on a compact invariant set if it
  strictly decreases along orbits wherever it is positive.
* `IsReversor`: an involution `R` with `ϕ_t ∘ R = R ∘ ϕ_{-t}` exchanges `ω`- and `α`-limit sets.
-/

open Set Filter Topology

namespace ConleyCheck.Conley

variable {X : Type*} [TopologicalSpace X] (ϕ : Flow ℝ X)

/-! ## Local to global invariance -/

theorem mem_of_local_fwd {N : Set X} (hN : IsClosed N)
    (h : ∀ p ∈ N, ∀ᶠ t in 𝓝[>] (0 : ℝ), ϕ t p ∈ N) {x : X} (hx : x ∈ N) {t : ℝ} (ht : 0 ≤ t) :
    ϕ t x ∈ N := by
  have hs : IsClosed ({r | ϕ r x ∈ N} ∩ Icc 0 t) :=
    (hN.preimage (ϕ.continuous continuous_id continuous_const)).inter isClosed_Icc
  have := hs.Icc_subset_of_forall_mem_nhdsWithin (a := 0) (b := t)
    (by simp only [mem_ofPred_eq, Flow.map_zero_apply]; exact hx) fun r hr => by
      have h1 := h _ hr.1
      have h2 : Tendsto (fun u => u - r) (𝓝[>] r) (𝓝[>] (0 : ℝ)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have := (continuous_sub_right r).tendsto r
          rw [sub_self] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with u hu
          exact sub_pos.2 (mem_Ioi.1 hu)
      filter_upwards [h2.eventually h1] with u hu
      rw [← Flow.map_add, sub_add_cancel] at hu
      exact hu
  exact this ⟨ht, le_rfl⟩

theorem mem_of_local_bwd {N : Set X} (hN : IsClosed N)
    (h : ∀ p ∈ N, ∀ᶠ t in 𝓝[<] (0 : ℝ), ϕ t p ∈ N) {x : X} (hx : x ∈ N) {t : ℝ} (ht : t ≤ 0) :
    ϕ t x ∈ N := by
  have := mem_of_local_fwd ϕ.reverse hN (fun p hp => by
    have h2 : Tendsto (fun u : ℝ => -u) (𝓝[>] (0 : ℝ)) (𝓝[<] (0 : ℝ)) := by
      have := tendsto_neg_nhdsGT (a := (0 : ℝ)); rwa [neg_zero] at this
    filter_upwards [h2.eventually (h p hp)] with u hu
    exact hu) hx (t := -t) (by linarith)
  simpa using this

/-! ## Limit sets -/

theorem tendsto_add_atTop (t : ℝ) : Tendsto (t + ·) atTop atTop := tendsto_atTop_add_const_left _ t
  tendsto_id

theorem tendsto_add_atBot (t : ℝ) : Tendsto (t + ·) atBot atBot := tendsto_atBot_add_const_left _ t
  tendsto_id

theorem omegaLim_invariant {x z : X} (hz : z ∈ omegaLim ϕ x) (t : ℝ) : ϕ t z ∈ omegaLim ϕ x :=
  Flow.isInvariant_omegaLimit atTop ϕ {x} tendsto_add_atTop t hz

theorem alphaLim_invariant {x z : X} (hz : z ∈ alphaLim ϕ x) (t : ℝ) : ϕ t z ∈ alphaLim ϕ x :=
  Flow.isInvariant_omegaLimit atBot ϕ {x} tendsto_add_atBot t hz

theorem isClosed_omegaLim (x : X) : IsClosed (omegaLim ϕ x) := isClosed_omegaLimit _ _ _

theorem isClosed_alphaLim (x : X) : IsClosed (alphaLim ϕ x) := isClosed_omegaLimit _ _ _

theorem omegaLim_subset_of_eventually {x : X} {N : Set X} (hN : IsClosed N)
    (h : ∀ᶠ t in atTop, ϕ t x ∈ N) : omegaLim ϕ x ⊆ N := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 h
  refine (omegaLimit_subset_closure_image2 _ _ _ (Ici_mem_atTop T)).trans (closure_minimal ?_ hN)
  rintro _ ⟨t, ht, y, rfl, rfl⟩
  exact hT t ht

theorem alphaLim_subset_of_eventually {x : X} {N : Set X} (hN : IsClosed N)
    (h : ∀ᶠ t in atBot, ϕ t x ∈ N) : alphaLim ϕ x ⊆ N := by
  obtain ⟨T, hT⟩ := eventually_atBot.1 h
  refine (omegaLimit_subset_closure_image2 _ _ _ (Iic_mem_atBot T)).trans (closure_minimal ?_ hN)
  rintro _ ⟨t, ht, y, rfl, rfl⟩
  exact hT t ht

theorem frequently_of_mem_omegaLim {x z : X} (hz : z ∈ omegaLim ϕ x) {U : Set X} (hU : U ∈ 𝓝 z) :
    ∃ᶠ t in atTop, ϕ t x ∈ U := by
  have := (mem_omegaLimit_iff_frequently _ _ _ _).1 hz U hU
  exact this.mono fun t ⟨y, hy, hyU⟩ => by rw [mem_singleton_iff.1 hy] at hyU; exact hyU

theorem frequently_of_mem_alphaLim {x z : X} (hz : z ∈ alphaLim ϕ x) {U : Set X} (hU : U ∈ 𝓝 z) :
    ∃ᶠ t in atBot, ϕ t x ∈ U := by
  have := (mem_omegaLimit_iff_frequently _ _ _ _).1 hz U hU
  exact this.mono fun t ⟨y, hy, hyU⟩ => by rw [mem_singleton_iff.1 hy] at hyU; exact hyU

section Compact

variable [CompactSpace X]

theorem omegaLim_nonempty' (x : X) : (omegaLim ϕ x).Nonempty :=
  nonempty_omegaLimit _ _ _ (singleton_nonempty x)

theorem alphaLim_nonempty' (x : X) : (alphaLim ϕ x).Nonempty :=
  nonempty_omegaLimit _ _ _ (singleton_nonempty x)

theorem eventually_of_omegaLim_subset {x : X} {U : Set X} (hU : IsOpen U)
    (h : omegaLim ϕ x ⊆ U) : ∀ᶠ t in atTop, ϕ t x ∈ U :=
  (eventually_mapsTo_of_isOpen_of_omegaLimit_subset _ _ _ hU h).mono fun _ ht => ht rfl

theorem eventually_of_alphaLim_subset {x : X} {U : Set X} (hU : IsOpen U)
    (h : alphaLim ϕ x ⊆ U) : ∀ᶠ t in atBot, ϕ t x ∈ U :=
  (eventually_mapsTo_of_isOpen_of_omegaLimit_subset _ _ _ hU h).mono fun _ ht => ht rfl

theorem tendsto_of_omegaLim_subset {x e : X} (h : omegaLim ϕ x ⊆ {e}) :
    Tendsto (fun t => ϕ t x) atTop (𝓝 e) := by
  intro U hU
  obtain ⟨V, hVU, hV, heV⟩ := mem_nhds_iff.1 hU
  exact mem_map.2 ((eventually_of_omegaLim_subset ϕ hV (h.trans (singleton_subset_iff.2 heV))).mono
    fun _ ht => hVU ht)

theorem tendsto_of_alphaLim_subset {x e : X} (h : alphaLim ϕ x ⊆ {e}) :
    Tendsto (fun t => ϕ t x) atBot (𝓝 e) := by
  intro U hU
  obtain ⟨V, hVU, hV, heV⟩ := mem_nhds_iff.1 hU
  exact mem_map.2 ((eventually_of_alphaLim_subset ϕ hV (h.trans (singleton_subset_iff.2 heV))).mono
    fun _ ht => hVU ht)

end Compact

/-! ## Orbit-convex neighborhoods -/

/-- `N` is a neighborhood of `M = Inv(N)` that every orbit meets in an interval of times. -/
structure IsConvexNbhd (M N : Set X) : Prop where
  isClosed : IsClosed N
  inv : Inv ϕ N = M
  subset_interior : M ⊆ interior N
  convex : ∀ x t₁ t₂ t₃, t₁ ≤ t₂ → t₂ ≤ t₃ → ϕ t₁ x ∈ N → ϕ t₃ x ∈ N → ϕ t₂ x ∈ N

namespace IsConvexNbhd

variable {ϕ} {M N : Set X} (h : IsConvexNbhd ϕ M N)
include h

theorem eventually_of_meets {x : X} (hx : (omegaLim ϕ x ∩ M).Nonempty) :
    ∀ᶠ t in atTop, ϕ t x ∈ N := by
  obtain ⟨z, hz, hzM⟩ := hx
  obtain ⟨t₁, ht₁⟩ := (frequently_of_mem_omegaLim ϕ hz
    (isOpen_interior.mem_nhds (h.subset_interior hzM))).exists
  refine eventually_atTop.2 ⟨t₁, fun t ht => ?_⟩
  obtain ⟨t₃, ht₃, hN⟩ := ((frequently_of_mem_omegaLim ϕ hz
    (isOpen_interior.mem_nhds (h.subset_interior hzM))).and_eventually (eventually_ge_atTop t)).exists
  exact h.convex x t₁ t t₃ ht hN (interior_subset ht₁) (interior_subset ht₃)

theorem eventually_of_meets_alpha {x : X} (hx : (alphaLim ϕ x ∩ M).Nonempty) :
    ∀ᶠ t in atBot, ϕ t x ∈ N := by
  obtain ⟨z, hz, hzM⟩ := hx
  obtain ⟨t₃, ht₃⟩ := (frequently_of_mem_alphaLim ϕ hz
    (isOpen_interior.mem_nhds (h.subset_interior hzM))).exists
  refine eventually_atBot.2 ⟨t₃, fun t ht => ?_⟩
  obtain ⟨t₁, ht₁, hN⟩ := ((frequently_of_mem_alphaLim ϕ hz
    (isOpen_interior.mem_nhds (h.subset_interior hzM))).and_eventually (eventually_le_atBot t)).exists
  exact h.convex x t₁ t t₃ hN ht (interior_subset ht₁) (interior_subset ht₃)

theorem omegaLim_subset_of_meets {x : X} (hx : (omegaLim ϕ x ∩ M).Nonempty) :
    omegaLim ϕ x ⊆ M := by
  rw [← h.inv]
  intro z hz t
  exact omegaLim_subset_of_eventually ϕ h.isClosed (h.eventually_of_meets hx)
    (omegaLim_invariant ϕ hz t)

theorem alphaLim_subset_of_meets {x : X} (hx : (alphaLim ϕ x ∩ M).Nonempty) :
    alphaLim ϕ x ⊆ M := by
  rw [← h.inv]
  intro z hz t
  exact alphaLim_subset_of_eventually ϕ h.isClosed (h.eventually_of_meets_alpha hx)
    (alphaLim_invariant ϕ hz t)

theorem mem_of_limits {x : X} (hω : (omegaLim ϕ x ∩ M).Nonempty)
    (hα : (alphaLim ϕ x ∩ M).Nonempty) : x ∈ M := by
  rw [← h.inv]
  intro t
  obtain ⟨T₁, hT₁⟩ := eventually_atBot.1 (h.eventually_of_meets_alpha hα)
  obtain ⟨T₃, hT₃⟩ := eventually_atTop.1 (h.eventually_of_meets hω)
  exact h.convex x (min T₁ t) t (max T₃ t) (min_le_right _ _) (le_max_right _ _)
    (hT₁ _ (min_le_left _ _)) (hT₃ _ (le_max_left _ _))

theorem isIsolatedInvariantSet [CompactSpace X] : IsIsolatedInvariantSet ϕ M :=
  ⟨N, ⟨h.isClosed.isCompact, h.inv.symm ▸ h.subset_interior⟩, h.inv⟩

end IsConvexNbhd

/-- A forward invariant closed neighborhood is orbit-convex. -/
theorem IsConvexNbhd.of_fwd {M N : Set X} (hN : IsClosed N) (hinv : Inv ϕ N = M)
    (hint : M ⊆ interior N) (hfwd : ∀ x ∈ N, ∀ t, 0 ≤ t → ϕ t x ∈ N) : IsConvexNbhd ϕ M N where
  isClosed := hN
  inv := hinv
  subset_interior := hint
  convex x t₁ t₂ _ h12 _ h1 _ := by
    have := hfwd _ h1 (t₂ - t₁) (by linarith)
    rwa [← Flow.map_add, sub_add_cancel] at this

/-! ## A maximum principle -/

theorem nonpos_of_deriv_neg {S : Set X} (hS : IsCompact S) (hSi : ∀ z ∈ S, ∀ t, ϕ t z ∈ S)
    {V : X → ℝ} (hV : ContinuousOn V S) {d : X → ℝ}
    (hd : ∀ z ∈ S, 0 < V z → HasDerivAt (fun t => V (ϕ t z)) (d z) 0 ∧ d z < 0) :
    ∀ z ∈ S, V z ≤ 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨z₀, hz₀, hpos⟩ := hne
  obtain ⟨z, hz, hmax⟩ := hS.exists_isMaxOn ⟨z₀, hz₀⟩ hV
  have hVz : 0 < V z := hpos.trans_le (hmax hz₀)
  obtain ⟨hder, hneg⟩ := hd z hz hVz
  have h := (ConleyCheck.ODE.eventually_sign hder hneg).2
  obtain ⟨t, ht, hlt⟩ := (h.and self_mem_nhdsWithin).exists
  have := hmax (hSi z hz t)
  simp only [Flow.map_zero_apply] at ht
  exact absurd this (not_le.2 ht)

theorem nonneg_of_deriv_pos {S : Set X} (hS : IsCompact S) (hSi : ∀ z ∈ S, ∀ t, ϕ t z ∈ S)
    {V : X → ℝ} (hV : ContinuousOn V S) {d : X → ℝ}
    (hd : ∀ z ∈ S, V z < 0 → HasDerivAt (fun t => V (ϕ t z)) (d z) 0 ∧ 0 < d z) :
    ∀ z ∈ S, 0 ≤ V z := by
  have := nonpos_of_deriv_neg ϕ hS hSi (V := fun z => -V z) hV.neg (d := fun z => -d z)
    fun z hz hz' => ⟨(hd z hz (by linarith)).1.neg, by linarith [(hd z hz (by linarith)).2]⟩
  exact fun z hz => by linarith [this z hz]

/-! ## Reversors -/

/-- An involution that conjugates `ϕ` to its time reversal. -/
structure IsReversor (R : X → X) : Prop where
  cont : Continuous R
  invol : ∀ x, R (R x) = x
  conj : ∀ t x, ϕ t (R x) = R (ϕ (-t) x)

namespace IsReversor

variable {ϕ} {R : X → X} (hR : IsReversor ϕ R)
include hR

theorem mem_omegaLim {x z : X} (hz : z ∈ alphaLim ϕ x) : R z ∈ omegaLim ϕ (R x) := by
  rw [omegaLim, mem_omegaLimit_singleton_iff_mapClusterPt]
  rw [alphaLim, mem_omegaLimit_singleton_iff_mapClusterPt] at hz
  have h1 : MapClusterPt (R z) atBot fun t => R (ϕ t x) :=
    hz.tendsto_comp (hR.cont.tendsto z)
  have h2 : (fun t => ϕ.toFun t (R x)) = (fun t => R (ϕ t x)) ∘ fun t => -t := by
    funext t
    simp only [Function.comp]
    exact hR.conj t x
  rw [h2, MapClusterPt, ← Filter.map_map, map_neg_atTop]
  exact h1

theorem mem_alphaLim {x z : X} (hz : z ∈ omegaLim ϕ x) : R z ∈ alphaLim ϕ (R x) := by
  rw [alphaLim, mem_omegaLimit_singleton_iff_mapClusterPt]
  rw [omegaLim, mem_omegaLimit_singleton_iff_mapClusterPt] at hz
  have h1 : MapClusterPt (R z) atTop fun t => R (ϕ t x) :=
    hz.tendsto_comp (hR.cont.tendsto z)
  have h2 : (fun t => ϕ.toFun t (R x)) = (fun t => R (ϕ t x)) ∘ fun t => -t := by
    funext t
    simp only [Function.comp]
    exact hR.conj t x
  rw [h2, MapClusterPt, ← Filter.map_map, map_neg_atBot]
  exact h1

theorem omegaLim_eq (x : X) : omegaLim ϕ (R x) = R '' alphaLim ϕ x := by
  ext z
  constructor
  · intro hz
    have := hR.mem_alphaLim hz
    rw [hR.invol] at this
    exact ⟨R z, this, hR.invol z⟩
  · rintro ⟨w, hw, rfl⟩
    exact hR.mem_omegaLim hw

theorem alphaLim_eq (x : X) : alphaLim ϕ (R x) = R '' omegaLim ϕ x := by
  ext z
  constructor
  · intro hz
    have := hR.mem_omegaLim hz
    rw [hR.invol] at this
    exact ⟨R z, this, hR.invol z⟩
  · rintro ⟨w, hw, rfl⟩
    exact hR.mem_alphaLim hw

theorem image_eq_preimage (S : Set X) : R '' S = R ⁻¹' S := by
  ext z
  exact ⟨fun ⟨w, hw, h⟩ => by rw [← h, mem_preimage, hR.invol]; exact hw,
    fun h => ⟨R z, h, hR.invol z⟩⟩

theorem Inv_preimage (N : Set X) : Inv ϕ (R ⁻¹' N) = R ⁻¹' Inv ϕ N := by
  ext x
  constructor
  · intro h t
    show ϕ t (R x) ∈ N
    rw [hR.conj]
    exact h (-t)
  · intro h t
    show R (ϕ t x) ∈ N
    have := h (-t)
    rwa [hR.conj, neg_neg] at this

theorem isConvexNbhd {M N : Set X} (h : IsConvexNbhd ϕ M N) :
    IsConvexNbhd ϕ (R ⁻¹' M) (R ⁻¹' N) where
  isClosed := h.isClosed.preimage hR.cont
  inv := by rw [hR.Inv_preimage, h.inv]
  subset_interior := (preimage_mono h.subset_interior).trans
    (preimage_interior_subset_interior_preimage hR.cont)
  convex x t₁ t₂ t₃ h12 h23 h1 h3 := by
    simp only [mem_preimage] at h1 h3 ⊢
    have e : ∀ t, R (ϕ t x) = ϕ (-t) (R x) := fun t => by rw [hR.conj, neg_neg]
    rw [e] at h1 h3 ⊢
    exact h.convex (R x) (-t₃) (-t₂) (-t₁) (by linarith) (by linarith) h3 h1

end IsReversor

end ConleyCheck.Conley
