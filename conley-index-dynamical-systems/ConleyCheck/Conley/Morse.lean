import ConleyCheck.Conley.Additivity

/-!
# Conley index theory, Stages 3–4: attractor–repeller pairs and index triples

* `exists_indexTriple` (Salamon 1985, Franzosa 1986): an attractor–repeller pair has
  an index triple `N₀ ⊆ N₁ ⊆ N₂`. Proved for flows on Hausdorff spaces. Starting from an index
  pair `(N₂, N₀)` for `S` inside an isolating neighborhood `N`, the middle set is
  `N₁ = N₀ ∪ (N₂ ∩ Z)`, where `Z` consists of the points that spent time `k` in a closed
  neighborhood of `A` disjoint from `R` and have since stayed in `N` for at most time `k`. A
  Cantor intersection argument gives `k` such that `Z` is positively invariant relative to `N`.
* `hasIndex_union` : the index of a disjoint union of isolated invariant sets is the wedge of
  the indices. Proved in `ConleyCheck.Conley.Additivity`.

The rest is proved.
-/

namespace ConleyCheck.Conley

open Set Filter

variable {α : Type*} [TopologicalSpace α] (ϕ : Flow ℝ α)

/-- The `ω`-limit set of a point. -/
def omegaLim (x : α) : Set α := omegaLimit atTop ϕ.toFun {x}

/-- The `α`-limit set of a point. -/
def alphaLim (x : α) : Set α := omegaLimit atBot ϕ.toFun {x}

/-- A Morse decomposition `{A < R}` of `S`: every point of `S` outside `A ∪ R` runs from `R` to
`A`. -/
structure IsAttractorRepellerPair (S A R : Set α) : Prop where
  isolated : IsIsolatedInvariantSet ϕ S
  isolated_A : IsIsolatedInvariantSet ϕ A
  isolated_R : IsIsolatedInvariantSet ϕ R
  subset_A : A ⊆ S
  subset_R : R ⊆ S
  disjoint : Disjoint A R
  connecting : ∀ x ∈ S, x ∉ A → x ∉ R → omegaLim ϕ x ⊆ A ∧ alphaLim ϕ x ⊆ R

/-- An index triple: `(N₂, N₀)`, `(N₁, N₀)`, `(N₂, N₁)` are index pairs for `S`, `A`, `R`. -/
structure IsIndexTriple (S A R N₀ N₁ N₂ : Set α) : Prop where
  sub₀₁ : N₀ ⊆ N₁
  sub₁₂ : N₁ ⊆ N₂
  pair_S : IsIndexPair ϕ S N₂ N₀
  pair_A : IsIndexPair ϕ A N₁ N₀
  pair_R : IsIndexPair ϕ R N₂ N₁

variable {ϕ}

/-- `{x : ∃ u ∈ [a, b], (u, x) ∈ C}` is closed for closed `C`. -/
theorem isClosed_exists_Icc_prod {X : Type*} [TopologicalSpace X] {C : Set (ℝ × X)}
    (hC : IsClosed C) (a b : ℝ) : IsClosed {x | ∃ u ∈ Icc a b, (u, x) ∈ C} := by
  have hmap : IsClosedMap (Prod.snd : Icc a b × X → X) := isClosedMap_snd_of_compactSpace
  have hcl : IsClosed {p : Icc a b × X | ((p.1 : ℝ), p.2) ∈ C} :=
    hC.preimage ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have e : {x | ∃ u ∈ Icc a b, (u, x) ∈ C} =
      Prod.snd '' {p : Icc a b × X | ((p.1 : ℝ), p.2) ∈ C} := by
    ext x
    constructor
    · rintro ⟨u, hu, h⟩; exact ⟨(⟨u, hu⟩, x), h, rfl⟩
    · rintro ⟨⟨u, y⟩, h, rfl⟩; exact ⟨u, u.2, h⟩
  rw [e]
  exact hmap _ hcl

section LimitSets

theorem mem_closure_of_mem_alphaLim {x z : α} (hz : z ∈ alphaLim ϕ x) :
    z ∈ closure ((fun t => ϕ.toFun t x) '' Iic 0) := by
  have := omegaLimit_subset_closure_image2 (f := atBot) (ϕ := ϕ.toFun) (s := {x})
    (Iic_mem_atBot 0) hz
  rwa [image2_singleton_right] at this

theorem mem_closure_of_mem_omegaLim {x z : α} (hz : z ∈ omegaLim ϕ x) :
    z ∈ closure ((fun t => ϕ.toFun t x) '' Ici 0) := by
  have := omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ.toFun) (s := {x})
    (Ici_mem_atTop 0) hz
  rwa [image2_singleton_right] at this

variable [T2Space α] {S : Set α}

theorem alphaLim_nonempty (hS : IsCompact S) (hSi : IsInvariantSet ϕ S) {x : α} (hx : x ∈ S) :
    (alphaLim ϕ x).Nonempty :=
  nonempty_omegaLimit_of_isCompact_absorbing (f := atBot) (ϕ := ϕ.toFun) (s := {x}) hS ⟨univ, univ_mem,
    closure_minimal (by rintro _ ⟨t, -, y, rfl, rfl⟩; exact hSi t _ hx) hS.isClosed⟩
    (singleton_nonempty x)

theorem omegaLim_nonempty (hS : IsCompact S) (hSi : IsInvariantSet ϕ S) {x : α} (hx : x ∈ S) :
    (omegaLim ϕ x).Nonempty :=
  nonempty_omegaLimit_of_isCompact_absorbing (f := atTop) (ϕ := ϕ.toFun) (s := {x}) hS ⟨univ, univ_mem,
    closure_minimal (by rintro _ ⟨t, -, y, rfl, rfl⟩; exact hSi t _ hx) hS.isClosed⟩
    (singleton_nonempty x)

end LimitSets

section Triple

variable [T2Space α] {S A R : Set α}

/-- A point of `S ∖ A` cannot have its backward orbit in a closed set disjoint from `R`. -/
theorem IsAttractorRepellerPair.false_of_backward (h : IsAttractorRepellerPair ϕ S A R)
    {F : Set α} (hF : IsClosed F) (hFR : Disjoint F R) {w : α} (hwS : w ∈ S) (hwA : w ∉ A)
    (hw : ∀ t ≤ 0, ϕ t w ∈ F) : False := by
  by_cases hwR : w ∈ R
  · have := hw 0 le_rfl
    rw [ϕ.map_zero_apply] at this
    exact hFR.ne_of_mem this hwR rfl
  · obtain ⟨z, hz⟩ := alphaLim_nonempty h.isolated.isCompact h.isolated.isInvariantSet hwS
    have hzR := (h.connecting w hwS hwA hwR).2 hz
    have hzF : z ∈ F := closure_minimal (by rintro _ ⟨t, ht, rfl⟩; exact hw t ht) hF
      (mem_closure_of_mem_alphaLim hz)
    exact hFR.ne_of_mem hzF hzR rfl

/-- A point of `S ∖ R` enters every open neighborhood of `A` in forward time. -/
theorem IsAttractorRepellerPair.exists_forward_mem (h : IsAttractorRepellerPair ϕ S A R)
    {O : Set α} (hO : IsOpen O) (hAO : A ⊆ O) {y : α} (hyS : y ∈ S) (hyR : y ∉ R) :
    ∃ t, 0 ≤ t ∧ ϕ t y ∈ O := by
  by_cases hyA : y ∈ A
  · exact ⟨0, le_rfl, by rw [ϕ.map_zero_apply]; exact hAO hyA⟩
  · obtain ⟨z, hz⟩ := omegaLim_nonempty h.isolated.isCompact h.isolated.isInvariantSet hyS
    have hzO := hAO ((h.connecting y hyS hyA hyR).1 hz)
    obtain ⟨_, hzo, t, ht, rfl⟩ :=
      mem_closure_iff.1 (mem_closure_of_mem_omegaLim hz) O hO hzO
    exact ⟨t, ht, hzo⟩

/-- Let `N` isolate `S` and let `NA ⊆ N` be a closed neighborhood of `A` disjoint from `R`. For
some `n`, an orbit that leaves `int NA` after spending time `n` in `NA` leaves `N` within time
`n`. -/
theorem IsAttractorRepellerPair.exists_exit_time (h : IsAttractorRepellerPair ϕ S A R)
    {N NA : Set α} (hN : IsCompact N) (hNS : Inv ϕ N = S) (hNA : IsClosed NA) (hNAN : NA ⊆ N)
    (hAN : A ⊆ interior NA) (hNAR : Disjoint NA R) :
    ∃ n : ℕ, ∀ w, w ∉ interior NA → (∀ s ∈ Icc (-(n : ℝ)) 0, ϕ s w ∈ NA) →
      ¬ ∀ s ∈ Icc 0 (n : ℝ), ϕ s w ∈ N := by
  by_contra hc
  push Not at hc
  let C : ℕ → Set α := fun n => (interior NA)ᶜ ∩ {w | ∀ s ∈ Icc (-(n : ℝ)) 0, ϕ s w ∈ NA} ∩
    {w | ∀ s ∈ Icc 0 (n : ℝ), ϕ s w ∈ N}
  have hcl : ∀ n, IsClosed (C n) := fun n =>
    (isOpen_interior.isClosed_compl.inter (isClosed_forall_Icc ϕ hNA _ _)).inter
      (isClosed_forall_Icc ϕ hN.isClosed _ _)
  have hdec : ∀ n, C (n + 1) ⊆ C n := by
    intro n w hw
    refine ⟨⟨hw.1.1, fun s hs => hw.1.2 s ⟨?_, hs.2⟩⟩, fun s hs => hw.2 s ⟨hs.1, ?_⟩⟩
    · push_cast; linarith [hs.1]
    · push_cast; linarith [hs.2]
  have hne : ∀ n, (C n).Nonempty := fun n => by
    obtain ⟨w, h1, h2, h3⟩ := hc n
    exact ⟨w, ⟨h1, h2⟩, h3⟩
  have hC0 : IsCompact (C 0) := hN.of_isClosed_subset (hcl 0) fun w hw => by
    have := hw.2 0 ⟨le_rfl, by simp⟩
    rwa [ϕ.map_zero_apply] at this
  obtain ⟨w, hw⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hdec hne hC0 hcl
  rw [mem_iInter] at hw
  have hback : ∀ t ≤ 0, ϕ t w ∈ NA := fun t ht => by
    obtain ⟨n, hn⟩ := exists_nat_ge (-t)
    exact (hw n).1.2 t ⟨by linarith, ht⟩
  have hwS : w ∈ S := by
    rw [← hNS]
    intro t
    rcases le_total t 0 with ht | ht
    · exact hNAN (hback t ht)
    · obtain ⟨n, hn⟩ := exists_nat_ge t
      exact (hw n).2 t ⟨ht, hn⟩
  exact h.false_of_backward hNA hNAR hwS (fun hwA => (hw 0).1.1 (hAN hwA)) hback

variable (ϕ) in
/-- Points that spent time `k` in `NA` and then at most time `k` in `N`. -/
def tripleZ (NA N : Set α) (k : ℝ) : Set α :=
  {z | ∃ u ∈ Icc 0 k, (∀ v ∈ Icc 0 k, ϕ (-u - v) z ∈ NA) ∧ ∀ v ∈ Icc 0 k, ϕ (-min v u) z ∈ N}

omit [T2Space α] in
theorem isClosed_tripleZ {NA N : Set α} {k : ℝ} (hNA : IsClosed NA) (hN : IsClosed N) :
    IsClosed (tripleZ ϕ NA N k) := by
  refine isClosed_exists_Icc_prod (C := {p : ℝ × α | (∀ v ∈ Icc 0 k, ϕ (-p.1 - v) p.2 ∈ NA) ∧
    ∀ v ∈ Icc 0 k, ϕ (-min v p.1) p.2 ∈ N}) ?_ 0 k
  have e1 : {p : ℝ × α | ∀ v ∈ Icc 0 k, ϕ (-p.1 - v) p.2 ∈ NA} =
      ⋂ v ∈ Icc (0 : ℝ) k, (fun p : ℝ × α => ϕ (-p.1 - v) p.2) ⁻¹' NA := by
    ext; simp
  have e2 : {p : ℝ × α | ∀ v ∈ Icc 0 k, ϕ (-min v p.1) p.2 ∈ N} =
      ⋂ v ∈ Icc (0 : ℝ) k, (fun p : ℝ × α => ϕ (-min v p.1) p.2) ⁻¹' N := by
    ext; simp
  show IsClosed ({p : ℝ × α | ∀ v ∈ Icc 0 k, ϕ (-p.1 - v) p.2 ∈ NA} ∩
    {p : ℝ × α | ∀ v ∈ Icc 0 k, ϕ (-min v p.1) p.2 ∈ N})
  rw [e1, e2]
  exact (isClosed_biInter fun v _ =>
      hNA.preimage (ϕ.continuous (continuous_fst.neg.sub continuous_const) continuous_snd)).inter
    (isClosed_biInter fun v _ =>
      hN.preimage (ϕ.continuous (continuous_const.min continuous_fst).neg continuous_snd))

omit [T2Space α] in
/-- An orbit segment in `N` starting after time `k` in `NA` ends in `tripleZ`. -/
theorem mem_tripleZ_of_back {NA N : Set α} {k : ℝ} (hNA : IsClosed NA) (hk : 0 ≤ k)
    (hexit : ∀ w, w ∉ interior NA → (∀ s ∈ Icc (-k) 0, ϕ s w ∈ NA) → ¬ ∀ s ∈ Icc 0 k, ϕ s w ∈ N)
    {w : α} (hw : ∀ s ∈ Icc (-k) 0, ϕ s w ∈ NA) {T : ℝ} (hT : 0 ≤ T)
    (hseg : ∀ s ∈ Icc 0 T, ϕ s w ∈ N) : ϕ T w ∈ tripleZ ϕ NA N k := by
  by_cases hJ : ∀ r ∈ Icc 0 T, ϕ r w ∈ interior NA
  · refine ⟨0, ⟨le_rfl, hk⟩, fun v hv => ?_, fun v hv => ?_⟩
    · rw [← ϕ.map_add]
      rcases le_or_gt 0 (-0 - v + T) with h0 | h0
      · exact interior_subset (hJ _ ⟨h0, by linarith [hv.1]⟩)
      · exact hw _ ⟨by linarith [hv.2], h0.le⟩
    · rw [min_eq_right hv.1, neg_zero, ϕ.map_zero_apply]
      exact hseg T ⟨hT, le_rfl⟩
  push Not at hJ
  let K : Set ℝ := Icc 0 T ∩ {r | ϕ r w ∈ (interior NA)ᶜ}
  have hKc : IsClosed K :=
    isClosed_Icc.inter (isOpen_interior.isClosed_compl.preimage (continuous_orbit ϕ w))
  have hKne : K.Nonempty := by
    obtain ⟨r, hr, h⟩ := hJ
    exact ⟨r, hr, h⟩
  have hKb : BddBelow K := ⟨0, fun s hs => hs.1.1⟩
  have hs₀ : sInf K ∈ K := hKc.csInf_mem hKne hKb
  set s₀ := sInf K
  have hbefore : ∀ r, 0 ≤ r → r < s₀ → ϕ r w ∈ interior NA := by
    intro r hr0 hrs
    by_contra hc
    have : r ∈ K := ⟨⟨hr0, by linarith [hs₀.1.2]⟩, hc⟩
    exact absurd (csInf_le hKb this) (not_le.2 hrs)
  have hs₀NA : ϕ s₀ w ∈ NA := by
    rcases eq_or_lt_of_le hs₀.1.1 with h0 | hpos
    · rw [← h0]
      exact hw 0 ⟨by linarith, le_rfl⟩
    · have hC : IsClosed {r : ℝ | ϕ r w ∈ NA} := hNA.preimage (continuous_orbit ϕ w)
      have hsub : Ico 0 s₀ ⊆ {r : ℝ | ϕ r w ∈ NA} :=
        fun r hr => show ϕ r w ∈ NA from interior_subset (hbefore r hr.1 hr.2)
      have := closure_minimal hsub hC
      rw [closure_Ico hpos.ne] at this
      exact this ⟨hpos.le, le_rfl⟩
  have hNAseg : ∀ r ∈ Icc (-k) s₀, ϕ r w ∈ NA := by
    intro r hr
    rcases lt_or_ge r 0 with h0 | h0
    · exact hw r ⟨hr.1, h0.le⟩
    · rcases eq_or_lt_of_le hr.2 with h1 | h1
      · rw [h1]; exact hs₀NA
      · exact interior_subset (hbefore r h0 h1)
  have he2 : ∀ s ∈ Icc (-k) 0, ϕ s (ϕ s₀ w) ∈ NA := by
    intro s hs
    rw [← ϕ.map_add]
    exact hNAseg _ ⟨by linarith [hs.1, hs₀.1.1], by linarith [hs.2]⟩
  have hlt : T - s₀ < k := by
    by_contra hge
    push Not at hge
    refine hexit _ hs₀.2 he2 fun s hs => ?_
    rw [← ϕ.map_add]
    exact hseg _ ⟨by linarith [hs.1, hs₀.1.1], by linarith [hs.2]⟩
  refine ⟨T - s₀, ⟨by linarith [hs₀.1.2], hlt.le⟩, fun v hv => ?_, fun v hv => ?_⟩
  · rw [← ϕ.map_add]
    exact hNAseg _ ⟨by linarith [hv.2, hs₀.1.1], by linarith [hv.1]⟩
  · rw [← ϕ.map_add]
    have h1 := min_le_right v (T - s₀)
    have h2 : 0 ≤ min v (T - s₀) := le_min hv.1 (by linarith [hs₀.1.2])
    exact hseg _ ⟨by linarith [hs₀.1.1], by linarith⟩

omit [T2Space α] in
theorem tripleZ_posInv {NA N : Set α} {k : ℝ} (hNA : IsClosed NA) (hk : 0 ≤ k)
    (hexit : ∀ w, w ∉ interior NA → (∀ s ∈ Icc (-k) 0, ϕ s w ∈ NA) →
      ¬ ∀ s ∈ Icc 0 k, ϕ s w ∈ N) :
    IsPosInvRel ϕ (tripleZ ϕ NA N k) N := by
  rintro z ⟨u, hu, hzA, hzN⟩ t ht hseg
  have e : ϕ t z = ϕ (u + t) (ϕ (-u) z) := by
    rw [← ϕ.map_add, show u + t + -u = t by ring]
  rw [e]
  refine mem_tripleZ_of_back hNA hk hexit (fun s hs => ?_) (by linarith [hu.1]) fun s hs => ?_
  · rw [← ϕ.map_add]
    have := hzA (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    rwa [show -u - -s = s + -u by ring] at this
  · rw [← ϕ.map_add]
    rcases le_or_gt s u with h1 | h1
    · have := hzN (u - s) ⟨by linarith, by linarith [hu.2, hs.1]⟩
      rwa [min_eq_left (by linarith [hs.1] : u - s ≤ u), show -(u - s) = s + -u by ring] at this
    · exact hseg _ ⟨by linarith, by linarith [hs.2]⟩

/-- Index triples refining a given index pair `(N₂, N₀)` of `S`, for an isolating neighborhood `N`
of `S` containing `N₂ ∖ N₀`. -/
theorem exists_indexTriple_of (h : IsAttractorRepellerPair ϕ S A R) {N N₂ N₀ : Set α}
    (hN : IsIsolatingNbhd ϕ N) (hNS : Inv ϕ N = S) (hP : IsIndexPair ϕ S N₂ N₀)
    (hN₂N : N₂ \ N₀ ⊆ N) :
    ∃ N₁, IsIndexTriple ϕ S A R N₀ N₁ N₂ := by
  obtain ⟨UA, UR, hUA, hUR, hAU, hRU, hdisj⟩ :=
    SeparatedNhds.of_isCompact_isCompact h.isolated_A.isCompact h.isolated_R.isCompact h.disjoint
  have hNAc : IsClosed (N \ UR) := hN.1.isClosed.sdiff hUR
  have hNAN : N \ UR ⊆ N := sdiff_subset
  have hSN : S ⊆ interior N := by rw [← hNS]; exact hN.2
  have hAN : A ⊆ interior (N \ UR) := by
    intro x hx
    have : interior N ∩ UA ⊆ interior (N \ UR) :=
      interior_maximal (fun y hy => ⟨interior_subset hy.1, disjoint_left.1 hdisj hy.2⟩)
        (isOpen_interior.inter hUA)
    exact this ⟨hSN (h.subset_A hx), hAU hx⟩
  have hNAR : Disjoint (N \ UR) R := disjoint_left.2 fun x hx hxR => hx.2 (hRU hxR)
  obtain ⟨n, hn⟩ := h.exists_exit_time hN.1 hNS hNAc hNAN hAN hNAR
  set k : ℝ := (n : ℝ)
  have hk : 0 ≤ k := Nat.cast_nonneg n
  set Z := tripleZ ϕ (N \ UR) N k
  have hZc : IsClosed Z := isClosed_tripleZ hNAc hN.1.isClosed
  have hZpos : IsPosInvRel ϕ Z N := tripleZ_posInv hNAc hk hn
  have hAZ : A ⊆ interior Z := by
    have hW := isOpen_forall_Icc ϕ (isOpen_interior (s := N \ UR)) (-k) 0
    have hWZ : {x | ∀ s ∈ Icc (-k) 0, ϕ s x ∈ interior (N \ UR)} ⊆ Z := fun x hx =>
      ⟨0, ⟨le_rfl, hk⟩, fun v hv => interior_subset (hx _ ⟨by linarith [hv.2], by linarith [hv.1]⟩),
        fun v hv => by
          rw [min_eq_right hv.1, neg_zero, ϕ.map_zero_apply]
          have := hx 0 ⟨by linarith, le_rfl⟩
          rw [ϕ.map_zero_apply] at this
          exact hNAN (interior_subset this)⟩
    exact fun x hx => interior_maximal hWZ hW fun s _ => hAN (h.isolated_A.isInvariantSet s x hx)
  have hZR : Disjoint Z R := disjoint_left.2 fun z hz hzR => by
    obtain ⟨u, hu, hzA, -⟩ := hz
    exact disjoint_left.1 hNAR (hzA 0 ⟨le_rfl, hk⟩) (h.isolated_R.isInvariantSet _ z hzR)
  have hMN₂ : N₀ ∪ (N₂ ∩ Z) ⊆ N₂ := union_subset hP.subset inter_subset_left
  have hcM : IsCompact (N₀ ∪ (N₂ ∩ Z)) :=
    hP.isCompact_L.union (hP.isCompact_N.inter_right hZc)
  have hSsub : S ⊆ N₂ \ N₀ := hP.nhds.trans interior_subset
  have hkey : ∀ x ∈ N₂, x ∈ Z → ∀ t, 0 ≤ t → (∀ r ∈ Icc 0 t, ϕ r x ∈ N₂) →
      ϕ t x ∈ N₀ ∪ (N₂ ∩ Z) := by
    intro x hx2 hxZ t ht hseg
    by_cases hhit : ∃ s ∈ Icc 0 t, ϕ s x ∈ N₀
    · obtain ⟨s, hs, hs0⟩ := hhit
      exact Or.inl (posInv_shift hP.posInv hs.2 hs0 fun r hr => hseg r ⟨hs.1.trans hr.1, hr.2⟩)
    · push Not at hhit
      exact Or.inr ⟨hseg t ⟨ht, le_rfl⟩,
        hZpos x hxZ t ht fun r hr => hN₂N ⟨hseg r hr, hhit r hr⟩⟩
  -- the pair `(N₁, N₀)` for the attractor
  have hA1 : (N₀ ∪ (N₂ ∩ Z)) \ N₀ ⊆ (N₂ \ N₀) ∩ Z := by
    rintro x ⟨hx | hx, hx0⟩
    · exact absurd hx hx0
    · exact ⟨⟨hx.1, hx0⟩, hx.2⟩
  have hA2 : (N₂ \ N₀) ∩ Z ⊆ (N₀ ∪ (N₂ ∩ Z)) \ N₀ := fun x hx => ⟨Or.inr ⟨hx.1.1, hx.2⟩, hx.1.2⟩
  have hAint : A ⊆ interior ((N₀ ∪ (N₂ ∩ Z)) \ N₀) := fun x hx =>
    interior_mono hA2 (by rw [interior_inter]; exact ⟨hP.nhds (h.subset_A hx), hAZ hx⟩)
  have hAinv : Inv ϕ (closure ((N₀ ∪ (N₂ ∩ Z)) \ N₀)) = A := by
    refine subset_antisymm (fun y hy => ?_)
      (subset_Inv h.isolated_A.isInvariantSet (hAint.trans (interior_subset.trans subset_closure)))
    have hcl : closure ((N₀ ∪ (N₂ ∩ Z)) \ N₀) ⊆ closure (N₂ \ N₀) ∩ Z :=
      closure_minimal (hA1.trans (inter_subset_inter_left _ subset_closure))
        (isClosed_closure.inter hZc)
    have hyS : y ∈ S := by rw [← hP.inv_eq]; exact fun t => (hcl (hy t)).1
    by_contra hyA
    exact h.false_of_backward hZc hZR hyS hyA fun t _ => (hcl (hy t)).2
  have pair_A : IsIndexPair ϕ A (N₀ ∪ (N₂ ∩ Z)) N₀ := {
    isCompact_N := hcM
    isCompact_L := hP.isCompact_L
    subset := subset_union_left
    isolating := ⟨hcM.of_isClosed_subset isClosed_closure
        (closure_minimal sdiff_subset hcM.isClosed),
      by rw [hAinv]; exact hAint.trans (interior_mono subset_closure)⟩
    inv_eq := hAinv
    nhds := hAint
    posInv := fun x hx t ht hseg => hP.posInv x hx t ht fun s hs => hMN₂ (hseg s hs)
    exit := by
      intro x hx t ht hout
      rcases hx with hx0 | ⟨hx2, hxZ⟩
      · refine ⟨0, ⟨le_rfl, ht⟩, fun r hr => ?_, by rw [ϕ.map_zero_apply]; exact hx0⟩
        rw [show r = 0 by linarith [hr.1, hr.2], ϕ.map_zero_apply]
        exact Or.inl hx0
      · by_cases hin : ∀ r ∈ Icc 0 t, ϕ r x ∈ N₂
        · exact absurd (hkey x hx2 hxZ t ht hin) hout
        · push Not at hin
          obtain ⟨t', ht', hout'⟩ := hin
          obtain ⟨s, hs, hseg, hsL⟩ := hP.exit x hx2 t' ht'.1 hout'
          exact ⟨s, ⟨hs.1, hs.2.trans ht'.2⟩, fun r hr =>
            hkey x hx2 hxZ r hr.1 fun q hq => hseg q ⟨hq.1, hq.2.trans hr.2⟩, hsL⟩ }
  -- the pair `(N₂, N₁)` for the repeller
  have hR1 : N₂ \ (N₀ ∪ (N₂ ∩ Z)) ⊆ (N₂ \ N₀) ∩ Zᶜ := fun x hx =>
    ⟨⟨hx.1, fun h0 => hx.2 (Or.inl h0)⟩, fun hz => hx.2 (Or.inr ⟨hx.1, hz⟩)⟩
  have hR2 : (N₂ \ N₀) ∩ Zᶜ ⊆ N₂ \ (N₀ ∪ (N₂ ∩ Z)) := fun x hx => ⟨hx.1.1, by
    rintro (h0 | ⟨-, hz⟩)
    · exact hx.1.2 h0
    · exact hx.2 hz⟩
  have hRint : R ⊆ interior (N₂ \ (N₀ ∪ (N₂ ∩ Z))) := fun x hx =>
    interior_mono hR2 (by
      rw [interior_inter, hZc.isOpen_compl.interior_eq]
      exact ⟨hP.nhds (h.subset_R hx), disjoint_right.1 hZR hx⟩)
  have hRinv : Inv ϕ (closure (N₂ \ (N₀ ∪ (N₂ ∩ Z)))) = R := by
    refine subset_antisymm (fun y hy => ?_)
      (subset_Inv h.isolated_R.isInvariantSet (hRint.trans (interior_subset.trans subset_closure)))
    have hcl : closure (N₂ \ (N₀ ∪ (N₂ ∩ Z))) ⊆ closure (N₂ \ N₀) ∩ closure Zᶜ :=
      closure_minimal (hR1.trans (inter_subset_inter subset_closure subset_closure))
        (isClosed_closure.inter isClosed_closure)
    have hyS : y ∈ S := by rw [← hP.inv_eq]; exact fun t => (hcl (hy t)).1
    by_contra hyR
    obtain ⟨t, -, hti⟩ := h.exists_forward_mem isOpen_interior hAZ hyS hyR
    have := (hcl (hy t)).2
    rw [closure_compl] at this
    exact this hti
  have pair_R : IsIndexPair ϕ R N₂ (N₀ ∪ (N₂ ∩ Z)) := {
    isCompact_N := hP.isCompact_N
    isCompact_L := hcM
    subset := hMN₂
    isolating := ⟨hP.isCompact_N.of_isClosed_subset isClosed_closure
        (closure_minimal sdiff_subset hP.isCompact_N.isClosed),
      by rw [hRinv]; exact hRint.trans (interior_mono subset_closure)⟩
    inv_eq := hRinv
    nhds := hRint
    posInv := by
      intro x hx t ht hseg
      rcases hx with hx0 | ⟨hx2, hxZ⟩
      · exact Or.inl (hP.posInv x hx0 t ht hseg)
      · exact hkey x hx2 hxZ t ht hseg
    exit := by
      intro x hx t ht hout
      obtain ⟨s, hs, hseg, hsL⟩ := hP.exit x hx t ht hout
      exact ⟨s, hs, hseg, Or.inl hsL⟩ }
  exact ⟨N₀ ∪ (N₂ ∩ Z), subset_union_left, hMN₂, hP, pair_A, pair_R⟩

/-- Existence of index triples. -/
theorem exists_indexTriple (h : IsAttractorRepellerPair ϕ S A R) :
    ∃ N₀ N₁ N₂, IsIndexTriple ϕ S A R N₀ N₁ N₂ := by
  obtain ⟨N, hN, hNS⟩ := h.isolated
  obtain ⟨N₂, N₀, hP, hN₂N⟩ := exists_indexPair_of_t2 hN
  rw [hNS] at hP
  obtain ⟨N₁, hT⟩ := exists_indexTriple_of h hN hNS hP (sdiff_subset.trans hN₂N)
  exact ⟨N₀, N₁, N₂, hT⟩

/-- Every index pair `(N₂, N₀)` of `S` refines to an index triple. -/
theorem exists_indexTriple_of_pair (h : IsAttractorRepellerPair ϕ S A R) {N₂ N₀ : Set α}
    (hP : IsIndexPair ϕ S N₂ N₀) : ∃ N₁, IsIndexTriple ϕ S A R N₀ N₁ N₂ :=
  exists_indexTriple_of h hP.isolating hP.inv_eq hP subset_closure

/-- An attractor in a set with an index pair `(N, ∅)` has an index pair `(B, ∅)` with `B ⊆ N`. -/
theorem IsAttractorRepellerPair.exists_attractorPair (h : IsAttractorRepellerPair ϕ S A R)
    {N : Set α} (hP : IsIndexPair ϕ S N ∅) : ∃ B, B ⊆ N ∧ IsIndexPair ϕ A B ∅ := by
  have hcl : closure (N \ ∅) = N := by rw [sdiff_empty, hP.isCompact_N.isClosed.closure_eq]
  have hN := hP.isolating
  have hNS := hP.inv_eq
  rw [hcl] at hN hNS
  obtain ⟨N₁, hT⟩ := exists_indexTriple_of h hN hNS hP sdiff_subset
  exact ⟨N₁, hT.sub₁₂, hT.pair_A⟩

end Triple

/-- Additivity: the index of a disjoint union is the wedge sum. -/
theorem hasIndex_union [T2Space α] {A R : Set α} (hA : IsIsolatedInvariantSet ϕ A) (hR : IsIsolatedInvariantSet ϕ R)
    (hAR : Disjoint A R) {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x₀ : X} {y₀ : Y}
    (hX : HasIndex ϕ A X x₀) (hY : HasIndex ϕ R Y y₀) :
    HasIndex ϕ (A ∪ R) (Wedge X Y x₀ y₀) (Wedge.pt x₀ y₀) :=
  hasIndex_union_of_t2 hA hR hAR hX hY

/-- Either there is a connecting orbit from `R` to `A`, or `S = A ∪ R`. -/
theorem IsAttractorRepellerPair.connecting_or_eq_union {S A R : Set α}
    (h : IsAttractorRepellerPair ϕ S A R) :
    (∃ x ∈ S, x ∉ A ∧ x ∉ R ∧ omegaLim ϕ x ⊆ A ∧ alphaLim ϕ x ⊆ R) ∨ S = A ∪ R := by
  by_cases hx : ∃ x ∈ S, x ∉ A ∧ x ∉ R
  · obtain ⟨x, hxS, hxA, hxR⟩ := hx
    exact Or.inl ⟨x, hxS, hxA, hxR, h.connecting x hxS hxA hxR⟩
  · push Not at hx
    refine Or.inr (subset_antisymm (fun x hxS => ?_) (union_subset h.subset_A h.subset_R))
    by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · exact Or.inr (hx x hxS hxA)

/-- If there are no connecting orbits, the index of `S` is the wedge of the indices of `A` and
`R`. -/
theorem IsAttractorRepellerPair.hasIndex_of_no_connecting [T2Space α] {S A R : Set α} (h : IsAttractorRepellerPair ϕ S A R)
    (hno : ∀ x ∈ S, x ∈ A ∨ x ∈ R) {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ : X} {y₀ : Y} (hX : HasIndex ϕ A X x₀) (hY : HasIndex ϕ R Y y₀) :
    HasIndex ϕ S (Wedge X Y x₀ y₀) (Wedge.pt x₀ y₀) := by
  have hS : S = A ∪ R :=
    subset_antisymm (fun x hx => hno x hx) (union_subset h.subset_A h.subset_R)
  rw [hS]
  exact hasIndex_union h.isolated_A h.isolated_R h.disjoint hX hY

end ConleyCheck.Conley
