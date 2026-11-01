import ConleyCheck.ON.Limits
import ConleyCheck.Conley.OrbitLimits

/-!
# Attractors and repellers of a Morse decomposition

Let `(M_i)_{i ∈ ι}` be a Morse decomposition of an isolated invariant set `S` with respect to a
strict partial order `r` on a finite index set, so that a connecting orbit with `ω`-limit in `M_i`
and `α`-limit in `M_j` forces `r i j`. A set `P ⊆ ι` is closed downward (`IsDown`) if `r i j` and
`j ∈ P` imply `i ∈ P`.

* `morseAttr ϕ S M P`: the points of `S` whose `α`-limit set lies in some `M_j` with `j ∈ P`, i.e.,
  the Morse sets of `P` together with the orbits connecting them.
* `morseRep ϕ S M Q`: the points of `S` whose `ω`-limit set lies in some `M_i` with `i ∈ Q`.
* `IsMorseDecomp.isClosed_attr`: for `P` closed downward, `morseAttr ϕ S M P` is closed. A point
  of the closure outside the set has its `α`-limit in some `M_j`, `j ∉ P`. Backward orbits of nearby
  points of the set leave a neighborhood of `M_j`, and a Cantor intersection argument produces a
  point of the closure whose `α`-limit lies in a Morse set strictly above `M_j`, also outside `P`.
  Since `ι` is finite, this cannot go on forever.
* `IsMorseDecomp.isAttractorRepellerPair`: for `Q ⊆ P` both closed downward, `morseAttr ϕ S M Q`
  and `morseAttr ϕ S M P ∩ morseRep ϕ S M Qᶜ` form an attractor–repeller pair in
  `morseAttr ϕ S M P`, all three sets being isolated (`isIsolated_of_limits`).
* `IsMorseDecomp.attr_inter_rep_eq`: if `P ∖ Q = {k}`, the repeller is `M_k`.
-/

open Set Filter Topology

namespace ConleyCheck.Conley

variable {α : Type*} [TopologicalSpace α]

/-! ## Limit sets along orbits and under time reversal -/

theorem alphaLim_flow (ϕ : Flow ℝ α) (x : α) (t : ℝ) : alphaLim ϕ (ϕ t x) = alphaLim ϕ x := by
  have := Flow.omegaLimit_image_eq (f := atBot) ϕ {x}
    (fun s => tendsto_atBot_add_const_right _ s tendsto_id) t
  simpa [alphaLim, image_singleton] using this

theorem omegaLim_flow (ϕ : Flow ℝ α) (x : α) (t : ℝ) : omegaLim ϕ (ϕ t x) = omegaLim ϕ x := by
  have := Flow.omegaLimit_image_eq (f := atTop) ϕ {x}
    (fun s => tendsto_atTop_add_const_right _ s tendsto_id) t
  simpa [omegaLim, image_singleton] using this

theorem omegaLim_reverse (ϕ : Flow ℝ α) (x : α) : omegaLim ϕ.reverse x = alphaLim ϕ x := by
  ext z
  simp only [omegaLim, alphaLim, mem_omegaLimit_singleton_iff_mapClusterPt, MapClusterPt]
  have e : (fun t => ϕ.reverse.toFun t x) = (fun t => ϕ.toFun t x) ∘ Neg.neg := rfl
  rw [e, ← Filter.map_map, Filter.map_neg_atTop]

theorem alphaLim_reverse (ϕ : Flow ℝ α) (x : α) : alphaLim ϕ.reverse x = omegaLim ϕ x := by
  ext z
  simp only [omegaLim, alphaLim, mem_omegaLimit_singleton_iff_mapClusterPt, MapClusterPt]
  have e : (fun t => ϕ.reverse.toFun t x) = (fun t => ϕ.toFun t x) ∘ Neg.neg := rfl
  rw [e, ← Filter.map_map, Filter.map_neg_atBot]

theorem Inv_reverse (ϕ : Flow ℝ α) (N : Set α) : Inv ϕ.reverse N = Inv ϕ N := by
  ext x
  refine ⟨fun h t => ?_, fun h t => h (-t)⟩
  have := h (-t)
  rwa [Flow.reverse_apply, neg_neg] at this

theorem IsIsolatedInvariantSet.reverse {ϕ : Flow ℝ α} {S : Set α}
    (h : IsIsolatedInvariantSet ϕ S) : IsIsolatedInvariantSet ϕ.reverse S := by
  obtain ⟨N, ⟨hNc, hNi⟩, hNS⟩ := h
  exact ⟨N, ⟨hNc, by rw [Inv_reverse]; exact hNi⟩, by rw [Inv_reverse]; exact hNS⟩

theorem IsMorseDecomp.reverse {ϕ : Flow ℝ α} {S : Set α} {ι : Type*} {M : ι → Set α}
    {r : ι → ι → Prop} (h : IsMorseDecomp ϕ S M r) :
    IsMorseDecomp ϕ.reverse S M fun i j => r j i where
  isolated := h.isolated.reverse
  isolated_M i := (h.isolated_M i).reverse
  subset := h.subset
  disjoint := h.disjoint
  irrefl := h.irrefl
  trans i j k hij hjk := h.trans k j i hjk hij
  connecting x hx hm := by
    obtain ⟨i, j, hr, hi, hj⟩ := h.connecting x hx hm
    exact ⟨j, i, hr, by rw [omegaLim_reverse]; exact hj, by rw [alphaLim_reverse]; exact hi⟩

/-! ## Two compactness lemmas -/

section Compactness

variable {ϕ : Flow ℝ α}

theorem isClosed_stay (ϕ : Flow ℝ α) {V : Set α} (hV : IsClosed V) (T : Set ℝ) :
    IsClosed {z | ∀ s ∈ T, ϕ s z ∈ V} := by
  have e : {z | ∀ s ∈ T, ϕ s z ∈ V} = ⋂ s ∈ T, ϕ s ⁻¹' V := by ext; simp
  rw [e]
  exact isClosed_biInter fun s _ => hV.preimage (ϕ.continuous_toFun s)

/-- If for every `m` some point of the compact set `K` lies outside `int V` and stays in the closed
set `V` for time `m`, then some point of `K` lies outside `int V` and stays in `V` forever. -/
theorem exists_stay_of_forall_nat {K V : Set α} (hK : IsCompact K) (hKc : IsClosed K)
    (hV : IsClosed V)
    (h : ∀ m : ℕ, ∃ z ∈ K, z ∉ interior V ∧ ∀ s ∈ Icc (0 : ℝ) m, ϕ s z ∈ V) :
    ∃ z ∈ K, z ∉ interior V ∧ ∀ s, 0 ≤ s → ϕ s z ∈ V := by
  set E : ℕ → Set α := fun m => K ∩ (interior V)ᶜ ∩ {z | ∀ s ∈ Icc (0 : ℝ) m, ϕ s z ∈ V}
  have hEc : ∀ m, IsClosed (E m) := fun m =>
    (hKc.inter isOpen_interior.isClosed_compl).inter (isClosed_stay ϕ hV _)
  have hmono : ∀ m, E (m + 1) ⊆ E m := fun m z hz =>
    ⟨hz.1, fun s hs => hz.2 s ⟨hs.1, hs.2.trans (by push_cast; linarith)⟩⟩
  have hne : ∀ m, (E m).Nonempty := fun m =>
    let ⟨z, hzK, hz1, hz2⟩ := h m
    ⟨z, ⟨hzK, hz1⟩, hz2⟩
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed E hmono hne
    (hK.of_isClosed_subset (hEc 0) fun z hz => hz.1.1) hEc
  rw [mem_iInter] at hz
  refine ⟨z, (hz 0).1.1, (hz 0).1.2, fun s hs => ?_⟩
  obtain ⟨m, hm⟩ := exists_nat_ge s
  exact (hz m).2 s ⟨hs, hm⟩

/-- If `ϕ_s w ∈ int V` for `s ∈ [-m, 0]` and `ϕ_{-T} w ∉ int V` with `T ≥ 0`, then for the first
backward time `σ ≥ m` at which the orbit is outside `int V`, the point `ϕ_{-σ} w` stays in `V`
for time `σ`. -/
theorem exists_last_entry {V : Set α} (hV : IsClosed V) {w : α} {m T : ℝ} (hm : 0 ≤ m)
    (hin : ∀ s ∈ Icc (-m) 0, ϕ s w ∈ interior V) (hT0 : 0 ≤ T) (hT : ϕ (-T) w ∉ interior V) :
    ∃ σ, m ≤ σ ∧ ϕ (-σ) w ∉ interior V ∧ ∀ s ∈ Icc 0 σ, ϕ s (ϕ (-σ) w) ∈ V := by
  have hc : Continuous fun σ : ℝ => ϕ (-σ) w := ϕ.continuous continuous_neg continuous_const
  set B := {σ : ℝ | 0 ≤ σ ∧ ϕ (-σ) w ∉ interior V}
  have hBc : IsClosed B := isClosed_Ici.inter (isOpen_interior.isClosed_compl.preimage hc)
  have hBbdd : BddBelow B := ⟨0, fun σ hσ => hσ.1⟩
  have hσB : sInf B ∈ B := hBc.csInf_mem ⟨T, hT0, hT⟩ hBbdd
  set σ := sInf B
  have hlow : ∀ σ' ∈ Ico 0 σ, ϕ (-σ') w ∈ interior V := fun σ' hσ' => by
    by_contra hn
    have := csInf_le hBbdd ⟨hσ'.1, hn⟩
    linarith [hσ'.2]
  have hσm : m ≤ σ := by
    by_contra hlt
    push Not at hlt
    exact hσB.2 (hin (-σ) ⟨by linarith, by linarith [hσB.1]⟩)
  have hV' : Icc 0 σ ⊆ {σ' | ϕ (-σ') w ∈ V} := by
    rcases eq_or_lt_of_le hσB.1 with h0 | hpos
    · intro σ' hσ'
      have : σ' = 0 := le_antisymm (h0 ▸ hσ'.2) hσ'.1
      subst this
      have h1 := hin 0 ⟨by linarith, le_rfl⟩
      simpa using interior_subset h1
    · rw [← closure_Ico hpos.ne]
      exact closure_minimal (fun σ' hσ' => show ϕ (-σ') w ∈ V from interior_subset (hlow σ' hσ'))
        (hV.preimage hc)
  refine ⟨σ, hσm, hσB.2, fun s hs => ?_⟩
  rw [← Flow.map_add]
  have : ϕ (-(σ - s)) w ∈ V := hV' (show σ - s ∈ Icc 0 σ from ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  rwa [show s + -σ = -(σ - s) by ring]

/-- `C ⊆ S` is isolated if `S` is, `C` is closed and invariant, and every other point of `S` has a
limit point in a closed set `D ⊆ S` disjoint from `C`. -/
theorem isIsolated_of_limits [T2Space α] {S C D : Set α} (hS : IsIsolatedInvariantSet ϕ S)
    (hCS : C ⊆ S) (hC : IsClosed C) (hCi : IsInvariantSet ϕ C) (hD : IsClosed D) (hDS : D ⊆ S)
    (hCD : Disjoint C D)
    (hlim : ∀ x ∈ S, x ∉ C → (alphaLim ϕ x ∩ D).Nonempty ∨ (omegaLim ϕ x ∩ D).Nonempty) :
    IsIsolatedInvariantSet ϕ C := by
  have hSc := hS.isCompact
  obtain ⟨U, V, hU, hV, hCU, hDV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hSc.of_isClosed_subset hC hCS)
      (hSc.of_isClosed_subset hD hDS) hCD
  obtain ⟨N, ⟨hNc, hNi⟩, hNS⟩ := hS
  have hInv : Inv ϕ (N ∩ Vᶜ) = C := by
    refine subset_antisymm (fun x hx => ?_) (subset_Inv hCi fun x hx => ⟨?_, ?_⟩)
    · have hxS : x ∈ S := hNS ▸ Inv_mono inter_subset_left hx
      by_contra hxC
      have hout : ∀ z, z ∈ D → (∃ᶠ t in atBot, ϕ t x ∈ V) ∨ (∃ᶠ t in atTop, ϕ t x ∈ V) → False :=
        fun z _ h => by
          rcases h with h | h
          · obtain ⟨t, ht⟩ := h.exists; exact (hx t).2 ht
          · obtain ⟨t, ht⟩ := h.exists; exact (hx t).2 ht
      rcases hlim x hxS hxC with ⟨z, hzα, hzD⟩ | ⟨z, hzω, hzD⟩
      · exact hout z hzD (Or.inl (frequently_of_mem_alphaLim ϕ hzα (hV.mem_nhds (hDV hzD))))
      · exact hout z hzD (Or.inr (frequently_of_mem_omegaLim ϕ hzω (hV.mem_nhds (hDV hzD))))
    · exact Inv_subset N (hNS ▸ hCS hx)
    · exact fun hxV => hUV.ne_of_mem (hCU hx) hxV rfl
  refine ⟨N ∩ Vᶜ, ⟨hNc.inter_right hV.isClosed_compl, ?_⟩, hInv⟩
  rw [hInv, interior_inter]
  intro x hx
  exact ⟨hNS ▸ hNi |>.trans (subset_refl _) (hCS hx),
    interior_maximal (fun y hy hyV => hUV.ne_of_mem hy hyV rfl) hU (hCU hx)⟩

end Compactness

/-! ## Attractors of a Morse decomposition -/

/-- `P` is closed downward for `r`. -/
def IsDown {ι : Type*} (r : ι → ι → Prop) (P : Set ι) : Prop := ∀ i j, r i j → j ∈ P → i ∈ P

/-- The Morse sets of `P` and the orbits connecting them, for `P` closed downward. -/
def morseAttr (ϕ : Flow ℝ α) (S : Set α) {ι : Type*} (M : ι → Set α) (P : Set ι) : Set α :=
  {x | x ∈ S ∧ ∃ j ∈ P, alphaLim ϕ x ⊆ M j}

/-- The Morse sets of `Q` and the orbits connecting them, for `Q` closed upward. -/
def morseRep (ϕ : Flow ℝ α) (S : Set α) {ι : Type*} (M : ι → Set α) (Q : Set ι) : Set α :=
  {x | x ∈ S ∧ ∃ i ∈ Q, omegaLim ϕ x ⊆ M i}

theorem morseRep_eq (ϕ : Flow ℝ α) (S : Set α) {ι : Type*} (M : ι → Set α) (Q : Set ι) :
    morseRep ϕ S M Q = morseAttr ϕ.reverse S M Q := by
  ext x
  simp only [morseRep, morseAttr, alphaLim_reverse]

theorem morseAttr_mono {ϕ : Flow ℝ α} {S : Set α} {ι : Type*} {M : ι → Set α} {P Q : Set ι}
    (hPQ : P ⊆ Q) : morseAttr ϕ S M P ⊆ morseAttr ϕ S M Q :=
  fun _ ⟨hx, j, hj, hα⟩ => ⟨hx, j, hPQ hj, hα⟩

theorem morseRep_mono {ϕ : Flow ℝ α} {S : Set α} {ι : Type*} {M : ι → Set α} {P Q : Set ι}
    (hPQ : P ⊆ Q) : morseRep ϕ S M P ⊆ morseRep ϕ S M Q :=
  fun _ ⟨hx, i, hi, hω⟩ => ⟨hx, i, hPQ hi, hω⟩

theorem IsDown.compl {ι : Type*} {r : ι → ι → Prop} {P : Set ι} (h : IsDown r P) :
    IsDown (fun i j => r j i) Pᶜ := fun i j hij hj hi => hj (h j i hij hi)

/-- An attractor–repeller pair without connecting orbits is also a repeller–attractor pair. -/
theorem IsAttractorRepellerPair.swap {ϕ : Flow ℝ α} {S A R : Set α}
    (h : IsAttractorRepellerPair ϕ S A R) (hS : S ⊆ A ∪ R) : IsAttractorRepellerPair ϕ S R A where
  isolated := h.isolated
  isolated_A := h.isolated_R
  isolated_R := h.isolated_A
  subset_A := h.subset_R
  subset_R := h.subset_A
  disjoint := h.disjoint.symm
  connecting _ hx hR hA := ((hS hx).elim hA hR).elim

namespace IsMorseDecomp

variable [T2Space α] {ϕ : Flow ℝ α} {S : Set α} {ι : Type*} {M : ι → Set α} {r : ι → ι → Prop}
  (h : IsMorseDecomp ϕ S M r)
include h

theorem isCompact_S : IsCompact S := h.isolated.isCompact

theorem isClosed_M (i : ι) : IsClosed (M i) := (h.isolated_M i).isCompact.isClosed

theorem alphaLim_ne {x : α} (hx : x ∈ S) : (alphaLim ϕ x).Nonempty :=
  alphaLim_nonempty h.isolated.isCompact h.isolated.isInvariantSet hx

theorem omegaLim_ne {x : α} (hx : x ∈ S) : (omegaLim ϕ x).Nonempty :=
  omegaLim_nonempty h.isolated.isCompact h.isolated.isInvariantSet hx

theorem alphaLim_subset_M {i : ι} {x : α} (hx : x ∈ M i) : alphaLim ϕ x ⊆ M i :=
  alphaLim_subset_of_invariant ϕ (h.isClosed_M i)
    (fun z hz t => (h.isolated_M i).isInvariantSet t z hz) hx

theorem omegaLim_subset_M {i : ι} {x : α} (hx : x ∈ M i) : omegaLim ϕ x ⊆ M i :=
  omegaLim_subset_of_invariant ϕ (h.isClosed_M i)
    (fun z hz t => (h.isolated_M i).isInvariantSet t z hz) hx

theorem exists_alpha {x : α} (hx : x ∈ S) : ∃ j, alphaLim ϕ x ⊆ M j := by
  by_cases hm : ∃ i, x ∈ M i
  · obtain ⟨i, hi⟩ := hm
    exact ⟨i, h.alphaLim_subset_M hi⟩
  · push Not at hm
    obtain ⟨i, j, -, -, hj⟩ := h.connecting x hx hm
    exact ⟨j, hj⟩

theorem exists_omega {x : α} (hx : x ∈ S) : ∃ i, omegaLim ϕ x ⊆ M i := by
  by_cases hm : ∃ i, x ∈ M i
  · obtain ⟨i, hi⟩ := hm
    exact ⟨i, h.omegaLim_subset_M hi⟩
  · push Not at hm
    obtain ⟨i, j, -, hi, -⟩ := h.connecting x hx hm
    exact ⟨i, hi⟩

theorem eq_of_alpha {x : α} (hx : x ∈ S) {i j : ι} (hi : alphaLim ϕ x ⊆ M i)
    (hj : alphaLim ϕ x ⊆ M j) : i = j := by
  by_contra hij
  obtain ⟨z, hz⟩ := h.alphaLim_ne hx
  exact (h.disjoint hij).ne_of_mem (hi hz) (hj hz) rfl

theorem eq_of_omega {x : α} (hx : x ∈ S) {i j : ι} (hi : omegaLim ϕ x ⊆ M i)
    (hj : omegaLim ϕ x ⊆ M j) : i = j := by
  by_contra hij
  obtain ⟨z, hz⟩ := h.omegaLim_ne hx
  exact (h.disjoint hij).ne_of_mem (hi hz) (hj hz) rfl

/-- The `ω`-limit of a point lies in the same Morse set as its `α`-limit, or below it. -/
theorem omega_alpha {x : α} (hx : x ∈ S) {i j : ι} (hi : omegaLim ϕ x ⊆ M i)
    (hj : alphaLim ϕ x ⊆ M j) : i = j ∨ r i j := by
  by_cases hm : ∃ k, x ∈ M k
  · obtain ⟨k, hk⟩ := hm
    exact Or.inl ((h.eq_of_omega hx hi (h.omegaLim_subset_M hk)).trans
      (h.eq_of_alpha hx (h.alphaLim_subset_M hk) hj))
  · push Not at hm
    obtain ⟨i', j', hr, hi', hj'⟩ := h.connecting x hx hm
    rw [h.eq_of_omega hx hi hi', h.eq_of_alpha hx hj hj']
    exact Or.inr hr

/-- A point whose two limit sets lie in the same Morse set belongs to it. -/
theorem mem_of_limits {x : α} (hx : x ∈ S) {i : ι} (hi : omegaLim ϕ x ⊆ M i)
    (hj : alphaLim ϕ x ⊆ M i) : x ∈ M i := by
  by_contra hxi
  by_cases hm : ∃ k, x ∈ M k
  · obtain ⟨k, hk⟩ := hm
    have := h.eq_of_omega hx hi (h.omegaLim_subset_M hk)
    exact hxi (this ▸ hk)
  · push Not at hm
    obtain ⟨i', j', hr, hi', hj'⟩ := h.connecting x hx hm
    rw [← h.eq_of_omega hx hi hi', ← h.eq_of_alpha hx hj hj'] at hr
    exact h.irrefl i hr

theorem M_subset_attr {P : Set ι} {j : ι} (hj : j ∈ P) : M j ⊆ morseAttr ϕ S M P :=
  fun _ hx => ⟨h.subset j hx, j, hj, h.alphaLim_subset_M hx⟩

theorem M_subset_rep {Q : Set ι} {i : ι} (hi : i ∈ Q) : M i ⊆ morseRep ϕ S M Q :=
  fun _ hx => ⟨h.subset i hx, i, hi, h.omegaLim_subset_M hx⟩

theorem attr_univ : morseAttr ϕ S M univ = S :=
  subset_antisymm (fun _ hx => hx.1) fun _ hx =>
    let ⟨j, hj⟩ := h.exists_alpha hx
    ⟨hx, j, mem_univ j, hj⟩

theorem rep_univ : morseRep ϕ S M univ = S :=
  subset_antisymm (fun _ hx => hx.1) fun _ hx =>
    let ⟨i, hi⟩ := h.exists_omega hx
    ⟨hx, i, mem_univ i, hi⟩

omit [T2Space α] in
theorem isInvariant_attr (P : Set ι) : IsInvariantSet ϕ (morseAttr ϕ S M P) :=
  fun t x ⟨hx, j, hj, hα⟩ => ⟨h.isolated.isInvariantSet t x hx, j, hj, by rw [alphaLim_flow]; exact hα⟩

omit [T2Space α] in
theorem isInvariant_rep (Q : Set ι) : IsInvariantSet ϕ (morseRep ϕ S M Q) :=
  fun t x ⟨hx, i, hi, hω⟩ => ⟨h.isolated.isInvariantSet t x hx, i, hi, by rw [omegaLim_flow]; exact hω⟩

theorem disjoint_attr_rep {P : Set ι} (hP : IsDown r P) :
    Disjoint (morseAttr ϕ S M P) (morseRep ϕ S M Pᶜ) := by
  rw [Set.disjoint_left]
  rintro x ⟨hx, j, hj, hα⟩ ⟨-, i, hi, hω⟩
  rcases h.omega_alpha hx hω hα with rfl | hr
  · exact hi hj
  · exact hi (hP i j hr hj)

/-- One step of the closedness argument. -/
theorem closure_step {P : Set ι} (hP : IsDown r P) {j : ι} (hjP : j ∉ P) {x : α}
    (hx : x ∈ closure (morseAttr ϕ S M P)) (hαx : alphaLim ϕ x ⊆ M j) :
    ∃ k, r j k ∧ k ∉ P ∧ ∃ z ∈ closure (morseAttr ϕ S M P), alphaLim ϕ z ⊆ M k := by
  set A := morseAttr ϕ S M P
  have hSc := h.isCompact_S
  have hAS : closure A ⊆ S := closure_minimal (fun y hy => hy.1) hSc.isClosed
  have hxS := hAS hx
  obtain ⟨N, ⟨hNc, hNi⟩, hNM⟩ := h.isolated_M j
  have hMint : M j ⊆ interior N := hNM ▸ hNi
  have hInvN : ∀ {Z : Set α}, Z ⊆ N → (∀ z ∈ Z, ∀ t, ϕ t z ∈ Z) → Z ⊆ M j := fun hZN hZi =>
    hNM ▸ fun z hz t => hZN (hZi z hz t)
  -- the backward orbit of `x` eventually lies in `int N`
  have hev : ∀ᶠ t in atBot, ϕ t x ∈ interior N := by
    have := eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset (f := atBot)
      (ϕ := ϕ.toFun) (s := {x}) hSc
      (Eventually.of_forall fun t => by
        intro y hy; rw [mem_singleton_iff.1 hy]; exact h.isolated.isInvariantSet t x hxS)
      isOpen_interior (hαx.trans hMint)
    exact this.mono fun t ht => ht rfl
  obtain ⟨T, hT⟩ := eventually_atBot.1 hev
  obtain ⟨z, hzA, hzN, hzfwd⟩ := exists_stay_of_forall_nat (ϕ := ϕ)
    (hSc.of_isClosed_subset isClosed_closure hAS) isClosed_closure hNc.isClosed fun m => by
      -- a neighborhood of `x` whose orbits lie in `int N` for times in `[T - m, T]`
      have hW : ∀ᶠ y in 𝓝 x, ∀ s ∈ Icc (T - m) T, ϕ s y ∈ interior N := by
        refine isCompact_Icc.eventually_forall_of_forall_eventually fun s hs => ?_
        have hc : Continuous fun p : α × ℝ => ϕ p.2 p.1 := ϕ.continuous continuous_snd continuous_fst
        exact (hc.continuousAt (x := (x, s))).eventually
          (isOpen_interior.mem_nhds (hT s hs.2))
      obtain ⟨y, hyW, hyA⟩ := mem_closure_iff_nhds.1 hx _ hW
      obtain ⟨hyS, j', hj', hαy⟩ := hyA
      have hleave : ∃ t₁ ≤ T, ϕ t₁ y ∉ N := by
        by_contra hn
        push Not at hn
        have hαN : alphaLim ϕ y ⊆ M j := hInvN
          (alphaLim_subset_of_eventually ϕ hNc.isClosed (eventually_atBot.2 ⟨T, hn⟩))
          fun z hz t => alphaLim_invariant ϕ hz t
        obtain ⟨w, hw⟩ := h.alphaLim_ne hyS
        rcases eq_or_ne j j' with rfl | hne
        · exact hjP hj'
        · exact (h.disjoint hne).ne_of_mem (hαN hw) (hαy hw) rfl
      obtain ⟨t₁, ht₁, ht₁N⟩ := hleave
      obtain ⟨σ, hσm, hσN, hσV⟩ := exists_last_entry (ϕ := ϕ) hNc.isClosed (w := ϕ T y)
        (m := m) (T := T - t₁) (Nat.cast_nonneg m)
        (fun s hs => by
          rw [← Flow.map_add]
          exact hyW _ ⟨by linarith [hs.1], by linarith [hs.2]⟩)
        (by linarith)
        (by
          rw [← Flow.map_add, show -(T - t₁) + T = t₁ by ring]
          exact fun hi => ht₁N (interior_subset hi))
      refine ⟨ϕ (-σ) (ϕ T y), subset_closure (h.isInvariant_attr P _ _
          (h.isInvariant_attr P _ _ ⟨hyS, j', hj', hαy⟩)), hσN, fun s hs => ?_⟩
      exact hσV s ⟨hs.1, hs.2.trans hσm⟩
  have hzS := hAS hzA
  have hωz : omegaLim ϕ z ⊆ M j := hInvN
    (omegaLim_subset_of_eventually ϕ hNc.isClosed (eventually_atTop.2 ⟨0, fun s hs => hzfwd s hs⟩))
    fun w hw t => omegaLim_invariant ϕ hw t
  obtain ⟨k, hk⟩ := h.exists_alpha hzS
  rcases h.omega_alpha hzS hωz hk with rfl | hr
  · exact absurd (hMint (h.mem_of_limits hzS hωz hk)) hzN
  · exact ⟨k, hr, fun hkP => hjP (hP j k hr hkP), z, hzA, hk⟩

/-- For `P` closed downward, `morseAttr ϕ S M P` is closed. -/
theorem isClosed_attr [Finite ι] {P : Set ι} (hP : IsDown r P) :
    IsClosed (morseAttr ϕ S M P) := by
  have : IsTrans ι (fun k j => r j k) := ⟨fun a b c hab hbc => h.trans c b a hbc hab⟩
  have : Std.Irrefl (fun k j : ι => r j k) := ⟨h.irrefl⟩
  have wf := Finite.wellFounded_of_trans_of_irrefl (fun k j : ι => r j k)
  have key : ∀ j, j ∉ P → ∀ x ∈ closure (morseAttr ϕ S M P), alphaLim ϕ x ⊆ M j → False := by
    intro j
    induction j using wf.induction with
    | _ j ih =>
      intro hjP x hx hαx
      obtain ⟨k, hk, hkP, z, hz, hαz⟩ := h.closure_step hP hjP hx hαx
      exact ih k hk hkP z hz hαz
  refine closure_subset_iff_isClosed.1 fun x hx => ?_
  have hxS : x ∈ S := closure_minimal (fun y hy => hy.1) h.isCompact_S.isClosed hx
  obtain ⟨j, hj⟩ := h.exists_alpha hxS
  by_cases hjP : j ∈ P
  · exact ⟨hxS, j, hjP, hj⟩
  · exact (key j hjP x hx hj).elim

/-- For `Q` closed upward, `morseRep ϕ S M Q` is closed. -/
theorem isClosed_rep [Finite ι] {P : Set ι} (hP : IsDown r P) :
    IsClosed (morseRep ϕ S M Pᶜ) := by
  rw [morseRep_eq]
  exact h.reverse.isClosed_attr hP.compl

theorem isIsolated_attr [Finite ι] {P : Set ι} (hP : IsDown r P) :
    IsIsolatedInvariantSet ϕ (morseAttr ϕ S M P) := by
  refine isIsolated_of_limits h.isolated (fun x hx => hx.1) (h.isClosed_attr hP)
    (h.isInvariant_attr P) (h.isClosed_rep hP) (fun x hx => hx.1) (h.disjoint_attr_rep hP)
    fun x hxS hxA => Or.inl ?_
  obtain ⟨j, hj⟩ := h.exists_alpha hxS
  have hjP : j ∉ P := fun hjP => hxA ⟨hxS, j, hjP, hj⟩
  obtain ⟨z, hz⟩ := h.alphaLim_ne hxS
  exact ⟨z, hz, h.M_subset_rep hjP (hj hz)⟩

/-- For `Q ⊆ P` closed downward, `morseAttr ϕ S M P ∩ morseRep ϕ S M Qᶜ` is isolated. -/
theorem isIsolated_attr_inter_rep [Finite ι] {P Q : Set ι} (hP : IsDown r P) (hQ : IsDown r Q)
    (hQP : Q ⊆ P) : IsIsolatedInvariantSet ϕ (morseAttr ϕ S M P ∩ morseRep ϕ S M Qᶜ) := by
  refine isIsolated_of_limits (h.isIsolated_attr hP) inter_subset_left
    ((h.isClosed_attr hP).inter (h.isClosed_rep hQ))
    (fun t x hx => ⟨h.isInvariant_attr P t x hx.1, h.isInvariant_rep _ t x hx.2⟩)
    (h.isClosed_attr hQ) (morseAttr_mono hQP)
    (Set.disjoint_left.2 fun x hx hxQ => Set.disjoint_left.1 (h.disjoint_attr_rep hQ) hxQ hx.2)
    fun x hxP hxR => Or.inr ?_
  obtain ⟨i, hi⟩ := h.exists_omega hxP.1
  have hiQ : i ∈ Q := by
    by_contra hiQ
    exact hxR ⟨hxP, hxP.1, i, hiQ, hi⟩
  obtain ⟨z, hz⟩ := h.omegaLim_ne hxP.1
  exact ⟨z, hz, h.M_subset_attr hiQ (hi hz)⟩

/-- For `Q ⊆ P` closed downward, `morseAttr ϕ S M Q` and `morseAttr ϕ S M P ∩ morseRep ϕ S M Qᶜ`
form an attractor–repeller pair in `morseAttr ϕ S M P`. -/
theorem isAttractorRepellerPair [Finite ι] {P Q : Set ι} (hP : IsDown r P) (hQ : IsDown r Q)
    (hQP : Q ⊆ P) :
    IsAttractorRepellerPair ϕ (morseAttr ϕ S M P) (morseAttr ϕ S M Q)
      (morseAttr ϕ S M P ∩ morseRep ϕ S M Qᶜ) where
  isolated := h.isIsolated_attr hP
  isolated_A := h.isIsolated_attr hQ
  isolated_R := h.isIsolated_attr_inter_rep hP hQ hQP
  subset_A := morseAttr_mono hQP
  subset_R := inter_subset_left
  disjoint := Set.disjoint_left.2 fun x hx hxR =>
    Set.disjoint_left.1 (h.disjoint_attr_rep hQ) hx hxR.2
  connecting x hxP hxA hxR := by
    obtain ⟨hxS, j, hjP, hj⟩ := hxP
    obtain ⟨i, hi⟩ := h.exists_omega hxS
    have hiQ : i ∈ Q := by
      by_contra hiQ
      exact hxR ⟨⟨hxS, j, hjP, hj⟩, hxS, i, hiQ, hi⟩
    have hjQ : j ∉ Q := fun hjQ => hxA ⟨hxS, j, hjQ, hj⟩
    exact ⟨hi.trans (h.M_subset_attr hiQ),
      hj.trans fun y hy => ⟨h.M_subset_attr hjP hy, h.M_subset_rep hjQ hy⟩⟩

/-- For `Q ⊆ P' ⊆ P` closed downward, the Morse sets of `P' ∖ Q` and of `P ∖ P'` with their
connecting orbits form an attractor–repeller pair in the Morse set of `P ∖ Q`. -/
theorem isAttractorRepellerPair_interval [Finite ι] {P P' Q : Set ι} (hP : IsDown r P)
    (hP' : IsDown r P') (hQ : IsDown r Q) (hQP' : Q ⊆ P') (hP'P : P' ⊆ P) :
    IsAttractorRepellerPair ϕ (morseAttr ϕ S M P ∩ morseRep ϕ S M Qᶜ)
      (morseAttr ϕ S M P' ∩ morseRep ϕ S M Qᶜ) (morseAttr ϕ S M P ∩ morseRep ϕ S M P'ᶜ) where
  isolated := h.isIsolated_attr_inter_rep hP hQ (hQP'.trans hP'P)
  isolated_A := h.isIsolated_attr_inter_rep hP' hQ hQP'
  isolated_R := h.isIsolated_attr_inter_rep hP hP' hP'P
  subset_A := fun _ hx => ⟨morseAttr_mono hP'P hx.1, hx.2⟩
  subset_R := fun _ hx => ⟨hx.1, morseRep_mono (compl_subset_compl.2 hQP') hx.2⟩
  disjoint := Set.disjoint_left.2 fun x hx hxR =>
    Set.disjoint_left.1 (h.disjoint_attr_rep hP') hx.1 hxR.2
  connecting x hx hxA hxR := by
    obtain ⟨⟨hxS, j, hjP, hj⟩, -, i, hiQ, hi⟩ := hx
    have hiP' : i ∈ P' := by
      by_contra hiP'
      exact hxR ⟨⟨hxS, j, hjP, hj⟩, hxS, i, hiP', hi⟩
    have hjP' : j ∉ P' := fun hjP' => hxA ⟨⟨hxS, j, hjP', hj⟩, hxS, i, hiQ, hi⟩
    exact ⟨hi.trans fun y hy => ⟨h.M_subset_attr hiP' hy, h.M_subset_rep hiQ hy⟩,
      hj.trans fun y hy => ⟨h.M_subset_attr hjP hy, h.M_subset_rep hjP' hy⟩⟩

/-- If `P ∖ Q = {k}`, the repeller of `isAttractorRepellerPair` is `M_k`. -/
theorem attr_inter_rep_eq {P Q : Set ι} (hP : IsDown r P) (hQ : IsDown r Q) {k : ι}
    (hkP : k ∈ P) (hkQ : k ∉ Q) (hPQ : ∀ l ∈ P, l ∉ Q → l = k) :
    morseAttr ϕ S M P ∩ morseRep ϕ S M Qᶜ = M k := by
  refine subset_antisymm ?_ fun x hx => ⟨h.M_subset_attr hkP hx, h.M_subset_rep hkQ hx⟩
  rintro x ⟨⟨hxS, j, hjP, hj⟩, -, i, hiQ, hi⟩
  have hiP : i ∈ P := by
    rcases h.omega_alpha hxS hi hj with rfl | hr
    · exact hjP
    · exact hP i j hr hjP
  have hjQ : j ∉ Q := fun hjQ => by
    rcases h.omega_alpha hxS hi hj with rfl | hr
    · exact hiQ hjQ
    · exact hiQ (hQ i j hr hjQ)
  rw [hPQ i hiP hiQ] at hi
  rw [hPQ j hjP hjQ] at hj
  exact h.mem_of_limits hxS hi hj

/-- A minimal Morse set is its own attractor. -/
theorem attr_singleton {k : ι} (hk : IsDown r {k}) : morseAttr ϕ S M {k} = M k := by
  refine subset_antisymm ?_ (h.M_subset_attr rfl)
  rintro x ⟨hxS, j, rfl, hj⟩
  obtain ⟨i, hi⟩ := h.exists_omega hxS
  rcases h.omega_alpha hxS hi hj with rfl | hr
  · exact h.mem_of_limits hxS hi hj
  · rw [hk i j hr rfl] at hi
    exact h.mem_of_limits hxS hi hj

end IsMorseDecomp

end ConleyCheck.Conley
