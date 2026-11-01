import ConleyCheck.Conley.Basic

/-!
# Existence of index pairs

For an isolating neighborhood `N` of `S = Inv(N)` in a Hausdorff space, Cantor's intersection
theorem gives a time `T ≥ 0` such that `ϕ([-T, T], x) ⊆ N` implies `x ∈ int N`. Then
`N₁ = {x : ϕ([-T, 0], x) ⊆ N}` and `N₀ = {x ∈ N₁ : ϕ([0, T], x) ⊄ int N}` form an index pair for
`S` with `N₁ ⊆ N` (cf. Salamon 1985, Thm. 4.3).
-/

namespace ConleyCheck.Conley

open Set

variable {α : Type*} [TopologicalSpace α] {ϕ : Flow ℝ α}

section Tube

variable (ϕ)

theorem continuous_orbit (x : α) : Continuous fun s : ℝ => ϕ s x :=
  ϕ.continuous continuous_id continuous_const

/-- `{x : ∃ s ∈ [a, b], ϕ s x ∈ C}` is closed for closed `C`. -/
theorem isClosed_exists_Icc {C : Set α} (hC : IsClosed C) (a b : ℝ) :
    IsClosed {x | ∃ s ∈ Icc a b, ϕ s x ∈ C} := by
  have hmap : IsClosedMap (Prod.snd : Icc a b × α → α) := isClosedMap_snd_of_compactSpace
  have hcl : IsClosed {p : Icc a b × α | ϕ p.1 p.2 ∈ C} :=
    hC.preimage (ϕ.continuous (continuous_subtype_val.comp continuous_fst) continuous_snd)
  have e : {x | ∃ s ∈ Icc a b, ϕ s x ∈ C} = Prod.snd '' {p : Icc a b × α | ϕ p.1 p.2 ∈ C} := by
    ext x
    constructor
    · rintro ⟨s, hs, h⟩; exact ⟨(⟨s, hs⟩, x), h, rfl⟩
    · rintro ⟨⟨s, y⟩, h, rfl⟩; exact ⟨s, s.2, h⟩
  rw [e]
  exact hmap _ hcl

/-- `{x : ϕ([a, b], x) ⊆ C}` is closed for closed `C`. -/
theorem isClosed_forall_Icc {C : Set α} (hC : IsClosed C) (a b : ℝ) :
    IsClosed {x | ∀ s ∈ Icc a b, ϕ s x ∈ C} := by
  have e : {x | ∀ s ∈ Icc a b, ϕ s x ∈ C} = ⋂ s ∈ Icc a b, ϕ s ⁻¹' C := by
    ext x; simp
  rw [e]
  exact isClosed_biInter fun s _ => hC.preimage (ϕ.continuous_toFun s)

/-- `{x : ϕ([a, b], x) ⊆ O}` is open for open `O`. -/
theorem isOpen_forall_Icc {O : Set α} (hO : IsOpen O) (a b : ℝ) :
    IsOpen {x | ∀ s ∈ Icc a b, ϕ s x ∈ O} := by
  have e : {x | ∀ s ∈ Icc a b, ϕ s x ∈ O} = {x | ∃ s ∈ Icc a b, ϕ s x ∈ Oᶜ}ᶜ := by
    ext x; simp
  rw [e]
  exact (isClosed_exists_Icc ϕ hO.isClosed_compl a b).isOpen_compl

end Tube

/-- There is `n` such that `ϕ([-n, n], x) ⊆ N` forces `x ∈ int N`. -/
theorem exists_nat_mem_interior [T2Space α] {N : Set α} (hN : IsIsolatingNbhd ϕ N) :
    ∃ n : ℕ, ∀ x, (∀ s ∈ Icc (-(n : ℝ)) n, ϕ s x ∈ N) → x ∈ interior N := by
  by_contra h
  push Not at h
  let K : ℕ → Set α := fun n => (interior N)ᶜ ∩ {x | ∀ s ∈ Icc (-(n : ℝ)) n, ϕ s x ∈ N}
  have hcl : ∀ n, IsClosed (K n) := fun n =>
    isOpen_interior.isClosed_compl.inter (isClosed_forall_Icc ϕ hN.1.isClosed _ _)
  have hdec : ∀ n, K (n + 1) ⊆ K n := by
    intro n x hx
    refine ⟨hx.1, fun s hs => hx.2 s ⟨?_, ?_⟩⟩ <;> push_cast <;> linarith [hs.1, hs.2]
  have hne : ∀ n, (K n).Nonempty := by
    intro n
    obtain ⟨x, hx, hxi⟩ := h n
    exact ⟨x, hxi, hx⟩
  have hK0 : IsCompact (K 0) := by
    refine hN.1.of_isClosed_subset (hcl 0) fun x hx => ?_
    have := hx.2 0 ⟨by simp, by simp⟩
    rwa [ϕ.map_zero_apply] at this
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hdec hne
    hK0 hcl
  rw [mem_iInter] at hx
  have hinv : x ∈ Inv ϕ N := by
    intro t
    obtain ⟨n, hn⟩ := exists_nat_ge |t|
    exact (hx n).2 t ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  exact (hx 0).1 (hN.2 hinv)

section Pair

variable (ϕ)

/-- `N₁ = {x : ϕ([-T, 0], x) ⊆ N}`. -/
def pairN₁ (N : Set α) (T : ℝ) : Set α := {x | ∀ s ∈ Icc (-T) 0, ϕ s x ∈ N}

/-- `N₀ = {x ∈ N₁ : ϕ([0, T], x) ⊄ int N}`. -/
def pairN₀ (N : Set α) (T : ℝ) : Set α :=
  pairN₁ ϕ N T ∩ {x | ∃ s ∈ Icc 0 T, ϕ s x ∉ interior N}

variable {ϕ}

variable {N : Set α} {T : ℝ}

theorem pairN₁_subset (hT : 0 ≤ T) : pairN₁ ϕ N T ⊆ N := fun x hx => by
  have := hx 0 ⟨by linarith, le_rfl⟩
  rwa [ϕ.map_zero_apply] at this

theorem isClosed_pairN₁ (hN : IsClosed N) : IsClosed (pairN₁ ϕ N T) :=
  isClosed_forall_Icc ϕ hN _ _

theorem isClosed_pairN₀ (hN : IsClosed N) : IsClosed (pairN₀ ϕ N T) := by
  refine (isClosed_pairN₁ hN).inter ?_
  have e : {x | ∃ s ∈ Icc 0 T, ϕ s x ∉ interior N} =
      {x | ∃ s ∈ Icc 0 T, ϕ s x ∈ (interior N)ᶜ} := rfl
  rw [e]
  exact isClosed_exists_Icc ϕ isOpen_interior.isClosed_compl _ _

/-- `N₁` is positively invariant relative to `N`. -/
theorem pairN₁_posInv {x : α} (hx : x ∈ pairN₁ ϕ N T) {t : ℝ} (ht : 0 ≤ t)
    (hseg : ∀ r ∈ Icc 0 t, ϕ r x ∈ N) : ϕ t x ∈ pairN₁ ϕ N T := by
  intro s hs
  rw [← ϕ.map_add]
  by_cases h : 0 ≤ s + t
  · exact hseg (s + t) ⟨h, by linarith [hs.2]⟩
  · exact hx (s + t) ⟨by linarith [hs.1], by linarith⟩

theorem pairN₀_posInv (hT : 0 ≤ T)
    (hTl : ∀ w, (∀ r ∈ Icc (-T) T, ϕ r w ∈ N) → w ∈ interior N) :
    IsPosInvRel ϕ (pairN₀ ϕ N T) (pairN₁ ϕ N T) := by
  intro x hx t ht hseg
  obtain ⟨hx1, s₀, hs₀, hout⟩ := hx
  refine ⟨hseg t ⟨ht, le_rfl⟩, ?_⟩
  by_cases hts : t ≤ s₀
  · refine ⟨s₀ - t, ⟨by linarith, by linarith [hs₀.2]⟩, ?_⟩
    rw [← ϕ.map_add, sub_add_cancel]
    exact hout
  · push Not at hts
    show ∃ s ∈ Icc 0 T, ϕ s (ϕ t x) ∉ interior N
    by_contra hcon
    push Not at hcon
    apply hout
    apply hTl
    intro r hr
    rw [← ϕ.map_add]
    rcases le_or_gt (r + s₀) 0 with h1 | h1
    · exact hx1 (r + s₀) ⟨by linarith [hr.1, hs₀.1], h1⟩
    · rcases le_or_gt (r + s₀) t with h2 | h2
      · exact pairN₁_subset hT (hseg (r + s₀) ⟨h1.le, h2⟩)
      · have e : ϕ (r + s₀) x = ϕ (r + s₀ - t) (ϕ t x) := by
          rw [← ϕ.map_add, sub_add_cancel]
        rw [e]
        exact interior_subset (hcon _ ⟨by linarith, by linarith [hr.2, hs₀.1]⟩)

theorem pair_exit (hN : IsClosed N) (hT : 0 ≤ T) :
    IsExitSet ϕ (pairN₀ ϕ N T) (pairN₁ ϕ N T) := by
  intro x hx t ht hout
  have hK : ∃ s ∈ Icc 0 t, ϕ s x ∉ interior N := by
    by_contra hcon
    push Not at hcon
    exact hout (pairN₁_posInv hx ht fun r hr => interior_subset (hcon r hr))
  let K : Set ℝ := Icc 0 t ∩ {s | ϕ s x ∈ (interior N)ᶜ}
  have hKc : IsClosed K :=
    isClosed_Icc.inter (isOpen_interior.isClosed_compl.preimage (continuous_orbit ϕ x))
  have hKne : K.Nonempty := by
    obtain ⟨s, hs, h⟩ := hK
    exact ⟨s, hs, h⟩
  have hKb : BddBelow K := ⟨0, fun s hs => hs.1.1⟩
  have hs₀ : sInf K ∈ K := hKc.csInf_mem hKne hKb
  have hbefore : ∀ r, 0 ≤ r → r < sInf K → ϕ r x ∈ interior N := by
    intro r hr0 hrs
    by_contra hc
    have : r ∈ K := ⟨⟨hr0, by linarith [hs₀.1.2]⟩, hc⟩
    exact absurd (csInf_le hKb this) (not_le.2 hrs)
  have hxN : x ∈ N := pairN₁_subset hT hx
  have hN' : ∀ r ∈ Icc 0 (sInf K), ϕ r x ∈ N := by
    rcases eq_or_lt_of_le hs₀.1.1 with h0 | hpos
    · intro r hr
      have : r = 0 := by linarith [hr.1, hr.2]
      rw [this, ϕ.map_zero_apply]
      exact hxN
    · have hC : IsClosed {r : ℝ | ϕ r x ∈ N} := hN.preimage (continuous_orbit ϕ x)
      have hsub : Ico 0 (sInf K) ⊆ {r : ℝ | ϕ r x ∈ N} :=
        fun r hr => show ϕ r x ∈ N from interior_subset (hbefore r hr.1 hr.2)
      have := closure_minimal hsub hC
      rw [closure_Ico hpos.ne] at this
      exact this
  refine ⟨sInf K, ⟨hs₀.1.1, hs₀.1.2⟩,
    fun r hr => pairN₁_posInv hx hr.1 fun r' hr' => hN' r' ⟨hr'.1, hr'.2.trans hr.2⟩, ?_⟩
  refine ⟨pairN₁_posInv hx hs₀.1.1 hN', 0, ⟨le_rfl, hT⟩, ?_⟩
  rw [ϕ.map_zero_apply]
  exact hs₀.2

/-- The open set `W = {x : ϕ([-T, T], x) ⊆ int N}` lies in `N₁ ∖ N₀` and contains `Inv(N)`. -/
theorem tube_subset (hT : 0 ≤ T) :
    {x | ∀ s ∈ Icc (-T) T, ϕ s x ∈ interior N} ⊆ pairN₁ ϕ N T \ pairN₀ ϕ N T := by
  intro x hx
  refine ⟨fun s hs => interior_subset (hx s ⟨hs.1, by linarith [hs.2]⟩), ?_⟩
  rintro ⟨-, s, hs, hout⟩
  exact hout (hx s ⟨by linarith [hs.1], hs.2⟩)

theorem Inv_subset_tube (hN : Inv ϕ N ⊆ interior N) :
    Inv ϕ N ⊆ {x | ∀ s ∈ Icc (-T) T, ϕ s x ∈ interior N} :=
  fun _ hx s _ => hN (flow_mem_Inv hx s)

end Pair

/-- `(N₁, N₀)` is an index pair of `Inv(N)` once `T` satisfies the time lemma. -/
theorem isIndexPair_pairN [T2Space α] {N : Set α} (hN : IsIsolatingNbhd ϕ N) {T : ℝ}
    (hT : 0 ≤ T) (hTl : ∀ w, (∀ r ∈ Icc (-T) T, ϕ r w ∈ N) → w ∈ interior N) :
    IsIndexPair ϕ (Inv ϕ N) (pairN₁ ϕ N T) (pairN₀ ϕ N T) := by
  have hNc : IsClosed N := hN.1.isClosed
  have h₁c := isClosed_pairN₁ (ϕ := ϕ) (T := T) hNc
  have h₀c := isClosed_pairN₀ (ϕ := ϕ) (T := T) hNc
  have h₁N := pairN₁_subset (ϕ := ϕ) (N := N) hT
  have h₁ : IsCompact (pairN₁ ϕ N T) := hN.1.of_isClosed_subset h₁c h₁N
  have hW := isOpen_forall_Icc ϕ (isOpen_interior (s := N)) (-T) T
  have hInvW := Inv_subset_tube (T := T) hN.2
  have hWsub := tube_subset (ϕ := ϕ) (N := N) hT
  have hint : Inv ϕ N ⊆ interior (pairN₁ ϕ N T \ pairN₀ ϕ N T) :=
    hInvW.trans (interior_maximal hWsub hW)
  have hclsub : closure (pairN₁ ϕ N T \ pairN₀ ϕ N T) ⊆ pairN₁ ϕ N T :=
    closure_minimal sdiff_subset h₁c
  have hinv : Inv ϕ (closure (pairN₁ ϕ N T \ pairN₀ ϕ N T)) = Inv ϕ N := by
    refine (Inv_mono (hclsub.trans h₁N)).antisymm (subset_Inv (isInvariantSet_Inv N) ?_)
    exact (hInvW.trans hWsub).trans subset_closure
  refine ⟨h₁, h₁.of_isClosed_subset h₀c inter_subset_left,
    inter_subset_left, ⟨h₁.of_isClosed_subset isClosed_closure hclsub, ?_⟩, hinv, hint,
    pairN₀_posInv hT hTl, pair_exit hNc hT⟩
  rw [hinv]
  exact hint.trans (interior_mono subset_closure)

/-- Existence of index pairs. -/
theorem exists_indexPair_of_t2 [T2Space α] {N : Set α} (hN : IsIsolatingNbhd ϕ N) :
    ∃ N₁ L, IsIndexPair ϕ (Inv ϕ N) N₁ L ∧ N₁ ⊆ N := by
  obtain ⟨n, hn⟩ := exists_nat_mem_interior hN
  exact ⟨_, _, isIndexPair_pairN hN (Nat.cast_nonneg n) hn,
    pairN₁_subset (Nat.cast_nonneg n)⟩

end ConleyCheck.Conley
