import ConleyCheck.Conley.Collar
import ConleyCheck.Conley.Morse

/-!
# Collared index pairs and triples

Every index pair `(N, L)` can be enlarged to a collared index pair `(N, L')`
(`exists_collared_of_indexPair`), and every attractor–repeller pair has an index triple whose
three pairs are collared (`exists_collared_indexTriple`). Hence the attractor–repeller sequence of
`ConleyCheck.Conley.Collar` holds for every attractor–repeller pair
(`homologyIndex_attractor_repeller_of_pair`).

The construction works on `N/L` with the semiflow `ψ_t` that pushes along the flow and sends
everything that has left through `L` to the base point. Let `A⁺` be the set of points whose forward
orbit stays in `cl(N ∖ L)`, and let `D : N → [0, 1]` be an Urysohn function with `D = 1` on `A⁺`
and `D = 0` on `L`. Then `Ψ(z) = sup_{t ≥ 0} D(ψ_t z) (2 - e^{-t})` is continuous, does not
increase along `ψ`, equals `2` on `A⁺` and strictly decreases at every other point where it is
positive. The set `L' = {Ψ ≤ 1}` is a new exit set, and the time needed to reach it is continuous,
which gives the collar.
-/

namespace ConleyCheck.Conley

open Set Filter Topology unitInterval

open scoped Classical

universe u

/-- `L` has a deformation collar in `N`, namely a neighborhood `V` of `L` in `N` and a homotopy
`G` of `N` starting at the identity, keeping `L` in `L` and `V` in `V`, and ending with `V` in `L`.
Unlike `IsCollared`, this condition does not refer to a flow and is stable under products. -/
def IsDeformCollared {α : Type u} [TopologicalSpace α] (N L : Set α) : Prop :=
  ∃ (V O : Set α) (G : C(I × N, N)), IsOpen O ∧ L ⊆ O ∧ O ∩ N ⊆ V ∧ V ⊆ N ∧
    (∀ x, G (0, x) = x) ∧ (∀ s (x : N), (x : α) ∈ L → (G (s, x) : α) ∈ L) ∧
    (∀ s (x : N), (x : α) ∈ V → (G (s, x) : α) ∈ V) ∧ (∀ x : N, (x : α) ∈ V → (G (1, x) : α) ∈ L)

variable {α : Type u} [TopologicalSpace α] [T2Space α] {ϕ : Flow ℝ α}

/-! ### The semiflow on `N/L` -/

section Semiflow

variable {S N L : Set α} (hP : IsIndexPair ϕ S N L)

/-- The semiflow on `N/L`, extended by the identity to negative times. -/
noncomputable def psi (t : ℝ) (z : IndexSpace N L) : IndexSpace N L :=
  if ht : 0 ≤ t then pushMap hP t ht z else z

theorem psi_pt (t : ℝ) : psi hP t (IndexSpace.pt N L) = IndexSpace.pt N L := by
  unfold psi
  split_ifs <;> rfl

theorem psi_proj {t : ℝ} (ht : 0 ≤ t) (y : N) :
    psi hP t (IndexSpace.proj N L y) =
      if ∀ r ∈ Icc 0 t, ϕ r (y : α) ∈ N then IndexSpace.Q N L (ϕ t (y : α))
      else IndexSpace.pt N L := by
  rw [psi, dif_pos ht, pushMap_proj]

theorem psi_proj_of_seg {t : ℝ} (ht : 0 ≤ t) (y : N) (hy : ∀ r ∈ Icc 0 t, ϕ r (y : α) ∈ N) :
    psi hP t (IndexSpace.proj N L y) = IndexSpace.Q N L (ϕ t (y : α)) := by
  rw [psi_proj hP ht, if_pos hy]

theorem psi_proj_of_not_seg {t : ℝ} (ht : 0 ≤ t) (y : N)
    (hy : ¬ ∀ r ∈ Icc 0 t, ϕ r (y : α) ∈ N) :
    psi hP t (IndexSpace.proj N L y) = IndexSpace.pt N L := by
  rw [psi_proj hP ht, if_neg hy]

theorem continuous_psi (t : ℝ) : Continuous (psi hP t) := by
  by_cases ht : 0 ≤ t
  · have e : psi hP t = pushMap hP t ht := funext fun z => dif_pos ht
    rw [e]
    exact (pushMap hP t ht).continuous
  · have e : psi hP t = id := funext fun z => dif_neg ht
    rw [e]
    exact continuous_id

theorem psi_zero (z : IndexSpace N L) : psi hP 0 z = z := by
  induction z using Quotient.inductionOn with
  | h a =>
    rcases a with y | v
    · change psi hP 0 (IndexSpace.proj N L y) = IndexSpace.proj N L y
      rw [psi_proj_of_seg hP le_rfl y, ϕ.map_zero_apply, IndexSpace.Q_of_mem y.2]
      intro r hr
      rw [show r = 0 from le_antisymm hr.2 hr.1, ϕ.map_zero_apply]
      exact y.2
    · exact psi_pt hP 0

theorem psi_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (z : IndexSpace N L) :
    psi hP s (psi hP t z) = psi hP (s + t) z := by
  induction z using Quotient.inductionOn with
  | h a =>
    rcases a with y | v
    · change psi hP s (psi hP t (IndexSpace.proj N L y)) =
        psi hP (s + t) (IndexSpace.proj N L y)
      by_cases hy : ∀ r ∈ Icc 0 t, ϕ r (y : α) ∈ N
      · have hyt : ϕ t (y : α) ∈ N := hy t ⟨ht, le_rfl⟩
        rw [psi_proj_of_seg hP ht y hy, IndexSpace.Q_of_mem hyt, psi_proj hP hs,
          psi_proj hP (add_nonneg hs ht)]
        have e : ∀ r, ϕ r (ϕ t (y : α)) = ϕ (r + t) (y : α) := fun r => (ϕ.map_add r t _).symm
        simp only [e]
        by_cases h2 : ∀ r ∈ Icc 0 (s + t), ϕ r (y : α) ∈ N
        · rw [if_pos h2, if_pos]
          intro r hr
          exact h2 (r + t) ⟨by linarith [hr.1], by linarith [hr.2]⟩
        · rw [if_neg h2, if_neg]
          intro h3
          apply h2
          intro r hr
          by_cases hrt : r ≤ t
          · exact hy r ⟨hr.1, hrt⟩
          · have := h3 (r - t) ⟨by linarith, by linarith [hr.2]⟩
            rwa [sub_add_cancel] at this
      · rw [psi_proj_of_not_seg hP ht y hy, psi_pt, psi_proj_of_not_seg hP (add_nonneg hs ht) y]
        intro h2
        exact hy fun r hr => h2 r ⟨hr.1, by linarith [hr.2]⟩
    · exact (congrArg (psi hP s) (psi_pt hP t)).trans ((psi_pt hP s).trans (psi_pt hP _).symm)

theorem psi_eq_pushHom {T : ℝ} (hT : 0 ≤ T) (v : I) (z : IndexSpace N L) :
    psi hP ((v : ℝ) * T) z = pushHom hP T hT (v, z) := by
  induction z using Quotient.inductionOn with
  | h a =>
    rcases a with y | w
    · change psi hP ((v : ℝ) * T) (IndexSpace.proj N L y) =
        (if (v, y) ∈ pushA (ϕ := ϕ) (N := N) T then
          IndexSpace.Q N L (ϕ ((v : ℝ) * T) (y : α)) else IndexSpace.pt N L)
      rw [psi_proj hP (mul_nonneg v.2.1 hT)]
      by_cases hy : ∀ r ∈ Icc 0 ((v : ℝ) * T), ϕ r (y : α) ∈ N
      · rw [if_pos hy, if_pos ((mem_pushA_iff hP T hT (v, y)).2 hy)]
      · rw [if_neg hy, if_neg fun h => hy ((mem_pushA_iff hP T hT (v, y)).1 h)]
    · exact psi_pt hP _

theorem psi_eq_pushHom_one {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (z : IndexSpace N L) :
    psi hP u z = pushHom hP 1 zero_le_one (projIcc 0 1 zero_le_one u, z) := by
  rw [projIcc_of_mem _ hu, ← psi_eq_pushHom hP zero_le_one]
  simp

end Semiflow

/-! ### Points that never leave -/

section Forward

variable (ϕ) in
/-- The points whose forward orbit stays in `cl(N ∖ L)`. -/
def fwdSet (N L : Set α) : Set α := {x | ∀ t, 0 ≤ t → ϕ t x ∈ closure (N \ L)}

variable {S N L : Set α} (hP : IsIndexPair ϕ S N L)

theorem isClosed_fwdSet : IsClosed (fwdSet ϕ N L) := by
  have e : fwdSet ϕ N L = ⋂ t ∈ Ici (0 : ℝ), ϕ t ⁻¹' closure (N \ L) := by
    ext x; simp [fwdSet]
  rw [e]
  exact isClosed_biInter fun t _ => isClosed_closure.preimage (ϕ.continuous_toFun t)

include hP

theorem closure_sdiff_subset : closure (N \ L) ⊆ N :=
  closure_minimal sdiff_subset hP.isCompact_N.isClosed

theorem fwdSet_subset : fwdSet ϕ N L ⊆ N := fun x hx => by
  have := hx 0 le_rfl
  rw [ϕ.map_zero_apply] at this
  exact closure_sdiff_subset hP this

theorem fwdSet_flow {x : α} (hx : x ∈ fwdSet ϕ N L) {s : ℝ} (hs : 0 ≤ s) :
    ϕ s x ∈ fwdSet ϕ N L := fun t ht => by
  rw [← ϕ.map_add]
  exact hx _ (add_nonneg ht hs)

theorem subset_fwdSet : S ⊆ fwdSet ϕ N L := fun x hx t _ => by
  rw [← hP.inv_eq] at hx
  exact hx t

/-- A forward orbit in `cl(N ∖ L)` never meets `L`, since its `ω`-limit would lie in `S ∩ L`. -/
theorem fwdSet_not_L {x : α} (hx : x ∈ fwdSet ϕ N L) {t : ℝ} (ht : 0 ≤ t) : ϕ t x ∉ L := by
  intro hL
  set y := ϕ t x
  have hC : ∀ s, 0 ≤ s → ϕ s y ∈ closure (N \ L) := fun s hs => by
    rw [show ϕ s y = ϕ (s + t) x from (ϕ.map_add s t x).symm]
    exact hx _ (add_nonneg hs ht)
  have hyL : ∀ s, 0 ≤ s → ϕ s y ∈ L := fun s hs =>
    hP.posInv y hL s hs fun r hr => closure_sdiff_subset hP (hC r hr.1)
  set K := L ∩ closure (N \ L)
  have hK : IsCompact K := hP.isCompact_L.inter_right isClosed_closure
  have himg : closure (image2 ϕ (Ici 0) {y}) ⊆ K := by
    refine closure_minimal ?_ hK.isClosed
    rintro _ ⟨s, hs, w, rfl, rfl⟩
    exact ⟨hyL s hs, hC s hs⟩
  obtain ⟨z, hz⟩ : (omegaLimit atTop ϕ {y}).Nonempty :=
    nonempty_omegaLimit_of_isCompact_absorbing _ _ _ hK ⟨Ici 0, Ici_mem_atTop 0, himg⟩
      (singleton_nonempty y)
  have hinv := Flow.isInvariant_omegaLimit atTop ϕ {y}
    (fun r => tendsto_atTop_add_const_left _ r tendsto_id)
  have hωK : omegaLimit atTop ϕ {y} ⊆ K := fun w hw =>
    himg (omegaLimit_subset_closure_image2 (f := atTop) (ϕ := ϕ) (s := {y}) (Ici_mem_atTop 0) hw)
  have hzS : z ∈ S := by
    rw [← hP.inv_eq]
    intro r
    exact (hωK (hinv r hz)).2
  exact (interior_subset (hP.nhds hzS)).2 (hωK hz).1

theorem disjoint_fwdSet_L : Disjoint (fwdSet ϕ N L) L :=
  disjoint_left.2 fun x hx hxL => fwdSet_not_L hP hx le_rfl (by rwa [ϕ.map_zero_apply])

/-- A point outside `fwdSet` has a neighborhood whose points reach the base point by a fixed time. -/
theorem exists_time_pt {x : α} (hx : x ∉ fwdSet ϕ N L) :
    ∃ t₀, 0 ≤ t₀ ∧ IsOpen {y | ϕ t₀ y ∉ closure (N \ L)} ∧ ϕ t₀ x ∉ closure (N \ L) ∧
      ∀ y : N, ϕ t₀ (y : α) ∉ closure (N \ L) → ∀ t, t₀ ≤ t →
        psi hP t (IndexSpace.proj N L y) = IndexSpace.pt N L := by
  simp only [fwdSet, mem_setOf_eq, not_forall] at hx
  obtain ⟨t₀, ht₀, hout⟩ := hx
  refine ⟨t₀, ht₀, isClosed_closure.isOpen_compl.preimage (ϕ.continuous_toFun t₀), hout,
    fun y hy t ht => ?_⟩
  by_cases hseg : ∀ r ∈ Icc 0 t, ϕ r (y : α) ∈ N
  · rw [psi_proj_of_seg hP (ht₀.trans ht) y hseg]
    have hL : ϕ t₀ (y : α) ∈ L := by
      by_contra hn
      exact hy (subset_closure ⟨hseg t₀ ⟨ht₀, ht⟩, hn⟩)
    exact IndexSpace.Q_of_mem_L hP.subset
      (posInv_shift hP.posInv ht hL fun r hr => hseg r ⟨ht₀.trans hr.1, hr.2⟩)
  · exact psi_proj_of_not_seg hP (ht₀.trans ht) y hseg

theorem psi_eventually_pt {y : N} (hy : (y : α) ∉ fwdSet ϕ N L) :
    ∃ t₀, 0 ≤ t₀ ∧ ∀ t, t₀ ≤ t → psi hP t (IndexSpace.proj N L y) = IndexSpace.pt N L := by
  obtain ⟨t₀, ht₀, -, hout, H⟩ := exists_time_pt hP hy
  exact ⟨t₀, ht₀, H y hout⟩

theorem psi_psi_eventually_pt {y : N} (hy : (y : α) ∉ fwdSet ϕ N L) {u : ℝ} (hu : 0 ≤ u) :
    ∃ t₀, 0 ≤ t₀ ∧ ∀ t, t₀ ≤ t → psi hP t (psi hP u (IndexSpace.proj N L y)) =
      IndexSpace.pt N L := by
  obtain ⟨t₀, ht₀, H⟩ := psi_eventually_pt hP hy
  exact ⟨t₀, ht₀, fun t ht => by
    rw [psi_add hP (ht₀.trans ht) hu]
    exact H _ (by linarith)⟩

end Forward

/-! ### The Lyapunov function -/

section Lyap

variable {S N L : Set α} (hP : IsIndexPair ϕ S N L) (D : C(N, ℝ))
  (hD0 : ∀ y : N, (y : α) ∈ L → D y = 0)

/-- `D` on `N/L`. -/
noncomputable def DQ : C(IndexSpace N L, ℝ) := descend 0 D hD0

/-- The weight `2 - e^{-t}`. -/
noncomputable def wt (t : ℝ) : ℝ := 2 - Real.exp (-t)

/-- `Ψ(z) = sup_{t ≥ 0} D(ψ_t z) (2 - e^{-t})`. -/
noncomputable def Psi (z : IndexSpace N L) : ℝ :=
  sSup ((fun t => DQ D hD0 (psi hP t z) * wt t) '' Ici 0)

variable (hD1 : ∀ y : N, (y : α) ∈ fwdSet ϕ N L → D y = 1) (hD01 : ∀ y, D y ∈ Icc (0 : ℝ) 1)

theorem exists_exp_lt {δ : ℝ} (hδ : 0 < δ) : ∃ t, 0 ≤ t ∧ Real.exp (-t) < δ := by
  refine ⟨δ⁻¹, (inv_pos.2 hδ).le, ?_⟩
  rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) hδ]
  linarith [Real.add_one_le_exp δ⁻¹]

theorem continuous_wt : Continuous wt :=
  continuous_const.sub (Real.continuous_exp.comp continuous_neg)

include hD01 in
theorem DQ_mem (z : IndexSpace N L) : DQ D hD0 z ∈ Icc (0 : ℝ) 1 := by
  induction z using Quotient.inductionOn with
  | h a =>
    rcases a with y | v
    · exact hD01 y
    · exact ⟨le_rfl, zero_le_one⟩

theorem wt_le_two (t : ℝ) : wt t ≤ 2 := by
  have := Real.exp_pos (-t)
  unfold wt; linarith

theorem one_le_wt {t : ℝ} (ht : 0 ≤ t) : 1 ≤ wt t := by
  have : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  unfold wt; linarith

theorem wt_mono {s t : ℝ} (h : s ≤ t) : wt s ≤ wt t := by
  have : Real.exp (-t) ≤ Real.exp (-s) := Real.exp_le_exp.2 (by linarith)
  unfold wt; linarith

include hD01

theorem term_le_two (z : IndexSpace N L) {t : ℝ} (ht : 0 ≤ t) :
    DQ D hD0 (psi hP t z) * wt t ≤ 2 := by
  have h := DQ_mem D hD0 hD01 (psi hP t z)
  have h1 := one_le_wt ht
  have h2 := wt_le_two t
  nlinarith [h.1, h.2]

theorem term_nonneg (z : IndexSpace N L) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ DQ D hD0 (psi hP t z) * wt t :=
  mul_nonneg (DQ_mem D hD0 hD01 _).1 (zero_le_one.trans (one_le_wt ht))

theorem Psi_bdd (z : IndexSpace N L) :
    BddAbove ((fun t => DQ D hD0 (psi hP t z) * wt t) '' Ici 0) :=
  ⟨2, by rintro _ ⟨t, ht, rfl⟩; exact term_le_two hP D hD0 hD01 z ht⟩

theorem term_le_Psi (z : IndexSpace N L) {t : ℝ} (ht : 0 ≤ t) :
    DQ D hD0 (psi hP t z) * wt t ≤ Psi hP D hD0 z :=
  le_csSup (Psi_bdd hP D hD0 hD01 z) ⟨t, ht, rfl⟩

theorem Psi_le_two (z : IndexSpace N L) : Psi hP D hD0 z ≤ 2 :=
  csSup_le (nonempty_Ici.image _) (by rintro _ ⟨t, ht, rfl⟩; exact term_le_two hP D hD0 hD01 z ht)

theorem Psi_nonneg (z : IndexSpace N L) : 0 ≤ Psi hP D hD0 z :=
  (term_nonneg hP D hD0 hD01 z le_rfl).trans (term_le_Psi hP D hD0 hD01 z le_rfl)

theorem Psi_pt : Psi hP D hD0 (IndexSpace.pt N L) = 0 := by
  refine le_antisymm (csSup_le (nonempty_Ici.image _) ?_) (Psi_nonneg hP D hD0 hD01 _)
  rintro _ ⟨t, -, rfl⟩
  dsimp only
  rw [psi_pt]
  show (0 : ℝ) * wt t ≤ 0
  rw [zero_mul]

theorem Psi_mono (z : IndexSpace N L) {s : ℝ} (hs : 0 ≤ s) :
    Psi hP D hD0 (psi hP s z) ≤ Psi hP D hD0 z := by
  refine csSup_le (nonempty_Ici.image _) ?_
  rintro _ ⟨t, ht, rfl⟩
  dsimp only
  rw [psi_add hP ht hs]
  calc DQ D hD0 (psi hP (t + s) z) * wt t
      ≤ DQ D hD0 (psi hP (t + s) z) * wt (t + s) :=
        mul_le_mul_of_nonneg_left (wt_mono (by linarith)) (DQ_mem D hD0 hD01 _).1
    _ ≤ Psi hP D hD0 z := term_le_Psi hP D hD0 hD01 z (add_nonneg ht hs)

/-- `Ψ` strictly decreases at points that reach the base point and where it is positive. -/
theorem Psi_strict (z : IndexSpace N L) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hz : ∀ t, t₀ ≤ t → psi hP t z = IndexSpace.pt N L) {s : ℝ} (hs : 0 < s)
    (hpos : 0 < Psi hP D hD0 z) : Psi hP D hD0 (psi hP s z) < Psi hP D hD0 z := by
  set δ := Real.exp (-t₀) * (1 - Real.exp (-s)) with hδdef
  have hes : Real.exp (-s) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hδ : 0 < δ := mul_pos (Real.exp_pos _) (by linarith)
  have hδ2 : δ < 2 := by
    have : Real.exp (-t₀) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have := Real.exp_pos (-s)
    calc δ ≤ 1 * (1 - Real.exp (-s)) :=
          mul_le_mul_of_nonneg_right ‹_› (by linarith)
      _ < 2 := by linarith
  set c := 1 - δ / 2 with hcdef
  have hc0 : 0 ≤ c := by linarith
  have hc1 : c < 1 := by linarith
  have hbound : Psi hP D hD0 (psi hP s z) ≤ c * Psi hP D hD0 z := by
    refine csSup_le (nonempty_Ici.image _) ?_
    rintro _ ⟨t, ht, rfl⟩
    dsimp only
    rw [psi_add hP ht hs.le]
    have hΨ := Psi_nonneg hP D hD0 hD01 z
    by_cases htt : t₀ ≤ t + s
    · rw [hz _ htt]
      show (0 : ℝ) * wt t ≤ c * Psi hP D hD0 z
      rw [zero_mul]
      exact mul_nonneg hc0 hΨ
    · push Not at htt
      have hd := DQ_mem D hD0 hD01 (psi hP (t + s) z)
      have hterm := term_le_Psi hP D hD0 hD01 z (add_nonneg ht hs.le)
      have het : Real.exp (-t₀) ≤ Real.exp (-t) := Real.exp_le_exp.2 (by linarith)
      have hw : wt t ≤ c * wt (t + s) := by
        have e : Real.exp (-(t + s)) = Real.exp (-t) * Real.exp (-s) := by
          rw [← Real.exp_add]; ring_nf
        have h2 := wt_le_two (t + s)
        have : wt (t + s) - wt t ≥ δ := by
          unfold wt
          rw [e]
          have : Real.exp (-t₀) * (1 - Real.exp (-s)) ≤ Real.exp (-t) * (1 - Real.exp (-s)) :=
            mul_le_mul_of_nonneg_right het (by linarith)
          linarith
        nlinarith
      calc DQ D hD0 (psi hP (t + s) z) * wt t
          ≤ DQ D hD0 (psi hP (t + s) z) * (c * wt (t + s)) :=
            mul_le_mul_of_nonneg_left hw hd.1
        _ = c * (DQ D hD0 (psi hP (t + s) z) * wt (t + s)) := by ring
        _ ≤ c * Psi hP D hD0 z := mul_le_mul_of_nonneg_left hterm hc0
  calc Psi hP D hD0 (psi hP s z) ≤ c * Psi hP D hD0 z := hbound
    _ < 1 * Psi hP D hD0 z := mul_lt_mul_of_pos_right hc1 hpos
    _ = Psi hP D hD0 z := one_mul _

include hD1

theorem DQ_psi_fwd {y : N} (hy : (y : α) ∈ fwdSet ϕ N L) {t : ℝ} (ht : 0 ≤ t) :
    DQ D hD0 (psi hP t (IndexSpace.proj N L y)) = 1 := by
  have hseg : ∀ r ∈ Icc 0 t, ϕ r (y : α) ∈ N := fun r hr =>
    fwdSet_subset hP (fwdSet_flow hP hy hr.1)
  rw [psi_proj_of_seg hP ht y hseg, IndexSpace.Q_of_mem (hseg t ⟨ht, le_rfl⟩)]
  exact hD1 _ (fwdSet_flow hP hy ht)

theorem Psi_fwd {y : N} (hy : (y : α) ∈ fwdSet ϕ N L) :
    Psi hP D hD0 (IndexSpace.proj N L y) = 2 := by
  refine le_antisymm (Psi_le_two hP D hD0 hD01 _) (le_of_forall_lt fun c hc => ?_)
  obtain ⟨t, ht, hexp⟩ := exists_exp_lt (sub_pos.2 hc)
  have := term_le_Psi hP D hD0 hD01 (IndexSpace.proj N L y) ht
  rw [DQ_psi_fwd hP D hD0 hD1 hD01 hy ht, one_mul] at this
  unfold wt at this
  linarith

/-- `Ψ` is continuous. Away from `fwdSet` it is locally a supremum over a compact time interval. -/
theorem continuous_Psi_proj : Continuous fun y : N => Psi hP D hD0 (IndexSpace.proj N L y) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  by_cases hy₀ : (y₀ : α) ∈ fwdSet ϕ N L
  · rw [ContinuousAt, Psi_fwd hP D hD0 hD1 hD01 hy₀, tendsto_order]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · obtain ⟨t, ht, hexp⟩ := exists_exp_lt (sub_pos.2 ha)
      have hcont : Continuous fun y : N => DQ D hD0 (psi hP t (IndexSpace.proj N L y)) * wt t :=
        ((DQ D hD0).continuous.comp ((continuous_psi hP t).comp
          (IndexSpace.proj N L).continuous)).mul continuous_const
      have hv : a < DQ D hD0 (psi hP t (IndexSpace.proj N L y₀)) * wt t := by
        rw [DQ_psi_fwd hP D hD0 hD1 hD01 hy₀ ht, one_mul]
        unfold wt
        linarith
      filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds hv)] with y hy
      exact hy.trans_le (term_le_Psi hP D hD0 hD01 _ ht)
    · exact Eventually.of_forall fun y => (Psi_le_two hP D hD0 hD01 _).trans_lt ha
  · obtain ⟨t₀, ht₀, hW, hx₀, H⟩ := exists_time_pt hP hy₀
    set F : N → ℝ := fun y => sSup ((fun v : I =>
      DQ D hD0 (pushHom hP t₀ ht₀ (v, IndexSpace.proj N L y)) * wt ((v : ℝ) * t₀)) '' univ)
    have hFc : Continuous F := by
      refine isCompact_univ.continuous_sSup ?_
      exact ((DQ D hD0).continuous.comp ((pushHom hP t₀ ht₀).continuous.comp
        (continuous_snd.prodMk ((IndexSpace.proj N L).continuous.comp continuous_fst)))).mul
        (continuous_wt.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_const))
    have hbddF : ∀ y : N, BddAbove ((fun v : I =>
        DQ D hD0 (pushHom hP t₀ ht₀ (v, IndexSpace.proj N L y)) * wt ((v : ℝ) * t₀)) '' univ) :=
      fun y => ⟨2, by
        rintro _ ⟨v, -, rfl⟩
        dsimp only
        rw [← psi_eq_pushHom hP ht₀]
        exact term_le_two hP D hD0 hD01 _ (mul_nonneg v.2.1 ht₀)⟩
    have heq : ∀ y : N, ϕ t₀ (y : α) ∉ closure (N \ L) →
        Psi hP D hD0 (IndexSpace.proj N L y) = F y := by
      intro y hy
      apply le_antisymm
      · refine csSup_le (nonempty_Ici.image _) ?_
        rintro _ ⟨t, ht, rfl⟩
        dsimp only
        by_cases htt : t₀ ≤ t
        · rw [H y hy t htt]
          show (0 : ℝ) * wt t ≤ F y
          rw [zero_mul]
          refine (term_nonneg hP D hD0 hD01 (IndexSpace.proj N L y) le_rfl).trans ?_
          refine le_csSup (hbddF y) ⟨0, mem_univ _, ?_⟩
          simp only [Icc.coe_zero, zero_mul]
          rw [← psi_eq_pushHom hP ht₀, Icc.coe_zero, zero_mul]
        · push Not at htt
          have hpos : 0 < t₀ := ht.trans_lt htt
          refine le_csSup (hbddF y) ⟨⟨t / t₀, div_nonneg ht hpos.le,
            (div_le_one hpos).2 htt.le⟩, mem_univ _, ?_⟩
          simp only
          rw [← psi_eq_pushHom hP ht₀]
          simp only [div_mul_cancel₀ t hpos.ne']
      · refine csSup_le (univ_nonempty.image _) ?_
        rintro _ ⟨v, -, rfl⟩
        dsimp only
        rw [← psi_eq_pushHom hP ht₀]
        exact term_le_Psi hP D hD0 hD01 _ (mul_nonneg v.2.1 ht₀)
    have hnhds : {y : N | ϕ t₀ (y : α) ∉ closure (N \ L)} ∈ 𝓝 y₀ :=
      (hW.preimage continuous_subtype_val).mem_nhds hx₀
    exact hFc.continuousAt.congr (Filter.mem_of_superset hnhds fun y hy => (heq y hy).symm)

theorem continuous_Psi : Continuous (Psi hP D hD0) := by
  refine (isQuotientMap_quotient_mk' (s := indexSetoid N L)).continuous_iff.2 ?_
  exact continuous_sum_dom.2 ⟨continuous_Psi_proj hP D hD0 hD1 hD01, continuous_of_discreteTopology⟩

end Lyap

/-! ### Continuity of the first crossing time -/

section Crossing

variable {X : Type*} [TopologicalSpace X] (g : X → ℝ → ℝ) (ε : ℝ)

/-- The first time at which `g x` drops to `ε`. -/
noncomputable def hitTime (x : X) : ℝ := sInf {u | 0 ≤ u ∧ g x u ≤ ε}

variable {g ε}

theorem hitTime_bdd (x : X) : BddBelow {u | 0 ≤ u ∧ g x u ≤ ε} := ⟨0, fun _ hu => hu.1⟩

variable (hg : Continuous fun p : X × ℝ => g p.1 p.2)
  (hanti : ∀ x u v, 0 ≤ u → u ≤ v → v ≤ 1 → g x v ≤ g x u)
  (hstrict : ∀ x, g x 1 < ε → ∀ u v, 0 ≤ u → u < v → v ≤ 1 → ε ≤ g x u → g x v < g x u)

theorem hitTime_nonneg {x : X} (hx : g x 1 < ε) : 0 ≤ hitTime g ε x :=
  le_csInf ⟨1, zero_le_one, hx.le⟩ fun _ hu => hu.1

theorem hitTime_le_one {x : X} (hx : g x 1 < ε) : hitTime g ε x ≤ 1 :=
  csInf_le (hitTime_bdd x) ⟨zero_le_one, hx.le⟩

theorem hitTime_zero {x : X} (hx : g x 0 ≤ ε) : hitTime g ε x = 0 :=
  le_antisymm (csInf_le (hitTime_bdd x) ⟨le_rfl, hx⟩) (le_csInf ⟨0, le_rfl, hx⟩ fun _ hu => hu.1)

include hg in
theorem hitTime_mem {x : X} (hx : g x 1 < ε) : g x (hitTime g ε x) ≤ ε := by
  have hcl : IsClosed {u | 0 ≤ u ∧ g x u ≤ ε} :=
    isClosed_Ici.inter (isClosed_le (hg.comp (continuous_const.prodMk continuous_id))
      continuous_const)
  exact (hcl.csInf_mem ⟨1, zero_le_one, hx.le⟩ (hitTime_bdd x)).2

theorem lt_of_lt_hitTime {x : X} {u : ℝ} (hu : 0 ≤ u) (hlt : u < hitTime g ε x) : ε < g x u := by
  by_contra h
  push Not at h
  exact absurd (csInf_le (hitTime_bdd x) ⟨hu, h⟩) (not_le.2 hlt)

include hg hanti hstrict in
theorem lt_of_hitTime_lt {x : X} (hx : g x 1 < ε) {v : ℝ} (hv : hitTime g ε x < v) (hv1 : v ≤ 1) :
    g x v < ε := by
  have h0 := hitTime_nonneg hx
  have hm := hitTime_mem hg hx
  by_cases h : ε ≤ g x (hitTime g ε x)
  · exact (hstrict x hx _ v h0 hv hv1 h).trans_le hm
  · push Not at h
    exact (hanti x _ v h0 hv.le hv1).trans_lt h

include hg hanti hstrict in
theorem continuousOn_hitTime : ContinuousOn (hitTime g ε) {x | g x 1 < ε} := by
  intro x₀ hx₀
  rw [ContinuousWithinAt, tendsto_order]
  have hτ0 := hitTime_nonneg hx₀
  constructor
  · intro a ha
    by_cases ha0 : a < 0
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact ha0.trans_le (hitTime_nonneg hx)
    push Not at ha0
    set b := (a + hitTime g ε x₀) / 2 with hbdef
    have hb0 : 0 ≤ b := by linarith
    have hab : a < b := by linarith
    have hbτ : b < hitTime g ε x₀ := by linarith
    have hcl : IsClosed {x | ∃ u ∈ Icc 0 b, (u, x) ∈ {p : ℝ × X | g p.2 p.1 ≤ ε}} :=
      isClosed_exists_Icc_prod (isClosed_le (hg.comp continuous_swap) continuous_const) 0 b
    have hmem : x₀ ∈ {x | ∃ u ∈ Icc 0 b, (u, x) ∈ {p : ℝ × X | g p.2 p.1 ≤ ε}}ᶜ := by
      rintro ⟨u, hu, hle⟩
      exact absurd hle (not_le.2 (lt_of_lt_hitTime hu.1 (hu.2.trans_lt hbτ)))
    filter_upwards [nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds hmem), self_mem_nhdsWithin]
      with x hx hxV
    refine hab.trans_le (le_csInf ⟨1, zero_le_one, (hxV : g x 1 < ε).le⟩ fun u hu => ?_)
    by_contra hlt
    push Not at hlt
    exact hx ⟨u, ⟨hu.1, hlt.le⟩, hu.2⟩
  · intro a ha
    set u := min ((hitTime g ε x₀ + a) / 2) 1
    have hu0 : 0 ≤ u := le_min (by linarith) zero_le_one
    have hua : u < a := (min_le_left _ _).trans_lt (by linarith)
    have hgu : g x₀ u < ε := by
      by_cases h : (hitTime g ε x₀ + a) / 2 ≤ 1
      · rw [show u = (hitTime g ε x₀ + a) / 2 from min_eq_left h]
        exact lt_of_hitTime_lt hg hanti hstrict hx₀ (by linarith) h
      · push Not at h
        rw [show u = 1 from min_eq_right h.le]
        exact hx₀
    have hopen : IsOpen {x | g x u < ε} :=
      isOpen_lt (hg.comp (continuous_id.prodMk continuous_const)) continuous_const
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hgu)] with x hx
    exact (csInf_le (hitTime_bdd x) ⟨hu0, (hx : g x u < ε).le⟩).trans_lt hua

end Crossing

/-! ### Collared index pairs -/

section Regularize

variable {S N L : Set α} (hP : IsIndexPair ϕ S N L)

include hP in
theorem exists_urysohn_D : ∃ D : C(N, ℝ), (∀ y : N, (y : α) ∈ L → D y = 0) ∧
    (∀ y : N, (y : α) ∈ fwdSet ϕ N L → D y = 1) ∧ ∀ y, D y ∈ Icc (0 : ℝ) 1 := by
  haveI : CompactSpace N := isCompact_iff_compactSpace.1 hP.isCompact_N
  obtain ⟨f, h0, h1, h01⟩ := exists_continuous_zero_one_of_isClosed
    (hP.isCompact_L.isClosed.preimage continuous_subtype_val :
      IsClosed {y : N | (y : α) ∈ L})
    ((isClosed_fwdSet (ϕ := ϕ) (N := N) (L := L)).preimage continuous_subtype_val :
      IsClosed {y : N | (y : α) ∈ fwdSet ϕ N L})
    (disjoint_left.2 fun y hyL hyF => disjoint_left.1 (disjoint_fwdSet_L hP) hyF hyL)
  exact ⟨f, fun y hy => h0 hy, fun y hy => h1 hy, h01⟩

include hP in
/-- Every index pair `(N, L)` can be enlarged to a collared index pair `(N, L')`. The open set `U`
contains the points whose forward orbit stays in `cl(N ∖ L)` and misses `L'`. -/
theorem exists_collared_of_indexPair :
    ∃ L', L ⊆ L' ∧ IsIndexPair ϕ S N L' ∧ IsCollared ϕ N L' ∧ IsDeformCollared N L' ∧
      ∃ U, IsOpen U ∧ fwdSet ϕ N L ⊆ U ∧ Disjoint U L' := by
  obtain ⟨D, hD0, hD1, hD01⟩ := exists_urysohn_D hP
  have hΨc : Continuous (Psi hP D hD0) := continuous_Psi hP D hD0 hD1 hD01
  have hNc := hP.isCompact_N.isClosed
  have hQ : ∀ x (hx : x ∈ N), IndexSpace.Q N L x = IndexSpace.proj N L ⟨x, hx⟩ :=
    fun x hx => IndexSpace.Q_of_mem hx
  let G : N → ℝ → ℝ := fun y u =>
    Psi hP D hD0 (pushHom hP 1 zero_le_one (projIcc 0 1 zero_le_one u, IndexSpace.proj N L y))
  have hGc : Continuous fun p : N × ℝ => G p.1 p.2 :=
    hΨc.comp ((pushHom hP 1 zero_le_one).continuous.comp
      ((continuous_projIcc.comp continuous_snd).prodMk
        ((IndexSpace.proj N L).continuous.comp continuous_fst)))
  have hG : ∀ y u, u ∈ Icc (0 : ℝ) 1 →
      G y u = Psi hP D hD0 (psi hP u (IndexSpace.proj N L y)) := fun y u hu => by
    show Psi hP D hD0 _ = Psi hP D hD0 _
    rw [psi_eq_pushHom_one hP hu]
  have hanti : ∀ y u v, 0 ≤ u → u ≤ v → v ≤ 1 → G y v ≤ G y u := by
    intro y u v hu huv hv
    rw [hG y v ⟨hu.trans huv, hv⟩, hG y u ⟨hu, huv.trans hv⟩,
      show v = (v - u) + u by ring, ← psi_add hP (by linarith) hu]
    exact Psi_mono hP D hD0 hD01 _ (by linarith)
  have hfwdG : ∀ y : N, G y 1 < 1 → (y : α) ∉ fwdSet ϕ N L := by
    intro y hy hf
    rw [hG y 1 ⟨zero_le_one, le_rfl⟩] at hy
    have hseg : ∀ r ∈ Icc (0 : ℝ) 1, ϕ r (y : α) ∈ N := fun r hr =>
      fwdSet_subset hP (fwdSet_flow hP hf hr.1)
    have h1N := hseg 1 ⟨zero_le_one, le_rfl⟩
    rw [psi_proj_of_seg hP zero_le_one y hseg, IndexSpace.Q_of_mem h1N,
      Psi_fwd hP D hD0 hD1 hD01 (y := ⟨_, h1N⟩) (fwdSet_flow hP hf zero_le_one)] at hy
    linarith
  have hstrict : ∀ y, G y 1 < 1 → ∀ u v, 0 ≤ u → u < v → v ≤ 1 → 1 ≤ G y u →
      G y v < G y u := by
    intro y hy u v hu huv hv hle
    obtain ⟨t₀, ht₀, H⟩ := psi_psi_eventually_pt hP (hfwdG y hy) hu
    have hu1 : u ∈ Icc (0 : ℝ) 1 := ⟨hu, by linarith⟩
    rw [hG y u hu1] at hle ⊢
    rw [hG y v ⟨by linarith, hv⟩, show v = (v - u) + u by ring, ← psi_add hP (by linarith) hu]
    exact Psi_strict hP D hD0 hD01 _ ht₀ H (by linarith) (by linarith)
  clear_value G
  -- the new exit set and the collar
  let L' : Set α := {x | x ∈ N ∧ Psi hP D hD0 (IndexSpace.Q N L x) ≤ 1}
  let V : Set α := {x | x ∈ N ∧ Psi hP D hD0 (psi hP 1 (IndexSpace.Q N L x)) < 1}
  have hLL' : L ⊆ L' := fun x hx => ⟨hP.subset hx, by
    rw [IndexSpace.Q_of_mem_L hP.subset hx, Psi_pt hP D hD0 hD01]; norm_num⟩
  have hL'c : IsClosed L' :=
    (hΨc.comp_continuousOn (IndexSpace.continuousOn_Q N L)).preimage_isClosed_of_isClosed hNc
      isClosed_Iic
  obtain ⟨O₂, hO₂, hO₂e⟩ := isOpen_induced_iff.1
    (isOpen_lt continuous_const (continuous_Psi_proj hP D hD0 hD1 hD01) :
      IsOpen {y : N | 1 < Psi hP D hD0 (IndexSpace.proj N L y)})
  have hmemO₂ : ∀ x (hx : x ∈ N), x ∈ O₂ ↔ 1 < Psi hP D hD0 (IndexSpace.proj N L ⟨x, hx⟩) :=
    fun x hx => Set.ext_iff.1 hO₂e ⟨x, hx⟩
  obtain ⟨O, hO, hOe⟩ := isOpen_induced_iff.1
    (isOpen_lt (hGc.comp (continuous_id.prodMk continuous_const)) continuous_const :
      IsOpen {y : N | G y 1 < 1})
  have hmemO : ∀ x (hx : x ∈ N), x ∈ O ↔ G ⟨x, hx⟩ 1 < 1 :=
    fun x hx => Set.ext_iff.1 hOe ⟨x, hx⟩
  have hV1 : ∀ x : V, G ⟨x, x.2.1⟩ 1 < 1 := fun x => by
    rw [hG _ 1 ⟨zero_le_one, le_rfl⟩, ← hQ x x.2.1]
    exact x.2.2
  let τ : V → ℝ := fun x => hitTime G 1 ⟨x, x.2.1⟩
  have hτc : Continuous τ :=
    (continuousOn_hitTime hGc hanti hstrict).comp_continuous
      (continuous_subtype_val.subtype_mk _) hV1
  have hsegV : ∀ x : V, ∀ r ∈ Icc 0 (τ x), ∀ q ∈ Icc 0 r, ϕ q (x : α) ∈ N := by
    intro x r hr q hq
    by_contra hout
    obtain ⟨p, hp, hpseg, hpL⟩ := hP.exit x x.2.1 q hq.1 hout
    by_cases hpτ : p < τ x
    · have h1 := lt_of_lt_hitTime (g := G) (ε := 1) hp.1 hpτ
      have e : psi hP p (IndexSpace.proj N L ⟨x, x.2.1⟩) = IndexSpace.Q N L (ϕ p (x : α)) :=
        psi_proj_of_seg hP hp.1 _ hpseg
      rw [hG _ p ⟨hp.1, hpτ.le.trans (hitTime_le_one (hV1 x))⟩, e,
        IndexSpace.Q_of_mem_L hP.subset hpL, Psi_pt hP D hD0 hD01] at h1
      linarith
    · push Not at hpτ
      have hpq : p = q := le_antisymm hp.2 (hq.2.trans (hr.2.trans hpτ))
      rw [← hpq] at hout
      exact hout (hP.subset hpL)
  have hL'G : ∀ y : N, Psi hP D hD0 (IndexSpace.proj N L y) ≤ 1 → G y 1 < 1 := by
    intro y hx2
    have hnf : (y : α) ∉ fwdSet ϕ N L := fun hf => by
      rw [Psi_fwd hP D hD0 hD1 hD01 hf] at hx2
      norm_num at hx2
    rw [hG _ 1 ⟨zero_le_one, le_rfl⟩]
    obtain ⟨t₀, ht₀, H⟩ := psi_eventually_pt hP hnf
    by_cases hpos : 0 < Psi hP D hD0 (IndexSpace.proj N L y)
    · exact (Psi_strict hP D hD0 hD01 _ ht₀ H one_pos hpos).trans_le hx2
    · push Not at hpos
      exact (Psi_mono hP D hD0 hD01 _ zero_le_one).trans_lt (hpos.trans_lt one_pos)
  have hcoll : IsCollared ϕ N L' := by
    refine ⟨V, O, τ, hO, ?_, ?_, fun x hx => hx.1, hτc,
      fun x => ⟨hitTime_nonneg (hV1 x), hitTime_le_one (hV1 x)⟩, ?_, ?_, ?_⟩
    · intro x hx
      refine (hmemO x hx.1).2 (hL'G _ ?_)
      rw [← hQ x hx.1]
      exact hx.2
    · rintro x ⟨hxO, hxN⟩
      refine ⟨hxN, ?_⟩
      have h1 := (hmemO x hxN).1 hxO
      rwa [hG _ 1 ⟨zero_le_one, le_rfl⟩, ← hQ x hxN] at h1
    · intro x hx
      apply hitTime_zero
      rw [hG _ 0 ⟨le_rfl, zero_le_one⟩, psi_zero, ← hQ x x.2.1]
      exact hx.2
    · intro x s hs
      have hseg := hsegV x s hs
      have hsN : ϕ s (x : α) ∈ N := hseg s ⟨hs.1, le_rfl⟩
      refine ⟨hsN, ?_⟩
      have e : psi hP s (IndexSpace.proj N L ⟨x, x.2.1⟩) = IndexSpace.Q N L (ϕ s (x : α)) :=
        psi_proj_of_seg hP hs.1 _ hseg
      rw [← e, psi_add hP zero_le_one hs.1, add_comm, ← psi_add hP hs.1 zero_le_one]
      refine (Psi_mono hP D hD0 hD01 _ hs.1).trans_lt ?_
      rw [← hQ x x.2.1]
      exact x.2.2
    · intro x
      have h0 := hitTime_nonneg (hV1 x)
      have hseg := hsegV x (τ x) ⟨h0, le_rfl⟩
      have hN' : ϕ (τ x) (x : α) ∈ N := hseg _ ⟨h0, le_rfl⟩
      refine ⟨hN', ?_⟩
      have e : psi hP (τ x) (IndexSpace.proj N L ⟨x, x.2.1⟩) =
          IndexSpace.Q N L (ϕ (τ x) (x : α)) := psi_proj_of_seg hP h0 _ hseg
      rw [← e, ← hG _ _ ⟨h0, hitTime_le_one (hV1 x)⟩]
      exact hitTime_mem hGc (hV1 x)
  -- a deformation collar, tapering the push to `L'` off away from `{Ψ ≤ 1 + δ}`
  let lam : N → ℝ := fun y => Psi hP D hD0 (IndexSpace.proj N L y)
  have hlamc : Continuous lam := continuous_Psi_proj hP D hD0 hD1 hD01
  have hopenG : IsOpen {y : N | G y 1 < 1} :=
    isOpen_lt (hGc.comp (continuous_id.prodMk continuous_const)) continuous_const
  obtain ⟨δ, hδ, hδG⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ y : N, lam y ≤ 1 + 3 * δ → G y 1 < 1 := by
    haveI : CompactSpace N := isCompact_iff_compactSpace.1 hP.isCompact_N
    have hCc : IsCompact {y : N | 1 ≤ G y 1} :=
      (isClosed_le continuous_const (hGc.comp (continuous_id.prodMk continuous_const))).isCompact
    rcases {y : N | 1 ≤ G y 1}.eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun y _ => ?_⟩
      by_contra h
      push Not at h
      exact (Set.eq_empty_iff_forall_notMem.1 he y) h
    · obtain ⟨y₀, hy₀, hmin⟩ := hCc.exists_isMinOn hne hlamc.continuousOn
      have h1 : 1 < lam y₀ := by
        by_contra h
        push Not at h
        exact absurd (hL'G y₀ h) (not_lt.2 hy₀)
      refine ⟨(lam y₀ - 1) / 4, by linarith, fun y hy => ?_⟩
      by_contra h
      push Not at h
      have : lam y₀ ≤ lam y := hmin h
      linarith
  let ρ : N → ℝ := fun y => max 0 (min 1 ((1 + 2 * δ - lam y) / δ))
  have hρc : Continuous ρ :=
    continuous_const.max (continuous_const.min ((continuous_const.sub hlamc).div_const δ))
  have hρ01 : ∀ y, 0 ≤ ρ y ∧ ρ y ≤ 1 := fun y =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hρ1 : ∀ y, lam y ≤ 1 + δ → ρ y = 1 := by
    intro y hy
    have : 1 ≤ (1 + 2 * δ - lam y) / δ := by rw [le_div_iff₀ hδ]; linarith
    show max 0 (min 1 _) = 1
    rw [min_eq_left this, max_eq_right zero_le_one]
  have hρ0 : ∀ y, 1 + 2 * δ ≤ lam y → ρ y = 0 := by
    intro y hy
    have : (1 + 2 * δ - lam y) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
    exact max_eq_left ((min_le_right _ _).trans this)
  let T : N → ℝ := fun y => ρ y * hitTime G 1 y
  have hT0 : ∀ y, ¬ G y 1 < 1 → T y = 0 := by
    intro y hy
    have : 1 + 2 * δ ≤ lam y := by
      by_contra h
      push Not at h
      exact hy (hδG y (by linarith))
    show ρ y * _ = 0
    rw [hρ0 y this, zero_mul]
  have hTnn : ∀ y, 0 ≤ T y := by
    intro y
    by_cases hy : G y 1 < 1
    · exact mul_nonneg (hρ01 y).1 (hitTime_nonneg hy)
    · exact (hT0 y hy).ge
  have hTc : Continuous T := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : G y 1 < 1
    · exact hρc.continuousAt.mul ((continuousOn_hitTime hGc hanti hstrict).continuousAt
        (hopenG.mem_nhds hy))
    · have hy' : 1 + 2 * δ < lam y := by
        by_contra h
        push Not at h
        exact hy (hδG y (by linarith))
      have hev : ∀ᶠ z in 𝓝 y, (0 : ℝ) = T z := by
        filter_upwards [(isOpen_lt continuous_const hlamc).mem_nhds hy'] with z hz
        show 0 = ρ z * _
        rw [hρ0 z (le_of_lt hz), zero_mul]
      exact continuousAt_const.congr hev
  have hTseg : ∀ (y : N) (r : ℝ), 0 ≤ r → r ≤ T y → ∀ q ∈ Icc 0 r, ϕ q (y : α) ∈ N := by
    intro y r hr hrT q hq
    by_cases hy : G y 1 < 1
    · have hyV : (y : α) ∈ V := ⟨y.2, by
        rw [hQ _ y.2]
        rwa [hG _ 1 ⟨zero_le_one, le_rfl⟩] at hy⟩
      exact hsegV ⟨y, hyV⟩ r ⟨hr, hrT.trans (mul_le_of_le_one_left (hitTime_nonneg hy)
        (hρ01 y).2)⟩ q hq
    · have hq0 : q = 0 := le_antisymm (hq.2.trans (hrT.trans (hT0 y hy).le)) hq.1
      rw [hq0, ϕ.map_zero_apply]
      exact y.2
  have hTN : ∀ (y : N) (s : I), ϕ ((s : ℝ) * T y) (y : α) ∈ N := fun y s =>
    hTseg y _ (mul_nonneg s.2.1 (hTnn y)) (mul_le_of_le_one_left (hTnn y) s.2.2) _
      ⟨mul_nonneg s.2.1 (hTnn y), le_rfl⟩
  let Gd : C(I × N, N) := ⟨fun p => ⟨ϕ ((p.1 : ℝ) * T p.2) p.2, hTN p.2 p.1⟩, by
    refine Continuous.subtype_mk ?_ _
    exact ϕ.continuous ((continuous_subtype_val.comp continuous_fst).mul (hTc.comp continuous_snd))
      (continuous_subtype_val.comp continuous_snd)⟩
  have hlam_mono : ∀ (y : N) (s : I), lam ⟨_, hTN y s⟩ ≤ lam y := by
    intro y s
    have h0 := mul_nonneg s.2.1 (hTnn y)
    have e : psi hP ((s : ℝ) * T y) (IndexSpace.proj N L y) =
        IndexSpace.Q N L (ϕ ((s : ℝ) * T y) (y : α)) :=
      psi_proj_of_seg hP h0 _ (hTseg y _ h0 (mul_le_of_le_one_left (hTnn y) s.2.2))
    show Psi hP D hD0 (IndexSpace.proj N L _) ≤ _
    rw [← hQ _ (hTN y s), ← e]
    exact Psi_mono hP D hD0 hD01 _ h0
  obtain ⟨Od, hOd, hOde⟩ := isOpen_induced_iff.1
    (isOpen_lt hlamc continuous_const : IsOpen {y : N | lam y < 1 + δ})
  have hmemOd : ∀ x (hx : x ∈ N), x ∈ Od ↔ lam ⟨x, hx⟩ < 1 + δ :=
    fun x hx => Set.ext_iff.1 hOde ⟨x, hx⟩
  have hdef : IsDeformCollared N L' := by
    refine ⟨{x | ∃ hx : x ∈ N, lam ⟨x, hx⟩ ≤ 1 + δ}, Od, Gd, hOd, ?_,
      fun x hx => ⟨hx.2, ((hmemOd x hx.2).1 hx.1).le⟩, fun x hx => hx.1, ?_, ?_, ?_, ?_⟩
    · intro x hx
      refine (hmemOd x hx.1).2 ?_
      have hx2 := hx.2
      rw [hQ x hx.1] at hx2
      show Psi hP D hD0 _ < _
      linarith
    · intro x
      apply Subtype.ext
      show ϕ (((0 : I) : ℝ) * T x) x = x
      rw [Icc.coe_zero, zero_mul, ϕ.map_zero_apply]
    · intro s x hx
      have hx2 := hx.2
      rw [hQ _ x.2] at hx2
      have hτ : hitTime G 1 x = 0 :=
        hitTime_zero (by rw [hG x 0 ⟨le_rfl, zero_le_one⟩, psi_zero]; exact hx2)
      show ϕ ((s : ℝ) * (ρ x * hitTime G 1 x)) (x : α) ∈ L'
      rw [hτ, mul_zero, mul_zero, ϕ.map_zero_apply]
      exact hx
    · rintro s x ⟨hx, hlx⟩
      exact ⟨hTN x s, (hlam_mono x s).trans hlx⟩
    · rintro x ⟨hx, hlx⟩
      have hlx' : lam x ≤ 1 + δ := hlx
      have hG1 : G x 1 < 1 := hδG x (by linarith)
      have hτ0 := hitTime_nonneg hG1
      have hTx : T x = hitTime G 1 x := by
        show ρ x * _ = _
        rw [hρ1 x hlx', one_mul]
      have hseg := hTseg x (hitTime G 1 x) hτ0 hTx.ge
      have hN' : ϕ (hitTime G 1 x) (x : α) ∈ N := hseg _ ⟨hτ0, le_rfl⟩
      have e : psi hP (hitTime G 1 x) (IndexSpace.proj N L x) =
          IndexSpace.Q N L (ϕ (hitTime G 1 x) (x : α)) := psi_proj_of_seg hP hτ0 _ hseg
      show ϕ (((1 : I) : ℝ) * T x) (x : α) ∈ L'
      rw [Icc.coe_one, one_mul, hTx]
      refine ⟨hN', ?_⟩
      rw [← e, ← hG _ _ ⟨hτ0, hitTime_le_one hG1⟩]
      exact hitTime_mem hGc hG1
  -- the index pair
  have hSfwd := subset_fwdSet hP
  have hSL' : ∀ x ∈ S, x ∈ N ∧ x ∉ L' := fun x hx => by
    have hxN := fwdSet_subset hP (hSfwd hx)
    refine ⟨hxN, fun h => ?_⟩
    have h2 := h.2
    rw [hQ x hxN, Psi_fwd hP D hD0 hD1 hD01 (y := ⟨x, hxN⟩) (hSfwd hx)] at h2
    norm_num at h2
  have hO₂L' : Disjoint O₂ L' := disjoint_left.2 fun x hxO hxL => by
    have h1 := (hmemO₂ x hxL.1).1 hxO
    have h2 := hxL.2
    rw [hQ x hxL.1] at h2
    linarith
  have hfO₂ : fwdSet ϕ N L ⊆ O₂ := fun x hx => by
    refine (hmemO₂ x (fwdSet_subset hP hx)).2 ?_
    rw [Psi_fwd hP D hD0 hD1 hD01 (y := ⟨x, fwdSet_subset hP hx⟩) hx]
    norm_num
  have hinv : Inv ϕ (closure (N \ L')) = S := by
    refine Subset.antisymm ((Inv_mono (closure_mono (sdiff_subset_sdiff_right hLL'))).trans
      hP.inv_eq.subset) ?_
    exact subset_Inv hP.isIsolatedInvariantSet.isInvariantSet fun x hx =>
      subset_closure ⟨(hSL' x hx).1, (hSL' x hx).2⟩
  have hnhds : S ⊆ interior (N \ L') := by
    intro x hx
    refine interior_maximal (t := interior (N \ L) ∩ O₂) ?_ (isOpen_interior.inter hO₂)
      ⟨hP.nhds hx, hfO₂ (hSfwd hx)⟩
    rintro y ⟨hy1, hy2⟩
    exact ⟨(interior_subset hy1).1, fun hyL => disjoint_left.1 hO₂L' hy2 hyL⟩
  have hpair : IsIndexPair ϕ S N L' :=
    { isCompact_N := hP.isCompact_N
      isCompact_L := hP.isCompact_N.of_isClosed_subset hL'c fun x hx => hx.1
      subset := fun x hx => hx.1
      isolating := ⟨hP.isCompact_N.of_isClosed_subset isClosed_closure
          (closure_minimal sdiff_subset hNc), by
        rw [hinv]; exact hnhds.trans (interior_mono subset_closure)⟩
      inv_eq := hinv
      nhds := hnhds
      posInv := fun x hx t ht hseg => by
        refine ⟨hseg t ⟨ht, le_rfl⟩, ?_⟩
        have e : psi hP t (IndexSpace.proj N L ⟨x, hx.1⟩) = IndexSpace.Q N L (ϕ t x) :=
          psi_proj_of_seg hP ht _ hseg
        rw [← e]
        refine (Psi_mono hP D hD0 hD01 _ ht).trans ?_
        rw [← hQ x hx.1]
        exact hx.2
      exit := fun x hx t ht hout => by
        obtain ⟨s, hs, hseg, hL⟩ := hP.exit x hx t ht hout
        exact ⟨s, hs, hseg, hLL' hL⟩ }
  exact ⟨L', hLL', hpair, hcoll, hdef, O₂, hO₂, hfO₂, hO₂L'⟩

end Regularize

/-- Every isolated invariant set has a collared index pair. -/
theorem exists_collared_indexPair {S : Set α} (hS : IsIsolatedInvariantSet ϕ S) :
    ∃ N L, IsIndexPair ϕ S N L ∧ IsCollared ϕ N L := by
  obtain ⟨N₀, hN₀, rfl⟩ := hS
  obtain ⟨N, L, hP, -⟩ := exists_indexPair_of_t2 hN₀
  obtain ⟨L', -, hP', hc, -⟩ := exists_collared_of_indexPair hP
  exact ⟨N, L', hP', hc⟩

/-- Every isolated invariant set has an index pair with a deformation collar. -/
theorem exists_deformCollared_indexPair {S : Set α} (hS : IsIsolatedInvariantSet ϕ S) :
    ∃ N L, IsIndexPair ϕ S N L ∧ IsDeformCollared N L := by
  obtain ⟨N₀, hN₀, rfl⟩ := hS
  obtain ⟨N, L, hP, -⟩ := exists_indexPair_of_t2 hN₀
  obtain ⟨L', -, hP', -, hd, -⟩ := exists_collared_of_indexPair hP
  exact ⟨N, L', hP', hd⟩

/-! ### Collared index triples -/

section Triple

omit [T2Space α] in
theorem IsCollared.restrict {N M L : Set α} (hc : IsCollared ϕ N L) (hMN : M ⊆ N)
    (hpos : IsPosInvRel ϕ M N) : IsCollared ϕ M L := by
  obtain ⟨V, O, τ, hO, hLO, hON, hVN, hτc, hτ01, hτL, hseg, hhit⟩ := hc
  refine ⟨V ∩ M, O, fun x => τ ⟨x, x.2.1⟩, hO, hLO, fun x hx => ⟨hON ⟨hx.1, hMN hx.2⟩, hx.2⟩,
    fun x hx => hx.2, hτc.comp (continuous_inclusion inter_subset_left), fun x => hτ01 _,
    fun x hx => hτL _ hx, fun x s hs => ⟨hseg _ s hs, ?_⟩, fun x => hhit _⟩
  exact hpos x x.2.2 s hs.1 fun r hr => hVN (hseg ⟨x, x.2.1⟩ r ⟨hr.1, hr.2.trans hs.2⟩)

/-- A compact `M` between `L` and `N`, positively invariant relative to `N`, gives an index pair
`(M, L)` as soon as `cl(M ∖ L)` isolates the right set. -/
theorem indexPair_of_posInv {S A N M L : Set α} (hP : IsIndexPair ϕ S N L) (hM : IsCompact M)
    (hLM : L ⊆ M) (hMN : M ⊆ N) (hpos : IsPosInvRel ϕ M N)
    (hinv : Inv ϕ (closure (M \ L)) = A) (hnhds : A ⊆ interior (M \ L)) :
    IsIndexPair ϕ A M L where
  isCompact_N := hM
  isCompact_L := hP.isCompact_L
  subset := hLM
  isolating := ⟨hM.of_isClosed_subset isClosed_closure (closure_minimal sdiff_subset hM.isClosed),
    by rw [hinv]; exact hnhds.trans (interior_mono subset_closure)⟩
  inv_eq := hinv
  nhds := hnhds
  posInv := fun x hx t ht hseg => hP.posInv x hx t ht fun r hr => hMN (hseg r hr)
  exit := by
    intro x hx t ht hout
    have : ∃ r ∈ Icc 0 t, ϕ r x ∉ N := by
      by_contra hc
      push Not at hc
      exact hout (hpos x hx t ht hc)
    obtain ⟨r, hr, hrN⟩ := this
    obtain ⟨s, hs, hseg, hL⟩ := hP.exit x (hMN hx) r hr.1 hrN
    exact ⟨s, ⟨hs.1, hs.2.trans hr.2⟩,
      fun q hq => hpos x hx q hq.1 fun q' hq' => hseg q' ⟨hq'.1, hq'.2.trans hq.2⟩, hL⟩

/-- Every attractor–repeller pair has an index triple whose three pairs are collared. -/
theorem exists_collared_indexTriple {S A R : Set α} (h : IsAttractorRepellerPair ϕ S A R) :
    ∃ N₀ N₁ N₂, IsIndexTriple ϕ S A R N₀ N₁ N₂ ∧ IsCollared ϕ N₁ N₀ ∧ IsCollared ϕ N₂ N₀ ∧
      IsCollared ϕ N₂ N₁ := by
  obtain ⟨N₀, N₁, N₂, hT⟩ := exists_indexTriple h
  obtain ⟨N₀', h0sub, hP0, hc0, -, U₀, hU₀, hfU₀, hdU₀⟩ := exists_collared_of_indexPair hT.pair_S
  have hSU₀ : S ⊆ U₀ := (subset_fwdSet hT.pair_S).trans hfU₀
  have hAU₀ : A ⊆ U₀ := h.subset_A.trans hSU₀
  have hRU₀ : R ⊆ U₀ := h.subset_R.trans hSU₀
  have hMc : IsCompact (N₁ ∪ N₀') := hT.pair_A.isCompact_N.union hP0.isCompact_L
  have hMN : N₁ ∪ N₀' ⊆ N₂ := union_subset hT.sub₁₂ hP0.subset
  have hMpos : IsPosInvRel ϕ (N₁ ∪ N₀') N₂ := by
    rintro x (hx | hx) t ht hseg
    · exact Or.inl (hT.pair_R.posInv x hx t ht hseg)
    · exact Or.inr (hP0.posInv x hx t ht hseg)
  have hPR : IsIndexPair ϕ R N₂ (N₁ ∪ N₀') := by
    have hRM : ∀ x ∈ R, x ∈ N₂ \ (N₁ ∪ N₀') := fun x hx => by
      have h1 := interior_subset (hT.pair_R.nhds hx)
      exact ⟨h1.1, fun hm => hm.elim h1.2 fun h0 => disjoint_left.1 hdU₀ (hRU₀ hx) h0⟩
    have hnhds : R ⊆ interior (N₂ \ (N₁ ∪ N₀')) := by
      intro x hx
      refine interior_maximal (t := interior (N₂ \ N₁) ∩ U₀) ?_ (isOpen_interior.inter hU₀)
        ⟨hT.pair_R.nhds hx, hRU₀ hx⟩
      rintro y ⟨hy1, hy2⟩
      have hy := interior_subset hy1
      exact ⟨hy.1, fun hm => hm.elim hy.2 fun h0 => disjoint_left.1 hdU₀ hy2 h0⟩
    have hinv : Inv ϕ (closure (N₂ \ (N₁ ∪ N₀'))) = R :=
      Subset.antisymm ((Inv_mono (closure_mono (sdiff_subset_sdiff_right subset_union_left))).trans
        hT.pair_R.inv_eq.subset)
        (subset_Inv h.isolated_R.isInvariantSet fun x hx => subset_closure (hRM x hx))
    exact
      { isCompact_N := hT.pair_S.isCompact_N
        isCompact_L := hMc
        subset := hMN
        isolating := ⟨hT.pair_S.isCompact_N.of_isClosed_subset isClosed_closure
            (closure_minimal sdiff_subset hT.pair_S.isCompact_N.isClosed), by
          rw [hinv]; exact hnhds.trans (interior_mono subset_closure)⟩
        inv_eq := hinv
        nhds := hnhds
        posInv := hMpos
        exit := fun x hx t ht hout => by
          obtain ⟨s, hs, hseg, hL⟩ := hT.pair_R.exit x hx t ht hout
          exact ⟨s, hs, hseg, Or.inl hL⟩ }
  obtain ⟨N₁', h1sub, hP1, hc1, -, U₁, -, hfU₁, hdU₁⟩ := exists_collared_of_indexPair hPR
  have hRU₁ : R ⊆ U₁ := (subset_fwdSet hPR).trans hfU₁
  have h01 : N₀' ⊆ N₁' := subset_union_right.trans h1sub
  have hPA : IsIndexPair ϕ A N₁' N₀' := by
    refine indexPair_of_posInv hP0 hP1.isCompact_L h01 hP1.subset hP1.posInv ?_ ?_
    · apply Subset.antisymm
      · intro x hx
        have hxS : x ∈ S := by
          rw [← hT.pair_S.inv_eq]
          exact Inv_mono (closure_mono (sdiff_subset_sdiff hP1.subset h0sub)) hx
        by_contra hxA
        refine h.false_of_backward isClosed_closure ?_ hxS hxA fun t _ => hx t
        refine disjoint_left.2 fun y hy hyR => ?_
        have hy1 : y ∈ N₁' := closure_minimal sdiff_subset hP1.isCompact_L.isClosed hy
        exact disjoint_left.1 hdU₁ (hRU₁ hyR) hy1
      · refine subset_Inv h.isolated_A.isInvariantSet fun x hx => subset_closure ⟨?_, ?_⟩
        · exact h1sub (Or.inl (interior_subset (hT.pair_A.nhds hx)).1)
        · exact disjoint_left.1 hdU₀ (hAU₀ hx)
    · intro x hx
      refine interior_maximal (t := interior (N₁ \ N₀) ∩ U₀) ?_ (isOpen_interior.inter hU₀)
        ⟨hT.pair_A.nhds hx, hAU₀ hx⟩
      rintro y ⟨hy1, hy2⟩
      exact ⟨h1sub (Or.inl (interior_subset hy1).1), disjoint_left.1 hdU₀ hy2⟩
  exact ⟨N₀', N₁', N₂, ⟨h01, hP1.subset, hP0, hPA, hP1⟩, hc0.restrict hP1.subset hP1.posInv,
    hc0, hc1⟩

end Triple

/-! ### The attractor–repeller sequence for `CH_*` -/

section Homology

variable (K : Type u) [Ring K]

/-- The attractor–repeller sequence
`⋯ → CH_n(A) → CH_n(S) → CH_n(R) → CH_{n-1}(A) → ⋯ → CH_0(R) → 0` (`eq:AR`). -/
theorem homologyIndex_attractor_repeller_of_pair {S A R : Set α}
    (h : IsAttractorRepellerPair ϕ S A R) :
    ∃ (i : ∀ n, homologyIndex K ϕ h.isolated_A n →ₗ[K] homologyIndex K ϕ h.isolated n)
      (p : ∀ n, homologyIndex K ϕ h.isolated n →ₗ[K] homologyIndex K ϕ h.isolated_R n)
      (d : ∀ n, homologyIndex K ϕ h.isolated_R (n + 1) →ₗ[K] homologyIndex K ϕ h.isolated_A n),
      (∀ n, Function.Exact (i n) (p n)) ∧ (∀ n, Function.Exact (p (n + 1)) (d n)) ∧
        (∀ n, Function.Exact (d n) (i n)) ∧ Function.Surjective (p 0) := by
  obtain ⟨N₀, N₁, N₂, hT, c₁, c₂, c₃⟩ := exists_collared_indexTriple h
  exact homologyIndex_attractor_repeller K hT h.isolated h.isolated_A h.isolated_R c₁ c₂ c₃

/-- If the repeller has trivial homology index, then `CH_*(A) ≅ CH_*(S)`. -/
theorem homologyIndex_attractor_iso_of_pair {S A R : Set α} (h : IsAttractorRepellerPair ϕ S A R)
    (hRt : ∀ n, Subsingleton (homologyIndex K ϕ h.isolated_R n)) :
    ∃ i : ∀ n, homologyIndex K ϕ h.isolated_A n →ₗ[K] homologyIndex K ϕ h.isolated n,
      ∀ n, Function.Bijective (i n) := by
  obtain ⟨N₀, N₁, N₂, hT, c₁, c₂, c₃⟩ := exists_collared_indexTriple h
  exact homologyIndex_attractor_iso K hT h.isolated h.isolated_A h.isolated_R c₁ c₂ c₃ hRt

/-- If the attractor has trivial homology index, then `CH_*(S) ≅ CH_*(R)`. -/
theorem homologyIndex_repeller_iso_of_pair {S A R : Set α} (h : IsAttractorRepellerPair ϕ S A R)
    (hAt : ∀ n, Subsingleton (homologyIndex K ϕ h.isolated_A n)) :
    ∃ p : ∀ n, homologyIndex K ϕ h.isolated n →ₗ[K] homologyIndex K ϕ h.isolated_R n,
      ∀ n, Function.Bijective (p n) := by
  obtain ⟨N₀, N₁, N₂, hT, c₁, c₂, c₃⟩ := exists_collared_indexTriple h
  exact homologyIndex_repeller_iso K hT h.isolated h.isolated_A h.isolated_R c₁ c₂ c₃ hAt

/-- `CH_*(S) ≅ H_*(N, L)` for some index pair of `S`. -/
theorem exists_indexPair_homologyIndexEquiv {S : Set α} (hS : IsIsolatedInvariantSet ϕ S) :
    ∃ N L, IsIndexPair ϕ S N L ∧
      ∀ n, Nonempty (homologyIndex K ϕ hS n ≃ₗ[K] singH K α (Int.ofNat n) N L) := by
  obtain ⟨N, L, hP, hc⟩ := exists_collared_indexPair hS
  exact ⟨N, L, hP, fun n => ⟨homologyIndexEquiv K hS hP hc n⟩⟩

end Homology

end ConleyCheck.Conley
