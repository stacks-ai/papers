import ConleyCheck.Conley.Existence
import ConleyCheck.Conley.Pointed

/-!
# Independence of the index pair

For index pairs `P = (N, L)` and `P' = (N', L')` of the same isolated invariant set and `T`
large, the map `f : N/L → N'/L'`,
`f[x] = [ϕ(3T, x)]` if `ϕ([0, 2T], x) ⊆ N ∖ L` and `ϕ([T, 3T], x) ⊆ N' ∖ L'`, and `f[x] = [L']`
otherwise, is continuous (Salamon 1985, Sec. 4). The composite of `f` with the map in the other
direction equals the push map `[x] ↦ [ϕ(6T, x)]` of `P`, and pushing for time `s · 6T`,
`s ∈ [0, 1]`, is a homotopy from the identity to it relative to the base point.
-/

namespace ConleyCheck.Conley

open Set Filter Topology unitInterval

open scoped Classical

variable {α : Type*} [TopologicalSpace α] {ϕ : Flow ℝ α}

/-! ### Closedness along compact time intervals -/

theorem isClosed_exists_Icc' {X : Type*} [TopologicalSpace X] {h : ℝ → X → α}
    (hh : Continuous fun p : ℝ × X => h p.1 p.2) {C : Set α} (hC : IsClosed C) (a b : ℝ) :
    IsClosed {x | ∃ u ∈ Icc a b, h u x ∈ C} := by
  have hmap : IsClosedMap (Prod.snd : Icc a b × X → X) := isClosedMap_snd_of_compactSpace
  have hcl : IsClosed {p : Icc a b × X | h p.1 p.2 ∈ C} :=
    hC.preimage (hh.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
  have e : {x | ∃ u ∈ Icc a b, h u x ∈ C} = Prod.snd '' {p : Icc a b × X | h p.1 p.2 ∈ C} := by
    ext x
    constructor
    · rintro ⟨s, hs, hx⟩; exact ⟨(⟨s, hs⟩, x), hx, rfl⟩
    · rintro ⟨⟨s, y⟩, hy, rfl⟩; exact ⟨s, s.2, hy⟩
  rw [e]
  exact hmap _ hcl

theorem isClosed_forall_Icc' {X : Type*} [TopologicalSpace X] {h : ℝ → X → α}
    (hh : Continuous fun p : ℝ × X => h p.1 p.2) {C : Set α} (hC : IsClosed C) (a b : ℝ) :
    IsClosed {x | ∀ u ∈ Icc a b, h u x ∈ C} := by
  have e : {x | ∀ u ∈ Icc a b, h u x ∈ C} = ⋂ u ∈ Icc a b, {x | h u x ∈ C} := by
    ext x; simp
  rw [e]
  exact isClosed_biInter fun u _ => hC.preimage (hh.comp (continuous_const.prodMk continuous_id))

theorem forall_Icc_mul_iff {c : ℝ} (hc : 0 ≤ c) {P : ℝ → Prop} :
    (∀ u ∈ Icc (0 : ℝ) 1, P (u * c)) ↔ ∀ r ∈ Icc 0 c, P r := by
  constructor
  · intro h r hr
    rcases eq_or_lt_of_le hc with h0 | hpos
    · have hr0 : r = 0 := by linarith [hr.1, hr.2]
      have := h 0 ⟨le_rfl, zero_le_one⟩
      rwa [zero_mul, ← hr0] at this
    · have := h (r / c) ⟨div_nonneg hr.1 hc, div_le_one_of_le₀ hr.2 hc⟩
      rwa [div_mul_cancel₀ r hpos.ne'] at this
  · intro h u hu
    exact h _ ⟨mul_nonneg hu.1 hc, mul_le_of_le_one_left hc hu.2⟩

theorem exists_Icc_mul_iff {c : ℝ} (hc : 0 ≤ c) {P : ℝ → Prop} :
    (∃ u ∈ Icc (0 : ℝ) 1, P (u * c)) ↔ ∃ r ∈ Icc 0 c, P r := by
  have := forall_Icc_mul_iff hc (P := fun r => ¬ P r)
  constructor
  · intro h
    by_contra h'
    push Not at h'
    obtain ⟨u, hu, hP⟩ := h
    exact this.2 h' u hu hP
  · intro h
    by_contra h'
    push Not at h'
    obtain ⟨r, hr, hP⟩ := h
    exact this.1 h' r hr hP

/-! ### Time lemma for an arbitrary neighborhood -/

theorem exists_nat_mem_of_Inv_subset [T2Space α] {K U : Set α} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : Inv ϕ K ⊆ U) : ∃ n : ℕ, ∀ x, (∀ s ∈ Icc (-(n : ℝ)) n, ϕ s x ∈ K) → x ∈ U := by
  by_contra h
  push Not at h
  let Kn : ℕ → Set α := fun n => Uᶜ ∩ {x | ∀ s ∈ Icc (-(n : ℝ)) n, ϕ s x ∈ K}
  have hcl : ∀ n, IsClosed (Kn n) := fun n =>
    hU.isClosed_compl.inter (isClosed_forall_Icc ϕ hK.isClosed _ _)
  have hdec : ∀ n, Kn (n + 1) ⊆ Kn n := by
    intro n x hx
    refine ⟨hx.1, fun s hs => hx.2 s ⟨?_, ?_⟩⟩ <;> push_cast <;> linarith [hs.1, hs.2]
  have hne : ∀ n, (Kn n).Nonempty := by
    intro n
    obtain ⟨x, hx, hxU⟩ := h n
    exact ⟨x, hxU, hx⟩
  have hK0 : IsCompact (Kn 0) := by
    refine hK.of_isClosed_subset (hcl 0) fun x hx => ?_
    have := hx.2 0 ⟨by simp, by simp⟩
    rwa [ϕ.map_zero_apply] at this
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed Kn hdec hne
    hK0 hcl
  rw [mem_iInter] at hx
  have hinv : x ∈ Inv ϕ K := by
    intro t
    obtain ⟨n, hn⟩ := exists_nat_ge |t|
    exact (hx n).2 t ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  exact (hx 0).1 (hKU hinv)

/-! ### Maps into `N/L` -/

/-- `z ↦ [z]` on `N`, extended by the base point. -/
noncomputable def IndexSpace.Q (N L : Set α) (z : α) : IndexSpace N L :=
  if h : z ∈ N then IndexSpace.proj N L ⟨z, h⟩ else IndexSpace.pt N L

theorem IndexSpace.Q_of_mem {N L : Set α} {z : α} (h : z ∈ N) :
    IndexSpace.Q N L z = IndexSpace.proj N L ⟨z, h⟩ := dif_pos h

theorem IndexSpace.Q_of_mem_L {N L : Set α} (hLN : L ⊆ N) {z : α} (h : z ∈ L) :
    IndexSpace.Q N L z = IndexSpace.pt N L := by
  rw [IndexSpace.Q_of_mem (hLN h)]
  exact IndexSpace.proj_eq_pt h

theorem IndexSpace.continuousOn_Q (N L : Set α) : ContinuousOn (IndexSpace.Q N L) N := by
  rw [continuousOn_iff_continuous_restrict]
  convert (IndexSpace.proj N L).continuous using 1
  funext z
  exact IndexSpace.Q_of_mem z.2

/-- Continuity criterion for `x ↦ [g x]` on `A` and `x ↦ [L]` off `A`. -/
theorem continuous_ite_Q {X : Type*} [TopologicalSpace X] {N L : Set α} (hLN : L ⊆ N)
    {g : X → α} (hg : Continuous g) {A : Set X} (hA : ∀ x ∈ A, g x ∈ N)
    (h1 : ∀ x ∈ A, g x ∉ L → A ∈ 𝓝 x) (h2 : ∀ x ∉ A, x ∈ closure A → g x ∈ L) :
    Continuous fun x => if x ∈ A then IndexSpace.Q N L (g x) else IndexSpace.pt N L := by
  set F := fun x => if x ∈ A then IndexSpace.Q N L (g x) else IndexSpace.pt N L
  have key : ∀ x, g x ∈ L → Tendsto F (𝓝 x) (𝓝 (IndexSpace.pt N L)) := by
    intro x hx V hV
    have hQ := IndexSpace.continuousOn_Q N L (g x) (hLN hx)
    rw [ContinuousWithinAt, IndexSpace.Q_of_mem_L hLN hx] at hQ
    have h₁ : ∀ᶠ z in 𝓝[N] (g x), IndexSpace.Q N L z ∈ V := hQ hV
    rw [eventually_nhdsWithin_iff] at h₁
    have h₂ := hg.continuousAt.eventually h₁
    rw [Filter.mem_map]
    filter_upwards [h₂] with y hy
    show (if y ∈ A then IndexSpace.Q N L (g y) else IndexSpace.pt N L) ∈ V
    by_cases hyA : y ∈ A
    · rw [if_pos hyA]
      exact hy (hA y hyA)
    · rw [if_neg hyA]
      exact mem_of_mem_nhds hV
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hxA : x ∈ A
  · by_cases hxL : g x ∈ L
    · have hFx : F x = IndexSpace.pt N L := by
        simp only [F, if_pos hxA]
        exact IndexSpace.Q_of_mem_L hLN hxL
      rw [ContinuousAt, hFx]
      exact key x hxL
    · have hAn := h1 x hxA hxL
      have hgN : ∀ᶠ y in 𝓝 x, g y ∈ N := Filter.mem_of_superset hAn fun y hy => hA y hy
      have hc : ContinuousAt (fun y => IndexSpace.Q N L (g y)) x :=
        (IndexSpace.continuousOn_Q N L (g x) (hA x hxA)).tendsto.comp
          (tendsto_nhdsWithin_iff.2 ⟨hg.continuousAt, hgN⟩)
      refine hc.congr ?_
      filter_upwards [hAn] with y hy
      simp only [F, if_pos hy]
  · by_cases hcl : x ∈ closure A
    · have hxL := h2 x hxA hcl
      have hFx : F x = IndexSpace.pt N L := by simp only [F, if_neg hxA]
      rw [ContinuousAt, hFx]
      exact key x hxL
    · have hev : ∀ᶠ y in 𝓝 x, y ∉ A :=
        Filter.mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hcl)
          fun y hy hyA => hy (subset_closure hyA)
      refine (continuousAt_const (y := IndexSpace.pt N L)).congr ?_
      filter_upwards [hev] with y hy
      simp only [F, if_neg hy]

/-! ### Maps out of `N/L` -/

theorem collapsed_elim {N L : Set α} {Y : Type*} (y₀ : Y) (F : N → Y)
    (hF : ∀ y : N, (y : α) ∈ L → F y = y₀) {a : N ⊕ Unit} (ha : collapsed N L a) :
    Sum.elim F (fun _ => y₀) a = y₀ := by
  rcases a with y | u
  · exact hF y ha
  · rfl

theorem elim_respects {N L : Set α} {Y : Type*} (y₀ : Y) (F : N → Y)
    (hF : ∀ y : N, (y : α) ∈ L → F y = y₀) (a b : N ⊕ Unit) (h : (indexSetoid N L).r a b) :
    Sum.elim F (fun _ => y₀) a = Sum.elim F (fun _ => y₀) b := by
  rcases (h : a = b ∨ (collapsed N L a ∧ collapsed N L b)) with rfl | ⟨ha, hb⟩
  · rfl
  · rw [collapsed_elim y₀ F hF ha, collapsed_elim y₀ F hF hb]

/-- A map `N → Y` sending `L` to `y₀` descends to `N/L`. -/
noncomputable def descend {N L : Set α} {Y : Type*} [TopologicalSpace Y] (y₀ : Y) (F : C(N, Y))
    (hF : ∀ y : N, (y : α) ∈ L → F y = y₀) : C(IndexSpace N L, Y) where
  toFun := Quotient.lift (s := indexSetoid N L) (Sum.elim F fun _ => y₀) (elim_respects y₀ F hF)
  continuous_toFun :=
    (F.continuous.sumElim continuous_const).quotient_lift _

theorem descend_proj {N L : Set α} {Y : Type*} [TopologicalSpace Y] (y₀ : Y) (F : C(N, Y))
    (hF : ∀ y : N, (y : α) ∈ L → F y = y₀) (y : N) :
    descend y₀ F hF (IndexSpace.proj N L y) = F y := rfl

theorem descend_pt {N L : Set α} {Y : Type*} [TopologicalSpace Y] (y₀ : Y) (F : C(N, Y))
    (hF : ∀ y : N, (y : α) ∈ L → F y = y₀) : descend y₀ F hF (IndexSpace.pt N L) = y₀ := rfl

/-- A map `I × N → Y` sending `I × L` to `y₀` descends to `I × N/L`. -/
noncomputable def descendProd {N L : Set α} {Y : Type*} [TopologicalSpace Y] (y₀ : Y)
    (F : C(I × N, Y)) (hF : ∀ (s : I) (y : N), (y : α) ∈ L → F (s, y) = y₀) :
    C(I × IndexSpace N L, Y) where
  toFun p := Quotient.lift (s := indexSetoid N L) (Sum.elim (fun y => F (p.1, y)) fun _ => y₀)
    (elim_respects y₀ (fun y => F (p.1, y)) (hF p.1)) p.2
  continuous_toFun := by
    apply Topology.IsQuotientMap.continuous_lift_prod_right
      (f := Quotient.mk (indexSetoid N L)) isQuotientMap_quotient_mk'
    have e : (fun p : I × (N ⊕ Unit) => Sum.elim (fun y => F (p.1, y)) (fun _ => y₀) p.2) =
        (Sum.elim F fun _ => y₀) ∘ Homeomorph.prodSumDistrib := by
      funext ⟨s, a⟩
      rcases a with y | u <;> rfl
    exact e ▸ (F.continuous.sumElim continuous_const).comp Homeomorph.prodSumDistrib.continuous

theorem descendProd_proj {N L : Set α} {Y : Type*} [TopologicalSpace Y] (y₀ : Y)
    (F : C(I × N, Y)) (hF : ∀ (s : I) (y : N), (y : α) ∈ L → F (s, y) = y₀) (s : I) (y : N) :
    descendProd y₀ F hF (s, IndexSpace.proj N L y) = F (s, y) := rfl

theorem descendProd_pt {N L : Set α} {Y : Type*} [TopologicalSpace Y] (y₀ : Y)
    (F : C(I × N, Y)) (hF : ∀ (s : I) (y : N), (y : α) ∈ L → F (s, y) = y₀) (s : I) :
    descendProd y₀ F hF (s, IndexSpace.pt N L) = y₀ := rfl

/-! ### Elementary consequences of the index pair axioms -/

section PairFacts

variable {N L : Set α}

theorem posInv_shift (hpos : IsPosInvRel ϕ L N) {x : α} {r c : ℝ} (hrc : r ≤ c)
    (hr : ϕ r x ∈ L) (hseg : ∀ s ∈ Icc r c, ϕ s x ∈ N) : ϕ c x ∈ L := by
  have := hpos _ hr (c - r) (by linarith) fun s hs => by
    rw [← ϕ.map_add]
    exact hseg _ ⟨by linarith [hs.1], by linarith [hs.2]⟩
  rwa [← ϕ.map_add, sub_add_cancel] at this

theorem stay_of_not_hit (hexit : IsExitSet ϕ L N) {x : α} (hx : x ∈ N) {c : ℝ}
    (h : ∀ s ∈ Icc 0 c, ϕ s x ∉ L) : ∀ s ∈ Icc 0 c, ϕ s x ∈ N := by
  intro s hs
  by_contra hout
  obtain ⟨s', hs', -, hL⟩ := hexit x hx s hs.1 hout
  exact h s' ⟨hs'.1, hs'.2.trans hs.2⟩ hL

end PairFacts

/-! ### The push map and its homotopy to the identity -/

section Push

theorem continuous_pushTime (N : Set α) (τ : ℝ) :
    Continuous fun p : I × N => ϕ ((p.1 : ℝ) * τ) (p.2 : α) :=
  ϕ.continuous ((continuous_subtype_val.comp continuous_fst).mul continuous_const)
    (continuous_subtype_val.comp continuous_snd)

theorem continuous_pushTime' (N : Set α) (τ : ℝ) :
    Continuous fun q : ℝ × (I × N) => ϕ (q.1 * ((q.2.1 : ℝ) * τ)) (q.2.2 : α) :=
  ϕ.continuous (continuous_fst.mul
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).mul continuous_const))
    (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))

variable [T2Space α] {S N L : Set α} (h : IsIndexPair ϕ S N L) (τ : ℝ) (hτ : 0 ≤ τ)

include h hτ

/-- Pairs `(s, y)` whose orbit stays in `N` up to time `s τ`. -/
def pushA : Set (I × N) := {p | ∀ u ∈ Icc (0 : ℝ) 1, ϕ (u * ((p.1 : ℝ) * τ)) (p.2 : α) ∈ N}

theorem mem_pushA_iff (p : I × N) :
    p ∈ pushA (ϕ := ϕ) (N := N) τ ↔ ∀ r ∈ Icc 0 ((p.1 : ℝ) * τ), ϕ r (p.2 : α) ∈ N :=
  forall_Icc_mul_iff (P := fun r => ϕ r (p.2 : α) ∈ N) (mul_nonneg p.1.2.1 hτ)

theorem continuous_pushFun :
    Continuous fun p : I × N => if p ∈ pushA (ϕ := ϕ) (N := N) τ then
      IndexSpace.Q N L (ϕ ((p.1 : ℝ) * τ) (p.2 : α)) else IndexSpace.pt N L := by
  have hNc := h.isCompact_N.isClosed
  have hLc := h.isCompact_L.isClosed
  refine continuous_ite_Q h.subset (continuous_pushTime N τ) ?_ ?_ ?_
  · intro p hp
    have := hp 1 ⟨zero_le_one, le_rfl⟩
    rwa [one_mul] at this
  · intro p hp hpL
    let B : Set (I × N) := {q | ∃ u ∈ Icc (0 : ℝ) 1, ϕ (u * ((q.1 : ℝ) * τ)) (q.2 : α) ∈ L}
    have hB : IsClosed B := isClosed_exists_Icc' (continuous_pushTime' N τ) hLc 0 1
    have hpB : p ∉ B := by
      rintro ⟨u, hu, hL⟩
      have hc : 0 ≤ (p.1 : ℝ) * τ := mul_nonneg p.1.2.1 hτ
      have hseg := (mem_pushA_iff h τ hτ p).1 hp
      exact hpL (posInv_shift h.posInv (mul_le_of_le_one_left hc hu.2) hL
        fun s hs => hseg s ⟨(mul_nonneg hu.1 hc).trans hs.1, hs.2⟩)
    refine Filter.mem_of_superset (hB.isOpen_compl.mem_nhds hpB) fun q hq => ?_
    have hc : 0 ≤ (q.1 : ℝ) * τ := mul_nonneg q.1.2.1 hτ
    rw [mem_pushA_iff h τ hτ]
    refine stay_of_not_hit h.exit q.2.2 fun s hs hL => hq ?_
    exact (exists_Icc_mul_iff hc (P := fun r => ϕ r (q.2 : α) ∈ L)).2 ⟨s, hs, hL⟩
  · intro p hp hcl
    have hA : IsClosed (pushA (ϕ := ϕ) (N := N) τ) :=
      isClosed_forall_Icc' (continuous_pushTime' N τ) hNc 0 1
    exact absurd (hA.closure_subset hcl) hp

theorem pushFun_L (s : I) (y : N) (hy : (y : α) ∈ L) :
    (if (s, y) ∈ pushA (ϕ := ϕ) (N := N) τ then
      IndexSpace.Q N L (ϕ ((s : ℝ) * τ) (y : α)) else IndexSpace.pt N L) = IndexSpace.pt N L := by
  split_ifs with hp
  · have hseg := (mem_pushA_iff h τ hτ (s, y)).1 hp
    have h0 : ϕ 0 (y : α) ∈ L := by rw [ϕ.map_zero_apply]; exact hy
    exact IndexSpace.Q_of_mem_L h.subset
      (posInv_shift h.posInv (mul_nonneg s.2.1 hτ) h0 hseg)
  · rfl

/-- The homotopy `(s, [x]) ↦ [ϕ(s τ, x)]`. -/
noncomputable def pushHom : C(I × IndexSpace N L, IndexSpace N L) :=
  descendProd (IndexSpace.pt N L) ⟨_, continuous_pushFun h τ hτ⟩
    fun s y hy => pushFun_L h τ hτ s y hy

/-- The push map `[x] ↦ [ϕ(τ, x)]`. -/
noncomputable def pushMap : C(IndexSpace N L, IndexSpace N L) :=
  (pushHom h τ hτ).comp ⟨fun x => (1, x), by fun_prop⟩

theorem pushMap_proj (y : N) :
    pushMap h τ hτ (IndexSpace.proj N L y) =
      if ∀ r ∈ Icc 0 τ, ϕ r (y : α) ∈ N then IndexSpace.Q N L (ϕ τ (y : α))
      else IndexSpace.pt N L := by
  show (if ((1 : I), y) ∈ pushA (ϕ := ϕ) (N := N) τ then
      IndexSpace.Q N L (ϕ (((1 : I) : ℝ) * τ) (y : α)) else IndexSpace.pt N L) = _
  have e := mem_pushA_iff h τ hτ ((1 : I), y)
  simp only [Icc.coe_one, one_mul] at e ⊢
  by_cases hy : ∀ r ∈ Icc 0 τ, ϕ r (y : α) ∈ N
  · rw [if_pos (e.2 hy), if_pos hy]
  · rw [if_neg (fun h' => hy (e.1 h')), if_neg hy]

theorem pushMap_pt : pushMap h τ hτ (IndexSpace.pt N L) = IndexSpace.pt N L := rfl

/-- Pushing along the flow is homotopic to the identity relative to the base point. -/
theorem pushMap_homotopicRel :
    (pushMap h τ hτ).HomotopicRel (ContinuousMap.id _) {IndexSpace.pt N L} := by
  refine ⟨ContinuousMap.HomotopyRel.symm
    { toFun := pushHom h τ hτ
      continuous_toFun := (pushHom h τ hτ).continuous
      map_zero_left := fun x => ?_
      map_one_left := fun x => rfl
      prop' := fun t x hx => ?_ }⟩
  · induction x using Quotient.inductionOn
    rename_i a
    rcases a with y | u
    · show (if ((0 : I), y) ∈ pushA (ϕ := ϕ) (N := N) τ then
          IndexSpace.Q N L (ϕ (((0 : I) : ℝ) * τ) (y : α)) else IndexSpace.pt N L) =
        IndexSpace.proj N L y
      have hp : ((0 : I), y) ∈ pushA (ϕ := ϕ) (N := N) τ := by
        intro u _
        simp only [Icc.coe_zero, zero_mul, mul_zero, ϕ.map_zero_apply]
        exact y.2
      rw [if_pos hp]
      simp only [Icc.coe_zero, zero_mul, ϕ.map_zero_apply]
      exact IndexSpace.Q_of_mem y.2
    · rfl
  · rw [mem_singleton_iff.1 hx]
    rfl

end Push

/-! ### The comparison map -/

section Comparison

variable [T2Space α] {S N L N' L' : Set α} (h : IsIndexPair ϕ S N L) (h' : IsIndexPair ϕ S N' L')
  (T : ℝ) (hT : 0 ≤ T)

/-- The time lemma hypotheses. -/
def TimeLemma (N L N' L' : Set α) (T : ℝ) : Prop :=
  ∀ x, (∀ s ∈ Icc (-T) T, ϕ s x ∈ closure (N \ L)) → x ∈ interior (N' \ L')

/-- Points whose orbit stays in `N ∖ L` on `[0, 2T]` and in `N' ∖ L'` on `[T, 3T]`. -/
def compA (N L N' L' : Set α) (T : ℝ) : Set α :=
  {y | (∀ s ∈ Icc 0 (2 * T), ϕ s y ∈ N \ L) ∧ ∀ s ∈ Icc T (3 * T), ϕ s y ∈ N' \ L'}

include h h' hT

theorem continuous_compFun (hT1 : TimeLemma (ϕ := ϕ) N L N' L' T)
    (hT2 : TimeLemma (ϕ := ϕ) N' L' N L T) :
    Continuous fun y : N => if (y : α) ∈ compA (ϕ := ϕ) N L N' L' T then
      IndexSpace.Q N' L' (ϕ (3 * T) (y : α)) else IndexSpace.pt N' L' := by
  have hNc := h.isCompact_N.isClosed
  have hLc := h.isCompact_L.isClosed
  have hN'c := h'.isCompact_N.isClosed
  have hL'c := h'.isCompact_L.isClosed
  have hg : Continuous fun y : N => ϕ (3 * T) (y : α) :=
    (ϕ.continuous_toFun _).comp continuous_subtype_val
  have e : (fun y : N => if (y : α) ∈ compA (ϕ := ϕ) N L N' L' T then
      IndexSpace.Q N' L' (ϕ (3 * T) (y : α)) else IndexSpace.pt N' L') =
      fun y : N => if y ∈ ((↑) : N → α) ⁻¹' compA (ϕ := ϕ) N L N' L' T then
      IndexSpace.Q N' L' (ϕ (3 * T) (y : α)) else IndexSpace.pt N' L' := rfl
  rw [e]
  refine continuous_ite_Q h'.subset hg ?_ ?_ ?_
  · intro y hy
    exact (hy.2 (3 * T) ⟨by linarith, le_rfl⟩).1
  · intro y hy _
    let B₁ : Set α := {z | ∃ s ∈ Icc 0 (2 * T), ϕ s z ∈ L}
    let B₂ : Set α := {z | ∃ s ∈ Icc 0 (2 * T), ϕ s z ∈ L'}
    have hB₁ : IsClosed B₁ := isClosed_exists_Icc ϕ hLc _ _
    have hB₂ : IsClosed B₂ := isClosed_exists_Icc ϕ hL'c _ _
    have hy1 : (y : α) ∉ B₁ := fun ⟨s, hs, hL⟩ => (hy.1 s hs).2 hL
    have hTy : ϕ T (y : α) ∈ interior (N' \ L') := by
      apply hT1
      intro s hs
      rw [← ϕ.map_add]
      exact subset_closure (hy.1 _ ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    have hy2 : ϕ T (y : α) ∉ B₂ := by
      rintro ⟨s, hs, hL⟩
      rw [← ϕ.map_add] at hL
      exact (hy.2 _ ⟨by linarith [hs.1], by linarith [hs.2]⟩).2 hL
    let W : Set N := {y' | (y' : α) ∉ B₁ ∧ ϕ T (y' : α) ∈ interior (N' \ L') ∧
      ϕ T (y' : α) ∉ B₂}
    have hcT : Continuous fun y' : N => ϕ T (y' : α) :=
      (ϕ.continuous_toFun _).comp continuous_subtype_val
    have hW : IsOpen W :=
      (hB₁.isOpen_compl.preimage continuous_subtype_val).inter
        ((isOpen_interior.preimage hcT).inter (hB₂.isOpen_compl.preimage hcT))
    refine Filter.mem_of_superset (hW.mem_nhds ⟨hy1, hTy, hy2⟩) fun y' ⟨h1, h2, h3⟩ => ?_
    have hnot1 : ∀ s ∈ Icc 0 (2 * T), ϕ s (y' : α) ∉ L := fun s hs hL => h1 ⟨s, hs, hL⟩
    have hstay1 := stay_of_not_hit h.exit y'.2 hnot1
    have hw : ϕ T (y' : α) ∈ N' := (interior_subset h2).1
    have hnot2 : ∀ s ∈ Icc 0 (2 * T), ϕ s (ϕ T (y' : α)) ∉ L' := fun s hs hL => h3 ⟨s, hs, hL⟩
    have hstay2 := stay_of_not_hit h'.exit hw hnot2
    refine ⟨fun s hs => ⟨hstay1 s hs, hnot1 s hs⟩, fun s hs => ?_⟩
    have e : ϕ s (y' : α) = ϕ (s - T) (ϕ T (y' : α)) := by rw [← ϕ.map_add, sub_add_cancel]
    rw [e]
    have hs' : s - T ∈ Icc 0 (2 * T) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact ⟨hstay2 _ hs', hnot2 _ hs'⟩
  · intro y hy hcl
    let C₁ : Set N := {y' | ∀ s ∈ Icc 0 (2 * T), ϕ s (y' : α) ∈ closure (N \ L)}
    let C₂ : Set N := {y' | ∀ s ∈ Icc T (3 * T), ϕ s (y' : α) ∈ closure (N' \ L')}
    have hcont : Continuous fun p : ℝ × N => ϕ p.1 (p.2 : α) :=
      ϕ.continuous continuous_fst (continuous_subtype_val.comp continuous_snd)
    have hC₁ : IsClosed C₁ := isClosed_forall_Icc' hcont isClosed_closure _ _
    have hC₂ : IsClosed C₂ := isClosed_forall_Icc' hcont isClosed_closure _ _
    have hy1 : y ∈ C₁ := (closure_minimal
      (show ((↑) : N → α) ⁻¹' compA (ϕ := ϕ) N L N' L' T ⊆ C₁ from
        fun y' hy' s hs => subset_closure (hy'.1 s hs)) hC₁) hcl
    have hy2 : y ∈ C₂ := (closure_minimal
      (show ((↑) : N → α) ⁻¹' compA (ϕ := ϕ) N L N' L' T ⊆ C₂ from
        fun y' hy' s hs => subset_closure (hy'.2 s hs)) hC₂) hcl
    have hclN : closure (N \ L) ⊆ N := closure_minimal sdiff_subset hNc
    have hclN' : closure (N' \ L') ⊆ N' := closure_minimal sdiff_subset hN'c
    have hnot : ¬ ((∀ s ∈ Icc 0 (2 * T), ϕ s (y : α) ∈ N \ L) ∧
        ∀ s ∈ Icc T (3 * T), ϕ s (y : α) ∈ N' \ L') := hy
    by_cases ha : ∀ s ∈ Icc 0 (2 * T), ϕ s (y : α) ∈ N \ L
    · have hb : ∃ s ∈ Icc T (3 * T), ϕ s (y : α) ∈ L' := by
        by_contra hb
        push Not at hb
        exact hnot ⟨ha, fun s hs => ⟨hclN' (hy2 s hs), hb s hs⟩⟩
      obtain ⟨s, hs, hL⟩ := hb
      exact posInv_shift h'.posInv hs.2 hL fun r hr =>
        hclN' (hy2 r ⟨by linarith [hs.1, hr.1], hr.2⟩)
    · exfalso
      push Not at ha
      obtain ⟨s, hs, hsL⟩ := ha
      have hsL' : ϕ s (y : α) ∈ L := by
        by_contra hc
        exact hsL ⟨hclN (hy1 s hs), hc⟩
      have h2T : ϕ (2 * T) (y : α) ∈ L :=
        posInv_shift h.posInv hs.2 hsL' fun r hr => hclN (hy1 r ⟨by linarith [hs.1, hr.1], hr.2⟩)
      have hin : ϕ (2 * T) (y : α) ∈ interior (N \ L) := by
        apply hT2
        intro r hr
        rw [← ϕ.map_add]
        exact hy2 _ ⟨by linarith [hr.1], by linarith [hr.2]⟩
      exact (interior_subset hin).2 h2T

theorem compFun_L (y : N) (hy : (y : α) ∈ L) :
    (if (y : α) ∈ compA (ϕ := ϕ) N L N' L' T then
      IndexSpace.Q N' L' (ϕ (3 * T) (y : α)) else IndexSpace.pt N' L') = IndexSpace.pt N' L' := by
  rw [if_neg]
  intro hA
  have := (hA.1 0 ⟨le_rfl, by linarith⟩).2
  rw [ϕ.map_zero_apply] at this
  exact this hy

/-- The comparison map `N/L → N'/L'`. -/
noncomputable def compMap (hT1 : TimeLemma (ϕ := ϕ) N L N' L' T)
    (hT2 : TimeLemma (ϕ := ϕ) N' L' N L T) : C(IndexSpace N L, IndexSpace N' L') :=
  descend (IndexSpace.pt N' L') ⟨_, continuous_compFun h h' T hT hT1 hT2⟩
    fun y hy => compFun_L h h' T hT y hy

end Comparison

/-! ### The composite of two comparison maps is the push map -/

section Composite

variable [T2Space α] {S N L N' L' : Set α} (h : IsIndexPair ϕ S N L) (h' : IsIndexPair ϕ S N' L')
  (T : ℝ) (hT : 0 ≤ T) (hT1 : TimeLemma (ϕ := ϕ) N L N' L' T)
  (hT2 : TimeLemma (ϕ := ϕ) N' L' N L T)

include h h' hT hT1 hT2

theorem comp_conditions {y : α} (hseg : ∀ r ∈ Icc 0 (6 * T), ϕ r y ∈ N)
    (hL : ϕ (6 * T) y ∉ L) :
    y ∈ compA (ϕ := ϕ) N L N' L' T ∧ ϕ (3 * T) y ∈ compA (ϕ := ϕ) N' L' N L T := by
  have hNL : ∀ r ∈ Icc 0 (6 * T), ϕ r y ∈ N \ L := by
    intro r hr
    refine ⟨hseg r hr, fun hrL => hL ?_⟩
    exact posInv_shift h.posInv hr.2 hrL fun s hs => hseg s ⟨hr.1.trans hs.1, hs.2⟩
  have hmid : ∀ r ∈ Icc T (5 * T), ϕ r y ∈ N' \ L' := by
    intro r hr
    apply interior_subset
    apply hT1
    intro s hs
    rw [← ϕ.map_add]
    exact subset_closure (hNL _ ⟨by linarith [hs.1, hr.1], by linarith [hs.2, hr.2]⟩)
  refine ⟨⟨fun s hs => hNL s ⟨hs.1, by linarith [hs.2]⟩,
    fun s hs => hmid s ⟨hs.1, by linarith [hs.2]⟩⟩, ⟨fun s hs => ?_, fun s hs => ?_⟩⟩
  · rw [← ϕ.map_add]
    exact hmid _ ⟨by linarith [hs.1], by linarith [hs.2]⟩
  · rw [← ϕ.map_add]
    exact hNL _ ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem comp_conditions' {y : α} (hA : y ∈ compA (ϕ := ϕ) N L N' L' T)
    (hA' : ϕ (3 * T) y ∈ compA (ϕ := ϕ) N' L' N L T) :
    (∀ r ∈ Icc 0 (6 * T), ϕ r y ∈ N) ∧ ϕ (6 * T) y ∉ L := by
  have hmid : ∀ r ∈ Icc T (5 * T), ϕ r y ∈ N' \ L' := by
    intro r hr
    by_cases hr3 : r ≤ 3 * T
    · exact hA.2 r ⟨hr.1, hr3⟩
    · have := hA'.1 (r - 3 * T) ⟨by linarith, by linarith [hr.2]⟩
      rwa [← ϕ.map_add, sub_add_cancel] at this
  have hlate : ∀ r ∈ Icc (4 * T) (6 * T), ϕ r y ∈ N \ L := by
    intro r hr
    have := hA'.2 (r - 3 * T) ⟨by linarith [hr.1], by linarith [hr.2]⟩
    rwa [← ϕ.map_add, sub_add_cancel] at this
  refine ⟨fun r hr => ?_, (hlate (6 * T) ⟨by linarith, le_rfl⟩).2⟩
  by_cases h2 : r ≤ 2 * T
  · exact (hA.1 r ⟨hr.1, h2⟩).1
  · by_cases h4 : r ≤ 4 * T
    · apply (interior_subset (hT2 _ fun s hs => ?_)).1
      rw [← ϕ.map_add]
      exact subset_closure (hmid _ ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    · exact (hlate r ⟨by linarith, hr.2⟩).1

theorem compMap_comp :
    (compMap h' h T hT hT2 hT1).comp (compMap h h' T hT hT1 hT2) =
      pushMap h (6 * T) (by linarith) := by
  have hLN := h.subset
  ext x
  induction x using Quotient.inductionOn
  rename_i a
  rcases a with y | u
  · show compMap h' h T hT hT2 hT1 (if (y : α) ∈ compA (ϕ := ϕ) N L N' L' T then
        IndexSpace.Q N' L' (ϕ (3 * T) (y : α)) else IndexSpace.pt N' L') =
      pushMap h (6 * T) (by linarith) (IndexSpace.proj N L y)
    rw [pushMap_proj]
    have e6 : ϕ (3 * T) (ϕ (3 * T) (y : α)) = ϕ (6 * T) (y : α) := by
      rw [← ϕ.map_add]; ring_nf
    by_cases hy : (∀ r ∈ Icc 0 (6 * T), ϕ r (y : α) ∈ N) ∧ ϕ (6 * T) (y : α) ∉ L
    · obtain ⟨hA, hA'⟩ := comp_conditions h h' T hT hT1 hT2 hy.1 hy.2
      have hw : ϕ (3 * T) (y : α) ∈ N' := (hA.2 (3 * T) ⟨by linarith, le_rfl⟩).1
      rw [if_pos hA, IndexSpace.Q_of_mem hw, if_pos hy.1]
      show (if ϕ (3 * T) (y : α) ∈ compA (ϕ := ϕ) N' L' N L T then
          IndexSpace.Q N L (ϕ (3 * T) (ϕ (3 * T) (y : α))) else IndexSpace.pt N L) = _
      rw [if_pos hA', e6]
    · have hrhs : (if ∀ r ∈ Icc 0 (6 * T), ϕ r (y : α) ∈ N then
          IndexSpace.Q N L (ϕ (6 * T) (y : α)) else IndexSpace.pt N L) = IndexSpace.pt N L := by
        split_ifs with hs
        · have : ϕ (6 * T) (y : α) ∈ L := by
            by_contra hc; exact hy ⟨hs, hc⟩
          exact IndexSpace.Q_of_mem_L hLN this
        · rfl
      rw [hrhs]
      by_cases hA : (y : α) ∈ compA (ϕ := ϕ) N L N' L' T
      · have hw : ϕ (3 * T) (y : α) ∈ N' := (hA.2 (3 * T) ⟨by linarith, le_rfl⟩).1
        rw [if_pos hA, IndexSpace.Q_of_mem hw]
        show (if ϕ (3 * T) (y : α) ∈ compA (ϕ := ϕ) N' L' N L T then
            IndexSpace.Q N L (ϕ (3 * T) (ϕ (3 * T) (y : α))) else IndexSpace.pt N L) = _
        rw [if_neg]
        intro hA'
        exact hy (comp_conditions' h h' T hT hT1 hT2 hA hA')
      · rw [if_neg hA]
        rfl
  · rfl

end Composite

/-- Independence of the index pair, in a Hausdorff space. -/
theorem indexPair_unique_of_t2 [T2Space α] {S N L N' L' : Set α} (h : IsIndexPair ϕ S N L)
    (h' : IsIndexPair ϕ S N' L') :
    Nonempty (PointedHomotopyEquiv (IndexSpace N L) (IndexSpace N' L')
      (IndexSpace.pt N L) (IndexSpace.pt N' L')) := by
  have hK : Inv ϕ (closure (N \ L)) ⊆ interior (N' \ L') := by rw [h.inv_eq]; exact h'.nhds
  have hK' : Inv ϕ (closure (N' \ L')) ⊆ interior (N \ L) := by rw [h'.inv_eq]; exact h.nhds
  obtain ⟨n₁, hn₁⟩ := exists_nat_mem_of_Inv_subset h.isolating.1 isOpen_interior hK
  obtain ⟨n₂, hn₂⟩ := exists_nat_mem_of_Inv_subset h'.isolating.1 isOpen_interior hK'
  set T : ℝ := max n₁ n₂
  have hT : 0 ≤ T := le_max_of_le_left (Nat.cast_nonneg n₁)
  have hT1 : TimeLemma (ϕ := ϕ) N L N' L' T := fun x hx =>
    hn₁ x fun s hs => hx s ⟨by linarith [hs.1, le_max_left (n₁ : ℝ) n₂],
      by linarith [hs.2, le_max_left (n₁ : ℝ) n₂]⟩
  have hT2 : TimeLemma (ϕ := ϕ) N' L' N L T := fun x hx =>
    hn₂ x fun s hs => hx s ⟨by linarith [hs.1, le_max_right (n₁ : ℝ) n₂],
      by linarith [hs.2, le_max_right (n₁ : ℝ) n₂]⟩
  refine ⟨{ toFun := compMap h h' T hT hT1 hT2
            invFun := compMap h' h T hT hT2 hT1
            map_pt := rfl
            inv_pt := rfl
            left := ?_
            right := ?_ }⟩
  · rw [compMap_comp h h' T hT hT1 hT2]
    exact pushMap_homotopicRel h _ _
  · rw [compMap_comp h' h T hT hT2 hT1]
    exact pushMap_homotopicRel h' _ _

end ConleyCheck.Conley
