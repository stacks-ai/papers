import ConleyCheck.Conley.Conjugacy

/-!
# Continuation of the Conley index

A family of flows parametrized by `λ ∈ [0,1]` is one flow `Φ` on `[0,1] × α` preserving the
parameter. If `N` isolates for every slice, then `[0,1] × N` isolates for `Φ`, and the fibers
`(Nt_λ, Lt_λ)` of an index pair `(Nt, Lt)` of `Φ` are index pairs for the slices.

To compare two fibers, flow for time `T` in the slice `λ`, switch the parameter to `μ`, and flow
for time `T` in the slice `μ`. By compactness there is one `η > 0` (a hybrid time lemma) such that
for `|λ - μ| < η` this gives a continuous map `Nt_λ/Lt_λ → Nt_μ/Lt_μ`. Going to `μ` and back is
homotopic, by sliding the intermediate parameter from `μ` to `λ`, to a push map, hence to the
identity. Chaining over a partition of `[0,1]` of mesh `< η` proves `continuation`.
-/

namespace ConleyCheck.Conley

open Set unitInterval Filter Topology

open scoped Classical

variable {α : Type*} [TopologicalSpace α]

/-- A family of flows parametrized by `λ ∈ [0,1]`, given as one flow on `[0,1] × α` that
preserves the parameter. -/
structure FlowFamily (α : Type*) [TopologicalSpace α] where
  flow : Flow ℝ (I × α)
  fst_eq : ∀ t p, (flow t p).1 = p.1

/-- The flow at parameter `λ`. -/
def FlowFamily.slice (Ψ : FlowFamily α) (l : I) : Flow ℝ α where
  toFun t x := (Ψ.flow t (l, x)).2
  cont' := continuous_snd.comp
    (Ψ.flow.continuous continuous_fst (continuous_const.prodMk continuous_snd))
  map_add' t₁ t₂ x := by
    have e : Ψ.flow t₂ (l, x) = (l, (Ψ.flow t₂ (l, x)).2) := Prod.ext (Ψ.fst_eq _ _) rfl
    show (Ψ.flow (t₁ + t₂) (l, x)).2 = (Ψ.flow t₁ (l, (Ψ.flow t₂ (l, x)).2)).2
    rw [Ψ.flow.map_add, ← e]
  map_zero' x := by
    show (Ψ.flow 0 (l, x)).2 = x
    rw [Ψ.flow.map_zero_apply]

namespace FlowFamily

variable (Ψ : FlowFamily α)

theorem flow_eq (t : ℝ) (l : I) (x : α) : Ψ.flow t (l, x) = (l, Ψ.slice l t x) :=
  Prod.ext (Ψ.fst_eq _ _) rfl

theorem mk_flow (t : ℝ) (p : I × α) : (p.1, (Ψ.flow t p).2) = Ψ.flow t p :=
  Prod.ext (Ψ.fst_eq t p).symm rfl

theorem mk_flow_mk (t : ℝ) (l : I) (x : α) : (l, (Ψ.flow t (l, x)).2) = Ψ.flow t (l, x) :=
  Ψ.mk_flow t (l, x)

theorem Inv_fiber (l : I) (M : Set (I × α)) :
    Inv (Ψ.slice l) (Prod.mk l ⁻¹' M) = Prod.mk l ⁻¹' Inv Ψ.flow M := by
  ext x
  show (∀ t, (l, Ψ.slice l t x) ∈ M) ↔ ∀ t, Ψ.flow t (l, x) ∈ M
  simp only [Ψ.flow_eq]

variable {Ψ}

/-- The fibers of an index pair of the family are index pairs of the slices. -/
theorem isIndexPair_fiber [T2Space α] {S Nt Lt : Set (I × α)} (h : IsIndexPair Ψ.flow S Nt Lt)
    (l : I) :
    IsIndexPair (Ψ.slice l) (Prod.mk l ⁻¹' S) (Prod.mk l ⁻¹' Nt) (Prod.mk l ⁻¹' Lt) := by
  have hc : Continuous (Prod.mk l : α → I × α) := continuous_const.prodMk continuous_id
  have hcpt : ∀ {M : Set (I × α)}, IsCompact M → IsCompact (Prod.mk l ⁻¹' M) := fun hM =>
    (hM.image continuous_snd).of_isClosed_subset (hM.isClosed.preimage hc)
      fun x hx => ⟨(l, x), hx, rfl⟩
  have hS : Prod.mk l ⁻¹' S ⊆ interior (Prod.mk l ⁻¹' Nt \ Prod.mk l ⁻¹' Lt) := by
    rw [← preimage_sdiff]
    exact (preimage_mono h.nhds).trans (preimage_interior_subset_interior_preimage hc)
  have hcl : closure (Prod.mk l ⁻¹' Nt \ Prod.mk l ⁻¹' Lt) ⊆ Prod.mk l ⁻¹' closure (Nt \ Lt) := by
    rw [← preimage_sdiff]
    exact hc.closure_preimage_subset _
  have hInv : Inv (Ψ.slice l) (closure (Prod.mk l ⁻¹' Nt \ Prod.mk l ⁻¹' Lt)) =
      Prod.mk l ⁻¹' S := by
    apply Subset.antisymm
    · refine (Inv_mono hcl).trans ?_
      rw [Inv_fiber, h.inv_eq]
    · refine subset_Inv (fun t x hx => ?_) (hS.trans (interior_subset.trans subset_closure))
      show (l, Ψ.slice l t x) ∈ S
      rw [← Ψ.flow_eq]
      rw [← h.inv_eq] at hx ⊢
      exact flow_mem_Inv hx t
  refine
    { isCompact_N := hcpt h.isCompact_N
      isCompact_L := hcpt h.isCompact_L
      subset := preimage_mono h.subset
      isolating := ⟨(hcpt h.isCompact_N).of_isClosed_subset isClosed_closure
          (closure_minimal sdiff_subset (h.isCompact_N.isClosed.preimage hc)), ?_⟩
      inv_eq := hInv
      nhds := hS
      posInv := ?_
      exit := ?_ }
  · rw [hInv]
    exact hS.trans (interior_mono subset_closure)
  · intro x hx t ht hseg
    show (l, Ψ.slice l t x) ∈ Lt
    rw [← Ψ.flow_eq]
    exact h.posInv _ hx t ht fun s hs => by rw [Ψ.flow_eq]; exact hseg s hs
  · intro x hx t ht hout
    obtain ⟨s, hs, hseg, hL⟩ := h.exit (l, x) hx t ht (by rw [Ψ.flow_eq]; exact hout)
    refine ⟨s, hs, fun r hr => ?_, ?_⟩
    · show (l, Ψ.slice l r x) ∈ Nt
      rw [← Ψ.flow_eq]
      exact hseg r hr
    · show (l, Ψ.slice l s x) ∈ Lt
      rw [← Ψ.flow_eq]
      exact hL

/-! ### The hybrid time lemma -/

section Hybrid

variable (Ψ) (Nt Lt : Set (I × α)) (T : ℝ)

/-- Flow for time `T`, then switch the parameter to `ν`. -/
def jumpPt (p : I × α) (ν : I) : I × α := (ν, (Ψ.flow T p).2)

/-- Both orbit segments of the jump stay in `Nt ∖ Lt`. -/
def JumpGood (p : I × α) (ν : I) : Prop :=
  (∀ s ∈ Icc 0 T, Ψ.flow s p ∈ Nt \ Lt) ∧ ∀ s ∈ Icc 0 T, Ψ.flow s (jumpPt Ψ T p ν) ∈ Nt \ Lt

/-- A backward segment at parameter `ν` followed by a forward segment at a nearby parameter `ν'`,
both in `cl(Nt ∖ Lt)`, forces both base points into `int(Nt ∖ Lt)`. -/
def HybridTime (η : ℝ) : Prop :=
  ∀ ν ν' : I, ∀ y : α, |(ν : ℝ) - ν'| < η →
    (∀ s ∈ Icc (-T) 0, Ψ.flow s (ν, y) ∈ closure (Nt \ Lt)) →
    (∀ s ∈ Icc 0 T, Ψ.flow s (ν', y) ∈ closure (Nt \ Lt)) →
    (ν, y) ∈ interior (Nt \ Lt) ∧ (ν', y) ∈ interior (Nt \ Lt)

variable {Ψ Nt Lt T}

theorem flow_back {M : Set (I × α)} {p : I × α} (hp : ∀ s ∈ Icc 0 T, Ψ.flow s p ∈ M) :
    ∀ s ∈ Icc (-T) 0, Ψ.flow s (p.1, (Ψ.flow T p).2) ∈ M := by
  intro s hs
  rw [Ψ.mk_flow, ← Ψ.flow.map_add]
  exact hp _ ⟨by linarith [hs.1], by linarith [hs.2]⟩

variable (Ψ) in
theorem exists_hybridTime [T2Space α] {S : Set (I × α)} (h : IsIndexPair Ψ.flow S Nt Lt) :
    ∃ T : ℝ, 0 ≤ T ∧ ∃ η > 0, HybridTime Ψ Nt Lt T η := by
  obtain ⟨n, hn⟩ := exists_nat_mem_of_Inv_subset h.isolating.1 isOpen_interior
    (by rw [h.inv_eq]; exact h.nhds)
  set T : ℝ := (n : ℝ)
  have hT : 0 ≤ T := Nat.cast_nonneg n
  set C := closure (Nt \ Lt)
  set U := interior (Nt \ Lt)
  have hC : IsCompact C := h.isolating.1
  let Bad : Set ((I × I) × α) := {p | (∀ s ∈ Icc (-T) 0, Ψ.flow s (p.1.1, p.2) ∈ C) ∧
    (∀ s ∈ Icc 0 T, Ψ.flow s (p.1.2, p.2) ∈ C) ∧ ((p.1.1, p.2) ∉ U ∨ (p.1.2, p.2) ∉ U)}
  have hc1 : Continuous fun p : (I × I) × α => (p.1.1, p.2) := by fun_prop
  have hc2 : Continuous fun p : (I × I) × α => (p.1.2, p.2) := by fun_prop
  have hBc : IsClosed Bad :=
    (isClosed_forall_Icc' (h := fun (u : ℝ) (p : (I × I) × α) => Ψ.flow u (p.1.1, p.2))
      (Ψ.flow.continuous continuous_fst (hc1.comp continuous_snd))
      isClosed_closure _ _).inter
      ((isClosed_forall_Icc' (h := fun (u : ℝ) (p : (I × I) × α) => Ψ.flow u (p.1.2, p.2))
        (Ψ.flow.continuous continuous_fst (hc2.comp continuous_snd))
        isClosed_closure _ _).inter
        ((isOpen_interior.isClosed_compl.preimage hc1).union
          (isOpen_interior.isClosed_compl.preimage hc2)))
  have hBk : IsCompact Bad := by
    refine (isCompact_univ.prod (hC.image continuous_snd)).of_isClosed_subset hBc
      fun p hp => ⟨mem_univ _, ⟨(p.1.1, p.2), ?_, rfl⟩⟩
    have := hp.1 0 ⟨by linarith, le_rfl⟩
    rwa [Ψ.flow.map_zero_apply] at this
  have hd : Continuous fun p : (I × I) × α => |(p.1.1 : ℝ) - p.1.2| := by fun_prop
  have hpos : ∀ p ∈ Bad, 0 < |(p.1.1 : ℝ) - p.1.2| := by
    rintro ⟨⟨ν, ν'⟩, y⟩ ⟨h1, h2, h3⟩
    refine abs_pos.2 (sub_ne_zero.2 fun e => ?_)
    have e' : ν = ν' := Subtype.ext e
    subst e'
    have hin : (ν, y) ∈ U := hn _ fun s hs => by
      rcases le_total s 0 with hs0 | hs0
      · exact h1 s ⟨hs.1, hs0⟩
      · exact h2 s ⟨hs0, hs.2⟩
    rcases h3 with h3 | h3 <;> exact h3 hin
  rcases Bad.eq_empty_or_nonempty with hB | hB
  · refine ⟨T, hT, 1, one_pos, fun ν ν' y _ h1 h2 => ?_⟩
    by_contra hc
    have hp : ((ν, ν'), y) ∈ Bad := ⟨h1, h2, not_and_or.1 hc⟩
    rw [hB] at hp
    exact hp
  · obtain ⟨p₀, hp₀, hmin⟩ := hBk.exists_isMinOn hB hd.continuousOn
    refine ⟨T, hT, _, hpos p₀ hp₀, fun ν ν' y hlt h1 h2 => ?_⟩
    by_contra hc
    have hp : ((ν, ν'), y) ∈ Bad := ⟨h1, h2, not_and_or.1 hc⟩
    exact absurd (hmin hp) (not_le.2 hlt)

variable [T2Space α] {S : Set (I × α)} (h : IsIndexPair Ψ.flow S Nt Lt) {η : ℝ}
  (hH : HybridTime Ψ Nt Lt T η)

include h hH

theorem jumpGood_nhds {Z : Type*} [TopologicalSpace Z] {a : Z → I × α} {b : Z → I}
    (ha : Continuous a) (hb : Continuous b) (haN : ∀ z, a z ∈ Nt)
    (hab : ∀ z, |((a z).1 : ℝ) - b z| < η) (z : Z) (hz : JumpGood Ψ Nt Lt T (a z) (b z)) :
    {z | JumpGood Ψ Nt Lt T (a z) (b z)} ∈ 𝓝 z := by
  have hLc := h.isCompact_L.isClosed
  set q : Z → I × α := fun z => jumpPt Ψ T (a z) (b z)
  have hq : Continuous q := hb.prodMk (continuous_snd.comp (Ψ.flow.continuous continuous_const ha))
  have hU := (hH (a z).1 (b z) (Ψ.flow T (a z)).2 (hab z)
    (flow_back fun s hs => subset_closure (hz.1 s hs)) fun s hs => subset_closure (hz.2 s hs)).2
  let W : Set Z := {z' | ∃ u ∈ Icc 0 T, Ψ.flow u (a z') ∈ Lt}ᶜ ∩ q ⁻¹' interior (Nt \ Lt) ∩
    {z' | ∃ u ∈ Icc 0 T, Ψ.flow u (q z') ∈ Lt}ᶜ
  have hW : IsOpen W :=
    ((isClosed_exists_Icc' (h := fun u z => Ψ.flow u (a z))
      (Ψ.flow.continuous continuous_fst (ha.comp continuous_snd)) hLc
      0 T).isOpen_compl.inter (isOpen_interior.preimage hq)).inter
      (isClosed_exists_Icc' (h := fun u z => Ψ.flow u (q z))
        (Ψ.flow.continuous continuous_fst (hq.comp continuous_snd)) hLc
        0 T).isOpen_compl
  have hzW : z ∈ W :=
    ⟨⟨fun ⟨u, hu, hL⟩ => (hz.1 u hu).2 hL, hU⟩, fun ⟨u, hu, hL⟩ => (hz.2 u hu).2 hL⟩
  refine Filter.mem_of_superset (hW.mem_nhds hzW) fun z' ⟨⟨h1, h2⟩, h3⟩ => ⟨?_, ?_⟩
  · intro s hs
    have hnot : ∀ s ∈ Icc 0 T, Ψ.flow s (a z') ∉ Lt := fun s hs hL => h1 ⟨s, hs, hL⟩
    exact ⟨stay_of_not_hit h.exit (haN z') hnot s hs, hnot s hs⟩
  · intro s hs
    have hnot : ∀ s ∈ Icc 0 T, Ψ.flow s (q z') ∉ Lt := fun s hs hL => h3 ⟨s, hs, hL⟩
    exact ⟨stay_of_not_hit h.exit (interior_subset h2).1 hnot s hs, hnot s hs⟩

theorem jump_closure {Z : Type*} [TopologicalSpace Z] {a : Z → I × α} {b : Z → I}
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ z, |((a z).1 : ℝ) - b z| < η) (z : Z)
    (hz : ¬JumpGood Ψ Nt Lt T (a z) (b z))
    (hcl : z ∈ closure {z | JumpGood Ψ Nt Lt T (a z) (b z)}) :
    Ψ.flow T (jumpPt Ψ T (a z) (b z)) ∈ Lt := by
  have hCN : closure (Nt \ Lt) ⊆ Nt := closure_minimal sdiff_subset h.isCompact_N.isClosed
  set q : Z → I × α := fun z => jumpPt Ψ T (a z) (b z)
  have hq : Continuous q := hb.prodMk (continuous_snd.comp (Ψ.flow.continuous continuous_const ha))
  have hC1 : IsClosed {z | ∀ s ∈ Icc 0 T, Ψ.flow s (a z) ∈ closure (Nt \ Lt)} :=
    isClosed_forall_Icc' (h := fun u z => Ψ.flow u (a z))
      (Ψ.flow.continuous continuous_fst (ha.comp continuous_snd))
      isClosed_closure 0 T
  have hC2 : IsClosed {z | ∀ s ∈ Icc 0 T, Ψ.flow s (q z) ∈ closure (Nt \ Lt)} :=
    isClosed_forall_Icc' (h := fun u z => Ψ.flow u (q z))
      (Ψ.flow.continuous continuous_fst (hq.comp continuous_snd))
      isClosed_closure 0 T
  have h1 : ∀ s ∈ Icc 0 T, Ψ.flow s (a z) ∈ closure (Nt \ Lt) :=
    hC1.closure_subset_iff.2 (fun z' hz' s hs => subset_closure (hz'.1 s hs)) hcl
  have h2 : ∀ s ∈ Icc 0 T, Ψ.flow s (q z) ∈ closure (Nt \ Lt) :=
    hC2.closure_subset_iff.2 (fun z' hz' s hs => subset_closure (hz'.2 s hs)) hcl
  by_cases hfirst : ∀ s ∈ Icc 0 T, Ψ.flow s (a z) ∈ Nt \ Lt
  · have hsec : ¬∀ s ∈ Icc 0 T, Ψ.flow s (q z) ∈ Nt \ Lt := fun h' => hz ⟨hfirst, h'⟩
    push Not at hsec
    obtain ⟨s, hs, hsn⟩ := hsec
    have hsL : Ψ.flow s (q z) ∈ Lt := by
      by_contra hL
      exact hsn ⟨hCN (h2 s hs), hL⟩
    exact posInv_shift h.posInv hs.2 hsL fun r hr => hCN (h2 r ⟨hs.1.trans hr.1, hr.2⟩)
  · exfalso
    push Not at hfirst
    obtain ⟨s, hs, hsn⟩ := hfirst
    have hsL : Ψ.flow s (a z) ∈ Lt := by
      by_contra hL
      exact hsn ⟨hCN (h1 s hs), hL⟩
    have hTL : Ψ.flow T (a z) ∈ Lt :=
      posInv_shift h.posInv hs.2 hsL fun r hr => hCN (h1 r ⟨hs.1.trans hr.1, hr.2⟩)
    have hU := (hH (a z).1 (b z) (Ψ.flow T (a z)).2 (hab z) (flow_back h1) h2).1
    rw [Ψ.mk_flow] at hU
    exact (interior_subset hU).2 hTL

end Hybrid

/-! ### Jump maps between fiber quotients -/

section Maps

variable {Nt Lt : Set (I × α)} {T η : ℝ}

/-- The parameter strip `|ν - c| < η`. -/
def strip (η : ℝ) (c : I) : Set (I × α) := {p | |(p.1 : ℝ) - c| < η}

variable (Nt Lt) in
/-- Inclusion of the fiber quotient at `ν` into the quotient of the strip around `c`. -/
noncomputable def fibIncl (ν c : I) (hν : |(ν : ℝ) - c| < η) :
    C(IndexSpace (Prod.mk ν ⁻¹' Nt) (Prod.mk ν ⁻¹' Lt),
      IndexSpace (Nt ∩ strip η c) (Lt ∩ strip η c)) :=
  descend (IndexSpace.pt _ _)
    ⟨fun y => IndexSpace.proj _ _ ⟨(ν, y.1), y.2, hν⟩,
      (IndexSpace.proj _ _).continuous.comp
        ((continuous_const.prodMk continuous_subtype_val).subtype_mk _)⟩
    fun _ hy => IndexSpace.proj_eq_pt ⟨hy, hν⟩

theorem fibIncl_Q (ν c : I) (hν : |(ν : ℝ) - c| < η) (w : α) :
    fibIncl Nt Lt ν c hν (IndexSpace.Q (Prod.mk ν ⁻¹' Nt) (Prod.mk ν ⁻¹' Lt) w) =
      IndexSpace.Q (Nt ∩ strip η c) (Lt ∩ strip η c) (ν, w) := by
  by_cases hw : (ν, w) ∈ Nt
  · rw [IndexSpace.Q_of_mem (N := Prod.mk ν ⁻¹' Nt) hw,
      IndexSpace.Q_of_mem (show (ν, w) ∈ Nt ∩ strip η c from ⟨hw, hν⟩)]
    rfl
  · rw [IndexSpace.Q, dite_eq_right (show w ∉ Prod.mk ν ⁻¹' Nt from hw), IndexSpace.Q,
      dite_eq_right fun h' => hw h'.1]
    rfl

/-- The segment from `l'` (at `t = 0`) to `l` (at `t = 1`). -/
def seg (l' l : I) (t : I) : I := Set.Icc.convexComb l' l t

theorem continuous_seg (l' l : I) : Continuous (seg l' l) :=
  Continuous.subtype_mk (f := fun t : I => (1 - (t : ℝ)) * l' + t * l) (by fun_prop)
    fun t => (seg l' l t).2

theorem abs_sub_seg (l' l t : I) : |(l : ℝ) - seg l' l t| ≤ |(l : ℝ) - l'| := by
  have e : (l : ℝ) - seg l' l t = (1 - t) * (l - l') := by
    show (l : ℝ) - ((1 - t) * l' + t * l) = _
    ring
  rw [e, abs_mul, abs_of_nonneg (sub_nonneg.2 t.2.2)]
  exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [t.2.1])

theorem continuous_jumpPt {Z : Type*} [TopologicalSpace Z] {a : Z → I × α} {b : Z → I}
    (ha : Continuous a) (hb : Continuous b) : Continuous fun z => jumpPt Ψ T (a z) (b z) :=
  hb.prodMk (continuous_snd.comp (Ψ.flow.continuous continuous_const ha))

theorem not_jumpGood_of_mem (hT : 0 ≤ T) {p : I × α} (hp : p ∈ Lt) (ν : I) :
    ¬JumpGood Ψ Nt Lt T p ν :=
  fun hg => (hg.1 0 ⟨le_rfl, hT⟩).2 (by rw [Ψ.flow.map_zero_apply]; exact hp)

variable [T2Space α] {S : Set (I × α)} (h : IsIndexPair Ψ.flow S Nt Lt) (hT : 0 ≤ T)
  (hH : HybridTime Ψ Nt Lt T η)

include h hT hH

/-- `[(ν, y)] ↦ [ϕ_c(T, ϕ_ν(T, y))]` from the strip around `c` to the fiber at `c`. -/
noncomputable def jumpIn (c : I) :
    C(IndexSpace (Nt ∩ strip η c) (Lt ∩ strip η c),
      IndexSpace (Prod.mk c ⁻¹' Nt) (Prod.mk c ⁻¹' Lt)) :=
  descend (IndexSpace.pt _ _)
    ⟨fun z => if z ∈ {z : ↥(Nt ∩ strip η c) | JumpGood Ψ Nt Lt T z.1 c} then
        IndexSpace.Q _ _ (Ψ.flow T (jumpPt Ψ T z.1 c)).2 else IndexSpace.pt _ _, by
      have hj := continuous_jumpPt (Ψ := Ψ) (T := T) (Z := ↥(Nt ∩ strip η c))
        (a := Subtype.val) (b := fun _ => c) continuous_subtype_val continuous_const
      refine continuous_ite_Q (preimage_mono h.subset)
        (continuous_snd.comp (Ψ.flow.continuous continuous_const hj)) (fun z hz => ?_)
        (fun z hz _ => jumpGood_nhds h hH continuous_subtype_val continuous_const
          (fun z => z.2.1) (fun z => z.2.2) z hz) (fun z hz hcl => ?_)
      · show ((jumpPt Ψ T z.1 c).1, (Ψ.flow T (jumpPt Ψ T z.1 c)).2) ∈ Nt
        rw [Ψ.mk_flow]
        exact (hz.2 T ⟨hT, le_rfl⟩).1
      · show ((jumpPt Ψ T z.1 c).1, (Ψ.flow T (jumpPt Ψ T z.1 c)).2) ∈ Lt
        rw [Ψ.mk_flow]
        exact jump_closure h hH continuous_subtype_val continuous_const (fun z => z.2.2) z hz
          hcl⟩
    fun z hz => ite_eq_right (not_jumpGood_of_mem hT hz.1 c)

/-- The homotopy `(t, [y]) ↦ [ϕ_ν(T, ϕ_l(T, y))]` with `ν` moving from `l'` to `l`. -/
noncomputable def jumpOut (l l' : I) (hll : |(l : ℝ) - l'| < η) :
    C(I × IndexSpace (Prod.mk l ⁻¹' Nt) (Prod.mk l ⁻¹' Lt),
      IndexSpace (Nt ∩ strip η l) (Lt ∩ strip η l)) :=
  descendProd (IndexSpace.pt _ _)
    ⟨fun z => if z ∈ {z : I × ↥(Prod.mk l ⁻¹' Nt) |
        JumpGood Ψ Nt Lt T (l, z.2.1) (seg l' l z.1)} then
        IndexSpace.Q _ _ (Ψ.flow T (jumpPt Ψ T (l, z.2.1) (seg l' l z.1)))
        else IndexSpace.pt _ _, by
      have ha : Continuous fun z : I × ↥(Prod.mk l ⁻¹' Nt) => ((l, z.2.1) : I × α) := by
        fun_prop
      have hb : Continuous fun z : I × ↥(Prod.mk l ⁻¹' Nt) => seg l' l z.1 :=
        (continuous_seg l' l).comp continuous_fst
      have hab : ∀ z : I × ↥(Prod.mk l ⁻¹' Nt),
          |(((l, z.2.1) : I × α).1 : ℝ) - seg l' l z.1| < η :=
        fun z => (abs_sub_seg l' l z.1).trans_lt hll
      have hstrip : ∀ z : I × ↥(Prod.mk l ⁻¹' Nt),
          Ψ.flow T (jumpPt Ψ T (l, z.2.1) (seg l' l z.1)) ∈ strip η l := fun z => by
        show |((Ψ.flow T _).1 : ℝ) - l| < η
        rw [Ψ.fst_eq, abs_sub_comm]
        exact hab z
      exact continuous_ite_Q (inter_subset_inter_left _ h.subset)
        (Ψ.flow.continuous continuous_const (continuous_jumpPt ha hb))
        (fun z hz => ⟨(hz.2 T ⟨hT, le_rfl⟩).1, hstrip z⟩)
        (fun z hz _ => jumpGood_nhds h hH ha hb (fun z => z.2.2) hab z hz)
        (fun z hz hcl => ⟨jump_closure h hH ha hb hab z hz hcl, hstrip z⟩)⟩
    fun _ _ hy => ite_eq_right (not_jumpGood_of_mem hT hy _)

theorem jumpOut_eq (l l' : I) (hll : |(l : ℝ) - l'| < η) (t ν : I) (hν : seg l' l t = ν)
    (h1 : |(ν : ℝ) - l| < η) (h2 : |(l : ℝ) - ν| < η) (x) :
    jumpOut h hT hH l l' hll (t, x) =
      fibIncl Nt Lt ν l h1 (jumpIn h hT hH ν (fibIncl Nt Lt l ν h2 x)) := by
  subst hν
  induction x using Quotient.inductionOn with
  | h a =>
    rcases a with y | u
    · show (if _ then _ else _) = fibIncl Nt Lt _ l h1 (if _ then _ else _)
      split_ifs with g1 g2 g2
      · rw [fibIncl_Q]
        exact congrArg _ (Ψ.mk_flow T (jumpPt Ψ T (l, y.1) (seg l' l t))).symm
      · exact absurd g1 g2
      · exact absurd g2 g1
      · rfl
    · rfl

theorem jumpIn_fibIncl_self (l : I) (hl : |(l : ℝ) - l| < η) (x) :
    jumpIn h hT hH l (fibIncl Nt Lt l l hl x) =
      pushMap (isIndexPair_fiber h l) (2 * T) (by positivity) x := by
  induction x using Quotient.inductionOn with
  | h a =>
    rcases a with y | u
    · rw [show Quotient.mk _ (Sum.inl y) = IndexSpace.proj _ _ y from rfl, pushMap_proj]
      show (if _ then _ else _) = _
      have hj : jumpPt Ψ T (l, y.1) l = Ψ.flow T (l, y.1) := Ψ.mk_flow_mk T l y.1
      have e : (Ψ.flow T (jumpPt Ψ T (l, y.1) l)).2 = Ψ.slice l (2 * T) y := by
        show _ = (Ψ.flow (2 * T) (l, y.1)).2
        rw [hj, ← Ψ.flow.map_add, two_mul]
      have hiff : JumpGood Ψ Nt Lt T (l, y.1) l ↔
          ∀ r ∈ Icc 0 (2 * T), Ψ.flow r (l, y.1) ∈ Nt \ Lt := by
        constructor
        · rintro ⟨g1, g2⟩ r hr
          rcases le_total r T with hrT | hrT
          · exact g1 r ⟨hr.1, hrT⟩
          · have := g2 (r - T) ⟨by linarith, by linarith [hr.2]⟩
            rwa [hj, ← Ψ.flow.map_add, sub_add_cancel] at this
        · intro g
          refine ⟨fun s hs => g s ⟨hs.1, by linarith [hs.2]⟩, fun s hs => ?_⟩
          rw [hj, ← Ψ.flow.map_add]
          exact g _ ⟨by linarith [hs.1], by linarith [hs.2]⟩
      split_ifs with g hp hp
      · exact congrArg _ e
      · exact absurd (fun r hr => by
          show (l, Ψ.slice l r y) ∈ Nt
          rw [← Ψ.flow_eq]
          exact (hiff.1 g r hr).1) hp
      · have hN : ∀ r ∈ Icc 0 (2 * T), Ψ.flow r (l, y.1) ∈ Nt := fun r hr => by
          rw [Ψ.flow_eq]
          exact hp r hr
        have hex : ∃ r ∈ Icc 0 (2 * T), Ψ.flow r (l, y.1) ∈ Lt := by
          by_contra hne
          push Not at hne
          exact g (hiff.2 fun r hr => ⟨hN r hr, hne r hr⟩)
        obtain ⟨r, hr, hrL⟩ := hex
        have hL := posInv_shift h.posInv hr.2 hrL fun s hs => hN s ⟨hr.1.trans hs.1, hs.2⟩
        rw [Ψ.flow_eq] at hL
        exact (IndexSpace.Q_of_mem_L (N := Prod.mk l ⁻¹' Nt) (preimage_mono h.subset)
          (show Ψ.slice l (2 * T) y ∈ Prod.mk l ⁻¹' Lt from hL)).symm
      · rfl
    · rfl

/-- Going to the fiber at `l'` and back is homotopic to the identity. -/
theorem back_and_forth (l l' : I) (hll : |(l : ℝ) - l'| < η) (hll' : |(l' : ℝ) - l| < η) :
    (((jumpIn h hT hH l).comp (fibIncl Nt Lt l' l hll')).comp
      ((jumpIn h hT hH l').comp (fibIncl Nt Lt l l' hll))).HomotopicRel (ContinuousMap.id _)
      {IndexSpace.pt _ _} := by
  have hl0 : |(l : ℝ) - l| < η := by
    rw [sub_self, abs_zero]
    exact (abs_nonneg _).trans_lt hll
  set P := isIndexPair_fiber h l
  set push := pushMap P (2 * T) (by positivity)
  set H := (jumpIn h hT hH l).comp (jumpOut h hT hH l l' hll)
  have e0 : ((jumpIn h hT hH l).comp (fibIncl Nt Lt l' l hll')).comp
      ((jumpIn h hT hH l').comp (fibIncl Nt Lt l l' hll)) =
      H.comp ⟨fun x => (0, x), by fun_prop⟩ := by
    ext x
    exact congrArg (jumpIn h hT hH l)
      (jumpOut_eq h hT hH l l' hll 0 l' (Set.Icc.convexComb_zero _ _) hll' hll x).symm
  have e1 : H.comp ⟨fun x => (1, x), by fun_prop⟩ = push.comp push := by
    ext x
    show jumpIn h hT hH l (jumpOut h hT hH l l' hll (1, x)) = push (push x)
    rw [jumpOut_eq h hT hH l l' hll 1 l (Set.Icc.convexComb_one _ _) hl0 hl0,
      jumpIn_fibIncl_self, jumpIn_fibIncl_self]
  have hH01 : (H.comp ⟨fun x => (0, x), by fun_prop⟩).HomotopicRel
      (H.comp ⟨fun x => (1, x), by fun_prop⟩) {IndexSpace.pt _ _} :=
    ⟨{ toFun := H
       continuous_toFun := H.continuous
       map_zero_left := fun _ => rfl
       map_one_left := fun _ => rfl
       prop' := fun t x hx => by
         rw [mem_singleton_iff.1 hx]
         rfl }⟩
  have hpp : (push.comp push).HomotopicRel (ContinuousMap.id _) {IndexSpace.pt _ _} := by
    have := HomotopicRel.precomp (pushMap_homotopicRel P (2 * T) (by positivity)) push
      (T := {IndexSpace.pt _ _}) fun x hx => by
        rw [mem_singleton_iff.1 hx]
        rfl
    rw [ContinuousMap.id_comp] at this
    exact this.trans (pushMap_homotopicRel P _ _)
  rw [e0]
  exact hH01.trans (e1 ▸ hpp)

/-- Fibers at nearby parameters have homotopy equivalent quotients. -/
theorem fiber_equiv_of_near (l l' : I) (hll : |(l : ℝ) - l'| < η) :
    Nonempty (PointedHomotopyEquiv (IndexSpace (Prod.mk l ⁻¹' Nt) (Prod.mk l ⁻¹' Lt))
      (IndexSpace (Prod.mk l' ⁻¹' Nt) (Prod.mk l' ⁻¹' Lt)) (IndexSpace.pt _ _)
      (IndexSpace.pt _ _)) := by
  have hll' : |(l' : ℝ) - l| < η := by rwa [abs_sub_comm]
  exact ⟨{ toFun := (jumpIn h hT hH l').comp (fibIncl Nt Lt l l' hll)
           invFun := (jumpIn h hT hH l).comp (fibIncl Nt Lt l' l hll')
           map_pt := rfl
           inv_pt := rfl
           left := back_and_forth h hT hH l l' hll hll'
           right := back_and_forth h hT hH l' l hll' hll }⟩

/-- The fibers at `0` and `1` have homotopy equivalent quotients. -/
theorem fiber_equiv (hη : 0 < η) :
    Nonempty (PointedHomotopyEquiv (IndexSpace (Prod.mk 0 ⁻¹' Nt) (Prod.mk 0 ⁻¹' Lt))
      (IndexSpace (Prod.mk 1 ⁻¹' Nt) (Prod.mk 1 ⁻¹' Lt)) (IndexSpace.pt _ _)
      (IndexSpace.pt _ _)) := by
  set p : ℕ → I := fun k => Set.Icc.addNSMul (zero_le_one : (0 : ℝ) ≤ 1) (η / 2) k
  have hstep : ∀ k, |((p k : I) : ℝ) - p (k + 1)| < η := by
    intro k
    refine (Set.abs_projIcc_sub_projIcc _).trans_lt ?_
    rw [zero_add, zero_add, succ_nsmul, sub_add_cancel_left, abs_neg,
      abs_of_pos (half_pos hη)]
    exact half_lt_self hη
  have hchain : ∀ k, Nonempty (PointedHomotopyEquiv
      (IndexSpace (Prod.mk (p 0) ⁻¹' Nt) (Prod.mk (p 0) ⁻¹' Lt))
      (IndexSpace (Prod.mk (p k) ⁻¹' Nt) (Prod.mk (p k) ⁻¹' Lt)) (IndexSpace.pt _ _)
      (IndexSpace.pt _ _)) := by
    intro k
    induction k with
    | zero => exact ⟨PointedHomotopyEquiv.refl _⟩
    | succ k ih =>
      obtain ⟨e⟩ := ih
      obtain ⟨e'⟩ := fiber_equiv_of_near h hT hH _ _ (hstep k)
      exact ⟨e.trans e'⟩
  obtain ⟨m, hm⟩ := Set.Icc.addNSMul_eq_right (zero_le_one : (0 : ℝ) ≤ 1) (half_pos hη)
  have h0 : p 0 = 0 := Subtype.ext (Set.Icc.addNSMul_zero _)
  have h1 : p m = 1 := Subtype.ext (hm m le_rfl)
  have := hchain m
  rw [h0, h1] at this
  exact this

end Maps

end FlowFamily

/-- Continuation: if `N` isolates for every slice, the indices at `λ = 0` and `λ = 1` agree. -/
theorem continuation [TopologicalSpace.MetrizableSpace α]
    (Ψ : FlowFamily α) {N : Set α} (hN : IsCompact N)
    (hiso : ∀ l, Inv (Ψ.slice l) N ⊆ interior N) {N₀ L₀ N₁ L₁ : Set α}
    (h₀ : IsIndexPair (Ψ.slice 0) (Inv (Ψ.slice 0) N) N₀ L₀)
    (h₁ : IsIndexPair (Ψ.slice 1) (Inv (Ψ.slice 1) N) N₁ L₁) :
    Nonempty (PointedHomotopyEquiv (IndexSpace N₀ L₀) (IndexSpace N₁ L₁)
      (IndexSpace.pt N₀ L₀) (IndexSpace.pt N₁ L₁)) := by
  have hiso' : IsIsolatingNbhd Ψ.flow (univ ×ˢ N) := by
    refine ⟨isCompact_univ.prod hN, fun p hp => ?_⟩
    rw [interior_prod_eq, interior_univ]
    exact ⟨mem_univ _, hiso p.1 fun t => (hp t).2⟩
  obtain ⟨Nt, Lt, hP, -⟩ := exists_indexPair hiso'
  have hS : ∀ l, Prod.mk l ⁻¹' Inv Ψ.flow (univ ×ˢ N) = Inv (Ψ.slice l) N := fun l => by
    rw [← Ψ.Inv_fiber]
    congr 1
    ext x
    simp
  have hfib : ∀ l, IsIndexPair (Ψ.slice l) (Inv (Ψ.slice l) N) (Prod.mk l ⁻¹' Nt)
      (Prod.mk l ⁻¹' Lt) := fun l => hS l ▸ FlowFamily.isIndexPair_fiber hP l
  obtain ⟨T, hT, η, hη, hH⟩ := FlowFamily.exists_hybridTime Ψ hP
  obtain ⟨e₀⟩ := indexPair_unique h₀ (hfib 0)
  obtain ⟨e⟩ := FlowFamily.fiber_equiv hP hT hH hη
  obtain ⟨e₁⟩ := indexPair_unique (hfib 1) h₁
  exact ⟨(e₀.trans e).trans e₁⟩

end ConleyCheck.Conley
