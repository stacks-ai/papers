import ConleyCheck.Conley.Skew

/-!
# The compactified extended phase space

The extended phase space `𝒮 = X × [-1, 1]` carries a skew-product flow `Φ` over a base flow `θ`
on `[-1, 1]` for which the coordinate `τ` is a height function (`IsHeight`), namely `θ` fixes
`±1` and moves every other point upwards. The flow of `ẋ = F(τ, x)`, `τ̇ = g(τ)` (equation
`eq:slab`) is of this form under Hypothesis `hyp:H`.

* `fiber_isolating` is Lemma `lem:isolation`(a), i.e., `K_± = {x : (x, ±1) ∈ S}` is an isolated
  invariant set of the boundary flow `f_±`.
* `slab_bot_indexTrivial` and `slab_top_hasIndex` are the two `𝒮` rows of Proposition
  `prop:boundary`, namely `h_𝒮(K × {-1}) = 0̄` and `h_𝒮(K × {+1}) ≅ h_{f_+}(K)`.
* `slab_index` is Theorem `thm:slab`, namely `(K_+ × {1}, K_- × {-1})` is an attractor–repeller
  pair of `S` and `CH_*(K_+; f_+) ≅ CH_*(S)`.
-/

namespace ConleyCheck.Conley

open Set Filter Topology unitInterval

open scoped Classical

/-- The base `[-1, 1]` of the compactified extended phase space. -/
abbrev Tau : Type := Icc (-1 : ℝ) 1

namespace Tau

/-- The infrared end `τ = 1`. -/
def top : Tau := ⟨1, by norm_num, le_rfl⟩

/-- The ultraviolet end `τ = -1`. -/
def bot : Tau := ⟨-1, le_rfl, by norm_num⟩

end Tau

/-! ### The base flow -/

section Base

variable {θ : Flow ℝ Tau} (hθ : IsHeight θ (fun b => (b : ℝ)))
include hθ

theorem base_top (t : ℝ) : θ t Tau.top = Tau.top := Subtype.ext (hθ.fix _ (Or.inl rfl) t)

theorem base_bot (t : ℝ) : θ t Tau.bot = Tau.bot := Subtype.ext (hθ.fix _ (Or.inr rfl) t)

theorem base_cancel (s : ℝ) (b : Tau) : θ (-s) (θ s b) = b := by
  rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]

/-- The base flow preserves the order of `[-1, 1]`. -/
theorem base_mono {b b' : Tau} (h : (b : ℝ) ≤ b') (t : ℝ) : (θ t b : ℝ) ≤ θ t b' := by
  by_contra hlt
  push Not at hlt
  have hc : Continuous fun s => (θ s b' : ℝ) - θ s b :=
    (continuous_subtype_val.comp (θ.continuous continuous_id continuous_const)).sub
      (continuous_subtype_val.comp (θ.continuous continuous_id continuous_const))
  have h0 : (0 : ℝ) ∈ uIcc ((θ 0 b' : ℝ) - θ 0 b) ((θ t b' : ℝ) - θ t b) := by
    rw [Flow.map_zero_apply, Flow.map_zero_apply]
    exact mem_uIcc.2 (Or.inr ⟨by linarith, by linarith⟩)
  obtain ⟨s, -, hs⟩ := intermediate_value_uIcc hc.continuousOn h0
  have heq : θ s b' = θ s b := Subtype.ext (by simp only at hs; linarith)
  have := congrArg (θ (-s)) heq
  rw [base_cancel hθ, base_cancel hθ] at this
  rw [this] at hlt
  exact lt_irrefl _ hlt

theorem base_lt_one {b : Tau} (hb : (b : ℝ) < 1) (t : ℝ) : (θ t b : ℝ) < 1 := by
  refine lt_of_le_of_ne (θ t b).2.2 fun h => ?_
  have := hθ.fix (θ t b) (Or.inl h) (-t)
  simp only [base_cancel hθ] at this
  linarith

theorem neg_one_lt_base {b : Tau} (hb : -1 < (b : ℝ)) (t : ℝ) : -1 < (θ t b : ℝ) := by
  refine lt_of_le_of_ne (θ t b).2.1 fun h => ?_
  have := hθ.fix (θ t b) (Or.inr h.symm) (-t)
  simp only [base_cancel hθ] at this
  linarith

/-- Below the top, the base flow tends to `-1` as `t → -∞`. -/
theorem base_tendsto_bot {b : Tau} (hb : (b : ℝ) < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ a₀, ∀ a ≤ a₀, (θ a b : ℝ) < -1 + ε := by
  by_cases hb1 : (b : ℝ) = -1
  · refine ⟨0, fun a _ => ?_⟩
    have := hθ.fix b (Or.inr hb1) a
    linarith
  have hlow : -1 < (b : ℝ) := lt_of_le_of_ne b.2.1 (Ne.symm hb1)
  obtain ⟨z, hz⟩ := alphaLim_nonempty (ϕ := θ) isCompact_univ (fun _ _ _ => mem_univ _)
    (mem_univ b)
  have hz1 : (z : ℝ) = -1 := hθ.alphaLim_bot hb hz
  have hcl := mem_closure_of_mem_alphaLim hz
  obtain ⟨_, hyO, ⟨t, ht, rfl⟩⟩ := mem_closure_iff.1 hcl {y : Tau | (y : ℝ) < -1 + ε}
    (isOpen_lt continuous_subtype_val continuous_const) (by show (z : ℝ) < _; linarith)
  exact ⟨t, fun a ha => (hθ.monotone_flow b ha).trans_lt hyO⟩

/-- Above the bottom, the base flow tends to `1` as `t → ∞`. -/
theorem base_tendsto_top {b : Tau} (hb : -1 < (b : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ a₀, ∀ a ≥ a₀, 1 - ε < (θ a b : ℝ) := by
  by_cases hb1 : (b : ℝ) = 1
  · refine ⟨0, fun a _ => ?_⟩
    have := hθ.fix b (Or.inl hb1) a
    linarith
  have hhigh : (b : ℝ) < 1 := lt_of_le_of_ne b.2.2 hb1
  obtain ⟨z, hz⟩ := omegaLim_nonempty (ϕ := θ) isCompact_univ (fun _ _ _ => mem_univ _)
    (mem_univ b)
  have hz1 : (z : ℝ) = 1 := hθ.omegaLim_top hb hz
  have hcl := mem_closure_of_mem_omegaLim hz
  obtain ⟨_, hyO, ⟨t, ht, rfl⟩⟩ := mem_closure_iff.1 hcl {y : Tau | 1 - ε < (y : ℝ)}
    (isOpen_lt continuous_const continuous_subtype_val) (by show _ < (z : ℝ); linarith)
  exact ⟨t, fun a ha => hyO.trans_le (hθ.monotone_flow b ha)⟩

/-! #### The two invariant halves `[-1, 1)` and `(-1, 1]` -/

/-- `[-1, 1)`. -/
def Ubot : Set Tau := {b | (b : ℝ) < 1}

/-- `(-1, 1]`. -/
def Utop : Set Tau := {b | -1 < (b : ℝ)}

omit hθ in
theorem isOpen_Ubot : IsOpen Ubot := isOpen_lt continuous_subtype_val continuous_const

omit hθ in
theorem isOpen_Utop : IsOpen Utop := isOpen_lt continuous_const continuous_subtype_val

theorem isInvariant_Ubot : IsInvariant θ Ubot := fun t _ hb => base_lt_one hθ hb t

theorem isInvariant_Utop : IsInvariant θ Utop := fun t _ hb => neg_one_lt_base hθ hb t

omit hθ in
theorem bot_mem_Ubot : Tau.bot ∈ Ubot := show (-1 : ℝ) < 1 by norm_num

omit hθ in
theorem top_mem_Utop : Tau.top ∈ Utop := show (-1 : ℝ) < 1 by norm_num

/-- `g(λ, b) = θ_{log λ} b`, extended by `-1` at `λ = 0`. -/
noncomputable def gBotFun (q : I × Ubot) : Ubot :=
  if (q.1 : ℝ) = 0 then ⟨Tau.bot, bot_mem_Ubot⟩
  else θ.restrict (isInvariant_Ubot hθ) (Real.log q.1) q.2

/-- `g(λ, b) = θ_{-log λ} b`, extended by `1` at `λ = 0`. -/
noncomputable def gTopFun (q : I × Utop) : Utop :=
  if (q.1 : ℝ) = 0 then ⟨Tau.top, top_mem_Utop⟩
  else θ.restrict (isInvariant_Utop hθ) (-Real.log q.1) q.2

theorem continuous_gBotFun : Continuous (gBotFun hθ) := by
  refine continuous_iff_continuousAt.2 fun ⟨l, b⟩ => ?_
  by_cases hl : (l : ℝ) = 0
  · show Tendsto _ _ (𝓝 (gBotFun hθ (l, b)))
    rw [gBotFun, if_pos hl, tendsto_subtype_rng, tendsto_subtype_rng]
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun q => ?_, fun a ha => ?_⟩
    · exact ha.trans_le ((gBotFun hθ q : Tau).2.1)
    · have hb : ((b : Tau) : ℝ) < 1 := b.2
      set c : ℝ := (((b : Tau) : ℝ) + 1) / 2 with hcdef
      have hbc : ((b : Tau) : ℝ) < c := by rw [hcdef]; linarith
      have hc1 : c < 1 := by rw [hcdef]; linarith
      have hcT : c ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [(b : Tau).2.1], hc1.le⟩
      obtain ⟨a₀, ha₀⟩ := base_tendsto_bot hθ (b := ⟨c, hcT⟩) hc1 (ε := a + 1) (by
        show (0 : ℝ) < a + 1
        have ha' : (-1 : ℝ) < a := ha
        linarith)
      have hopen : IsOpen {q : I × Ubot | ((q.1 : ℝ)) < Real.exp a₀ ∧
          (((q.2 : Tau) : ℝ)) < c} :=
        (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).inter
          (isOpen_lt (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
            continuous_const)
      refine Filter.eventually_of_mem (hopen.mem_nhds (x := (l, b))
        ⟨show (l : ℝ) < _ by rw [hl]; exact Real.exp_pos _, hbc⟩) fun q hq => ?_
      show ((gBotFun hθ q : Tau) : ℝ) < a
      unfold gBotFun
      split_ifs with hq0
      · show (-1 : ℝ) < a
        have : ((⟨Tau.bot, bot_mem_Ubot⟩ : Ubot) : Tau) = Tau.bot := rfl
        simpa [this, Tau.bot] using ha
      · have hpos : 0 < (q.1 : ℝ) := lt_of_le_of_ne q.1.2.1 (Ne.symm hq0)
        have hlog : Real.log q.1 ≤ a₀ := ((Real.log_lt_iff_lt_exp hpos).2 hq.1).le
        have h1 := base_mono hθ (b := (q.2 : Tau)) (b' := ⟨c, hcT⟩) hq.2.le (Real.log q.1)
        have h2 := ha₀ _ hlog
        show ((θ (Real.log q.1) (q.2 : Tau) : Tau) : ℝ) < a
        linarith
  · have hcont : ContinuousAt (fun q : I × Ubot =>
        θ.restrict (isInvariant_Ubot hθ) (Real.log q.1) q.2) (l, b) :=
      (θ.restrict (isInvariant_Ubot hθ)).cont'.continuousAt.comp
        (((Real.continuousAt_log hl).comp (x := (l, b)) (f := fun q : I × Ubot => (q.1 : ℝ))
          (continuous_subtype_val.comp continuous_fst).continuousAt).prodMk
            continuousAt_snd)
    refine hcont.congr ?_
    have hopen : IsOpen {q : I × Ubot | (q.1 : ℝ) ≠ 0} :=
      isOpen_ne_fun (continuous_subtype_val.comp continuous_fst) continuous_const
    filter_upwards [hopen.mem_nhds hl] with q hq
    show _ = gBotFun hθ q
    rw [gBotFun, if_neg hq]

theorem continuous_gTopFun : Continuous (gTopFun hθ) := by
  refine continuous_iff_continuousAt.2 fun ⟨l, b⟩ => ?_
  by_cases hl : (l : ℝ) = 0
  · show Tendsto _ _ (𝓝 (gTopFun hθ (l, b)))
    rw [gTopFun, if_pos hl, tendsto_subtype_rng, tendsto_subtype_rng]
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => Eventually.of_forall fun q => ?_⟩
    · have hb : -1 < ((b : Tau) : ℝ) := b.2
      set c : ℝ := (((b : Tau) : ℝ) - 1) / 2 with hcdef
      have hbc : c < ((b : Tau) : ℝ) := by rw [hcdef]; linarith [(b : Tau).2.2]
      have hc1 : -1 < c := by rw [hcdef]; linarith
      have hcT : c ∈ Icc (-1 : ℝ) 1 := ⟨hc1.le, by linarith [(b : Tau).2.2]⟩
      obtain ⟨a₀, ha₀⟩ := base_tendsto_top hθ (b := ⟨c, hcT⟩) hc1 (ε := 1 - a) (by
        show (0 : ℝ) < 1 - a
        have ha' : a < (1 : ℝ) := ha
        linarith)
      have hopen : IsOpen {q : I × Utop | ((q.1 : ℝ)) < Real.exp (-a₀) ∧
          c < (((q.2 : Tau) : ℝ))} :=
        (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).inter
          (isOpen_lt continuous_const
            (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))
      refine Filter.eventually_of_mem (hopen.mem_nhds (x := (l, b))
        ⟨show (l : ℝ) < _ by rw [hl]; exact Real.exp_pos _, hbc⟩) fun q hq => ?_
      show a < ((gTopFun hθ q : Tau) : ℝ)
      unfold gTopFun
      split_ifs with hq0
      · show a < (1 : ℝ)
        have : ((⟨Tau.top, top_mem_Utop⟩ : Utop) : Tau) = Tau.top := rfl
        simpa [this, Tau.top] using ha
      · have hpos : 0 < (q.1 : ℝ) := lt_of_le_of_ne q.1.2.1 (Ne.symm hq0)
        have hlog : a₀ ≤ -Real.log q.1 := by
          have := ((Real.log_lt_iff_lt_exp hpos).2 hq.1).le
          linarith
        have h1 := base_mono hθ (b := ⟨c, hcT⟩) (b' := (q.2 : Tau)) hq.2.le (-Real.log q.1)
        have h2 := ha₀ _ hlog
        show a < ((θ (-Real.log q.1) (q.2 : Tau) : Tau) : ℝ)
        linarith
    · exact ((gTopFun hθ q : Tau).2.2).trans_lt ha
  · have hcont : ContinuousAt (fun q : I × Utop =>
        θ.restrict (isInvariant_Utop hθ) (-Real.log q.1) q.2) (l, b) :=
      (θ.restrict (isInvariant_Utop hθ)).cont'.continuousAt.comp
        (((Real.continuousAt_log hl).comp (x := (l, b)) (f := fun q : I × Utop => (q.1 : ℝ))
          (continuous_subtype_val.comp continuous_fst).continuousAt).neg.prodMk
            continuousAt_snd)
    refine hcont.congr ?_
    have hopen : IsOpen {q : I × Utop | (q.1 : ℝ) ≠ 0} :=
      isOpen_ne_fun (continuous_subtype_val.comp continuous_fst) continuous_const
    filter_upwards [hopen.mem_nhds hl] with q hq
    show _ = gTopFun hθ q
    rw [gTopFun, if_neg hq]

/-- The base contraction onto the ultraviolet end. -/
noncomputable def contractionBot :
    SkewContraction (θ.restrict (isInvariant_Ubot hθ)) ⟨Tau.bot, bot_mem_Ubot⟩ where
  g := ⟨gBotFun hθ, continuous_gBotFun hθ⟩
  one b := by
    show gBotFun hθ (1, b) = b
    rw [gBotFun, if_neg (by norm_num), Icc.coe_one, Real.log_one, Flow.map_zero_apply]
  zero b := by
    show gBotFun hθ (0, b) = _
    unfold gBotFun
    exact if_pos rfl
  fix l := by
    show gBotFun hθ (l, _) = _
    unfold gBotFun
    split_ifs
    · rfl
    · exact Subtype.ext (base_bot hθ _)
  equivariant l t b := by
    show gBotFun hθ (l, _) = θ.restrict _ t (gBotFun hθ (l, b))
    unfold gBotFun
    split_ifs
    · exact (Subtype.ext (base_bot hθ t)).symm
    · rw [← Flow.map_add, ← Flow.map_add, add_comm]

/-- The base contraction onto the infrared end. -/
noncomputable def contractionTop :
    SkewContraction (θ.restrict (isInvariant_Utop hθ)) ⟨Tau.top, top_mem_Utop⟩ where
  g := ⟨gTopFun hθ, continuous_gTopFun hθ⟩
  one b := by
    show gTopFun hθ (1, b) = b
    rw [gTopFun, if_neg (by norm_num), Icc.coe_one, Real.log_one, neg_zero,
      Flow.map_zero_apply]
  zero b := by
    show gTopFun hθ (0, b) = _
    unfold gTopFun
    exact if_pos rfl
  fix l := by
    show gTopFun hθ (l, _) = _
    unfold gTopFun
    split_ifs
    · rfl
    · exact Subtype.ext (base_top hθ _)
  equivariant l t b := by
    show gTopFun hθ (l, _) = θ.restrict _ t (gTopFun hθ (l, b))
    unfold gTopFun
    split_ifs
    · exact (Subtype.ext (base_top hθ t)).symm
    · rw [← Flow.map_add, ← Flow.map_add, add_comm]

/-! #### Index pairs of the two ends -/

/-- `([-1, 0], {0})` is an index pair for the ultraviolet end. -/
theorem isIndexPair_bot :
    IsIndexPair θ {Tau.bot} {b : Tau | (b : ℝ) ≤ 0} {b : Tau | (b : ℝ) = 0} := by
  have hNc : IsClosed {b : Tau | (b : ℝ) ≤ 0} := isClosed_le continuous_subtype_val continuous_const
  have hInvN : Inv θ {b : Tau | (b : ℝ) ≤ 0} ⊆ {Tau.bot} := fun b hb => by
    by_contra hne
    have hlow : -1 < (b : ℝ) := lt_of_le_of_ne b.2.1 fun h => hne (Subtype.ext h.symm)
    obtain ⟨a₀, ha₀⟩ := base_tendsto_top hθ hlow (ε := 1 / 2) (by norm_num)
    have h1 := ha₀ a₀ le_rfl
    have h2 : (θ a₀ b : ℝ) ≤ 0 := hb a₀
    linarith
  have hbotO : Tau.bot ∈ interior ({b : Tau | (b : ℝ) ≤ 0} \ {b : Tau | (b : ℝ) = 0}) := by
    have hsub : {b : Tau | (b : ℝ) < 0} ⊆ {b : Tau | (b : ℝ) ≤ 0} \ {b : Tau | (b : ℝ) = 0} :=
      fun b hb => ⟨le_of_lt (show (b : ℝ) < 0 from hb), ne_of_lt (show (b : ℝ) < 0 from hb)⟩
    exact interior_maximal hsub (isOpen_lt continuous_subtype_val continuous_const)
      (show (-1 : ℝ) < 0 by norm_num)
  have hbotInv : {Tau.bot} ⊆ Inv θ (closure ({b : Tau | (b : ℝ) ≤ 0} \ {b : Tau | (b : ℝ) = 0})) :=
    by
      rintro _ rfl t
      rw [base_bot hθ]
      exact subset_closure (interior_subset hbotO)
  have hInv : Inv θ (closure ({b : Tau | (b : ℝ) ≤ 0} \ {b : Tau | (b : ℝ) = 0})) = {Tau.bot} :=
    Subset.antisymm ((Inv_mono (closure_minimal sdiff_subset hNc)).trans hInvN) hbotInv
  exact
    { isCompact_N := hNc.isCompact
      isCompact_L := (isClosed_eq continuous_subtype_val continuous_const).isCompact
      subset := fun b hb => le_of_eq hb
      isolating := ⟨isClosed_closure.isCompact, by
        rw [hInv, singleton_subset_iff]
        exact interior_mono subset_closure hbotO⟩
      inv_eq := hInv
      nhds := singleton_subset_iff.2 hbotO
      posInv := fun b hb t ht hseg => by
        rcases ht.eq_or_lt with rfl | ht
        · rw [Flow.map_zero_apply]; exact hb
        · have hb' : (b : ℝ) = 0 := hb
          have := hθ.strict b (by rw [hb']; norm_num) (by rw [hb']; norm_num) t ht
          have h2 : (θ t b : ℝ) ≤ 0 := hseg t ⟨ht.le, le_rfl⟩
          linarith
      exit := fun b hb t ht hout => by
        have hb' : (b : ℝ) ≤ 0 := hb
        have hout' : 0 < (θ t b : ℝ) := lt_of_not_ge hout
        obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc ht
          (continuous_subtype_val.comp (θ.continuous continuous_id continuous_const)).continuousOn
          (show (0 : ℝ) ∈ Icc ((θ 0 b : Tau) : ℝ) (θ t b : ℝ) by
            rw [Flow.map_zero_apply]; exact ⟨hb', hout'.le⟩)
        refine ⟨s, hs, fun r hr => ?_, hs0⟩
        show (θ r b : ℝ) ≤ 0
        have := hθ.monotone_flow b hr.2
        have hs0' : (θ s b : ℝ) = 0 := hs0
        linarith }

/-- `([0, 1], ∅)` is an index pair for the infrared end. -/
theorem isIndexPair_top : IsIndexPair θ {Tau.top} {b : Tau | 0 ≤ (b : ℝ)} ∅ := by
  have hNc : IsClosed {b : Tau | 0 ≤ (b : ℝ)} := isClosed_le continuous_const continuous_subtype_val
  have hInvN : Inv θ {b : Tau | 0 ≤ (b : ℝ)} ⊆ {Tau.top} := fun b hb => by
    by_contra hne
    have hhigh : (b : ℝ) < 1 := lt_of_le_of_ne b.2.2 fun h => hne (Subtype.ext h)
    obtain ⟨a₀, ha₀⟩ := base_tendsto_bot hθ hhigh (ε := 1 / 2) (by norm_num)
    have h1 := ha₀ a₀ le_rfl
    have h2 : 0 ≤ (θ a₀ b : ℝ) := hb a₀
    linarith
  have htopO : Tau.top ∈ interior ({b : Tau | 0 ≤ (b : ℝ)} \ ∅) := by
    rw [sdiff_empty]
    have hsub : {b : Tau | 0 < (b : ℝ)} ⊆ {b : Tau | 0 ≤ (b : ℝ)} :=
      fun b hb => le_of_lt (show (0 : ℝ) < b from hb)
    exact interior_maximal hsub (isOpen_lt continuous_const continuous_subtype_val)
      (show (0 : ℝ) < 1 by norm_num)
  have hcl : closure ({b : Tau | 0 ≤ (b : ℝ)} \ ∅) = {b : Tau | 0 ≤ (b : ℝ)} := by
    rw [sdiff_empty, hNc.closure_eq]
  have hInv : Inv θ (closure ({b : Tau | 0 ≤ (b : ℝ)} \ ∅)) = {Tau.top} := by
    rw [hcl]
    refine Subset.antisymm hInvN ?_
    rintro _ rfl t
    rw [base_top hθ]
    show (0 : ℝ) ≤ 1
    norm_num
  exact
    { isCompact_N := hNc.isCompact
      isCompact_L := isCompact_empty
      subset := empty_subset _
      isolating := ⟨isClosed_closure.isCompact, by
        rw [hInv, singleton_subset_iff]
        exact interior_mono subset_closure htopO⟩
      inv_eq := hInv
      nhds := singleton_subset_iff.2 htopO
      posInv := fun _ hb => absurd hb (notMem_empty _)
      exit := fun b hb t ht hout => absurd (show 0 ≤ (θ t b : ℝ) from
        le_trans hb (hθ.le_flow b ht)) hout }

end Base

/-! ### Fibers of skew products -/

section Fiber

variable {X B : Type*} [TopologicalSpace X] [TopologicalSpace B] [T2Space X] [T2Space B]
  {Φ : Flow ℝ (X × B)} {θ : Flow ℝ B} (hΦ : IsSkew Φ θ) {b₀ : B} (hfix : ∀ t, θ t b₀ = b₀)

/-- Lemma `lem:isolation`(a): the fiber of an isolating neighborhood over a fixed point of the
base isolates `K = {x : (x, b₀) ∈ S}` for the fiber flow. -/
theorem IsSkew.fiber_isolating {N : Set (X × B)} (hN : IsIsolatingNbhd Φ N) :
    IsIsolatingNbhd (fiberFlow hΦ b₀ hfix) ((fun x => (x, b₀)) ⁻¹' N) ∧
      Inv (fiberFlow hΦ b₀ hfix) ((fun x => (x, b₀)) ⁻¹' N) = {x | (x, b₀) ∈ Inv Φ N} := by
  have hc : Continuous fun x : X => (x, b₀) := continuous_id.prodMk continuous_const
  have hInv : Inv (fiberFlow hΦ b₀ hfix) ((fun x => (x, b₀)) ⁻¹' N) =
      {x | (x, b₀) ∈ Inv Φ N} := by
    ext x
    have e : ∀ t, Φ t (x, b₀) = ((Φ t (x, b₀)).1, b₀) := fun t =>
      Prod.ext rfl ((hΦ t _).trans (hfix t))
    exact forall_congr' fun t => by
      show ((Φ t (x, b₀)).1, b₀) ∈ N ↔ Φ t (x, b₀) ∈ N
      rw [← e t]
  refine ⟨⟨?_, ?_⟩, hInv⟩
  · refine (hN.1.image continuous_fst).of_isClosed_subset (hN.1.isClosed.preimage hc) ?_
    intro x hx
    exact ⟨(x, b₀), hx, rfl⟩
  · rw [hInv]
    intro x hx
    exact preimage_interior_subset_interior_preimage hc (hN.2 hx)

end Fiber

/-! ### The extended phase space -/

section Slab

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [TopologicalSpace.MetrizableSpace X]
  {Φ : Flow ℝ (X × Tau)} {θ : Flow ℝ Tau} (hΦ : IsSkew Φ θ)
  (hθ : IsHeight θ (fun b => (b : ℝ)))

include hΦ hθ in
/-- The coordinate `τ` is a height function on the extended phase space. -/
theorem IsSkew.isHeight : IsHeight Φ (fun p => (p.2 : ℝ)) where
  continuous := continuous_subtype_val.comp continuous_snd
  mem p := p.2.2
  fix p h t := by
    show ((Φ t p).2 : ℝ) = p.2
    rw [hΦ]
    exact hθ.fix p.2 h t
  strict p h1 h2 t ht := by
    show (p.2 : ℝ) < (Φ t p).2
    rw [hΦ]
    exact hθ.strict p.2 h1 h2 t ht

omit [TopologicalSpace X] [T2Space X] [TopologicalSpace.MetrizableSpace X] in
theorem deformBot_mem {s r : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (-1 : ℝ) 0) :
    (1 - s) * r ∈ Icc (-1 : ℝ) 0 := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hr0, hr1⟩ := hr
  constructor <;> nlinarith

omit [TopologicalSpace X] [T2Space X] [TopologicalSpace.MetrizableSpace X] in
theorem deformTop_mem {s r : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1) :
    r + s * (1 - r) ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hr0, hr1⟩ := hr
  constructor <;> nlinarith

/-- The deformation `b ↦ (1 - s) b` of `[-1, 0]` into `{0}`. -/
noncomputable def deformBot :
    C(I × (Subtype.val ⁻¹' {b : Tau | (b : ℝ) ≤ 0} : Set Ubot),
      (Subtype.val ⁻¹' {b : Tau | (b : ℝ) ≤ 0} : Set Ubot)) where
  toFun q :=
    have h := deformBot_mem q.1.2 ⟨((q.2 : Ubot) : Tau).2.1, q.2.2⟩
    ⟨⟨⟨(1 - (q.1 : ℝ)) * (((q.2 : Ubot) : Tau) : ℝ), h.1, h.2.trans (by norm_num)⟩,
      show _ < (1 : ℝ) from h.2.trans_lt (by norm_num)⟩, h.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _) _
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_snd)))

/-- The deformation `b ↦ b + s (1 - b)` of `[0, 1]` onto `1`. -/
noncomputable def deformTop :
    C(I × (Subtype.val ⁻¹' {b : Tau | 0 ≤ (b : ℝ)} : Set Utop),
      (Subtype.val ⁻¹' {b : Tau | 0 ≤ (b : ℝ)} : Set Utop)) where
  toFun q :=
    have h := deformTop_mem q.1.2 ⟨q.2.2, ((q.2 : Utop) : Tau).2.2⟩
    ⟨⟨⟨(((q.2 : Utop) : Tau) : ℝ) + (q.1 : ℝ) * (1 - (((q.2 : Utop) : Tau) : ℝ)),
      (by norm_num : (-1 : ℝ) ≤ 0).trans h.1, h.2⟩,
      show (-1 : ℝ) < _ from (by norm_num : (-1 : ℝ) < 0).trans_le h.1⟩, h.1⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _) _
    have hb : Continuous fun q : I × (Subtype.val ⁻¹' {b : Tau | 0 ≤ (b : ℝ)} : Set Utop) =>
        (((q.2 : Utop) : Tau) : ℝ) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_snd))
    exact hb.add ((continuous_subtype_val.comp continuous_fst).mul (continuous_const.sub hb))

include hΦ hθ in
/-- Proposition `prop:boundary`, `𝒮` row at `τ = -1`: `h_𝒮(K × {-1}) = 0̄`. -/
theorem slab_bot_indexTrivial {M : Set X}
    (hM : IsIsolatingNbhd (fiberFlow hΦ Tau.bot (base_bot hθ)) M) :
    IndexTrivial Φ (Inv (fiberFlow hΦ Tau.bot (base_bot hθ)) M ×ˢ {Tau.bot}) :=
  skew_indexTrivial hΦ (isInvariant_Ubot hθ) isOpen_Ubot bot_mem_Ubot (contractionBot hθ) hM
    (isIndexPair_bot hθ) (fun b (hb : (b : ℝ) ≤ 0) => show (b : ℝ) < 1 by linarith)
    deformBot
    (fun b => Subtype.ext (Subtype.ext (Subtype.ext (by
      show (1 - ((0 : I) : ℝ)) * _ = _
      simp))))
    (fun b => show (1 - ((1 : I) : ℝ)) * _ = (0 : ℝ) by simp)
    (fun s b (hb : (((b : Ubot) : Tau) : ℝ) = 0) =>
      show (1 - (s : ℝ)) * _ = (0 : ℝ) by rw [hb, mul_zero])

include hΦ hθ in
/-- Proposition `prop:boundary`, `𝒮` row at `τ = 1`: `h_𝒮(K × {1}) ≅ h_{f_+}(K)`. -/
theorem slab_top_hasIndex {M : Set X}
    (hM : IsIsolatingNbhd (fiberFlow hΦ Tau.top (base_top hθ)) M) {NK LK : Set X}
    (hK : IsIndexPair (fiberFlow hΦ Tau.top (base_top hθ))
      (Inv (fiberFlow hΦ Tau.top (base_top hθ)) M) NK LK) :
    HasIndex Φ (Inv (fiberFlow hΦ Tau.top (base_top hθ)) M ×ˢ {Tau.top}) (IndexSpace NK LK)
      (IndexSpace.pt _ _) :=
  skew_hasIndex hΦ (isInvariant_Utop hθ) isOpen_Utop top_mem_Utop (contractionTop hθ) hM
    (isIndexPair_top hθ) (fun b (hb : 0 ≤ (b : ℝ)) => show (-1 : ℝ) < b by linarith)
    (show (0 : ℝ) ≤ 1 by norm_num) deformTop
    (fun b => Subtype.ext (Subtype.ext (Subtype.ext (by
      show _ + ((0 : I) : ℝ) * _ = _
      simp))))
    (fun b => Subtype.ext (Subtype.ext (Subtype.ext (by
      show _ + ((1 : I) : ℝ) * _ = (1 : ℝ)
      simp)))) hK

variable (K : Type u) [Ring K]

include hΦ hθ in
/-- Theorem `thm:slab`. For an isolated invariant set `S` of the extended phase space,
`(K_+ × {1}, K_- × {-1})` is an attractor–repeller pair of `S`, `K_+ = {x : (x, 1) ∈ S}` is an
isolated invariant set of the infrared flow `f_+`, and `CH_*(K_+; f_+) ≅ CH_*(S)`. -/
theorem slab_index {S : Set (X × Tau)} (hS : IsIsolatedInvariantSet Φ S) :
    IsAttractorRepellerPair Φ S (S ∩ {p | (p.2 : ℝ) = 1}) (S ∩ {p | (p.2 : ℝ) = -1}) ∧
      ∃ hK : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ))
          {x | (x, Tau.top) ∈ S},
        ∀ n, Nonempty (homologyIndex K (fiberFlow hΦ Tau.top (base_top hθ)) hK n ≃ₗ[K]
          homologyIndex K Φ hS n) := by
  obtain ⟨N, hN, hNS⟩ := id hS
  have hAR := (hΦ.isHeight hθ).isAttractorRepellerPair hS
  refine ⟨hAR, ?_⟩
  obtain ⟨hMT, hInvT⟩ := hΦ.fiber_isolating (base_top hθ) hN
  obtain ⟨hMB, hInvB⟩ := hΦ.fiber_isolating (base_bot hθ) hN
  rw [hNS] at hInvT hInvB
  set fT := fiberFlow hΦ Tau.top (base_top hθ)
  set fB := fiberFlow hΦ Tau.bot (base_bot hθ)
  set MT := (fun x => (x, Tau.top)) ⁻¹' N
  set MB := (fun x => (x, Tau.bot)) ⁻¹' N
  have hK : IsIsolatedInvariantSet fT {x | (x, Tau.top) ∈ S} := ⟨MT, hMT, hInvT⟩
  refine ⟨hK, fun n => ?_⟩
  -- the repeller has trivial index
  have hRset : S ∩ (fun p : X × Tau => (p.2 : ℝ)) ⁻¹' {-1} = Inv fB MB ×ˢ {Tau.bot} := by
    rw [hInvB]
    ext ⟨x, b⟩
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_prod, mem_setOf_eq]
    constructor
    · rintro ⟨hx, hb⟩
      obtain rfl : b = Tau.bot := Subtype.ext hb
      exact ⟨hx, rfl⟩
    · rintro ⟨hx, rfl⟩
      exact ⟨hx, rfl⟩
  have hRt : ∀ n, Subsingleton (homologyIndex K Φ hAR.isolated_R n) := by
    intro n
    obtain ⟨NR, LR, hPR, hcR⟩ := slab_bot_indexTrivial hΦ hθ hMB
    rw [← hRset] at hPR
    obtain ⟨iso⟩ := homologyIndexIso K hAR.isolated_R hPR n
    haveI := redH_subsingleton K hcR n
    exact iso.toLinearEquiv.toEquiv.subsingleton
  obtain ⟨i, hi⟩ := homologyIndex_attractor_iso_of_pair K hAR hRt
  -- the attractor has the index of `K_+`
  have hAset : S ∩ (fun p : X × Tau => (p.2 : ℝ)) ⁻¹' {1} = Inv fT MT ×ˢ {Tau.top} := by
    rw [hInvT]
    ext ⟨x, b⟩
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_prod, mem_setOf_eq]
    constructor
    · rintro ⟨hx, hb⟩
      obtain rfl : b = Tau.top := Subtype.ext hb
      exact ⟨hx, rfl⟩
    · rintro ⟨hx, rfl⟩
      exact ⟨hx, rfl⟩
  obtain ⟨NK, LK, hPK, -⟩ := exists_indexPair_of_t2 hMT
  obtain ⟨NA, LA, hPA, ⟨e⟩⟩ := slab_top_hasIndex hΦ hθ hMT hPK
  rw [← hAset] at hPA
  rw [hInvT] at hPK
  obtain ⟨iso₁⟩ := homologyIndexIso K hAR.isolated_A hPA n
  obtain ⟨iso₃⟩ := homologyIndexIso K hK hPK n
  exact ⟨(iso₃.toLinearEquiv.trans ((redIso K e n).symm.toLinearEquiv.trans
    iso₁.symm.toLinearEquiv)).trans (LinearEquiv.ofBijective _ (hi n))⟩

end Slab

end ConleyCheck.Conley
