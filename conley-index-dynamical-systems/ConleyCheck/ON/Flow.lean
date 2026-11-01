import ConleyCheck.ON.Model
import ConleyCheck.ODE.Fence
import ConleyCheck.Conley.IsolatingBlock
import ConleyCheck.Conley.Skew
import ConleyCheck.Conley.HomologyIndex

/-!
# The flow of the `O(N)`-type model: Proposition `prop:ON`(a), (c) and Lemma `lem:ONstructure`(iv)

The field `eq:ONy` is multiplied by a smooth bump function equal to `1` on the unit square, which
gives a bounded, globally Lipschitz field and hence a global flow `flowON N`. It agrees with
`eq:ONy` on a neighborhood of the block `R`, so the block, its invariant set and its index are those
of `eq:ONy`.

* `bounded_sol_mem`: every bounded full solution of `eq:ONy` lies in
  `[-1/9, 0] × [-1/(N+2), 0]`. Each of the four bounds is a growth argument: if it fails at some
  time, one coordinate grows at least linearly in forward or backward time.
* `prop_ON_a`: `R` is an isolating block with exit set `L`, and `Inv(R) = B_N ⊆ [-1/9,0] × [-1/(N+2),0]`.
* `prop_ON_c`: `h(B_N) = 0̄`, and the homology index vanishes.
-/

open Set Filter Topology Metric
open scoped NNReal unitInterval

namespace ConleyCheck.ON

open ConleyCheck.Conley ConleyCheck.ODE

/-! ## Bounded solutions of `eq:ONy` -/

/-- The vector field `eq:ONy` on `ℝ × ℝ`. -/
def field (N : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (f₁ N p.1 p.2, f₂ N p.1 p.2)

theorem sol_fst {N : ℝ} {γ : ℝ → ℝ × ℝ} (hγ : IsSol (field N) γ) (t : ℝ) :
    HasDerivAt (fun s => (γ s).1) (f₁ N (γ t).1 (γ t).2) t := by
  have h := (hasFDerivAt_fst (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t (hγ t)
  exact h

theorem sol_snd {N : ℝ} {γ : ℝ → ℝ × ℝ} (hγ : IsSol (field N) γ) (t : ℝ) :
    HasDerivAt (fun s => (γ s).2) (f₂ N (γ t).1 (γ t).2) t := by
  have h := (hasFDerivAt_snd (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t (hγ t)
  exact h

theorem bounded_coords {γ : ℝ → ℝ × ℝ} (hb : Bornology.IsBounded (range γ)) :
    ∃ M, ∀ t, |(γ t).1| ≤ M ∧ |(γ t).2| ≤ M := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
  refine ⟨M, fun t => ?_⟩
  have := norm_prod_le_iff.1 (hM _ (mem_range_self t))
  simpa only [Real.norm_eq_abs] using this

/-- Lemma `lem:ONstructure`(iv) for bounded solutions, `y₁ ≥ -1/9`. -/
theorem bounded_sol_fst_ge {N : ℝ} (hN : 1 < N) {γ : ℝ → ℝ × ℝ} (hγ : IsSol (field N) γ)
    (hb : Bornology.IsBounded (range γ)) (t₀ : ℝ) : -1 / 9 ≤ (γ t₀).1 := by
  obtain ⟨M, hM⟩ := bounded_coords hb
  by_contra hlt
  push Not at hlt
  set a := -(γ t₀).1
  have ha : 1 / 9 < a := by simp only [a]; linarith
  have hG : ∀ t, HasDerivAt (fun s => -(γ s).1) (-f₁ N (γ t).1 (γ t).2) t :=
    fun t => (sol_fst hγ t).neg
  refine no_growth_fwd hG (t₀ := t₀) (M := M) (c := a * (9 * a - 1)) (by nlinarith)
    (fun t _ hat => ?_) (fun t => by linarith [(abs_le.1 (hM t).1).1])
  have h1 := blowup_x (N := N) (y₁ := (γ t).1) (y₂ := (γ t).2) hN.le
  have : a ≤ -(γ t).1 := hat
  nlinarith

/-- Bounded solutions have `y₁ ≤ 0`. -/
theorem bounded_sol_fst_le {N : ℝ} (hN : 1 < N) {γ : ℝ → ℝ × ℝ} (hγ : IsSol (field N) γ)
    (hb : Bornology.IsBounded (range γ)) (t₀ : ℝ) : (γ t₀).1 ≤ 0 := by
  obtain ⟨M, hM⟩ := bounded_coords hb
  by_contra hlt
  push Not at hlt
  refine no_growth_bwd (sol_fst hγ) (t₀ := t₀) (c := (γ t₀).1) hlt (fun t _ hat => ?_)
    (fun t => (abs_le.1 (hM t).1).2)
  simp only [f₁]
  have : 0 ≤ (N - 1) * (γ t).2 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  nlinarith

/-- Bounded solutions have `y₂ ≤ 0`. -/
theorem bounded_sol_snd_le {N : ℝ} (hN : 1 < N) {γ : ℝ → ℝ × ℝ} (hγ : IsSol (field N) γ)
    (hb : Bornology.IsBounded (range γ)) (t₀ : ℝ) : (γ t₀).2 ≤ 0 := by
  obtain ⟨M, hM⟩ := bounded_coords hb
  by_contra hlt
  push Not at hlt
  refine no_growth_bwd (sol_snd hγ) (t₀ := t₀) (c := (γ t₀).2 / 3) (by positivity)
    (fun t _ hat => ?_) (fun t => (abs_le.1 (hM t).2).2)
  have h1 := bounded_sol_fst_ge hN hγ hb t
  have hy : 0 < (γ t).2 := lt_of_lt_of_le hlt hat
  simp only [f₂]
  have : 0 ≤ (γ t).2 * (6 * (γ t).1 + 2 / 3) := mul_nonneg hy.le (by linarith)
  have : 0 ≤ (N + 2) * (γ t).2 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  nlinarith

/-- Lemma `lem:ONstructure`(iv) for bounded solutions, `y₂ ≥ -1/(N+2)`. -/
theorem bounded_sol_snd_ge {N : ℝ} (hN : 1 < N) {γ : ℝ → ℝ × ℝ} (hγ : IsSol (field N) γ)
    (hb : Bornology.IsBounded (range γ)) (t₀ : ℝ) : -1 / (N + 2) ≤ (γ t₀).2 := by
  obtain ⟨M, hM⟩ := bounded_coords hb
  have hk : 0 < N + 2 := by linarith
  by_contra hlt
  push Not at hlt
  set a := -(γ t₀).2
  have ha : 1 < a * (N + 2) := by
    have : 1 / (N + 2) < a := by simp only [a]; rw [neg_div] at hlt; linarith
    exact (div_lt_iff₀ hk).1 this
  have ha0 : 0 < a := by nlinarith
  have hG : ∀ t, HasDerivAt (fun s => -(γ s).2) (-f₂ N (γ t).1 (γ t).2) t :=
    fun t => (sol_snd hγ t).neg
  refine no_growth_fwd hG (t₀ := t₀) (M := M) (c := a * ((N + 2) * a - 1)) (by nlinarith)
    (fun t _ hat => ?_) (fun t => by linarith [(abs_le.1 (hM t).2).1])
  have h1 := blowup_w_ge (N := N) (bounded_sol_fst_le hN hγ hb t) (bounded_sol_snd_le hN hγ hb t)
  have : a ≤ -(γ t).2 := hat
  have : 0 ≤ (-(γ t).2 - a) * ((N + 2) * (-(γ t).2 + a) - 1) :=
    mul_nonneg (by linarith) (by nlinarith)
  nlinarith

/-- Every bounded full solution of `eq:ONy` lies in `[-1/9, 0] × [-1/(N+2), 0]`. -/
theorem bounded_sol_mem {N : ℝ} (hN : 1 < N) {γ : ℝ → ℝ × ℝ} (hγ : IsSol (field N) γ)
    (hb : Bornology.IsBounded (range γ)) (t : ℝ) :
    γ t ∈ Icc (-1 / 9 : ℝ) 0 ×ˢ Icc (-1 / (N + 2)) 0 :=
  ⟨⟨bounded_sol_fst_ge hN hγ hb t, bounded_sol_fst_le hN hγ hb t⟩,
    ⟨bounded_sol_snd_ge hN hγ hb t, bounded_sol_snd_le hN hγ hb t⟩⟩

/-! ## The cut-off field and its flow -/

/-- A smooth bump on `ℝ × ℝ`, equal to `1` on the closed unit ball (the square `[-1, 1]²`). -/
noncomputable def bump : ContDiffBump (0 : ℝ × ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cut-off field, equal to `eq:ONy` on `[-1, 1]²`. -/
noncomputable def cutField (N : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := bump p • field N p

theorem contDiff_field (N : ℝ) : ContDiff ℝ 1 (field N) := by
  unfold field f₁ f₂
  fun_prop

theorem cutField_eq {N : ℝ} {p : ℝ × ℝ} (hp : ‖p‖ ≤ 1) : cutField N p = field N p := by
  have : bump p = 1 := bump.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hp)
  simp [cutField, this]

theorem contDiff_cutField (N : ℝ) : ContDiff ℝ 1 (cutField N) :=
  bump.contDiff.smul (contDiff_field N)

theorem hasCompactSupport_cutField (N : ℝ) : HasCompactSupport (cutField N) :=
  bump.hasCompactSupport.smul_right

theorem exists_lipschitz_cutField (N : ℝ) : ∃ K : ℝ≥0, LipschitzWith K (cutField N) :=
  ContDiff.lipschitzWith_of_hasCompactSupport (hasCompactSupport_cutField N)
    (contDiff_cutField N) one_ne_zero

theorem exists_bound_cutField (N : ℝ) : ∃ L : ℝ≥0, ∀ x, ‖cutField N x‖ ≤ L := by
  obtain ⟨C, hC⟩ := (hasCompactSupport_cutField N).exists_bound_of_continuous
    (contDiff_cutField N).continuous
  exact ⟨⟨max C 0, le_max_right _ _⟩, fun x => (hC x).trans (le_max_left _ _)⟩

/-- The global flow of the cut-off `O(N)` field. -/
noncomputable def flowON (N : ℝ) : Flow ℝ (ℝ × ℝ) :=
  flowOf (exists_lipschitz_cutField N).choose_spec (exists_bound_cutField N).choose_spec

theorem hasDerivAt_flowON (N : ℝ) (x : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun s => flowON N s x) (cutField N (flowON N t x)) t :=
  hasDerivAt_flowOf _ _ x t

theorem flowON_eq_of_isSol (N : ℝ) {γ : ℝ → ℝ × ℝ} (hγ : IsSol (cutField N) γ) (t₀ t : ℝ) :
    flowON N t (γ t₀) = γ (t + t₀) :=
  flowOf_eq_of_isSol _ _ hγ t₀ t

theorem hasDerivAt_flowON_fst {N : ℝ} {x : ℝ × ℝ} (hx : ‖x‖ ≤ 1) :
    HasDerivAt (fun s => (flowON N s x).1) (f₁ N x.1 x.2) 0 := by
  have h := hasFDerivAt_fst.comp_hasDerivAt 0 (hasDerivAt_flowON N x 0)
  rw [Flow.map_zero_apply, cutField_eq hx] at h
  exact h

theorem hasDerivAt_flowON_snd {N : ℝ} {x : ℝ × ℝ} (hx : ‖x‖ ≤ 1) :
    HasDerivAt (fun s => (flowON N s x).2) (f₂ N x.1 x.2) 0 := by
  have h := hasFDerivAt_snd.comp_hasDerivAt 0 (hasDerivAt_flowON N x 0)
  rw [Flow.map_zero_apply, cutField_eq hx] at h
  exact h

/-! ## Faces of the block -/

/-- The block `R = [-1/8, δ] × [-1/2, δ]` of `eq:ONblock`. -/
def blockR : Set (ℝ × ℝ) := Icc (-1 / 8 : ℝ) δ ×ˢ Icc (-1 / 2 : ℝ) δ

/-- Its exit set `L`, two adjacent sides of `R`. -/
def blockL : Set (ℝ × ℝ) :=
  ({-1 / 8} : Set ℝ) ×ˢ Icc (-1 / 2 : ℝ) δ ∪ Icc (-1 / 8 : ℝ) δ ×ˢ ({-1 / 2} : Set ℝ)

theorem norm_le_one_of_mem_R {x : ℝ × ℝ} (hx : x ∈ blockR) : ‖x‖ ≤ 1 := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
  simp only [δ] at h2 h4
  refine norm_prod_le_iff.2 ⟨?_, ?_⟩ <;> rw [Real.norm_eq_abs, abs_le] <;>
    constructor <;> linarith

theorem interior_R : interior blockR = Ioo (-1 / 8 : ℝ) δ ×ˢ Ioo (-1 / 2 : ℝ) δ := by
  rw [blockR, interior_prod_eq, interior_Icc, interior_Icc]

theorem mem_R_of_mem_L {x : ℝ × ℝ} (hx : x ∈ blockL) : x ∈ blockR := by
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [mem_singleton_iff] at h1
    exact ⟨⟨h1.ge, by rw [h1]; norm_num [δ]⟩, h2⟩
  · rw [mem_singleton_iff] at h2
    exact ⟨h1, ⟨h2.ge, by rw [h2]; norm_num [δ]⟩⟩

section Faces

variable {N : ℝ} {c : ℝ → ℝ × ℝ} {x : ℝ × ℝ}

/-- Strict exit through `L` of any curve whose velocity at time `0` is that of `eq:ONy`. -/
theorem R_exit (hN : 1 < N) (hx : x ∈ blockL) (h0 : c 0 = x)
    (h1 : HasDerivAt (fun s => (c s).1) (f₁ N x.1 x.2) 0)
    (h2 : HasDerivAt (fun s => (c s).2) (f₂ N x.1 x.2) 0) :
    ∃ ε > 0, ∀ t ∈ Ioo 0 ε, c t ∉ blockR := by
  have hxR := mem_R_of_mem_L hx
  have hout : ∀ᶠ s in 𝓝[>] (0 : ℝ), c s ∉ blockR := by
    rcases hx with ⟨h1', -⟩ | ⟨-, h2'⟩
    · rw [mem_singleton_iff] at h1'
      have hd : f₁ N x.1 x.2 < 0 := by rw [h1']; exact face_left hN
      filter_upwards [(eventually_sign h1 hd).1] with s hs hR
      rw [h0, h1'] at hs
      exact absurd hR.1.1 (not_le.2 hs)
    · rw [mem_singleton_iff] at h2'
      have hd : f₂ N x.1 x.2 < 0 := by rw [h2']; exact face_bottom hN hxR.1.2
      filter_upwards [(eventually_sign h2 hd).1] with s hs hR
      rw [h0, h2'] at hs
      exact absurd hR.2.1 (not_le.2 hs)
  obtain ⟨ε, hε, -, h⟩ := exists_eps (P := fun _ => True) (Eventually.of_forall fun _ => trivial)
    hout
  exact ⟨ε, hε, h⟩

/-- Strict entrance through the rest of the boundary of `R`, for any curve whose velocity at
time `0` is that of `eq:ONy`. -/
theorem R_entrance (hN : 1 < N) (hxR : x ∈ blockR) (hint : x ∉ interior blockR) (hL : x ∉ blockL)
    (h0 : c 0 = x) (h1 : HasDerivAt (fun s => (c s).1) (f₁ N x.1 x.2) 0)
    (h2 : HasDerivAt (fun s => (c s).2) (f₂ N x.1 x.2) 0) :
    ∃ ε > 0, (∀ t ∈ Ioo (-ε) 0, c t ∉ blockR) ∧ ∀ t ∈ Ioo 0 ε, c t ∈ blockR := by
  obtain ⟨⟨h1a, h1b⟩, h2a, h2b⟩ := hxR
  have h1a' : -1 / 8 < x.1 := lt_of_le_of_ne h1a fun h => hL (Or.inl ⟨h.symm, h2a, h2b⟩)
  have h2a' : -1 / 2 < x.2 := lt_of_le_of_ne h2a fun h => hL (Or.inr ⟨⟨h1a, h1b⟩, h.symm⟩)
  rw [interior_R] at hint
  have hface : x.1 = δ ∨ x.2 = δ := by
    by_contra hc
    push Not at hc
    exact hint ⟨⟨h1a', lt_of_le_of_ne h1b hc.1⟩, h2a', lt_of_le_of_ne h2b hc.2⟩
  have hd1 : x.1 = δ → f₁ N x.1 x.2 < 0 := fun h => by rw [h]; exact face_right hN
  have hd2 : x.2 = δ → f₂ N x.1 x.2 < 0 := fun h => by
    rw [h]; have := face_top hN h1a; have : (0 : ℝ) < δ := by norm_num [δ]
    linarith
  have hback : ∀ᶠ s in 𝓝[<] (0 : ℝ), c s ∉ blockR := by
    rcases hface with h | h
    · filter_upwards [(eventually_sign h1 (hd1 h)).2] with s hs hR
      rw [h0, h] at hs
      exact absurd hR.1.2 (not_le.2 hs)
    · filter_upwards [(eventually_sign h2 (hd2 h)).2] with s hs hR
      rw [h0, h] at hs
      exact absurd hR.2.2 (not_le.2 hs)
  have hfwd : ∀ᶠ s in 𝓝[>] (0 : ℝ), c s ∈ blockR := by
    have e1 := eventually_mem_Icc h1 (a := -1 / 8) (b := δ)
      (by rw [h0]; exact h1a') (by rw [h0]; exact h1b)
      (by rw [h0]; exact hd1)
    have e2 := eventually_mem_Icc h2 (a := -1 / 2) (b := δ)
      (by rw [h0]; exact h2a') (by rw [h0]; exact h2b)
      (by rw [h0]; exact hd2)
    filter_upwards [e1, e2] with s h1 h2 using ⟨h1, h2⟩
  exact exists_eps hback hfwd

end Faces

theorem isClosed_L : IsClosed blockL :=
  (isClosed_singleton.prod isClosed_Icc).union (isClosed_Icc.prod isClosed_singleton)

/-- Proposition `prop:ON`(a), first part: `R` is an isolating block with exit set `L`. -/
theorem isBlock_R {N : ℝ} (hN : 1 < N) : IsBlock (flowON N) blockR blockL where
  isCompact := isCompact_Icc.prod isCompact_Icc
  isClosed_L := isClosed_L
  subset _ := mem_R_of_mem_L
  exit x hx := by
    have hn := norm_le_one_of_mem_R (mem_R_of_mem_L hx)
    exact R_exit hN hx (Flow.map_zero_apply _ _) (hasDerivAt_flowON_fst hn)
      (hasDerivAt_flowON_snd hn)
  entrance x hxR hint hL := by
    have hn := norm_le_one_of_mem_R hxR
    exact R_entrance hN hxR hint hL (Flow.map_zero_apply _ _) (hasDerivAt_flowON_fst hn)
      (hasDerivAt_flowON_snd hn)

/-! ## `Inv(R) = B_N` -/

/-- `B_N`, the union of all bounded full orbits of `eq:ONy`. -/
def boundedOrbits (N : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ γ : ℝ → ℝ × ℝ, IsSol (field N) γ ∧ Bornology.IsBounded (range γ) ∧ p ∈ range γ}

theorem inner_subset_R {N : ℝ} (hN : 1 < N) :
    Icc (-1 / 9 : ℝ) 0 ×ˢ Icc (-1 / (N + 2)) 0 ⊆ interior blockR := by
  obtain ⟨h1, h2, h3⟩ := inner_rect_in_interior hN
  rw [interior_R]
  rintro x ⟨⟨a, b⟩, c, d⟩
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem boundedOrbits_subset {N : ℝ} (hN : 1 < N) :
    boundedOrbits N ⊆ Icc (-1 / 9 : ℝ) 0 ×ˢ Icc (-1 / (N + 2)) 0 := by
  rintro _ ⟨γ, hγ, hb, t, rfl⟩
  exact bounded_sol_mem hN hγ hb t

theorem Inv_R_eq {N : ℝ} (hN : 1 < N) : Inv (flowON N) blockR = boundedOrbits N := by
  ext x
  constructor
  · intro hx
    refine ⟨fun t => flowON N t x, fun t => ?_, ?_, 0, Flow.map_zero_apply _ _⟩
    · rw [← cutField_eq (norm_le_one_of_mem_R (hx t))]
      exact hasDerivAt_flowON N x t
    · exact (isCompact_Icc.prod isCompact_Icc).isBounded.subset (range_subset_iff.2 hx)
  · rintro ⟨γ, hγ, hb, t₀, rfl⟩ t
    have hin : ∀ s, γ s ∈ blockR := fun s =>
      interior_subset (inner_subset_R hN (bounded_sol_mem hN hγ hb s))
    have hγ' : IsSol (cutField N) γ := fun s => by
      rw [cutField_eq (norm_le_one_of_mem_R (hin s))]
      exact hγ s
    rw [flowON_eq_of_isSol N hγ' t₀ t]
    exact hin _

/-- Proposition `prop:ON`(a). -/
theorem prop_ON_a {N : ℝ} (hN : 1 < N) :
    IsBlock (flowON N) blockR blockL ∧ Inv (flowON N) blockR = boundedOrbits N ∧
      boundedOrbits N ⊆ Icc (-1 / 9 : ℝ) 0 ×ˢ Icc (-1 / (N + 2)) 0 :=
  ⟨isBlock_R hN, Inv_R_eq hN, boundedOrbits_subset hN⟩

/-- The flow `flowON N` is the flow of `eq:ONy` on a neighborhood of `R`. -/
theorem cutField_eq_on_R {N : ℝ} {x : ℝ × ℝ} (hx : x ∈ blockR) : cutField N x = field N x :=
  cutField_eq (norm_le_one_of_mem_R hx)

/-! ## Proposition `prop:ON`(c): the index of `B_N` is trivial -/

theorem retract_mem {s b : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (-1 / 2 : ℝ) δ) :
    b - s * (b + 1 / 2) ∈ Icc (-1 / 2 : ℝ) δ := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hb0, hb1⟩ := hb
  constructor <;> nlinarith

/-- The deformation `b ↦ b - s (b + 1/2)` of `[-1/2, δ]` onto `-1/2`. -/
noncomputable def retractH : C(I × Icc (-1 / 2 : ℝ) δ, Icc (-1 / 2 : ℝ) δ) where
  toFun q := ⟨(q.2 : ℝ) - (q.1 : ℝ) * ((q.2 : ℝ) + 1 / 2), retract_mem q.1.2 q.2.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have hb : Continuous fun q : I × Icc (-1 / 2 : ℝ) δ => (q.2 : ℝ) :=
      continuous_subtype_val.comp continuous_snd
    exact hb.sub ((continuous_subtype_val.comp continuous_fst).mul (hb.add continuous_const))

theorem pointedContractible_R :
    PointedContractible (IndexSpace blockR blockL) (IndexSpace.pt blockR blockL) :=
  IndexSpace.prod_pointedContractible (X := ℝ) (B := ℝ) (N₁ := Icc (-1 / 8 : ℝ) δ)
    (L₁ := {-1 / 8}) (N₂ := Icc (-1 / 2 : ℝ) δ) (L₂ := {-1 / 2}) retractH
    (fun b => Subtype.ext (by simp [retractH]))
    (fun b => show (b : ℝ) - ((1 : I) : ℝ) * ((b : ℝ) + 1 / 2) = -1 / 2 by
      simp only [Set.Icc.coe_one, one_mul]; ring)
    (fun s b (hb : (b : ℝ) = -1 / 2) =>
      show (b : ℝ) - (s : ℝ) * ((b : ℝ) + 1 / 2) = -1 / 2 by rw [hb]; ring)

theorem isIndexPair_R {N : ℝ} (hN : 1 < N) :
    IsIndexPair (flowON N) (boundedOrbits N) blockR blockL := by
  rw [← Inv_R_eq hN]
  exact (isBlock_R hN).isIndexPair

theorem isIsolatedInvariantSet_B {N : ℝ} (hN : 1 < N) :
    IsIsolatedInvariantSet (flowON N) (boundedOrbits N) :=
  (isIndexPair_R hN).isIsolatedInvariantSet

/-- Proposition `prop:ON`(c): `h(B_N) = 0̄`, and so `CH_*(B_N) = 0` over any ring. -/
theorem prop_ON_c {N : ℝ} (hN : 1 < N) (K : Type) [Ring K] :
    IndexTrivial (flowON N) (boundedOrbits N) ∧
      ∀ k, Subsingleton (homologyIndex K (flowON N) (isIsolatedInvariantSet_B hN) k) := by
  refine ⟨⟨_, _, isIndexPair_R hN, pointedContractible_R⟩, fun k => ?_⟩
  obtain ⟨iso⟩ := homologyIndexIso K (isIsolatedInvariantSet_B hN) (isIndexPair_R hN) k
  have := redH_subsingleton K pointedContractible_R k
  exact iso.toLinearEquiv.toEquiv.subsingleton

end ConleyCheck.ON
