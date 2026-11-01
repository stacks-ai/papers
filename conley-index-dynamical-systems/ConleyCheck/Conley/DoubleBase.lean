import ConleyCheck.Conley.Slab
import ConleyCheck.Conley.Suspension

/-!
# The base of the double

The double `𝒟 = X × S¹` of the paper has base flow `θ̇ = G(θ)` with an attractor at `θ = 0` (IR)
and a repeller at `θ = π` (UV), and `q(x, θ) = (x, cos θ)` semiconjugates it onto the extended phase
space. We work on the lift of the circle to the interval `u ∈ [-1, 2]`, with `u = θ/π`. The tent
map `tent : [-1, 2] → [-1, 1]` plays the role of `cos θ`. It is `1 - 2u` on the upper sheet
`[0, 1]`, `1 + 2u` on `[-1, 0]` and `2u - 3` on `[1, 2]`, the latter two being the two halves of the
lower sheet adjacent to the arc `A_η = [-η, 1 + η]`. The base flow `dblFlow` is the lift of the base
flow of the extended phase space through the three branches of `tent`, so that `tent` is a
semiconjugacy (`tentT_dblFlow`, lemma `lem:double`(a)).

The IR point `u = 0` is a two-sided attractor and the UV point `u = 1` a two-sided repeller. We give
the base contractions (`contraction0`, `contraction1`), the base index pairs (`isIndexPair0`,
`isIndexPair1`), and the interval chart of `([1/2, 3/2], {1/2, 3/2})` (`chart1`), which are the
inputs of `skew_hasIndex` and `skew_suspension`.
-/

namespace ConleyCheck.Conley

open Set Filter Topology unitInterval

/-- The lifted base `[-1, 2]` of the double. -/
abbrev Dbl : Type := Icc (-1 : ℝ) 2

namespace Dbl

/-- The IR point `θ = 0`. -/
def zero : Dbl := ⟨0, by norm_num, by norm_num⟩

/-- The UV point `θ = π`. -/
def one : Dbl := ⟨1, by norm_num, by norm_num⟩

end Dbl

/-! ### The tent map and its branches -/

/-- The tent map, the analogue of `cos θ`. -/
noncomputable def tent (u : ℝ) : ℝ := 1 - 2 * min |u| |u - 2|

theorem tent_of_le_zero {u : ℝ} (hu : u ≤ 0) : tent u = 1 + 2 * u := by
  rw [tent, abs_of_nonpos hu, abs_of_nonpos (by linarith : u - 2 ≤ 0), min_eq_left (by linarith)]
  ring

theorem tent_of_mem {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : tent u = 1 - 2 * u := by
  rw [tent, abs_of_nonneg h0, abs_of_nonpos (by linarith : u - 2 ≤ 0), min_eq_left (by linarith)]

theorem tent_of_one_le {u : ℝ} (h1 : 1 ≤ u) (h2 : u ≤ 2) : tent u = 2 * u - 3 := by
  rw [tent, abs_of_nonneg (by linarith : 0 ≤ u), abs_of_nonpos (by linarith : u - 2 ≤ 0),
    min_eq_right (by linarith)]
  ring

theorem continuous_tent : Continuous tent :=
  continuous_const.sub (continuous_const.mul (continuous_abs.min
    (continuous_abs.comp (continuous_id.sub continuous_const))))

theorem tent_mem (u : Dbl) : tent u ∈ Icc (-1 : ℝ) 1 := by
  obtain ⟨u, h1, h2⟩ := u
  by_cases h0 : u ≤ 0
  · rw [tent_of_le_zero h0]; constructor <;> linarith
  by_cases h1' : u ≤ 1
  · rw [tent_of_mem (by linarith) h1']; constructor <;> linarith
  · rw [tent_of_one_le (by linarith) h2]; constructor <;> linarith

/-- The tent map `[-1, 2] → [-1, 1]`. -/
noncomputable def tentT (u : Dbl) : Tau := ⟨tent u, tent_mem u⟩

theorem continuous_tentT : Continuous tentT :=
  (continuous_tent.comp continuous_subtype_val).subtype_mk _

theorem tentT_zero : tentT Dbl.zero = Tau.top := Subtype.ext (by
  show tent 0 = 1
  rw [tent_of_le_zero le_rfl]; norm_num)

theorem tentT_one : tentT Dbl.one = Tau.bot := Subtype.ext (by
  show tent 1 = -1
  rw [tent_of_mem zero_le_one le_rfl]; norm_num)

/-- The branch of `tent⁻¹` with values in `[-1, 0]`. -/
noncomputable def br₀ (τ : ℝ) : ℝ := (τ - 1) / 2

/-- The branch with values in `[0, 1]`, the upper sheet. -/
noncomputable def br₁ (τ : ℝ) : ℝ := (1 - τ) / 2

/-- The branch with values in `[1, 2]`. -/
noncomputable def br₂ (τ : ℝ) : ℝ := (τ + 3) / 2

theorem tent_br₀ {τ : ℝ} (h : τ ≤ 1) : tent (br₀ τ) = τ := by
  rw [tent_of_le_zero (by unfold br₀; linarith), br₀]; ring

theorem tent_br₁ {τ : ℝ} (h : τ ∈ Icc (-1 : ℝ) 1) : tent (br₁ τ) = τ := by
  rw [tent_of_mem (by unfold br₁; linarith [h.2]) (by unfold br₁; linarith [h.1]), br₁]; ring

theorem tent_br₂ {τ : ℝ} (h : τ ∈ Icc (-1 : ℝ) 1) : tent (br₂ τ) = τ := by
  rw [tent_of_one_le (by unfold br₂; linarith [h.1]) (by unfold br₂; linarith [h.2]), br₂]; ring

theorem br₀_tent {u : ℝ} (h : u ≤ 0) : br₀ (tent u) = u := by
  rw [tent_of_le_zero h, br₀]; ring

theorem br₁_tent {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : br₁ (tent u) = u := by
  rw [tent_of_mem h0 h1, br₁]; ring

theorem br₂_tent {u : ℝ} (h : 1 ≤ u) (h2 : u ≤ 2) : br₂ (tent u) = u := by
  rw [tent_of_one_le h h2, br₂]; ring

/-! ### The base flow -/

section Flow

variable {θ : Flow ℝ Tau}

/-- The lifted base flow, as a real-valued function. -/
noncomputable def dblFun (θ : Flow ℝ Tau) (t : ℝ) (u : Dbl) : ℝ :=
  if (u : ℝ) ≤ 0 then br₀ (θ t (tentT u))
  else if (u : ℝ) ≤ 1 then br₁ (θ t (tentT u)) else br₂ (θ t (tentT u))

theorem dblFun_mem (t : ℝ) (u : Dbl) : dblFun θ t u ∈ Icc (-1 : ℝ) 2 := by
  have h := (θ t (tentT u)).2
  unfold dblFun br₀ br₁ br₂
  split_ifs <;> constructor <;> linarith [h.1, h.2]

theorem dblFun_of_le_zero {u : Dbl} (hu : (u : ℝ) ≤ 0) (t : ℝ) :
    dblFun θ t u = br₀ (θ t (tentT u)) := if_pos hu

variable (hθ : IsHeight θ (fun b => (b : ℝ)))
include hθ

omit hθ in
theorem tentT_eq_top {u : Dbl} (hu : (u : ℝ) = 0) : tentT u = Tau.top :=
  Subtype.ext (by show tent u = 1; rw [hu, tent_of_le_zero le_rfl]; norm_num)

omit hθ in
theorem tentT_eq_bot {u : Dbl} (hu : (u : ℝ) = 1) : tentT u = Tau.bot :=
  Subtype.ext (by show tent u = -1; rw [hu, tent_of_mem zero_le_one le_rfl]; norm_num)

theorem dblFun_of_mem {u : Dbl} (h0 : 0 ≤ (u : ℝ)) (h1 : (u : ℝ) ≤ 1) (t : ℝ) :
    dblFun θ t u = br₁ (θ t (tentT u)) := by
  unfold dblFun
  by_cases hu : (u : ℝ) ≤ 0
  · rw [if_pos hu, tentT_eq_top (le_antisymm hu h0), base_top hθ]
    simp [br₀, br₁, Tau.top]
  · rw [if_neg hu, if_pos h1]

theorem dblFun_of_one_le {u : Dbl} (h1 : 1 ≤ (u : ℝ)) (t : ℝ) :
    dblFun θ t u = br₂ (θ t (tentT u)) := by
  unfold dblFun
  rw [if_neg (by linarith)]
  by_cases hu : (u : ℝ) ≤ 1
  · rw [if_pos hu, tentT_eq_bot (le_antisymm hu h1), base_bot hθ]
    simp [br₁, br₂, Tau.bot]
    norm_num
  · rw [if_neg hu]

theorem tent_dblFun (t : ℝ) (u : Dbl) : tent (dblFun θ t u) = θ t (tentT u) := by
  have h := (θ t (tentT u)).2
  by_cases h0 : (u : ℝ) ≤ 0
  · rw [dblFun_of_le_zero h0, tent_br₀ h.2]
  by_cases h1 : (u : ℝ) ≤ 1
  · rw [dblFun_of_mem hθ (by linarith) h1, tent_br₁ h]
  · rw [dblFun_of_one_le hθ (by linarith), tent_br₂ h]

theorem continuous_dblFun : Continuous fun p : ℝ × Dbl => dblFun θ p.1 p.2 := by
  have hb : ∀ f : ℝ → ℝ, Continuous f →
      Continuous fun p : ℝ × Dbl => f (θ p.1 (tentT p.2) : ℝ) := fun f hf =>
    hf.comp (continuous_subtype_val.comp
      (θ.continuous continuous_fst (continuous_tentT.comp continuous_snd)))
  have h₀ := hb br₀ ((continuous_id.sub continuous_const).div_const 2)
  have h₁ := hb br₁ ((continuous_const.sub continuous_id).div_const 2)
  have h₂ := hb br₂ ((continuous_id.add continuous_const).div_const 2)
  have hu : Continuous fun p : ℝ × Dbl => (p.2 : ℝ) := continuous_subtype_val.comp continuous_snd
  have hin : Continuous fun p : ℝ × Dbl => if (p.2 : ℝ) ≤ 1 then br₁ (θ p.1 (tentT p.2))
      else br₂ (θ p.1 (tentT p.2)) := by
    refine continuous_if_le hu continuous_const h₁.continuousOn h₂.continuousOn fun p hp => ?_
    rw [tentT_eq_bot hp, base_bot hθ]
    simp [br₁, br₂, Tau.bot]
    norm_num
  exact continuous_if_le hu continuous_const h₀.continuousOn hin.continuousOn fun p hp => by
    rw [if_pos (by rw [hp]; norm_num), tentT_eq_top hp, base_top hθ]
    simp [br₀, br₁, Tau.top]

/-- The base flow of the double, lifted to `[-1, 2]`. -/
noncomputable def dblFlow : Flow ℝ Dbl where
  toFun t u := ⟨dblFun θ t u, dblFun_mem t u⟩
  cont' := (continuous_dblFun hθ).subtype_mk _
  map_add' s t u := by
    apply Subtype.ext
    show dblFun θ (s + t) u = dblFun θ s ⟨dblFun θ t u, dblFun_mem t u⟩
    have h := (θ t (tentT u)).2
    have e : tentT ⟨dblFun θ t u, dblFun_mem t u⟩ = θ t (tentT u) :=
      Subtype.ext (tent_dblFun hθ t u)
    by_cases h0 : (u : ℝ) ≤ 0
    · have hv : dblFun θ t u ≤ 0 := by
        rw [dblFun_of_le_zero h0]; unfold br₀; linarith [h.2]
      rw [dblFun_of_le_zero h0, dblFun_of_le_zero (u := ⟨_, dblFun_mem t u⟩) hv, e,
        Flow.map_add]
    by_cases h1 : (u : ℝ) ≤ 1
    · have hv : dblFun θ t u ∈ Icc (0 : ℝ) 1 := by
        rw [dblFun_of_mem hθ (by linarith) h1]; unfold br₁; constructor <;> linarith [h.1, h.2]
      rw [dblFun_of_mem hθ (by linarith) h1, dblFun_of_mem hθ (u := ⟨_, dblFun_mem t u⟩) hv.1 hv.2,
        e, Flow.map_add]
    · have hv : 1 ≤ dblFun θ t u := by
        rw [dblFun_of_one_le hθ (by linarith)]; unfold br₂; linarith [h.1]
      rw [dblFun_of_one_le hθ (by linarith), dblFun_of_one_le hθ (u := ⟨_, dblFun_mem t u⟩) hv,
        e, Flow.map_add]
  map_zero' u := by
    apply Subtype.ext
    show dblFun θ 0 u = u
    by_cases h0 : (u : ℝ) ≤ 0
    · rw [dblFun_of_le_zero h0, Flow.map_zero_apply]; exact br₀_tent h0
    by_cases h1 : (u : ℝ) ≤ 1
    · rw [dblFun_of_mem hθ (by linarith) h1, Flow.map_zero_apply]; exact br₁_tent (by linarith) h1
    · rw [dblFun_of_one_le hθ (by linarith), Flow.map_zero_apply]; exact br₂_tent (by linarith) u.2.2

theorem dblFlow_apply (t : ℝ) (u : Dbl) : (dblFlow hθ t u : ℝ) = dblFun θ t u := rfl

/-- Lemma `lem:double`(a) for the base: `tent` semiconjugates the double onto the slab. -/
theorem tentT_dblFlow (t : ℝ) (u : Dbl) : tentT (dblFlow hθ t u) = θ t (tentT u) :=
  Subtype.ext (tent_dblFun hθ t u)

theorem dblFlow_zero (t : ℝ) : dblFlow hθ t Dbl.zero = Dbl.zero := by
  apply Subtype.ext
  rw [dblFlow_apply, dblFun_of_le_zero (le_refl (0 : ℝ)), tentT_zero, base_top hθ]
  simp [br₀, Tau.top, Dbl.zero]

theorem dblFlow_one (t : ℝ) : dblFlow hθ t Dbl.one = Dbl.one := by
  apply Subtype.ext
  rw [dblFlow_apply, dblFun_of_one_le hθ (le_refl (1 : ℝ)), tentT_one, base_bot hθ]
  simp [br₂, Tau.bot, Dbl.one]
  norm_num

/-! #### Branches, monotonicity and limits -/

theorem dblFlow_mem01 {u : Dbl} (h0 : 0 ≤ (u : ℝ)) (h1 : (u : ℝ) ≤ 1) (t : ℝ) :
    (dblFlow hθ t u : ℝ) = br₁ (θ t (tentT u)) := dblFun_of_mem hθ h0 h1 t

theorem dblFlow_le0 {u : Dbl} (h0 : (u : ℝ) ≤ 0) (t : ℝ) :
    (dblFlow hθ t u : ℝ) = br₀ (θ t (tentT u)) := dblFun_of_le_zero h0 t

theorem dblFlow_ge1 {u : Dbl} (h1 : 1 ≤ (u : ℝ)) (t : ℝ) :
    (dblFlow hθ t u : ℝ) = br₂ (θ t (tentT u)) := dblFun_of_one_le hθ h1 t

omit hθ in
/-- A flow on an interval preserves the order. -/
theorem flow_mono_Icc {a b : ℝ} (ψ : Flow ℝ (Icc a b)) {u v : Icc a b} (h : (u : ℝ) ≤ v)
    (t : ℝ) : (ψ t u : ℝ) ≤ ψ t v := by
  by_contra hlt
  push Not at hlt
  have hc : Continuous fun s => (ψ s v : ℝ) - ψ s u :=
    (continuous_subtype_val.comp (ψ.continuous continuous_id continuous_const)).sub
      (continuous_subtype_val.comp (ψ.continuous continuous_id continuous_const))
  have h0 : (0 : ℝ) ∈ uIcc ((ψ 0 v : ℝ) - ψ 0 u) ((ψ t v : ℝ) - ψ t u) := by
    rw [Flow.map_zero_apply, Flow.map_zero_apply]
    exact mem_uIcc.2 (Or.inr ⟨by linarith, by linarith⟩)
  obtain ⟨s, -, hs⟩ := intermediate_value_uIcc hc.continuousOn h0
  have heq : ψ s v = ψ s u := Subtype.ext (by simp only at hs; linarith)
  have := congrArg (ψ (-s)) heq
  rw [← Flow.map_add, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply,
    Flow.map_zero_apply] at this
  rw [this] at hlt
  exact lt_irrefl _ hlt

omit hθ in
theorem tent_lt_one_of_pos {u : Dbl} (h0 : 0 < (u : ℝ)) (h2 : (u : ℝ) < 2) :
    ((tentT u : Tau) : ℝ) < 1 := by
  show tent u < 1
  by_cases h1 : (u : ℝ) ≤ 1
  · rw [tent_of_mem h0.le h1]; linarith
  · rw [tent_of_one_le (by linarith) h2.le]; linarith

omit hθ in
theorem neg_one_lt_tent {u : Dbl} (h0 : -1 < (u : ℝ)) (h1 : (u : ℝ) < 1) :
    -1 < ((tentT u : Tau) : ℝ) := by
  show -1 < tent u
  by_cases h : (u : ℝ) ≤ 0
  · rw [tent_of_le_zero h]; linarith
  · rw [tent_of_mem (by linarith) h1.le]; linarith

omit hθ in
theorem neg_one_lt_tent_of_gt {u : Dbl} (h1 : 1 < (u : ℝ)) : -1 < ((tentT u : Tau) : ℝ) := by
  show -1 < tent u
  rw [tent_of_one_le h1.le u.2.2]; linarith

omit hθ in
theorem tent_lt_one_of_neg {u : Dbl} (h0 : (u : ℝ) < 0) : ((tentT u : Tau) : ℝ) < 1 := by
  show tent u < 1
  rw [tent_of_le_zero h0.le]; linarith

/-- Forward limit `0` from `(-1, 1)`, upper bound. -/
theorem dblFlow_tendsto0_upper {u : Dbl} (h0 : -1 < (u : ℝ)) (h1 : (u : ℝ) < 1) {ε : ℝ}
    (hε : 0 < ε) : ∃ T, ∀ t ≥ T, (dblFlow hθ t u : ℝ) < ε := by
  obtain ⟨T, hT⟩ := base_tendsto_top hθ (neg_one_lt_tent h0 h1) (ε := 2 * ε) (by linarith)
  refine ⟨T, fun t ht => ?_⟩
  have := hT t ht
  by_cases hu : (u : ℝ) ≤ 0
  · rw [dblFlow_le0 hθ hu]; unfold br₀; linarith [(θ t (tentT u)).2.2]
  · rw [dblFlow_mem01 hθ (by linarith) h1.le]; unfold br₁; linarith

/-- Forward limit `0` from `(-1, 1)`, lower bound. -/
theorem dblFlow_tendsto0_lower {u : Dbl} (h0 : -1 < (u : ℝ)) (h1 : (u : ℝ) < 1) {ε : ℝ}
    (hε : 0 < ε) : ∃ T, ∀ t ≥ T, -ε < (dblFlow hθ t u : ℝ) := by
  obtain ⟨T, hT⟩ := base_tendsto_top hθ (neg_one_lt_tent h0 h1) (ε := 2 * ε) (by linarith)
  refine ⟨T, fun t ht => ?_⟩
  have := hT t ht
  by_cases hu : (u : ℝ) ≤ 0
  · rw [dblFlow_le0 hθ hu]; unfold br₀; linarith
  · rw [dblFlow_mem01 hθ (by linarith) h1.le]; unfold br₁; linarith [(θ t (tentT u)).2.2]

/-- Backward limit `1` from `(0, 2)`, upper bound. -/
theorem dblFlow_tendsto1_upper {u : Dbl} (h0 : 0 < (u : ℝ)) (h2 : (u : ℝ) < 2) {ε : ℝ}
    (hε : 0 < ε) : ∃ T, ∀ t ≤ T, (dblFlow hθ t u : ℝ) < 1 + ε := by
  obtain ⟨T, hT⟩ := base_tendsto_bot hθ (tent_lt_one_of_pos h0 h2) (ε := 2 * ε) (by linarith)
  refine ⟨T, fun t ht => ?_⟩
  have := hT t ht
  by_cases hu : (u : ℝ) ≤ 1
  · rw [dblFlow_mem01 hθ h0.le hu]; unfold br₁; linarith [(θ t (tentT u)).2.1]
  · rw [dblFlow_ge1 hθ (by linarith)]; unfold br₂; linarith

/-- Backward limit `1` from `(0, 2)`, lower bound. -/
theorem dblFlow_tendsto1_lower {u : Dbl} (h0 : 0 < (u : ℝ)) (h2 : (u : ℝ) < 2) {ε : ℝ}
    (hε : 0 < ε) : ∃ T, ∀ t ≤ T, 1 - ε < (dblFlow hθ t u : ℝ) := by
  obtain ⟨T, hT⟩ := base_tendsto_bot hθ (tent_lt_one_of_pos h0 h2) (ε := 2 * ε) (by linarith)
  refine ⟨T, fun t ht => ?_⟩
  have := hT t ht
  by_cases hu : (u : ℝ) ≤ 1
  · rw [dblFlow_mem01 hθ h0.le hu]; unfold br₁; linarith
  · rw [dblFlow_ge1 hθ (by linarith)]; unfold br₂; linarith [(θ t (tentT u)).2.1]

/-- Backward limit `-1` from `[-1, 0)`. -/
theorem dblFlow_tendsto_neg_one {u : Dbl} (h0 : (u : ℝ) < 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ T, ∀ t ≤ T, (dblFlow hθ t u : ℝ) < -1 + ε := by
  obtain ⟨T, hT⟩ := base_tendsto_bot hθ (tent_lt_one_of_neg h0) (ε := 2 * ε) (by linarith)
  refine ⟨T, fun t ht => ?_⟩
  have := hT t ht
  rw [dblFlow_le0 hθ h0.le]; unfold br₀; linarith

/-- Forward limit `2` from `(1, 2]`. -/
theorem dblFlow_tendsto_two {u : Dbl} (h1 : 1 < (u : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ T, ∀ t ≥ T, 2 - ε < (dblFlow hθ t u : ℝ) := by
  obtain ⟨T, hT⟩ := base_tendsto_top hθ (neg_one_lt_tent_of_gt h1) (ε := 2 * ε) (by linarith)
  refine ⟨T, fun t ht => ?_⟩
  have := hT t ht
  rw [dblFlow_ge1 hθ h1.le]; unfold br₂; linarith

/-! #### The open invariant sets `(-1, 1)` and `(0, 2)` -/

/-- The basin `(-1, 1)` of the IR point. -/
def U0 : Set Dbl := {u | -1 < (u : ℝ) ∧ (u : ℝ) < 1}

/-- The basin `(0, 2)` of the UV point under the reversed flow. -/
def U1 : Set Dbl := {u | 0 < (u : ℝ) ∧ (u : ℝ) < 2}

omit hθ in
theorem isOpen_U0 : IsOpen U0 :=
  (isOpen_lt continuous_const continuous_subtype_val).inter
    (isOpen_lt continuous_subtype_val continuous_const)

omit hθ in
theorem isOpen_U1 : IsOpen U1 :=
  (isOpen_lt continuous_const continuous_subtype_val).inter
    (isOpen_lt continuous_subtype_val continuous_const)

omit hθ in
theorem zero_mem_U0 : Dbl.zero ∈ U0 := ⟨show (-1 : ℝ) < 0 by norm_num, show (0 : ℝ) < 1 by norm_num⟩

omit hθ in
theorem one_mem_U1 : Dbl.one ∈ U1 := ⟨show (0 : ℝ) < 1 by norm_num, show (1 : ℝ) < 2 by norm_num⟩

theorem isInvariant_U0 : IsInvariant (dblFlow hθ) U0 := by
  intro t u hu
  obtain ⟨h0, h1⟩ := hu
  have hτ := neg_one_lt_base hθ (neg_one_lt_tent h0 h1) t
  have hτ' := (θ t (tentT u)).2
  by_cases hu : (u : ℝ) ≤ 0
  · show -1 < (dblFlow hθ t u : ℝ) ∧ (dblFlow hθ t u : ℝ) < 1
    rw [dblFlow_le0 hθ hu]; unfold br₀; constructor <;> linarith [hτ'.2]
  · show -1 < (dblFlow hθ t u : ℝ) ∧ (dblFlow hθ t u : ℝ) < 1
    rw [dblFlow_mem01 hθ (by linarith) h1.le]; unfold br₁; constructor <;> linarith [hτ'.2]

theorem isInvariant_U1 : IsInvariant (dblFlow hθ) U1 := by
  intro t u hu
  obtain ⟨h0, h2⟩ := hu
  have hτ := base_lt_one hθ (tent_lt_one_of_pos h0 h2) t
  have hτ' := (θ t (tentT u)).2
  by_cases hu : (u : ℝ) ≤ 1
  · show 0 < (dblFlow hθ t u : ℝ) ∧ (dblFlow hθ t u : ℝ) < 2
    rw [dblFlow_mem01 hθ h0.le hu]; unfold br₁; constructor <;> linarith [hτ'.1]
  · show 0 < (dblFlow hθ t u : ℝ) ∧ (dblFlow hθ t u : ℝ) < 2
    rw [dblFlow_ge1 hθ (by linarith)]; unfold br₂; constructor <;> linarith [hτ'.1]

/-! #### The base contractions -/

/-- `g(λ, u) = ϑ_{-log λ} u`, extended by `0` at `λ = 0`. -/
noncomputable def g0Fun (q : I × U0) : U0 :=
  if (q.1 : ℝ) = 0 then ⟨Dbl.zero, zero_mem_U0⟩
  else (dblFlow hθ).restrict (isInvariant_U0 hθ) (-Real.log q.1) q.2

/-- `g(λ, u) = ϑ_{log λ} u`, extended by `1` at `λ = 0`. -/
noncomputable def g1Fun (q : I × U1) : U1 :=
  if (q.1 : ℝ) = 0 then ⟨Dbl.one, one_mem_U1⟩
  else (dblFlow hθ).restrict (isInvariant_U1 hθ) (Real.log q.1) q.2

theorem continuous_g0Fun : Continuous (g0Fun hθ) := by
  refine continuous_iff_continuousAt.2 fun ⟨l, b⟩ => ?_
  by_cases hl : (l : ℝ) = 0
  · show Tendsto _ _ (𝓝 (g0Fun hθ (l, b)))
    rw [g0Fun, if_pos hl, tendsto_subtype_rng, tendsto_subtype_rng]
    obtain ⟨hb0, hb1⟩ := b.2
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have ha' : a < 0 := ha
      set w : ℝ := (min ((b : Dbl) : ℝ) 0 - 1) / 2 with hw
      have hwm : min ((b : Dbl) : ℝ) 0 ≤ ((b : Dbl) : ℝ) := min_le_left _ _
      have hwm' : -1 < min ((b : Dbl) : ℝ) 0 := lt_min hb0 (by norm_num)
      have hwb : w < ((b : Dbl) : ℝ) := by rw [hw]; linarith [min_le_right ((b : Dbl) : ℝ) 0]
      have hw1 : -1 < w := by rw [hw]; linarith
      have hw0 : w < 0 := by rw [hw]; linarith [min_le_right ((b : Dbl) : ℝ) 0]
      have hwD : w ∈ Icc (-1 : ℝ) 2 := ⟨hw1.le, by linarith⟩
      obtain ⟨T, hT⟩ := dblFlow_tendsto0_lower hθ (u := ⟨w, hwD⟩) hw1 (by show w < 1; linarith)
        (ε := -a) (by linarith)
      have hopen : IsOpen {q : I × U0 | (q.1 : ℝ) < Real.exp (-T) ∧ w < ((q.2 : Dbl) : ℝ)} :=
        (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).inter
          (isOpen_lt continuous_const
            (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))
      refine Filter.eventually_of_mem (hopen.mem_nhds (x := (l, b))
        ⟨show (l : ℝ) < _ by rw [hl]; exact Real.exp_pos _, hwb⟩) fun q hq => ?_
      show a < ((g0Fun hθ q : Dbl) : ℝ)
      unfold g0Fun
      split_ifs with hq0
      · exact ha'
      · have hpos : 0 < (q.1 : ℝ) := lt_of_le_of_ne q.1.2.1 (Ne.symm hq0)
        have hlog : T ≤ -Real.log q.1 := by
          have := ((Real.log_lt_iff_lt_exp hpos).2 hq.1).le
          linarith
        have h1 := flow_mono_Icc (dblFlow hθ) (u := ⟨w, hwD⟩) (v := (q.2 : Dbl)) hq.2.le
          (-Real.log q.1)
        have h2 := hT _ hlog
        show a < ((dblFlow hθ (-Real.log q.1) (q.2 : Dbl) : Dbl) : ℝ)
        linarith
    · have ha' : 0 < a := ha
      set v : ℝ := (max ((b : Dbl) : ℝ) 0 + 1) / 2 with hv
      have hvm : ((b : Dbl) : ℝ) ≤ max ((b : Dbl) : ℝ) 0 := le_max_left _ _
      have hvm' : max ((b : Dbl) : ℝ) 0 < 1 := max_lt hb1 (by norm_num)
      have hvb : ((b : Dbl) : ℝ) < v := by rw [hv]; linarith
      have hv1 : v < 1 := by rw [hv]; linarith
      have hv0 : 0 < v := by rw [hv]; linarith [le_max_right ((b : Dbl) : ℝ) 0]
      have hvD : v ∈ Icc (-1 : ℝ) 2 := ⟨by linarith, by linarith⟩
      obtain ⟨T, hT⟩ := dblFlow_tendsto0_upper hθ (u := ⟨v, hvD⟩) (by show (-1 : ℝ) < v; linarith)
        hv1 (ε := a) ha'
      have hopen : IsOpen {q : I × U0 | (q.1 : ℝ) < Real.exp (-T) ∧ ((q.2 : Dbl) : ℝ) < v} :=
        (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).inter
          (isOpen_lt (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
            continuous_const)
      refine Filter.eventually_of_mem (hopen.mem_nhds (x := (l, b))
        ⟨show (l : ℝ) < _ by rw [hl]; exact Real.exp_pos _, hvb⟩) fun q hq => ?_
      show ((g0Fun hθ q : Dbl) : ℝ) < a
      unfold g0Fun
      split_ifs with hq0
      · exact ha'
      · have hpos : 0 < (q.1 : ℝ) := lt_of_le_of_ne q.1.2.1 (Ne.symm hq0)
        have hlog : T ≤ -Real.log q.1 := by
          have := ((Real.log_lt_iff_lt_exp hpos).2 hq.1).le
          linarith
        have h1 := flow_mono_Icc (dblFlow hθ) (u := (q.2 : Dbl)) (v := ⟨v, hvD⟩) hq.2.le
          (-Real.log q.1)
        have h2 := hT _ hlog
        show ((dblFlow hθ (-Real.log q.1) (q.2 : Dbl) : Dbl) : ℝ) < a
        linarith
  · have hcont : ContinuousAt (fun q : I × U0 =>
        (dblFlow hθ).restrict (isInvariant_U0 hθ) (-Real.log q.1) q.2) (l, b) :=
      ((dblFlow hθ).restrict (isInvariant_U0 hθ)).cont'.continuousAt.comp
        (((Real.continuousAt_log hl).comp (x := (l, b)) (f := fun q : I × U0 => (q.1 : ℝ))
          (continuous_subtype_val.comp continuous_fst).continuousAt).neg.prodMk
            continuousAt_snd)
    refine hcont.congr ?_
    have hopen : IsOpen {q : I × U0 | (q.1 : ℝ) ≠ 0} :=
      isOpen_ne_fun (continuous_subtype_val.comp continuous_fst) continuous_const
    filter_upwards [hopen.mem_nhds hl] with q hq
    show _ = g0Fun hθ q
    rw [g0Fun, if_neg hq]

set_option maxHeartbeats 2000000 in
theorem continuous_g1Fun : Continuous (g1Fun hθ) := by
  refine continuous_iff_continuousAt.2 fun ⟨l, b⟩ => ?_
  by_cases hl : (l : ℝ) = 0
  · show Tendsto _ _ (𝓝 (g1Fun hθ (l, b)))
    rw [g1Fun, if_pos hl, tendsto_subtype_rng, tendsto_subtype_rng]
    obtain ⟨hb0, hb2⟩ := b.2
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have ha' : a < 1 := ha
      set w : ℝ := min ((b : Dbl) : ℝ) 1 / 2 with hw
      have hwm : min ((b : Dbl) : ℝ) 1 ≤ ((b : Dbl) : ℝ) := min_le_left _ _
      have hwm' : 0 < min ((b : Dbl) : ℝ) 1 := lt_min hb0 (by norm_num)
      have hwb : w < ((b : Dbl) : ℝ) := by rw [hw]; linarith
      have hw0 : 0 < w := by rw [hw]; linarith
      have hw2 : w < 2 := by rw [hw]; linarith [min_le_right ((b : Dbl) : ℝ) 1]
      have hwD : w ∈ Icc (-1 : ℝ) 2 := ⟨by linarith, hw2.le⟩
      obtain ⟨T, hT⟩ := dblFlow_tendsto1_lower hθ (u := ⟨w, hwD⟩) hw0 hw2 (ε := 1 - a)
        (by linarith)
      have hopen : IsOpen {q : I × U1 | (q.1 : ℝ) < Real.exp T ∧ w < ((q.2 : Dbl) : ℝ)} :=
        (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).inter
          (isOpen_lt continuous_const
            (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))
      refine Filter.eventually_of_mem (hopen.mem_nhds (x := (l, b))
        ⟨show (l : ℝ) < _ by rw [hl]; exact Real.exp_pos _, hwb⟩) fun q hq => ?_
      show a < ((g1Fun hθ q : Dbl) : ℝ)
      unfold g1Fun
      split_ifs with hq0
      · exact ha'
      · have hpos : 0 < (q.1 : ℝ) := lt_of_le_of_ne q.1.2.1 (Ne.symm hq0)
        have hlog : Real.log q.1 ≤ T := ((Real.log_lt_iff_lt_exp hpos).2 hq.1).le
        have h1 := flow_mono_Icc (dblFlow hθ) (u := ⟨w, hwD⟩) (v := (q.2 : Dbl)) hq.2.le
          (Real.log q.1)
        have h2 := hT _ hlog
        show a < ((dblFlow hθ (Real.log q.1) (q.2 : Dbl) : Dbl) : ℝ)
        linarith
    · have ha' : 1 < a := ha
      set v : ℝ := (max ((b : Dbl) : ℝ) 1 + 2) / 2 with hv
      have hvm : ((b : Dbl) : ℝ) ≤ max ((b : Dbl) : ℝ) 1 := le_max_left _ _
      have hvm' : max ((b : Dbl) : ℝ) 1 < 2 := max_lt hb2 (by norm_num)
      have hvb : ((b : Dbl) : ℝ) < v := by rw [hv]; linarith
      have hv2 : v < 2 := by rw [hv]; linarith
      have hv0 : 0 < v := by rw [hv]; linarith [le_max_right ((b : Dbl) : ℝ) 1]
      have hvD : v ∈ Icc (-1 : ℝ) 2 := ⟨by linarith, hv2.le⟩
      obtain ⟨T, hT⟩ := dblFlow_tendsto1_upper hθ (u := ⟨v, hvD⟩) hv0 hv2 (ε := a - 1)
        (by linarith)
      have hopen : IsOpen {q : I × U1 | (q.1 : ℝ) < Real.exp T ∧ ((q.2 : Dbl) : ℝ) < v} :=
        (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).inter
          (isOpen_lt (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
            continuous_const)
      refine Filter.eventually_of_mem (hopen.mem_nhds (x := (l, b))
        ⟨show (l : ℝ) < _ by rw [hl]; exact Real.exp_pos _, hvb⟩) fun q hq => ?_
      show ((g1Fun hθ q : Dbl) : ℝ) < a
      unfold g1Fun
      split_ifs with hq0
      · exact ha'
      · have hpos : 0 < (q.1 : ℝ) := lt_of_le_of_ne q.1.2.1 (Ne.symm hq0)
        have hlog : Real.log q.1 ≤ T := ((Real.log_lt_iff_lt_exp hpos).2 hq.1).le
        have h1 := flow_mono_Icc (dblFlow hθ) (u := (q.2 : Dbl)) (v := ⟨v, hvD⟩) hq.2.le
          (Real.log q.1)
        have h2 := hT _ hlog
        show ((dblFlow hθ (Real.log q.1) (q.2 : Dbl) : Dbl) : ℝ) < a
        linarith
  · have hf : ContinuousAt (fun q : I × U1 => (Real.log (q.1 : ℝ), q.2)) (l, b) :=
      ((Real.continuousAt_log hl).comp (x := (l, b)) (f := fun q : I × U1 => (q.1 : ℝ))
        (continuous_subtype_val.comp continuous_fst).continuousAt).prodMk continuousAt_snd
    have hcont : ContinuousAt (fun q : I × U1 =>
        (dblFlow hθ).restrict (isInvariant_U1 hθ) (Real.log q.1) q.2) (l, b) :=
      (((dblFlow hθ).restrict (isInvariant_U1 hθ)).continuous continuous_fst
        continuous_snd).continuousAt.comp hf
    refine hcont.congr ?_
    have hopen : IsOpen {q : I × U1 | (q.1 : ℝ) ≠ 0} :=
      isOpen_ne_fun (continuous_subtype_val.comp continuous_fst) continuous_const
    filter_upwards [hopen.mem_nhds hl] with q hq
    show _ = g1Fun hθ q
    rw [g1Fun, if_neg hq]

/-- The base contraction onto the IR point. -/
noncomputable def contraction0 :
    SkewContraction ((dblFlow hθ).restrict (isInvariant_U0 hθ)) ⟨Dbl.zero, zero_mem_U0⟩ where
  g := ⟨g0Fun hθ, continuous_g0Fun hθ⟩
  one b := by
    show g0Fun hθ (1, b) = b
    rw [g0Fun, if_neg (by norm_num), Icc.coe_one, Real.log_one, neg_zero, Flow.map_zero_apply]
  zero b := by
    show g0Fun hθ (0, b) = _
    unfold g0Fun
    exact if_pos rfl
  fix l := by
    show g0Fun hθ (l, _) = _
    unfold g0Fun
    split_ifs
    · rfl
    · exact Subtype.ext (dblFlow_zero hθ _)
  equivariant l t b := by
    show g0Fun hθ (l, _) = (dblFlow hθ).restrict _ t (g0Fun hθ (l, b))
    unfold g0Fun
    split_ifs
    · exact (Subtype.ext (dblFlow_zero hθ t)).symm
    · rw [← Flow.map_add, ← Flow.map_add, add_comm]

/-- The base contraction onto the UV point (along the reversed flow). -/
noncomputable def contraction1 :
    SkewContraction ((dblFlow hθ).restrict (isInvariant_U1 hθ)) ⟨Dbl.one, one_mem_U1⟩ where
  g := ⟨g1Fun hθ, continuous_g1Fun hθ⟩
  one b := by
    show g1Fun hθ (1, b) = b
    rw [g1Fun, if_neg (by norm_num), Icc.coe_one, Real.log_one, Flow.map_zero_apply]
  zero b := by
    show g1Fun hθ (0, b) = _
    unfold g1Fun
    exact if_pos rfl
  fix l := by
    show g1Fun hθ (l, _) = _
    unfold g1Fun
    split_ifs
    · rfl
    · exact Subtype.ext (dblFlow_one hθ _)
  equivariant l t b := by
    show g1Fun hθ (l, _) = (dblFlow hθ).restrict _ t (g1Fun hθ (l, b))
    unfold g1Fun
    split_ifs
    · exact (Subtype.ext (dblFlow_one hθ t)).symm
    · rw [← Flow.map_add, ← Flow.map_add, add_comm]

/-! #### Monotonicity in time on the three branches -/

theorem dblFlow_mem_01 {u : Dbl} (h0 : 0 ≤ (u : ℝ)) (h1 : (u : ℝ) ≤ 1) (t : ℝ) :
    (dblFlow hθ t u : ℝ) ∈ Icc (0 : ℝ) 1 := by
  have h := (θ t (tentT u)).2
  rw [dblFlow_mem01 hθ h0 h1]; unfold br₁; constructor <;> linarith [h.1, h.2]

theorem dblFlow_nonpos {u : Dbl} (h0 : (u : ℝ) ≤ 0) (t : ℝ) : (dblFlow hθ t u : ℝ) ≤ 0 := by
  have h := (θ t (tentT u)).2
  rw [dblFlow_le0 hθ h0]; unfold br₀; linarith [h.2]

theorem one_le_dblFlow {u : Dbl} (h1 : 1 ≤ (u : ℝ)) (t : ℝ) : 1 ≤ (dblFlow hθ t u : ℝ) := by
  have h := (θ t (tentT u)).2
  rw [dblFlow_ge1 hθ h1]; unfold br₂; linarith [h.1]

theorem dblFlow_anti_01 {u : Dbl} (h0 : 0 ≤ (u : ℝ)) (h1 : (u : ℝ) ≤ 1) {s t : ℝ} (hst : s ≤ t) :
    (dblFlow hθ t u : ℝ) ≤ dblFlow hθ s u := by
  have := hθ.monotone_flow (tentT u) hst
  rw [dblFlow_mem01 hθ h0 h1, dblFlow_mem01 hθ h0 h1]; unfold br₁; linarith

theorem dblFlow_mono_nonpos {u : Dbl} (h0 : (u : ℝ) ≤ 0) {s t : ℝ} (hst : s ≤ t) :
    (dblFlow hθ s u : ℝ) ≤ dblFlow hθ t u := by
  have := hθ.monotone_flow (tentT u) hst
  rw [dblFlow_le0 hθ h0, dblFlow_le0 hθ h0]; unfold br₀; linarith

theorem dblFlow_mono_ge1 {u : Dbl} (h1 : 1 ≤ (u : ℝ)) {s t : ℝ} (hst : s ≤ t) :
    (dblFlow hθ s u : ℝ) ≤ dblFlow hθ t u := by
  have := hθ.monotone_flow (tentT u) hst
  rw [dblFlow_ge1 hθ h1, dblFlow_ge1 hθ h1]; unfold br₂; linarith

theorem dblFlow_lt_of_01 {u : Dbl} (h0 : 0 < (u : ℝ)) (h1 : (u : ℝ) < 1) {t : ℝ} (ht : 0 < t) :
    (dblFlow hθ t u : ℝ) < u := by
  have hτ0 : tent u = 1 - 2 * u := tent_of_mem h0.le h1.le
  have := hθ.strict (tentT u) (by show -1 < tent u; linarith) (by show tent u < 1; linarith) t ht
  rw [dblFlow_mem01 hθ h0.le h1.le]
  have e : ((tentT u : Tau) : ℝ) = tent u := rfl
  unfold br₁
  rw [e, hτ0] at this
  linarith

theorem lt_dblFlow_of_gt1 {u : Dbl} (h1 : 1 < (u : ℝ)) (h2 : (u : ℝ) < 2) {t : ℝ} (ht : 0 < t) :
    (u : ℝ) < dblFlow hθ t u := by
  have hτ0 : tent u = 2 * u - 3 := tent_of_one_le h1.le h2.le
  have := hθ.strict (tentT u) (by show -1 < tent u; linarith) (by show tent u < 1; linarith) t ht
  rw [dblFlow_ge1 hθ h1.le]
  have e : ((tentT u : Tau) : ℝ) = tent u := rfl
  unfold br₂
  rw [e, hτ0] at this
  linarith

theorem continuous_dblFlow_time (u : Dbl) : Continuous fun t => (dblFlow hθ t u : ℝ) :=
  continuous_subtype_val.comp ((dblFlow hθ).continuous continuous_id continuous_const)

/-! #### Index pairs of the IR and UV points -/

/-- `[-1/2, 1/2]`, an attracting neighborhood of the IR point. -/
def N0 : Set Dbl := {u | (u : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2)}

/-- `[1/2, 3/2]`, an isolating neighborhood of the UV point. -/
def N1 : Set Dbl := {u | (u : ℝ) ∈ Icc (1 / 2 : ℝ) (3 / 2)}

/-- The exit set `{1/2, 3/2}` of `N1`. -/
def L1 : Set Dbl := {u | (u : ℝ) = 1 / 2 ∨ (u : ℝ) = 3 / 2}

/-- `([-1/2, 1/2], ∅)` is an index pair for the IR point. -/
theorem isIndexPair0 : IsIndexPair (dblFlow hθ) {Dbl.zero} N0 ∅ := by
  have hNc : IsClosed N0 := isClosed_Icc.preimage continuous_subtype_val
  have hInvN : Inv (dblFlow hθ) N0 ⊆ {Dbl.zero} := fun u hu => by
    by_contra hne
    have hne' : (u : ℝ) ≠ 0 := fun h => hne (Subtype.ext h)
    have hu0 := hu 0
    rw [Flow.map_zero_apply] at hu0
    obtain ⟨hl, hr⟩ : (u : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2) := hu0
    rcases lt_or_gt_of_ne hne' with hneg | hpos
    · obtain ⟨T, hT⟩ := dblFlow_tendsto_neg_one hθ hneg (ε := 1 / 4) (by norm_num)
      have h1 := hT T le_rfl
      have h2 : (dblFlow hθ T u : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2) := hu T
      linarith [h2.1]
    · obtain ⟨T, hT⟩ := dblFlow_tendsto1_lower hθ hpos (by linarith) (ε := 1 / 4) (by norm_num)
      have h1 := hT T le_rfl
      have h2 : (dblFlow hθ T u : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2) := hu T
      linarith [h2.2]
  have hO : Dbl.zero ∈ interior (N0 \ ∅) := by
    rw [sdiff_empty]
    have hsub : {u : Dbl | -1 / 2 < (u : ℝ) ∧ (u : ℝ) < 1 / 2} ⊆ N0 :=
      fun u hu => ⟨hu.1.le, hu.2.le⟩
    exact interior_maximal hsub ((isOpen_lt continuous_const continuous_subtype_val).inter
      (isOpen_lt continuous_subtype_val continuous_const))
      ⟨show (-1 / 2 : ℝ) < 0 by norm_num, show (0 : ℝ) < 1 / 2 by norm_num⟩
  have hcl : closure (N0 \ ∅) = N0 := by rw [sdiff_empty, hNc.closure_eq]
  have hInv : Inv (dblFlow hθ) (closure (N0 \ ∅)) = {Dbl.zero} := by
    rw [hcl]
    refine Subset.antisymm hInvN ?_
    rintro _ rfl t
    rw [dblFlow_zero hθ]
    show (0 : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2)
    norm_num
  exact
    { isCompact_N := hNc.isCompact
      isCompact_L := isCompact_empty
      subset := empty_subset _
      isolating := ⟨isClosed_closure.isCompact, by
        rw [hInv, singleton_subset_iff]
        exact interior_mono subset_closure hO⟩
      inv_eq := hInv
      nhds := singleton_subset_iff.2 hO
      posInv := fun _ hb => absurd hb (notMem_empty _)
      exit := fun u hu t ht hout => by
        exfalso
        apply hout
        obtain ⟨hl, hr⟩ : (u : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2) := hu
        show (dblFlow hθ t u : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2)
        by_cases h0 : 0 ≤ (u : ℝ)
        · have h1 := dblFlow_anti_01 hθ h0 (by linarith) ht
          rw [Flow.map_zero_apply] at h1
          have h2 := (dblFlow_mem_01 hθ h0 (by linarith) t).1
          constructor <;> linarith
        · push Not at h0
          have h1 := dblFlow_mono_nonpos hθ h0.le ht
          rw [Flow.map_zero_apply] at h1
          have h2 := dblFlow_nonpos hθ h0.le t
          constructor <;> linarith }

/-- `([1/2, 3/2], {1/2, 3/2})` is an index pair for the UV point. -/
theorem isIndexPair1 : IsIndexPair (dblFlow hθ) {Dbl.one} N1 L1 := by
  have hNc : IsClosed N1 := isClosed_Icc.preimage continuous_subtype_val
  have hLc : IsClosed L1 := (isClosed_eq continuous_subtype_val continuous_const).union
    (isClosed_eq continuous_subtype_val continuous_const)
  have hLN : L1 ⊆ N1 := by
    rintro u (h | h) <;> (show (u : ℝ) ∈ Icc (1 / 2 : ℝ) (3 / 2); rw [h]; norm_num)
  have hInvN : Inv (dblFlow hθ) N1 ⊆ {Dbl.one} := fun u hu => by
    by_contra hne
    have hne' : (u : ℝ) ≠ 1 := fun h => hne (Subtype.ext h)
    have hu0 := hu 0
    rw [Flow.map_zero_apply] at hu0
    obtain ⟨hl, hr⟩ : (u : ℝ) ∈ Icc (1 / 2 : ℝ) (3 / 2) := hu0
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · obtain ⟨T, hT⟩ := dblFlow_tendsto0_upper hθ (by linarith) hlt (ε := 1 / 4) (by norm_num)
      have h1 := hT T le_rfl
      have h2 : (dblFlow hθ T u : ℝ) ∈ Icc (1 / 2 : ℝ) (3 / 2) := hu T
      linarith [h2.1]
    · obtain ⟨T, hT⟩ := dblFlow_tendsto_two hθ hgt (ε := 1 / 4) (by norm_num)
      have h1 := hT T le_rfl
      have h2 : (dblFlow hθ T u : ℝ) ∈ Icc (1 / 2 : ℝ) (3 / 2) := hu T
      linarith [h2.2]
  have hO : Dbl.one ∈ interior (N1 \ L1) := by
    have hsub : {u : Dbl | 1 / 2 < (u : ℝ) ∧ (u : ℝ) < 3 / 2} ⊆ N1 \ L1 := by
      rintro u ⟨h1, h2⟩
      refine ⟨⟨h1.le, h2.le⟩, ?_⟩
      rintro (h | h) <;> linarith
    exact interior_maximal hsub ((isOpen_lt continuous_const continuous_subtype_val).inter
      (isOpen_lt continuous_subtype_val continuous_const))
      ⟨show (1 / 2 : ℝ) < 1 by norm_num, show (1 : ℝ) < 3 / 2 by norm_num⟩
  have hInv : Inv (dblFlow hθ) (closure (N1 \ L1)) = {Dbl.one} := by
    refine Subset.antisymm ((Inv_mono (closure_minimal sdiff_subset hNc)).trans hInvN) ?_
    rintro _ rfl t
    rw [dblFlow_one hθ]
    exact subset_closure (interior_subset hO)
  exact
    { isCompact_N := hNc.isCompact
      isCompact_L := hLc.isCompact
      subset := hLN
      isolating := ⟨isClosed_closure.isCompact, by
        rw [hInv, singleton_subset_iff]
        exact interior_mono subset_closure hO⟩
      inv_eq := hInv
      nhds := singleton_subset_iff.2 hO
      posInv := fun u hu t ht hseg => by
        rcases ht.eq_or_lt with rfl | ht
        · rw [Flow.map_zero_apply]; exact hu
        · exfalso
          have h2 : (dblFlow hθ t u : ℝ) ∈ Icc (1 / 2 : ℝ) (3 / 2) := hseg t ⟨ht.le, le_rfl⟩
          rcases hu with h | h
          · have := dblFlow_lt_of_01 hθ (u := u) (by rw [h]; norm_num) (by rw [h]; norm_num) ht
            rw [h] at this
            linarith [h2.1]
          · have := lt_dblFlow_of_gt1 hθ (u := u) (by rw [h]; norm_num) (by rw [h]; norm_num) ht
            rw [h] at this
            linarith [h2.2]
      exit := fun u hu t ht hout => by
        obtain ⟨hl, hr⟩ : (u : ℝ) ∈ Icc (1 / 2 : ℝ) (3 / 2) := hu
        have hout' : (dblFlow hθ t u : ℝ) ∉ Icc (1 / 2 : ℝ) (3 / 2) := hout
        by_cases h1 : (u : ℝ) ≤ 1
        · have h0 : 0 ≤ (u : ℝ) := by linarith
          have hle : (dblFlow hθ t u : ℝ) ≤ u := by
            have := dblFlow_anti_01 hθ h0 h1 ht
            rwa [Flow.map_zero_apply] at this
          have hlt : (dblFlow hθ t u : ℝ) < 1 / 2 := by
            by_contra hc
            push Not at hc
            exact hout' ⟨hc, by linarith⟩
          obtain ⟨s, hs, hs2⟩ := intermediate_value_Icc' ht
            (continuous_dblFlow_time hθ u).continuousOn
            (show (1 / 2 : ℝ) ∈ Icc ((dblFlow hθ t u : ℝ)) ((dblFlow hθ 0 u : Dbl) : ℝ) by
              rw [Flow.map_zero_apply]; exact ⟨hlt.le, hl⟩)
          refine ⟨s, hs, fun r hr => ?_, Or.inl hs2⟩
          show (dblFlow hθ r u : ℝ) ∈ Icc (1 / 2 : ℝ) (3 / 2)
          have ha := dblFlow_anti_01 hθ h0 h1 hr.2
          have hb := dblFlow_anti_01 hθ h0 h1 hr.1
          rw [Flow.map_zero_apply] at hb
          have hs2' : (dblFlow hθ s u : ℝ) = 1 / 2 := hs2
          constructor <;> linarith
        · push Not at h1
          have hge : (u : ℝ) ≤ dblFlow hθ t u := by
            have := dblFlow_mono_ge1 hθ h1.le ht
            rwa [Flow.map_zero_apply] at this
          have hgt : 3 / 2 < (dblFlow hθ t u : ℝ) := by
            by_contra hc
            push Not at hc
            exact hout' ⟨by linarith, hc⟩
          obtain ⟨s, hs, hs2⟩ := intermediate_value_Icc ht
            (continuous_dblFlow_time hθ u).continuousOn
            (show (3 / 2 : ℝ) ∈ Icc ((dblFlow hθ 0 u : Dbl) : ℝ) ((dblFlow hθ t u : ℝ)) by
              rw [Flow.map_zero_apply]; exact ⟨hr, hgt.le⟩)
          refine ⟨s, hs, fun r hr => ?_, Or.inr hs2⟩
          show (dblFlow hθ r u : ℝ) ∈ Icc (1 / 2 : ℝ) (3 / 2)
          have ha := dblFlow_mono_ge1 hθ h1.le hr.2
          have hb := dblFlow_mono_ge1 hθ h1.le hr.1
          rw [Flow.map_zero_apply] at hb
          have hs2' : (dblFlow hθ s u : ℝ) = 3 / 2 := hs2
          constructor <;> linarith }

omit hθ in
theorem N0_subset_U0 : N0 ⊆ U0 := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩

omit hθ in
theorem N1_subset_U1 : N1 ⊆ U1 := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩

omit hθ in
theorem deform0_mem {s r : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    (1 - s) * r ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hr0, hr1⟩ := hr
  constructor <;> nlinarith

omit hθ in
/-- The deformation `u ↦ (1 - s) u` of `[-1/2, 1/2]` onto the IR point. -/
noncomputable def deform0 :
    C(I × (Subtype.val ⁻¹' N0 : Set U0), (Subtype.val ⁻¹' N0 : Set U0)) where
  toFun q :=
    have h := deform0_mem q.1.2 q.2.2
    ⟨⟨⟨(1 - (q.1 : ℝ)) * (((q.2 : U0) : Dbl) : ℝ), by linarith [h.1], by linarith [h.2]⟩,
      N0_subset_U0 h⟩, h⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _) _
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_snd)))

omit hθ in
theorem chart1_mem (t : ℝ) :
    (projIcc (1 / 2 : ℝ) (3 / 2) (by norm_num) (1 / 2 + t) : ℝ) ∈ Icc (-1 : ℝ) 2 := by
  have h := (projIcc (1 / 2 : ℝ) (3 / 2) (by norm_num) (1 / 2 + t)).2
  constructor <;> linarith [h.1, h.2]

omit hθ in
/-- The interval chart `t ↦ 1/2 + t` of `([1/2, 3/2], {1/2, 3/2})` inside `(0, 2)`. -/
noncomputable def chart1 :
    IntervalChart (Subtype.val ⁻¹' N1 : Set U1) (Subtype.val ⁻¹' L1 : Set U1) where
  e := ⟨fun t => ⟨⟨projIcc (1 / 2 : ℝ) (3 / 2) (by norm_num) (1 / 2 + t), chart1_mem t⟩,
      N1_subset_U1 (projIcc (1 / 2 : ℝ) (3 / 2) (by norm_num) (1 / 2 + t)).2⟩, by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact continuous_subtype_val.comp (continuous_projIcc.comp (continuous_const.add continuous_id))⟩
  injOn s hs t ht h := by
    have h' := congrArg (fun u : U1 => ((u : Dbl) : ℝ)) h
    simp only [ContinuousMap.coe_mk] at h'
    rw [projIcc_of_mem _ ⟨by linarith [hs.1], by linarith [hs.2]⟩,
      projIcc_of_mem _ ⟨by linarith [ht.1], by linarith [ht.2]⟩] at h'
    simpa using h'
  image_eq := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (projIcc (1 / 2 : ℝ) (3 / 2) (by norm_num) (1 / 2 + t)).2
    · intro hu
      obtain ⟨h1, h2⟩ : ((u : Dbl) : ℝ) ∈ Icc (1 / 2 : ℝ) (3 / 2) := hu
      refine ⟨((u : Dbl) : ℝ) - 1 / 2, ⟨by linarith, by linarith⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      show (projIcc (1 / 2 : ℝ) (3 / 2) (by norm_num) (1 / 2 + (((u : Dbl) : ℝ) - 1 / 2)) : ℝ) = _
      rw [projIcc_of_mem _ ⟨by linarith, by linarith⟩]
      ring
  mem_iff t ht := by
    show (projIcc (1 / 2 : ℝ) (3 / 2) (by norm_num) (1 / 2 + t) : ℝ) = 1 / 2 ∨
      (projIcc (1 / 2 : ℝ) (3 / 2) (by norm_num) (1 / 2 + t) : ℝ) = 3 / 2 ↔ _
    have hp : (projIcc (1 / 2 : ℝ) (3 / 2) (by norm_num) (1 / 2 + t) : ℝ) = 1 / 2 + t := by
      rw [projIcc_of_mem _ ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    rw [hp]
    constructor
    · rintro (h | h)
      · left; linarith
      · right; linarith
    · rintro (h | h)
      · left; rw [h]; norm_num
      · right; rw [h]; norm_num
  subset u hu := by
    rcases hu with h | h <;>
      (show ((u : Dbl) : ℝ) ∈ Icc (1 / 2 : ℝ) (3 / 2); rw [h]; norm_num)

end Flow

end ConleyCheck.Conley
