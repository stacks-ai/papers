import ConleyCheck.Conley.Circle
import ConleyCheck.Conley.EquivHomology

/-!
# The action of `R` on the boundary indices of the circle double

The sheet exchange `R(x, θ) = (x, -θ)` of the double `X × S¹` acts on the homology of the boundary
indices. This file proves the sign statement of Proposition `prop:boundary` and with it
Theorem `thm:equivariant`(ii):

* the base data on the circle: contractions of `S¹ ∖ {0}` onto `π` and of `S¹ ∖ {π}` onto `0`
  through maps commuting with the base flow and with the reflection (`contractionPi`,
  `contractionZero`), the index pairs `({cos ≤ 0}, {cos = 0})` of `π` and `({cos ≥ 0}, ∅)` of `0`,
  and a chart of the arc `{cos ≤ 0}` intertwining `t ↦ 1 - t` with the reflection (`arcChart`);
* `circ_sign_repeller`: `R_* = -1` on `H_*(q⁻¹N₂, q⁻¹N₁)`, the homology index of `K₋ × {π}`;
* `circ_sign_attractor`: `R_* = +1` on `H_*(q⁻¹N₁, q⁻¹N₀)`, the homology index of `K₊ × {0}`;
* `equivariant_ii`: the connecting map `∂` of the attractor–repeller sequence of `S̃` satisfies
  `2∂ = 0`, so `∂ = 0` if the target has no `2`-torsion.

The paper states Theorem `thm:equivariant`(ii) in the stronger form `∂ = 0` over every coefficient
ring, proved with the projection `q` and Theorem `thm:slab`. That form is not proved here.
-/

namespace ConleyCheck.Conley

open Set Filter Topology unitInterval

open scoped Classical

universe u

/-! ### Points of the circle -/

namespace Circ

/-- The reflection as a continuous map. -/
def reflC : C(Circ, Circ) := ⟨refl, continuous_refl⟩

theorem refl_pi : refl pi = pi := (refl_eq_self_iff _).2 (Or.inr rfl)

theorem refl_zero : refl zero = zero := (refl_eq_self_iff _).2 (Or.inl rfl)

theorem tendsto_pi {Y : Type*} {F : Filter Y} {f : Y → Circ}
    (h : Tendsto (fun y => (f y).1.1) F (𝓝 (-1))) : Tendsto f F (𝓝 pi) := by
  have hs : ∀ y, ‖(f y).1.2‖ ≤ √(1 - (f y).1.1 ^ 2) := fun y => by
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    have := (f y).2
    exact Real.sqrt_le_sqrt (by linarith)
  have hc : Continuous fun x : ℝ => √(1 - x ^ 2) := by fun_prop
  have ht : Tendsto (fun y => √(1 - (f y).1.1 ^ 2)) F (𝓝 0) := by
    have := (hc.tendsto (-1)).comp h
    have e : √(1 - (-1 : ℝ) ^ 2) = 0 := by norm_num
    rw [e] at this
    exact this
  exact tendsto_subtype_rng.2 (h.prodMk_nhds (squeeze_zero_norm hs ht))

theorem tendsto_zero {Y : Type*} {F : Filter Y} {f : Y → Circ}
    (h : Tendsto (fun y => (f y).1.1) F (𝓝 1)) : Tendsto f F (𝓝 zero) := by
  have hs : ∀ y, ‖(f y).1.2‖ ≤ √(1 - (f y).1.1 ^ 2) := fun y => by
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    have := (f y).2
    exact Real.sqrt_le_sqrt (by linarith)
  have hc : Continuous fun x : ℝ => √(1 - x ^ 2) := by fun_prop
  have ht : Tendsto (fun y => √(1 - (f y).1.1 ^ 2)) F (𝓝 0) := by
    have := (hc.tendsto 1).comp h
    have e : √(1 - (1 : ℝ) ^ 2) = 0 := by norm_num
    rw [e] at this
    exact this
  exact tendsto_subtype_rng.2 (h.prodMk_nhds (squeeze_zero_norm hs ht))

end Circ

/-! ### Base contractions on the circle -/

section CircBase

variable {θ : Flow ℝ Tau} (hθ : IsHeight θ (fun b => (b : ℝ)))

theorem cflow_pi (t : ℝ) : cflow hθ t Circ.pi = Circ.pi := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show ((θ t Tau.bot : Tau) : ℝ) = -1
    rw [base_bot hθ]
    rfl
  · exact (csnd_eq_zero_iff hθ t _).2 rfl

theorem cflow_zero (t : ℝ) : cflow hθ t Circ.zero = Circ.zero := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show ((θ t Tau.top : Tau) : ℝ) = 1
    rw [base_top hθ]
    rfl
  · exact (csnd_eq_zero_iff hθ t _).2 rfl

/-- `S¹ ∖ {0}`. -/
def Upi : Set Circ := Circ.cos ⁻¹' Ubot

/-- `S¹ ∖ {π}`. -/
def Uzero : Set Circ := Circ.cos ⁻¹' Utop

omit hθ in
theorem isOpen_Upi : IsOpen Upi := isOpen_Ubot.preimage Circ.continuous_cos

omit hθ in
theorem isOpen_Uzero : IsOpen Uzero := isOpen_Utop.preimage Circ.continuous_cos

omit hθ in
theorem pi_mem_Upi : Circ.pi ∈ Upi := bot_mem_Ubot

omit hθ in
theorem zero_mem_Uzero : Circ.zero ∈ Uzero := top_mem_Utop

theorem isInvariant_Upi : IsInvariant (cflow hθ) Upi :=
  fun t _ hz => isInvariant_Ubot hθ t hz

theorem isInvariant_Uzero : IsInvariant (cflow hθ) Uzero :=
  fun t _ hz => isInvariant_Utop hθ t hz

omit hθ in
theorem rInv_Upi : RInv Circ.reflC Upi := fun _ => Iff.rfl

omit hθ in
theorem rInv_Uzero : RInv Circ.reflC Uzero := fun _ => Iff.rfl

/-- `g(λ, z) = θ_{log λ} z` on `S¹ ∖ {0}`, extended by `π` at `λ = 0`. -/
noncomputable def gPiFun (q : I × Upi) : Upi :=
  if (q.1 : ℝ) = 0 then ⟨Circ.pi, pi_mem_Upi⟩
  else (cflow hθ).restrict (isInvariant_Upi hθ) (Real.log q.1) q.2

/-- `g(λ, z) = θ_{-log λ} z` on `S¹ ∖ {π}`, extended by `0` at `λ = 0`. -/
noncomputable def gZeroFun (q : I × Uzero) : Uzero :=
  if (q.1 : ℝ) = 0 then ⟨Circ.zero, zero_mem_Uzero⟩
  else (cflow hθ).restrict (isInvariant_Uzero hθ) (-Real.log q.1) q.2

theorem gPiFun_cos (q : I × Upi) : (((gPiFun hθ q : Upi) : Circ).1.1) =
    (((gBotFun hθ (q.1, ⟨Circ.cos q.2, q.2.2⟩) : Ubot) : Tau) : ℝ) := by
  unfold gPiFun gBotFun
  split_ifs <;> rfl

theorem gZeroFun_cos (q : I × Uzero) : (((gZeroFun hθ q : Uzero) : Circ).1.1) =
    (((gTopFun hθ (q.1, ⟨Circ.cos q.2, q.2.2⟩) : Utop) : Tau) : ℝ) := by
  unfold gZeroFun gTopFun
  split_ifs <;> rfl

theorem continuous_gPiFun : Continuous (gPiFun hθ) := by
  refine continuous_iff_continuousAt.2 fun ⟨l, b⟩ => ?_
  by_cases hl : (l : ℝ) = 0
  · show Tendsto _ _ (𝓝 (gPiFun hθ (l, b)))
    have hv : gPiFun hθ (l, b) = ⟨Circ.pi, pi_mem_Upi⟩ := by
      unfold gPiFun
      exact ite_eq_left hl
    rw [hv, tendsto_subtype_rng]
    have hcU : Continuous fun q : I × Upi => (q.1, (⟨Circ.cos q.2, q.2.2⟩ : Ubot)) :=
      continuous_fst.prodMk ((Circ.continuous_cos.comp
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _)
    have hcont : Continuous fun q : I × Upi =>
        (((gBotFun hθ (q.1, ⟨Circ.cos q.2, q.2.2⟩) : Ubot) : Tau) : ℝ) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp ((continuous_gBotFun hθ).comp hcU))
    have h2 : (((gBotFun hθ (l, ⟨Circ.cos b, b.2⟩) : Ubot) : Tau) : ℝ) = -1 := by
      unfold gBotFun
      rw [ite_eq_left hl]
      rfl
    have h1 := (hcont.tendsto (l, b)).mono_right (le_of_eq (congrArg 𝓝 h2))
    exact Circ.tendsto_pi (h1.congr fun q => (gPiFun_cos hθ q).symm)
  · have hcont : ContinuousAt (fun q : I × Upi =>
        (cflow hθ).restrict (isInvariant_Upi hθ) (Real.log q.1) q.2) (l, b) :=
      ((cflow hθ).restrict (isInvariant_Upi hθ)).cont'.continuousAt.comp
        (((Real.continuousAt_log hl).comp (x := (l, b)) (f := fun q : I × Upi => (q.1 : ℝ))
          (continuous_subtype_val.comp continuous_fst).continuousAt).prodMk
            continuousAt_snd)
    refine hcont.congr ?_
    have hopen : IsOpen {q : I × Upi | (q.1 : ℝ) ≠ 0} :=
      isOpen_ne_fun (continuous_subtype_val.comp continuous_fst) continuous_const
    filter_upwards [hopen.mem_nhds hl] with q hq
    show _ = gPiFun hθ q
    rw [gPiFun, ite_eq_right hq]

theorem continuous_gZeroFun : Continuous (gZeroFun hθ) := by
  refine continuous_iff_continuousAt.2 fun ⟨l, b⟩ => ?_
  by_cases hl : (l : ℝ) = 0
  · show Tendsto _ _ (𝓝 (gZeroFun hθ (l, b)))
    have hv : gZeroFun hθ (l, b) = ⟨Circ.zero, zero_mem_Uzero⟩ := by
      unfold gZeroFun
      exact ite_eq_left hl
    rw [hv, tendsto_subtype_rng]
    have hcU : Continuous fun q : I × Uzero => (q.1, (⟨Circ.cos q.2, q.2.2⟩ : Utop)) :=
      continuous_fst.prodMk ((Circ.continuous_cos.comp
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _)
    have hcont : Continuous fun q : I × Uzero =>
        (((gTopFun hθ (q.1, ⟨Circ.cos q.2, q.2.2⟩) : Utop) : Tau) : ℝ) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp ((continuous_gTopFun hθ).comp hcU))
    have h2 : (((gTopFun hθ (l, ⟨Circ.cos b, b.2⟩) : Utop) : Tau) : ℝ) = 1 := by
      unfold gTopFun
      rw [ite_eq_left hl]
      rfl
    have h1 := (hcont.tendsto (l, b)).mono_right (le_of_eq (congrArg 𝓝 h2))
    exact Circ.tendsto_zero (h1.congr fun q => (gZeroFun_cos hθ q).symm)
  · have hcont : ContinuousAt (fun q : I × Uzero =>
        (cflow hθ).restrict (isInvariant_Uzero hθ) (-Real.log q.1) q.2) (l, b) :=
      ((cflow hθ).restrict (isInvariant_Uzero hθ)).cont'.continuousAt.comp
        (((Real.continuousAt_log hl).comp (x := (l, b)) (f := fun q : I × Uzero => (q.1 : ℝ))
          (continuous_subtype_val.comp continuous_fst).continuousAt).neg.prodMk
            continuousAt_snd)
    refine hcont.congr ?_
    have hopen : IsOpen {q : I × Uzero | (q.1 : ℝ) ≠ 0} :=
      isOpen_ne_fun (continuous_subtype_val.comp continuous_fst) continuous_const
    filter_upwards [hopen.mem_nhds hl] with q hq
    show _ = gZeroFun hθ q
    rw [gZeroFun, ite_eq_right hq]

/-- The base contraction of `S¹ ∖ {0}` onto the UV point `π`. -/
noncomputable def contractionPi :
    SkewContraction ((cflow hθ).restrict (isInvariant_Upi hθ)) ⟨Circ.pi, pi_mem_Upi⟩ where
  g := ⟨gPiFun hθ, continuous_gPiFun hθ⟩
  one b := by
    show gPiFun hθ (1, b) = b
    rw [gPiFun, ite_eq_right (by norm_num), Icc.coe_one, Real.log_one, Flow.map_zero_apply]
  zero b := by
    show gPiFun hθ (0, b) = _
    unfold gPiFun
    exact ite_eq_left rfl
  fix l := by
    show gPiFun hθ (l, _) = _
    unfold gPiFun
    split_ifs
    · rfl
    · exact Subtype.ext (cflow_pi hθ _)
  equivariant l t b := by
    show gPiFun hθ (l, _) = (cflow hθ).restrict _ t (gPiFun hθ (l, b))
    unfold gPiFun
    split_ifs
    · exact (Subtype.ext (cflow_pi hθ t)).symm
    · rw [← Flow.map_add, ← Flow.map_add, add_comm]

/-- The base contraction of `S¹ ∖ {π}` onto the IR point `0`. -/
noncomputable def contractionZero :
    SkewContraction ((cflow hθ).restrict (isInvariant_Uzero hθ)) ⟨Circ.zero, zero_mem_Uzero⟩ where
  g := ⟨gZeroFun hθ, continuous_gZeroFun hθ⟩
  one b := by
    show gZeroFun hθ (1, b) = b
    rw [gZeroFun, ite_eq_right (by norm_num), Icc.coe_one, Real.log_one, neg_zero,
      Flow.map_zero_apply]
  zero b := by
    show gZeroFun hθ (0, b) = _
    unfold gZeroFun
    exact ite_eq_left rfl
  fix l := by
    show gZeroFun hθ (l, _) = _
    unfold gZeroFun
    split_ifs
    · rfl
    · exact Subtype.ext (cflow_zero hθ _)
  equivariant l t b := by
    show gZeroFun hθ (l, _) = (cflow hθ).restrict _ t (gZeroFun hθ (l, b))
    unfold gZeroFun
    split_ifs
    · exact (Subtype.ext (cflow_zero hθ t)).symm
    · rw [← Flow.map_add, ← Flow.map_add, add_comm]

theorem contractionPi_refl (l : I) (b : Upi) :
    (contractionPi hθ).g (l, restrictR Circ.reflC rInv_Upi b) =
      restrictR Circ.reflC rInv_Upi ((contractionPi hθ).g (l, b)) := by
  show gPiFun hθ (l, _) = restrictR Circ.reflC rInv_Upi (gPiFun hθ (l, b))
  unfold gPiFun
  split_ifs
  · exact Subtype.ext Circ.refl_pi.symm
  · exact Subtype.ext (cflow_refl hθ _ _)

theorem contractionZero_refl (l : I) (b : Uzero) :
    (contractionZero hθ).g (l, restrictR Circ.reflC rInv_Uzero b) =
      restrictR Circ.reflC rInv_Uzero ((contractionZero hθ).g (l, b)) := by
  show gZeroFun hθ (l, _) = restrictR Circ.reflC rInv_Uzero (gZeroFun hθ (l, b))
  unfold gZeroFun
  split_ifs
  · exact Subtype.ext Circ.refl_zero.symm
  · exact Subtype.ext (cflow_refl hθ _ _)

/-- The cap `{cos ≥ 0}` is preserved by the contraction onto `0`. -/
theorem gZeroFun_cap (l : I) (b : Uzero) (hb : 0 ≤ (b : Circ).1.1) :
    0 ≤ ((gZeroFun hθ (l, b) : Uzero) : Circ).1.1 := by
  rw [gZeroFun_cos]
  unfold gTopFun
  split_ifs with hl
  · show (0 : ℝ) ≤ 1
    norm_num
  · have hpos : 0 < (l : ℝ) := lt_of_le_of_ne l.2.1 (Ne.symm hl)
    have hlog : 0 ≤ -Real.log l := neg_nonneg.2 (Real.log_nonpos hpos.le l.2.2)
    exact hb.trans (hθ.le_flow (Circ.cos b) hlog)

/-! ### Base index pairs -/

/-- `({cos ≤ 0}, {cos = 0})` is an index pair of the UV point `π`. -/
theorem isIndexPair_circPi :
    IsIndexPair (cflow hθ) {Circ.pi} (Circ.cos ⁻¹' {b : Tau | (b : ℝ) ≤ 0})
      (Circ.cos ⁻¹' {b : Tau | (b : ℝ) = 0}) := by
  have h := (isIndexPair_bot hθ).preimage_semiconj Circ.continuous_cos
    (fun t z => cos_cflow hθ t z)
    (fun K hK => (hK.isClosed.preimage Circ.continuous_cos).isCompact)
  have hs : Circ.cos ⁻¹' {Tau.bot} = {Circ.pi} := by
    ext z
    exact Circ.cos_eq_bot_iff z
  rwa [hs] at h

/-- `({cos ≥ 0}, ∅)` is an index pair of the IR point `0`. -/
theorem isIndexPair_circZero :
    IsIndexPair (cflow hθ) {Circ.zero} (Circ.cos ⁻¹' {b : Tau | 0 ≤ (b : ℝ)}) ∅ := by
  have h := (isIndexPair_top hθ).preimage_semiconj Circ.continuous_cos
    (fun t z => cos_cflow hθ t z)
    (fun K hK => (hK.isClosed.preimage Circ.continuous_cos).isCompact)
  have hs : Circ.cos ⁻¹' {Tau.top} = {Circ.zero} := by
    ext z
    exact Circ.cos_eq_top_iff z
  rwa [hs, preimage_empty] at h

end CircBase

/-! ### The arc through `π` -/

section Arc

/-- `t ↦ max 0 (min 1 t)`. -/
noncomputable def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clamp01_mem (t : ℝ) : clamp01 t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem clamp01_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clamp01 t = t := by
  rw [clamp01, min_eq_right ht.2, max_eq_right ht.1]

theorem clamp01_one_sub (t : ℝ) : clamp01 (1 - t) = 1 - clamp01 t := by
  unfold clamp01
  rcases le_total t 0 with h | h
  · rw [min_eq_left (by linarith), max_eq_right zero_le_one, min_eq_right (h.trans zero_le_one),
      max_eq_left h]
    ring
  · rcases le_total t 1 with h' | h'
    · rw [min_eq_right (by linarith), max_eq_right (by linarith), min_eq_right h', max_eq_right h]
    · rw [min_eq_right (by linarith), max_eq_left (by linarith), min_eq_left h',
        max_eq_right zero_le_one]
      ring

/-- `s ↦ (-sin πs, cos πs)`, the arc from `π/2` through `π` to `3π/2`. -/
noncomputable def arcPt (s : ℝ) : Circ :=
  ⟨(-Real.sin (Real.pi * s), Real.cos (Real.pi * s)), by
    rw [neg_sq]; exact Real.sin_sq_add_cos_sq _⟩

theorem sin_pi_mul_nonneg {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 0 ≤ Real.sin (Real.pi * s) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le hs.1)
    (by nlinarith [Real.pi_pos, hs.2])

theorem arcPt_mem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : arcPt s ∈ Upi := by
  show -Real.sin (Real.pi * s) < 1
  linarith [sin_pi_mul_nonneg hs]

/-- The chart of the arc `{cos ≤ 0}` in `S¹ ∖ {0}`. -/
noncomputable def arcE : C(ℝ, Upi) :=
  ⟨fun t => ⟨arcPt (clamp01 t), arcPt_mem (clamp01_mem t)⟩, by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_clamp01)).neg).prodMk
      (Real.continuous_cos.comp (continuous_const.mul continuous_clamp01))⟩

theorem arcE_val {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ((arcE t : Upi) : Circ).1 = (-Real.sin (Real.pi * t), Real.cos (Real.pi * t)) := by
  show (arcPt (clamp01 t)).1 = _
  rw [clamp01_of_mem ht]
  rfl

theorem arcE_one_sub (t : ℝ) :
    arcE (1 - t) = restrictR Circ.reflC rInv_Upi (arcE t) := by
  refine Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))
  · show -Real.sin (Real.pi * clamp01 (1 - t)) = -Real.sin (Real.pi * clamp01 t)
    rw [clamp01_one_sub, mul_one_sub, Real.sin_pi_sub]
  · show Real.cos (Real.pi * clamp01 (1 - t)) = -Real.cos (Real.pi * clamp01 t)
    rw [clamp01_one_sub, mul_one_sub, Real.cos_pi_sub]

/-- The arc `({cos ≤ 0}, {cos = 0})` with its chart. -/
noncomputable def arcChart :
    IntervalChart (Subtype.val ⁻¹' (Circ.cos ⁻¹' {b : Tau | (b : ℝ) ≤ 0}) : Set Upi)
      (Subtype.val ⁻¹' (Circ.cos ⁻¹' {b : Tau | (b : ℝ) = 0}) : Set Upi) where
  e := arcE
  injOn s hs s' hs' h := by
    have h2 := congrArg (fun u : Upi => ((u : Circ).1).2) h
    change ((arcE s : Upi) : Circ).1.2 = ((arcE s' : Upi) : Circ).1.2 at h2
    rw [arcE_val hs, arcE_val hs'] at h2
    have := Real.injOn_cos ⟨mul_nonneg Real.pi_pos.le hs.1, by nlinarith [Real.pi_pos, hs.2]⟩
      ⟨mul_nonneg Real.pi_pos.le hs'.1, by nlinarith [Real.pi_pos, hs'.2]⟩ h2
    exact mul_left_cancel₀ Real.pi_pos.ne' this
  image_eq := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      show ((arcE t : Upi) : Circ).1.1 ≤ 0
      rw [arcE_val ht]
      exact neg_nonpos.2 (sin_pi_mul_nonneg ht)
    · intro hu
      have hc : ((u : Circ).1.1) ≤ 0 := hu
      have hu2 := (u : Circ).2
      have hs1 : -1 ≤ (u : Circ).1.2 := by nlinarith [sq_nonneg ((u : Circ).1.1)]
      have hs2 : (u : Circ).1.2 ≤ 1 := by nlinarith [sq_nonneg ((u : Circ).1.1)]
      set t := Real.arccos ((u : Circ).1.2) / Real.pi with ht
      have htm : t ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le,
          (div_le_one Real.pi_pos).2 (Real.arccos_le_pi _)⟩
      have hpt : Real.pi * t = Real.arccos ((u : Circ).1.2) := by
        rw [ht, mul_div_cancel₀ _ Real.pi_pos.ne']
      refine ⟨t, htm, Subtype.ext (Subtype.ext ?_)⟩
      rw [arcE_val htm, hpt, Real.cos_arccos hs1 hs2, Real.sin_arccos]
      refine Prod.ext ?_ rfl
      show -√(1 - (u : Circ).1.2 ^ 2) = (u : Circ).1.1
      rw [show 1 - (u : Circ).1.2 ^ 2 = (u : Circ).1.1 ^ 2 by linarith, Real.sqrt_sq_eq_abs,
        abs_of_nonpos hc, neg_neg]
  mem_iff t ht := by
    show ((arcE t : Upi) : Circ).1.1 = 0 ↔ _
    rw [arcE_val ht]
    show -Real.sin (Real.pi * t) = 0 ↔ _
    constructor
    · intro h
      by_contra hne
      push Not at hne
      have h0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hne.1)
      have h1 : t < 1 := lt_of_le_of_ne ht.2 hne.2
      have := Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos h0)
        (by nlinarith [Real.pi_pos])
      linarith
    · rintro (rfl | rfl)
      · simp
      · simp
  subset u hu := le_of_eq hu

end Arc

/-! ### Generalities -/

theorem isDeformCollared_of_forall_notMem {α : Type u} [TopologicalSpace α] (N L : Set α)
    (hL : ∀ x, x ∉ L) : IsDeformCollared N L :=
  ⟨∅, ∅, ⟨Prod.snd, continuous_snd⟩, isOpen_empty, fun _ hx => absurd hx (hL _),
    fun _ h => h.1, empty_subset _, fun _ => rfl, fun _ _ hx => absurd hx (hL _),
    fun _ _ hx => absurd hx (notMem_empty _), fun _ hx => absurd hx (notMem_empty _)⟩

/-! ### The double -/

section DoubleSign

variable {X : Type u} [TopologicalSpace X] [T2Space X] [TopologicalSpace.MetrizableSpace X]
  {Φ : Flow ℝ (X × Tau)} {θ : Flow ℝ Tau} (hΦ : IsSkew Φ θ) (hθ : IsHeight θ (fun b => (b : ℝ)))

omit [T2Space X] [TopologicalSpace.MetrizableSpace X] in
theorem isSkew_circ : IsSkew (circΦ hΦ hθ) (cflow hθ) := fun _ _ => rfl

omit [T2Space X] [TopologicalSpace.MetrizableSpace X] in
theorem circΦ_rprod (t : ℝ) (p : X × Circ) :
    circΦ hΦ hθ t (rprod Circ.reflC p) = rprod Circ.reflC (circΦ hΦ hθ t p) :=
  (cR_circΦ hΦ hθ t p).symm

omit [TopologicalSpace X] [T2Space X] [TopologicalSpace.MetrizableSpace X] in
theorem rInv_cq_preimage [TopologicalSpace X] (M : Set (X × Tau)) :
    RInv (rprod Circ.reflC) (cq ⁻¹' M) := fun _ => Iff.rfl

omit [TopologicalSpace.MetrizableSpace X] in
theorem circ_pair {S N L : Set (X × Tau)} (h : IsIndexPair Φ S N L) :
    IsIndexPair (circΦ hΦ hθ) (cq ⁻¹' S) (cq ⁻¹' N) (cq ⁻¹' L) :=
  h.preimage_semiconj continuous_cq (cq_circΦ hΦ hθ) fun _ hM => isCompact_cq_preimage hM

omit [T2Space X] [TopologicalSpace.MetrizableSpace X] in
/-- Collars pull back to the double. -/
theorem circ_collared {N L : Set (X × Tau)} (hc : IsCollared Φ N L) :
    IsCollared (circΦ hΦ hθ) (cq ⁻¹' N) (cq ⁻¹' L) := by
  obtain ⟨V, O, τ, hO, hLO, hON, hVN, hτc, hτ01, hτL, hseg, hhit⟩ := hc
  let f : (cq ⁻¹' V : Set (X × Circ)) → V := fun y => ⟨cq (y : X × Circ), y.2⟩
  have hf : Continuous f := (continuous_cq.comp continuous_subtype_val).subtype_mk _
  refine ⟨cq ⁻¹' V, cq ⁻¹' O, τ ∘ f, hO.preimage continuous_cq, preimage_mono hLO,
    fun y hy => hON hy, preimage_mono hVN, hτc.comp hf, fun y => hτ01 (f y),
    fun y hy => hτL (f y) hy, fun y s hs => ?_, fun y => ?_⟩
  · show cq (circΦ hΦ hθ s y) ∈ V
    rw [cq_circΦ]
    exact hseg (f y) s hs
  · show cq (circΦ hΦ hθ _ y) ∈ L
    rw [cq_circΦ]
    exact hhit (f y)

omit [T2Space X] [TopologicalSpace.MetrizableSpace X] in
theorem circ_f₀_pi :
    (contractionPi hθ).f₀ (isSkew_circ hΦ hθ) (isInvariant_Upi hθ) pi_mem_Upi =
      fiberFlow hΦ Tau.bot (base_bot hθ) :=
  Flow.ext fun _ _ => rfl

omit [T2Space X] [TopologicalSpace.MetrizableSpace X] in
theorem circ_f₀_zero :
    (contractionZero hθ).f₀ (isSkew_circ hΦ hθ) (isInvariant_Uzero hθ) zero_mem_Uzero =
      fiberFlow hΦ Tau.top (base_top hθ) :=
  Flow.ext fun _ _ => rfl

omit [TopologicalSpace X] [T2Space X] [TopologicalSpace.MetrizableSpace X] in
theorem circ_Nb_pi :
    Circ.cos ⁻¹' {b : Tau | (b : ℝ) ≤ 0} ⊆ Upi := fun z (hz : ((Circ.cos z : Tau) : ℝ) ≤ 0) =>
  show ((Circ.cos z : Tau) : ℝ) < 1 by linarith

omit [TopologicalSpace X] [T2Space X] [TopologicalSpace.MetrizableSpace X] in
theorem circ_Nb_zero :
    Circ.cos ⁻¹' {b : Tau | 0 ≤ (b : ℝ)} ⊆ Uzero := fun z (hz : 0 ≤ ((Circ.cos z : Tau) : ℝ)) =>
  show (-1 : ℝ) < ((Circ.cos z : Tau) : ℝ) by linarith

omit [TopologicalSpace.MetrizableSpace X] in
include hΦ hθ in
/-- The fibers of an isolating neighborhood of `S` over `τ = ±1` isolate `K_±`. -/
theorem fiber_isolating_pm {S : Set (X × Tau)} (hS : IsIsolatedInvariantSet Φ S) :
    ∃ MT MB, IsIsolatingNbhd (fiberFlow hΦ Tau.top (base_top hθ)) MT ∧
      Inv (fiberFlow hΦ Tau.top (base_top hθ)) MT = {x | (x, Tau.top) ∈ S} ∧
      IsIsolatingNbhd (fiberFlow hΦ Tau.bot (base_bot hθ)) MB ∧
      Inv (fiberFlow hΦ Tau.bot (base_bot hθ)) MB = {x | (x, Tau.bot) ∈ S} := by
  obtain ⟨N, hN, hNS⟩ := hS
  obtain ⟨hMT, hInvT⟩ := hΦ.fiber_isolating (base_top hθ) hN
  obtain ⟨hMB, hInvB⟩ := hΦ.fiber_isolating (base_bot hθ) hN
  rw [hNS] at hInvT hInvB
  exact ⟨_, _, hMT, hInvT, hMB, hInvB⟩

variable (K : Type u) [Ring K]

include hΦ hθ in
/-- Proposition `prop:boundary`, sign at `π`: `R_* = -1` on `H_*(q⁻¹N₂, q⁻¹N₁)` for every collared
index pair `(N₂, N₁)` of the repeller `K₋ × {-1}` of `S`, with any coefficients. -/
theorem circ_sign_repeller {S : Set (X × Tau)} (hS : IsIsolatedInvariantSet Φ S)
    {N₂ N₁ : Set (X × Tau)} (hP : IsIndexPair Φ (S ∩ (fun p => (p.2 : ℝ)) ⁻¹' {-1}) N₂ N₁)
    (hc : IsCollared Φ N₂ N₁) (k : ℤ) (z : singH K (X × Circ) k (cq ⁻¹' N₂) (cq ⁻¹' N₁)) :
    (pairAct K (rprod Circ.reflC) (rInv_cq_preimage N₂) (rInv_cq_preimage N₁) k).hom z = -z := by
  obtain ⟨-, MB, -, -, hMB, hInvB⟩ := fiber_isolating_pm hΦ hθ hS
  have hΦc := isSkew_circ hΦ hθ
  have hf := circ_f₀_pi hΦ hθ
  have hM : IsIsolatingNbhd ((contractionPi hθ).f₀ hΦc (isInvariant_Upi hθ) pi_mem_Upi) MB := by
    rw [hf]; exact hMB
  have hNb : RInv Circ.reflC (Circ.cos ⁻¹' {b : Tau | (b : ℝ) ≤ 0}) := fun _ => Iff.rfl
  have hLb : RInv Circ.reflC (Circ.cos ⁻¹' {b : Tau | (b : ℝ) = 0}) := fun _ => Iff.rfl
  obtain ⟨N', L', hN', hL', hP', hE⟩ := skew_boundary_setup_equivariant hΦc
    (isInvariant_Upi hθ) isOpen_Upi pi_mem_Upi (contractionPi hθ) (ρ := Circ.reflC)
    Circ.refl_refl (cflow_refl hθ) (fun _ _ _ => rfl) rInv_Upi hM (isIndexPair_circPi hθ)
    circ_Nb_pi (contractionPi_refl hθ) hNb hLb
  have hRset : Inv ((contractionPi hθ).f₀ hΦc (isInvariant_Upi hθ) pi_mem_Upi) MB ×ˢ
      {Circ.pi} = cq ⁻¹' (S ∩ (fun p : X × Tau => (p.2 : ℝ)) ⁻¹' {-1}) := by
    rw [hf, hInvB]
    exact (cq_preimage_inter_bot S).symm
  rw [hRset] at hP'
  have hpair := circ_pair hΦ hθ hP
  obtain ⟨e₂, he₂⟩ := indexPair_unique_equivariant hP' hpair (circΦ_rprod hΦ hθ) hN' hL'
    (rInv_cq_preimage N₂) (rInv_cq_preimage N₁)
  obtain ⟨NK, LK, hPK, hcK⟩ := exists_deformCollared_indexPair
    (⟨_, hM, rfl⟩ : IsIsolatedInvariantSet
      ((contractionPi hθ).f₀ hΦc (isInvariant_Upi hθ) pi_mem_Upi)
      (Inv ((contractionPi hθ).f₀ hΦc (isInvariant_Upi hθ) pi_mem_Upi) MB))
  obtain ⟨e₁, he₁⟩ := hE NK LK hPK
  have hb := isIndexPair_circPi hθ
  have hJc : IsClosed (Subtype.val ⁻¹' (Circ.cos ⁻¹' {b : Tau | (b : ℝ) ≤ 0}) : Set Upi) :=
    hb.isCompact_N.isClosed.preimage continuous_subtype_val
  have hDc : IsClosed (Subtype.val ⁻¹' (Circ.cos ⁻¹' {b : Tau | (b : ℝ) = 0}) : Set Upi) :=
    hb.isCompact_L.isClosed.preimage continuous_subtype_val
  have hQc := (hPK.isCompact_L.isClosed.prod hJc).union (hPK.isCompact_N.isClosed.prod hDc)
  have hQP : LK ×ˢ (Subtype.val ⁻¹' (Circ.cos ⁻¹' {b : Tau | (b : ℝ) ≤ 0}) : Set Upi) ∪
      NK ×ˢ (Subtype.val ⁻¹' (Circ.cos ⁻¹' {b : Tau | (b : ℝ) = 0}) : Set Upi) ⊆
      NK ×ˢ (Subtype.val ⁻¹' (Circ.cos ⁻¹' {b : Tau | (b : ℝ) ≤ 0}) : Set Upi) := by
    rintro p (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨hPK.subset h1, h2⟩
    · exact ⟨h1, hb.subset h2⟩
  have hp := projMap_bijective_of_deform K hQc hQP (hcK.prod arcChart.isDeformCollared) k
  have hp' := projMap_bijective K (cq ⁻¹' N₂) (cq ⁻¹' N₁) hpair (circ_collared hΦ hθ hc) k
  rw [act_transfer K ((RInv.val_preimage rInv_Upi hNb).prod NK)
    (((RInv.val_preimage rInv_Upi hNb).prod LK).union ((RInv.val_preimage rInv_Upi hLb).prod NK))
    (rInv_cq_preimage N₂) (rInv_cq_preimage N₁) (e₁.trans e₂) (he₁.trans he₂) k hp hp' (-1)
    (fun z => pairAct_chart_neg K arcChart arcE_one_sub (RInv.val_preimage rInv_Upi hNb)
      (RInv.val_preimage rInv_Upi hLb) hPK.subset k z) z, neg_one_smul]

include hΦ hθ in
/-- Proposition `prop:boundary`, sign at `0`: `R_* = +1` on `H_*(q⁻¹N₁, q⁻¹N₀)` for every collared
index pair `(N₁, N₀)` of the attractor `K₊ × {1}` of `S`, with any coefficients. -/
theorem circ_sign_attractor {S : Set (X × Tau)} (hS : IsIsolatedInvariantSet Φ S)
    {N₁ N₀ : Set (X × Tau)} (hP : IsIndexPair Φ (S ∩ (fun p => (p.2 : ℝ)) ⁻¹' {1}) N₁ N₀)
    (hc : IsCollared Φ N₁ N₀) (k : ℤ) (z : singH K (X × Circ) k (cq ⁻¹' N₁) (cq ⁻¹' N₀)) :
    (pairAct K (rprod Circ.reflC) (rInv_cq_preimage N₁) (rInv_cq_preimage N₀) k).hom z = z := by
  obtain ⟨MT, -, hMT, hInvT, -, -⟩ := fiber_isolating_pm hΦ hθ hS
  have hΦc := isSkew_circ hΦ hθ
  have hf := circ_f₀_zero hΦ hθ
  have hM : IsIsolatingNbhd ((contractionZero hθ).f₀ hΦc (isInvariant_Uzero hθ) zero_mem_Uzero)
      MT := by
    rw [hf]; exact hMT
  have hNb : RInv Circ.reflC (Circ.cos ⁻¹' {b : Tau | 0 ≤ (b : ℝ)}) := fun _ => Iff.rfl
  obtain ⟨N', L', hN', hL', hP', hE⟩ := skew_boundary_setup_equivariant hΦc
    (isInvariant_Uzero hθ) isOpen_Uzero zero_mem_Uzero (contractionZero hθ) (ρ := Circ.reflC)
    Circ.refl_refl (cflow_refl hθ) (fun _ _ _ => rfl) rInv_Uzero hM (isIndexPair_circZero hθ)
    circ_Nb_zero (contractionZero_refl hθ) hNb RInv.empty
  have hAset : Inv ((contractionZero hθ).f₀ hΦc (isInvariant_Uzero hθ) zero_mem_Uzero) MT ×ˢ
      {Circ.zero} = cq ⁻¹' (S ∩ (fun p : X × Tau => (p.2 : ℝ)) ⁻¹' {1}) := by
    rw [hf, hInvT]
    exact (cq_preimage_inter_top S).symm
  rw [hAset] at hP'
  have hpair := circ_pair hΦ hθ hP
  obtain ⟨e₂, he₂⟩ := indexPair_unique_equivariant hP' hpair (circΦ_rprod hΦ hθ) hN' hL'
    (rInv_cq_preimage N₁) (rInv_cq_preimage N₀)
  obtain ⟨NK, LK, hPK, hcK⟩ := exists_deformCollared_indexPair
    (⟨_, hM, rfl⟩ : IsIsolatedInvariantSet
      ((contractionZero hθ).f₀ hΦc (isInvariant_Uzero hθ) zero_mem_Uzero)
      (Inv ((contractionZero hθ).f₀ hΦc (isInvariant_Uzero hθ) zero_mem_Uzero) MT))
  have hb := isIndexPair_circZero hθ
  set J := (Subtype.val ⁻¹' (Circ.cos ⁻¹' {b : Tau | 0 ≤ (b : ℝ)}) : Set Uzero) with hJ
  set D := (Subtype.val ⁻¹' (∅ : Set Circ) : Set Uzero) with hD
  obtain ⟨e₁, he₁⟩ := hE NK LK hPK
  have hDe : ∀ u, u ∉ D := fun u hu => notMem_empty (u : Circ) hu
  have hJc : IsClosed J := hb.isCompact_N.isClosed.preimage continuous_subtype_val
  have hQc : IsClosed (LK ×ˢ J ∪ NK ×ˢ D) :=
    (hPK.isCompact_L.isClosed.prod hJc).union (hPK.isCompact_N.isClosed.prod
      (isClosed_empty.preimage continuous_subtype_val))
  have hQP : LK ×ˢ J ∪ NK ×ˢ D ⊆ NK ×ˢ J := by
    rintro p (⟨h1, h2⟩ | ⟨-, h2⟩)
    · exact ⟨hPK.subset h1, h2⟩
    · exact absurd h2 (hDe _)
  have hp := projMap_bijective_of_deform K hQc hQP
    (hcK.prod (isDeformCollared_of_forall_notMem J D hDe)) k
  have hp' := projMap_bijective K (cq ⁻¹' N₁) (cq ⁻¹' N₀) hpair (circ_collared hΦ hθ hc) k
  let ρU := restrictR Circ.reflC rInv_Uzero
  let g := (contractionZero hθ).g
  have hcap : ∀ (s : I) (u : Uzero), u ∈ J → g (s, u) ∈ J := fun s u hu =>
    gZeroFun_cap hθ s u hu
  let F : C(I × (X × Uzero), X × Uzero) :=
    ⟨fun q => (q.2.1, g (σ q.1, ρU q.2.2)), (continuous_fst.comp continuous_snd).prodMk
      (g.continuous.comp ((continuous_symm.comp continuous_fst).prodMk
        (ρU.continuous.comp (continuous_snd.comp continuous_snd))))⟩
  let G : C(I × (X × Uzero), X × Uzero) :=
    ⟨fun q => (q.2.1, g (σ q.1, q.2.2)), (continuous_fst.comp continuous_snd).prodMk
      (g.continuous.comp ((continuous_symm.comp continuous_fst).prodMk
        (continuous_snd.comp continuous_snd)))⟩
  let c : C(X × Uzero, X × Uzero) :=
    ⟨fun q => (q.1, ⟨Circ.zero, zero_mem_Uzero⟩), continuous_fst.prodMk continuous_const⟩
  have hF0 : ∀ q, F (0, q) = rprod ρU q := fun q => by
    show (q.1, g (σ 0, ρU q.2)) = (q.1, ρU q.2)
    rw [symm_zero, (contractionZero hθ).one]
  have hF1 : ∀ q, F (1, q) = c q := fun q => by
    show (q.1, g (σ 1, ρU q.2)) = (q.1, _)
    rw [symm_one, (contractionZero hθ).zero]
  have hG0 : ∀ q, G (0, q) = q := fun q => by
    show (q.1, g (σ 0, q.2)) = q
    rw [symm_zero, (contractionZero hθ).one]
  have hG1 : ∀ q, G (1, q) = c q := fun q => by
    show (q.1, g (σ 1, q.2)) = (q.1, _)
    rw [symm_one, (contractionZero hθ).zero]
  have hFN : ∀ s, ∀ q ∈ NK ×ˢ J, F (s, q) ∈ NK ×ˢ J := fun s q hq =>
    ⟨hq.1, hcap _ (ρU q.2) hq.2⟩
  have hGN : ∀ s, ∀ q ∈ NK ×ˢ J, G (s, q) ∈ NK ×ˢ J := fun s q hq =>
    ⟨hq.1, hcap _ q.2 hq.2⟩
  have hFL : ∀ s, ∀ q ∈ LK ×ˢ J ∪ NK ×ˢ D, F (s, q) ∈ LK ×ˢ J ∪ NK ×ˢ D := by
    rintro s q (⟨h1, h2⟩ | ⟨-, h2⟩)
    · exact Or.inl ⟨h1, hcap _ (ρU q.2) h2⟩
    · exact absurd h2 (hDe _)
  have hGL : ∀ s, ∀ q ∈ LK ×ˢ J ∪ NK ×ˢ D, G (s, q) ∈ LK ×ˢ J ∪ NK ×ˢ D := by
    rintro s q (⟨h1, h2⟩ | ⟨-, h2⟩)
    · exact Or.inl ⟨h1, hcap _ q.2 h2⟩
    · exact absurd h2 (hDe _)
  have hN₀ : RInv (rprod ρU) (NK ×ˢ J) := (RInv.val_preimage rInv_Uzero hNb).prod NK
  have hL₀ : RInv (rprod ρU) (LK ×ˢ J ∪ NK ×ˢ D) :=
    ((RInv.val_preimage rInv_Uzero hNb).prod LK).union
      ((RInv.val_preimage rInv_Uzero RInv.empty).prod NK)
  rw [act_transfer K hN₀ hL₀ (rInv_cq_preimage N₁) (rInv_cq_preimage N₀) (e₁.trans e₂)
    (he₁.trans he₂) k hp hp' 1
    (fun z => pairAct_eq_self_of_homotopy K hQP hN₀ hL₀ F G hF0 hF1 hG0 hG1 hFN hFL hGN hGL k z)
    z, one_smul]

include hΦ hθ in
/-- Proposition `prop:boundary`, double row at `0`: `CH_*(K₊ × {0}) ≅ CH_*(K₊; f₊)`. -/
theorem circ_index_attractor {S : Set (X × Tau)}
    (hA : IsIsolatedInvariantSet (circΦ hΦ hθ) ({x | (x, Tau.top) ∈ S} ×ˢ {Circ.zero}))
    (hK : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ)) {x | (x, Tau.top) ∈ S})
    (n : ℕ) :
    Nonempty (homologyIndex K (circΦ hΦ hθ) hA n ≃ₗ[K]
      homologyIndex K (fiberFlow hΦ Tau.top (base_top hθ)) hK n) := by
  obtain ⟨M, hM, hMS⟩ := id hK
  have hΦc := isSkew_circ hΦ hθ
  have hf := circ_f₀_zero hΦ hθ
  set f₀ := (contractionZero hθ).f₀ hΦc (isInvariant_Uzero hθ) zero_mem_Uzero
  have hM' : IsIsolatingNbhd f₀ M := by rw [hf]; exact hM
  have hK' : IsIsolatedInvariantSet f₀ (Inv f₀ M) := ⟨M, hM', rfl⟩
  have hInv : Inv f₀ M = {x | (x, Tau.top) ∈ S} := by rw [hf]; exact hMS
  obtain ⟨NK, LK, hPK, -⟩ := exists_indexPair_of_t2 hM'
  have hb := isIndexPair_circZero hθ
  let g := (contractionZero hθ).g
  let H : C(I × (Subtype.val ⁻¹' (Circ.cos ⁻¹' {b : Tau | 0 ≤ (b : ℝ)}) : Set Uzero),
      (Subtype.val ⁻¹' (Circ.cos ⁻¹' {b : Tau | 0 ≤ (b : ℝ)}) : Set Uzero)) :=
    ⟨fun q => ⟨g (σ q.1, q.2), gZeroFun_cap hθ _ _ q.2.2⟩, Continuous.subtype_mk
      (g.continuous.comp ((continuous_symm.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))) _⟩
  have hb₀ : Circ.zero ∈ Circ.cos ⁻¹' {b : Tau | 0 ≤ (b : ℝ)} :=
    show (0 : ℝ) ≤ 1 by norm_num
  obtain ⟨NA, LA, hPA, ⟨e⟩⟩ := skew_hasIndex hΦc (isInvariant_Uzero hθ) isOpen_Uzero
    zero_mem_Uzero (contractionZero hθ) hM' hb circ_Nb_zero hb₀ H
    (fun q => Subtype.ext (by
      show g (σ 0, _) = _
      rw [symm_zero, (contractionZero hθ).one]))
    (fun q => Subtype.ext (by
      show g (σ 1, _) = _
      rw [symm_one, (contractionZero hθ).zero])) hPK
  have hS' : IsIsolatedInvariantSet (circΦ hΦ hθ) (Inv f₀ M ×ˢ {Circ.zero}) := by
    rw [hInv]; exact hA
  obtain ⟨iso₁⟩ := homologyIndexIso K hS' hPA n
  obtain ⟨iso₃⟩ := homologyIndexIso K hK' hPK n
  obtain ⟨t₁⟩ := homologyIndex_congr K rfl (by rw [hInv]) hA hS' n
  obtain ⟨t₂⟩ := homologyIndex_congr K hf hInv hK' hK n
  exact ⟨t₁.trans (iso₁.toLinearEquiv.trans ((redIso K e n).toLinearEquiv.trans
    (iso₃.symm.toLinearEquiv.trans t₂)))⟩

include hΦ hθ in
/-- Proposition `prop:boundary`, double row at `π`: `CH_{n+1}(K₋ × {π}) ≅ CH_n(K₋; f₋)` and
`CH_0(K₋ × {π}) = 0`. -/
theorem circ_index_repeller {S : Set (X × Tau)}
    (hR : IsIsolatedInvariantSet (circΦ hΦ hθ) ({x | (x, Tau.bot) ∈ S} ×ˢ {Circ.pi}))
    (hK : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ)) {x | (x, Tau.bot) ∈ S}) :
    (∀ n : ℕ, Nonempty (homologyIndex K (circΦ hΦ hθ) hR (n + 1) ≃ₗ[K]
      homologyIndex K (fiberFlow hΦ Tau.bot (base_bot hθ)) hK n)) ∧
      Subsingleton (homologyIndex K (circΦ hΦ hθ) hR 0) := by
  obtain ⟨M, hM, hMS⟩ := id hK
  have hΦc := isSkew_circ hΦ hθ
  have hf := circ_f₀_pi hΦ hθ
  set f₀ := (contractionPi hθ).f₀ hΦc (isInvariant_Upi hθ) pi_mem_Upi
  have hM' : IsIsolatingNbhd f₀ M := by rw [hf]; exact hM
  have hK' : IsIsolatedInvariantSet f₀ (Inv f₀ M) := ⟨M, hM', rfl⟩
  have hInv : Inv f₀ M = {x | (x, Tau.bot) ∈ S} := by rw [hf]; exact hMS
  have hS' : IsIsolatedInvariantSet (circΦ hΦ hθ) (Inv f₀ M ×ˢ {Circ.pi}) := by
    rw [hInv]; exact hR
  obtain ⟨t₁⟩ := homologyIndex_congr K rfl (by rw [hInv]) hR hS' 0
  refine ⟨fun n => ?_, ?_⟩
  · obtain ⟨e⟩ := skew_suspension K hΦc (isInvariant_Upi hθ) isOpen_Upi pi_mem_Upi
      (contractionPi hθ) hM' (isIndexPair_circPi hθ) circ_Nb_pi arcChart hS' hK' n
    obtain ⟨t₁⟩ := homologyIndex_congr K rfl (by rw [hInv]) hR hS' (n + 1)
    obtain ⟨t₂⟩ := homologyIndex_congr K hf hInv hK' hK n
    exact ⟨t₁.trans (e.trans t₂)⟩
  · have := skew_suspension_zero K hΦc (isInvariant_Upi hθ) isOpen_Upi pi_mem_Upi
      (contractionPi hθ) hM' (isIndexPair_circPi hθ) circ_Nb_pi arcChart hS' hK'
    exact t₁.toEquiv.subsingleton

include hΦ hθ in
/-- Theorem `thm:equivariant`(ii). Let `(K₊ × {0}, K₋ × {π})` be the attractor–repeller pair of
`S̃ = q⁻¹(S)` in the circle double. Its homology sequence
`⋯ → CH_n(K₊ × {0}) → CH_n(S̃) → CH_n(K₋ × {π}) → CH_{n-1}(K₊ × {0}) → ⋯` has a connecting map
`∂` with `2∂ = 0`, over any coefficient ring. If `CH_*(K₊ × {0})` has no `2`-torsion (for instance
if it is torsion free over `ℤ`, or if `2` is invertible in `K`), then `∂ = 0` and
`0 → CH_n(K₊ × {0}) → CH_n(S̃) → CH_n(K₋ × {π}) → 0` is exact. -/
theorem equivariant_ii {S : Set (X × Tau)} (hS : IsIsolatedInvariantSet Φ S)
    (h : IsAttractorRepellerPair (circΦ hΦ hθ) (cq ⁻¹' S) ({x | (x, Tau.top) ∈ S} ×ˢ {Circ.zero})
      ({x | (x, Tau.bot) ∈ S} ×ˢ {Circ.pi})) :
    ∃ (i : ∀ n, homologyIndex K (circΦ hΦ hθ) h.isolated_A n →ₗ[K]
        homologyIndex K (circΦ hΦ hθ) h.isolated n)
      (p : ∀ n, homologyIndex K (circΦ hΦ hθ) h.isolated n →ₗ[K]
        homologyIndex K (circΦ hΦ hθ) h.isolated_R n)
      (d : ∀ n, homologyIndex K (circΦ hΦ hθ) h.isolated_R (n + 1) →ₗ[K]
        homologyIndex K (circΦ hΦ hθ) h.isolated_A n),
      (∀ n, Function.Exact (i n) (p n)) ∧ (∀ n, Function.Exact (p (n + 1)) (d n)) ∧
      (∀ n, Function.Exact (d n) (i n)) ∧ Function.Surjective (p 0) ∧
      (∀ n z, (2 : ℕ) • d n z = 0) ∧
      ((∀ n (a : homologyIndex K (circΦ hΦ hθ) h.isolated_A n), (2 : ℕ) • a = 0 → a = 0) →
        (∀ n, d n = 0) ∧ (∀ n, Function.Injective (i n)) ∧ (∀ n, Function.Surjective (p n))) := by
  obtain ⟨N₀, N₁, N₂, hT, c₁, c₂, c₃⟩ :=
    exists_collared_indexTriple ((hΦ.isHeight hθ).isAttractorRepellerPair hS)
  have pS := circ_pair hΦ hθ hT.pair_S
  have pA := circ_pair hΦ hθ hT.pair_A
  have pR := circ_pair hΦ hθ hT.pair_R
  have eAset : cq ⁻¹' (S ∩ (fun p : X × Tau => (p.2 : ℝ)) ⁻¹' {1}) =
      {x | (x, Tau.top) ∈ S} ×ˢ {Circ.zero} := cq_preimage_inter_top S
  have eRset : cq ⁻¹' (S ∩ (fun p : X × Tau => (p.2 : ℝ)) ⁻¹' {-1}) =
      {x | (x, Tau.bot) ∈ S} ×ˢ {Circ.pi} := cq_preimage_inter_bot S
  rw [eAset] at pA
  rw [eRset] at pR
  have s₀₁ : cq ⁻¹' N₀ ⊆ cq ⁻¹' N₁ := preimage_mono hT.sub₀₁
  have s₁₂ : cq ⁻¹' N₁ ⊆ cq ⁻¹' N₂ := preimage_mono hT.sub₁₂
  let eA := homologyIndexEquiv K h.isolated_A pA (circ_collared hΦ hθ c₁)
  let eS := homologyIndexEquiv K h.isolated pS (circ_collared hΦ hθ c₂)
  let eR := homologyIndexEquiv K h.isolated_R pR (circ_collared hΦ hθ c₃)
  have h2 : ∀ (n : ℕ) (z : singH K (X × Circ) (Int.ofNat n + 1) (cq ⁻¹' N₂) (cq ⁻¹' N₁)),
      (2 : ℕ) • (singδ K (Int.ofNat n) (cq ⁻¹' N₂) (cq ⁻¹' N₁) (cq ⁻¹' N₀)).hom z = 0 := by
    intro n z
    have hnat := singδ_natural_apply K (rprod Circ.reflC) s₀₁ s₁₂ s₀₁ s₁₂
      (rInv_cq_preimage N₂).mapsTo (rInv_cq_preimage N₁).mapsTo (rInv_cq_preimage N₀).mapsTo
      (Int.ofNat n) z
    have hA := circ_sign_attractor hΦ hθ K hS hT.pair_A c₁ (Int.ofNat n)
      ((singδ K (Int.ofNat n) (cq ⁻¹' N₂) (cq ⁻¹' N₁) (cq ⁻¹' N₀)).hom z)
    have hR := circ_sign_repeller hΦ hθ K hS hT.pair_R c₃ (Int.ofNat n + 1) z
    unfold pairAct at hA hR
    rw [hA, hR, map_neg] at hnat
    rw [two_nsmul]
    nth_rewrite 1 [hnat]
    exact neg_add_cancel _
  refine ⟨fun n => (eS n).symm.toLinearMap ∘ₗ
      (singIncl K (Int.ofNat n) s₁₂ (subset_refl (cq ⁻¹' N₀))).hom ∘ₗ (eA n).toLinearMap,
    fun n => (eR n).symm.toLinearMap ∘ₗ
      (singIncl K (Int.ofNat n) (subset_refl (cq ⁻¹' N₂)) s₀₁).hom ∘ₗ (eS n).toLinearMap,
    fun n => (eA n).symm.toLinearMap ∘ₗ
      (singδ K (Int.ofNat n) (cq ⁻¹' N₂) (cq ⁻¹' N₁) (cq ⁻¹' N₀)).hom ∘ₗ
      (eR (n + 1)).toLinearMap, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n => exact_conj K (eA n) (eS n) (eR n) (sing_exact_incl K (Int.ofNat n) s₀₁ s₁₂)
  · exact fun n => exact_conj K (eS (n + 1)) (eR (n + 1)) (eA n)
      (sing_exact_δ K (Int.ofNat n) s₀₁ s₁₂)
  · exact fun n => exact_conj K (eR (n + 1)) (eA n) (eS n)
      (sing_exact_δ' K (Int.ofNat n) s₀₁ s₁₂)
  · intro y
    obtain ⟨x, hx⟩ := (sing_exact_δ K (Int.negSucc 0) s₀₁ s₁₂ (eR 0 y)).1
      (Subsingleton.elim _ _)
    refine ⟨(eS 0).symm x, ?_⟩
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.apply_symm_apply]
    rw [LinearEquiv.symm_apply_eq]
    exact hx
  · intro n z
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [← map_nsmul, h2, map_zero]
  · intro htor
    have hd : ∀ n z, (eA n).symm ((singδ K (Int.ofNat n) (cq ⁻¹' N₂) (cq ⁻¹' N₁)
        (cq ⁻¹' N₀)).hom (eR (n + 1) z)) = 0 := fun n z =>
      htor n _ (by rw [← map_nsmul, h2, map_zero])
    have hd0 : ∀ n, ((eA n).symm.toLinearMap ∘ₗ
        (singδ K (Int.ofNat n) (cq ⁻¹' N₂) (cq ⁻¹' N₁) (cq ⁻¹' N₀)).hom ∘ₗ
        (eR (n + 1)).toLinearMap) = 0 := fun n => LinearMap.ext fun z => hd n z
    refine ⟨hd0, fun n => ?_, fun n => ?_⟩
    · refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
      obtain ⟨y, rfl⟩ := ((exact_conj K (eR (n + 1)) (eA n) (eS n)
        (sing_exact_δ' K (Int.ofNat n) s₀₁ s₁₂)) a).1 ha
      exact hd n y
    · cases n with
      | zero =>
        intro y
        obtain ⟨x, hx⟩ := (sing_exact_δ K (Int.negSucc 0) s₀₁ s₁₂ (eR 0 y)).1
          (Subsingleton.elim _ _)
        refine ⟨(eS 0).symm x, ?_⟩
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          LinearEquiv.apply_symm_apply]
        rw [LinearEquiv.symm_apply_eq]
        exact hx
      | succ m =>
        intro y
        exact ((exact_conj K (eS (m + 1)) (eR (m + 1)) (eA m)
          (sing_exact_δ K (Int.ofNat m) s₀₁ s₁₂)) y).1 (hd m y)

include hΦ hθ in
/-- Theorem `thm:equivariant`(ii) over a field in which `2 ≠ 0` (e.g. `ℚ` or `𝔽_p`, `p` odd):
`CH_0(S̃) ≅ CH_0(K₊; f₊)` and `CH_{n+1}(S̃) ≅ CH_{n+1}(K₊; f₊) ⊕ CH_n(K₋; f₋)`. -/
theorem equivariant_ii_field (F : Type u) [Field F] (h2 : (2 : F) ≠ 0) {S : Set (X × Tau)}
    (hS : IsIsolatedInvariantSet Φ S)
    (h : IsAttractorRepellerPair (circΦ hΦ hθ) (cq ⁻¹' S) ({x | (x, Tau.top) ∈ S} ×ˢ {Circ.zero})
      ({x | (x, Tau.bot) ∈ S} ×ˢ {Circ.pi}))
    (hKp : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ)) {x | (x, Tau.top) ∈ S})
    (hKm : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ)) {x | (x, Tau.bot) ∈ S}) :
    Nonempty (homologyIndex F (circΦ hΦ hθ) h.isolated 0 ≃ₗ[F]
      homologyIndex F (fiberFlow hΦ Tau.top (base_top hθ)) hKp 0) ∧
    ∀ n, Nonempty (homologyIndex F (circΦ hΦ hθ) h.isolated (n + 1) ≃ₗ[F]
      homologyIndex F (fiberFlow hΦ Tau.top (base_top hθ)) hKp (n + 1) ×
        homologyIndex F (fiberFlow hΦ Tau.bot (base_bot hθ)) hKm n) := by
  obtain ⟨i, p, d, hip, -, -, -, -, htor⟩ := equivariant_ii hΦ hθ F hS h
  obtain ⟨-, hi, hp⟩ := htor fun n a ha => by
    rw [← Nat.cast_smul_eq_nsmul F, Nat.cast_ofNat] at ha
    exact (smul_eq_zero.1 ha).resolve_left h2
  have hA := circ_index_attractor hΦ hθ F h.isolated_A hKp
  have hR := circ_index_repeller hΦ hθ F h.isolated_R hKm
  refine ⟨?_, fun n => ?_⟩
  · haveI := hR.2
    obtain ⟨a⟩ := hA 0
    exact ⟨(LinearEquiv.ofBijective (i 0) ⟨hi 0, fun y =>
      (hip 0 y).1 (Subsingleton.elim _ _)⟩).symm.trans a⟩
  · haveI : Module.Free F (homologyIndex F (circΦ hΦ hθ) h.isolated_R (n + 1)) :=
      Module.Free.of_divisionRing _ _
    haveI : Module.Projective F (homologyIndex F (circΦ hΦ hθ) h.isolated_R (n + 1)) :=
      Module.Projective.of_free
    obtain ⟨l, hl⟩ := (p (n + 1)).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.2 (hp (n + 1)))
    obtain ⟨a⟩ := hA (n + 1)
    obtain ⟨r⟩ := hR.1 n
    exact ⟨((hip (n + 1)).splitSurjectiveEquiv (hi (n + 1)) ⟨l, hl⟩).1.trans
      (a.prodCongr r)⟩

end DoubleSign

end ConleyCheck.Conley
