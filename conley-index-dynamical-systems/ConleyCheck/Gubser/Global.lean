import ConleyCheck.Gubser.Fiber
import ConleyCheck.Gubser.Torus

/-!
# The doubled compactified Gubser flow (section `sec:full3d`)

The phase space is `Ω = HF × S¹ ⊂ ℝ³ × ℝ²` (`OmG`). A point is `(y, w)`, where `y` lies in the
closed upper hemisphere `HF`, the Poincaré compactification of the `(T, π̄)`-plane, and
`w = (cos θ, sin θ)` is the doubled base, with `τ = cos θ = w₁`. The field is
`fieldG = (fieldF c w₁ y, y₃ (w₂², -w₁ w₂))`. In the finite part `y₃ > 0` the coordinates
`T = y₁/y₃`, `π̄ = y₂/y₃`, `τ = w₁` solve `eq:gT`–`eq:gtau` after the time change `dρ = y₃ dt`, and
`θ' = -sin θ` in the time `ρ`. On the torus at infinity `y₃ = 0` the base is frozen.

* `ϕG`: the flow on `Ω`, `hasDerivAt_ϕG`.
* `ϕG_rev`: the reversor `S̃ (y, w) = ((-y₁, y₂, y₃), (-w₁, w₂))` conjugates `ϕG` to its time
  reversal.
* The signs of `y₁`, `y₃` and `w₂` are invariant, `τ` is nondecreasing, and every linear function
  `ℓ(y)` satisfies `ℓ' = ℓ(P) - s ℓ` (`hasDerivAt_lin`).
-/

open Set Filter Topology
open ConleyCheck.Conley ConleyCheck.ODE

namespace ConleyCheck.Gubser

/-- The ambient space `ℝ³ × ℝ²`. -/
abbrev EG := E3 × (ℝ × ℝ)

/-- The doubled compactified phase space `HF × S¹`. -/
def OmG : Set EG := {p | p.1 ∈ HF ∧ p.2 ∈ S1}

/-- The doubled compactified Gubser field. -/
noncomputable def fieldG (c : ℝ) (p : EG) : EG :=
  (fieldF c p.2.1 p.1, (p.1.2.2 * p.2.2 ^ 2, -(p.1.2.2 * p.2.1 * p.2.2)))

theorem contDiff_fieldG (c : ℝ) : ContDiff ℝ 1 (fieldG c) := by
  unfold fieldG fieldF fS fP1 fP2; fun_prop

/-- The flow of the cut-off field on `ℝ³ × ℝ²`. -/
noncomputable def flowG (c : ℝ) : Flow ℝ EG := bumpFlow (contDiff_fieldG c) 2 two_pos

/-- The cut-off, equal to `1` on the ball of radius `2`. -/
noncomputable def bG : EG → ℝ := (bumpOf (E := EG) 2 two_pos : EG → ℝ)

theorem continuous_bG : Continuous bG := continuous_bumpOf

theorem hasDerivAt_flowG (c : ℝ) (p : EG) (t : ℝ) :
    HasDerivAt (fun s => flowG c s p) (bG (flowG c t p) • fieldG c (flowG c t p)) t :=
  hasDerivAt_bumpFlow _ p t

theorem continuous_fSG (c : ℝ) : Continuous fun q : EG => fS c q.2.1 q.1 := by
  unfold fS fP1 fP2; fun_prop

theorem isInvariant_OmG (c : ℝ) : IsInvariant (flowG c) OmG := by
  intro t p hp
  have hγ := hasDerivAt_flowG c p
  have hcγ : Continuous fun s => flowG c s p :=
    (flowG c).continuous continuous_id continuous_const
  have hk : Continuous fun s => bG (flowG c s p) * fS c (flowG c s p).2.1 (flowG c s p).1 :=
    (continuous_bG.comp hcγ).mul ((continuous_fSG c).comp hcγ)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hW : ∀ s, HasDerivAt (fun r => (flowG c r p).1.1 ^ 2 + (flowG c r p).1.2.1 ^ 2 +
        (flowG c r p).1.2.2 ^ 2 - 1)
        ((-2 * (bG (flowG c s p) * fS c (flowG c s p).2.1 (flowG c s p).1)) *
          ((flowG c s p).1.1 ^ 2 + (flowG c s p).1.2.1 ^ 2 + (flowG c s p).1.2.2 ^ 2 - 1)) s := by
      intro s
      have hy := hasDerivAt_fst' (hγ s)
      have h1 := (hasDerivAt_fst' hy).pow 2
      have h2 := (hasDerivAt_fst' (hasDerivAt_snd' hy)).pow 2
      have h3 := (hasDerivAt_snd' (hasDerivAt_snd' hy)).pow 2
      convert ((h1.add h2).add h3).sub_const 1 using 1
      simp only [Prod.smul_fst, Prod.smul_snd, fieldG, fieldF, fS, smul_eq_mul, Nat.cast_ofNat]
      ring
    have h0 : (flowG c 0 p).1.1 ^ 2 + (flowG c 0 p).1.2.1 ^ 2 + (flowG c 0 p).1.2.2 ^ 2 - 1 = 0 := by
      rw [Flow.map_zero_apply]; linarith [hp.1.1]
    have := eq_zero_of_linear_all hW (continuous_const.mul hk) h0 t
    linarith
  · have hV : ∀ s, HasDerivAt (fun r => (flowG c r p).1.2.2)
        ((-(bG (flowG c s p) * fS c (flowG c s p).2.1 (flowG c s p).1)) * (flowG c s p).1.2.2) s := by
      intro s
      convert hasDerivAt_snd' (hasDerivAt_snd' (hasDerivAt_fst' (hγ s))) using 1
      simp only [Prod.smul_fst, Prod.smul_snd, fieldG, fieldF, smul_eq_mul]; ring
    have h0 : 0 ≤ (flowG c 0 p).1.2.2 := by rw [Flow.map_zero_apply]; exact hp.1.2
    exact nonneg_of_linear_all hV hk.neg h0 t
  · have hW : ∀ s, HasDerivAt (fun r => (flowG c r p).2.1 ^ 2 + (flowG c r p).2.2 ^ 2 - 1)
        (0 * ((flowG c s p).2.1 ^ 2 + (flowG c s p).2.2 ^ 2 - 1)) s := by
      intro s
      have hw := hasDerivAt_snd' (hγ s)
      have h1 := (hasDerivAt_fst' hw).pow 2
      have h2 := (hasDerivAt_snd' hw).pow 2
      convert (h1.add h2).sub_const 1 using 1
      simp only [Prod.smul_snd, Prod.smul_fst, fieldG, smul_eq_mul, Nat.cast_ofNat]
      ring
    have h0 : (flowG c 0 p).2.1 ^ 2 + (flowG c 0 p).2.2 ^ 2 - 1 = 0 := by
      rw [Flow.map_zero_apply]; have := hp.2; simp only [S1, mem_ofPred_eq] at this; linarith
    have := eq_zero_of_linear_all hW continuous_const h0 t
    show (flowG c t p).2.1 ^ 2 + (flowG c t p).2.2 ^ 2 = 1
    linarith

/-- The doubled compactified Gubser flow on `Ω`. -/
noncomputable def ϕG (c : ℝ) : Flow ℝ OmG := (flowG c).restrict (isInvariant_OmG c)

theorem norm_le_one_of_OmG {p : EG} (hp : p ∈ OmG) : ‖p‖ ≤ 1 :=
  norm_prod_le_iff.2 ⟨norm_le_one_of_HF hp.1, norm_le_one_of_S1 hp.2⟩

theorem bG_eq_one {p : EG} (hp : p ∈ OmG) : bG p = 1 :=
  bumpOf_eq_one ((norm_le_one_of_OmG hp).trans one_le_two)

theorem ϕG_coe (c t : ℝ) (p : OmG) : (ϕG c t p : EG) = flowG c t p := rfl

theorem hasDerivAt_ϕG (c : ℝ) (p : OmG) (t : ℝ) :
    HasDerivAt (fun s => (ϕG c s p : EG)) (fieldG c (ϕG c t p)) t := by
  have h := hasDerivAt_flowG c p t
  have h1 : bG (flowG c t p) = 1 := bG_eq_one (ϕG c t p).2
  rw [h1, one_smul] at h
  exact h

theorem continuous_orbitG (c : ℝ) (p : OmG) : Continuous fun s => (ϕG c s p : EG) :=
  continuous_subtype_val.comp ((ϕG c).continuous continuous_id continuous_const)

theorem isCompact_OmG : IsCompact OmG := by
  have hc : IsCompact (HF ×ˢ S1) := by
    refine IsCompact.prod ?_ isCompact_S1
    refine Metric.isCompact_of_isClosed_isBounded isClosed_HF ?_
    exact (Metric.isBounded_closedBall (x := (0 : E3)) (r := 1)).subset fun y hy =>
      mem_closedBall_zero_iff.2 (norm_le_one_of_HF hy)
  exact hc

instance : CompactSpace OmG := isCompact_iff_compactSpace.1 isCompact_OmG

/-! ## Coordinates -/

/-- The coordinates of a point of `Ω`. -/
def gy1 (q : OmG) : ℝ := (q : EG).1.1
def gy2 (q : OmG) : ℝ := (q : EG).1.2.1
def gy3 (q : OmG) : ℝ := (q : EG).1.2.2
def gw1 (q : OmG) : ℝ := (q : EG).2.1
def gw2 (q : OmG) : ℝ := (q : EG).2.2

theorem continuous_gy1 : Continuous gy1 := by unfold gy1; fun_prop
theorem continuous_gy2 : Continuous gy2 := by unfold gy2; fun_prop
theorem continuous_gy3 : Continuous gy3 := by unfold gy3; fun_prop
theorem continuous_gw1 : Continuous gw1 := by unfold gw1; fun_prop
theorem continuous_gw2 : Continuous gw2 := by unfold gw2; fun_prop

theorem sphere_G (q : OmG) : gy1 q ^ 2 + gy2 q ^ 2 + gy3 q ^ 2 = 1 := q.2.1.1
theorem gy3_nonneg (q : OmG) : 0 ≤ gy3 q := q.2.1.2
theorem circle_G (q : OmG) : gw1 q ^ 2 + gw2 q ^ 2 = 1 := q.2.2

theorem gw1_mem (q : OmG) : gw1 q ∈ Icc (-1 : ℝ) 1 := fst_mem_Icc_of_S1 q.2.2

/-- The homogenized field `P` and radial part `s` at a point of `Ω`. -/
noncomputable def gP1 (q : OmG) : ℝ := fP1 (gw1 q) (q : EG).1
noncomputable def gP2 (c : ℝ) (q : OmG) : ℝ := fP2 c (gw1 q) (q : EG).1
noncomputable def gS (c : ℝ) (q : OmG) : ℝ := fS c (gw1 q) (q : EG).1

theorem continuous_gS (c : ℝ) : Continuous (gS c) :=
  (continuous_fSG c).comp continuous_subtype_val

section Orbit

variable (c : ℝ) (p : OmG)

theorem hasDerivAt_y (t : ℝ) : HasDerivAt (fun s => (ϕG c s p : EG).1)
    (fieldF c (gw1 (ϕG c t p)) (ϕG c t p : EG).1) t :=
  hasDerivAt_fst' (hasDerivAt_ϕG c p t)

theorem hasDerivAt_gy1 (t : ℝ) : HasDerivAt (fun s => gy1 (ϕG c s p))
    (gP1 (ϕG c t p) - gS c (ϕG c t p) * gy1 (ϕG c t p)) t :=
  hasDerivAt_fst' (hasDerivAt_y c p t)

theorem hasDerivAt_gy2 (t : ℝ) : HasDerivAt (fun s => gy2 (ϕG c s p))
    (gP2 c (ϕG c t p) - gS c (ϕG c t p) * gy2 (ϕG c t p)) t :=
  hasDerivAt_fst' (hasDerivAt_snd' (hasDerivAt_y c p t))

theorem hasDerivAt_gy3 (t : ℝ) : HasDerivAt (fun s => gy3 (ϕG c s p))
    (-(gS c (ϕG c t p) * gy3 (ϕG c t p))) t :=
  hasDerivAt_snd' (hasDerivAt_snd' (hasDerivAt_y c p t))

theorem hasDerivAt_gw1 (t : ℝ) : HasDerivAt (fun s => gw1 (ϕG c s p))
    (gy3 (ϕG c t p) * (1 - gw1 (ϕG c t p) ^ 2)) t := by
  have h := hasDerivAt_fst' (hasDerivAt_snd' (hasDerivAt_ϕG c p t))
  refine h.congr_deriv ?_
  have := circle_G (ϕG c t p)
  simp only [fieldG, gy3, gw1, gw2] at this ⊢
  rw [show (ϕG c t p : EG).2.2 ^ 2 = 1 - (ϕG c t p : EG).2.1 ^ 2 by linarith]

theorem hasDerivAt_gw2 (t : ℝ) : HasDerivAt (fun s => gw2 (ϕG c s p))
    (-(gy3 (ϕG c t p) * gw1 (ϕG c t p)) * gw2 (ϕG c t p)) t := by
  have h := hasDerivAt_snd' (hasDerivAt_snd' (hasDerivAt_ϕG c p t))
  exact h.congr_deriv (by simp only [fieldG, gy3, gw1, gw2]; ring)

/-- Every linear function `ℓ(y) = l₁ y₁ + l₂ y₂ + l₃ y₃` satisfies `ℓ' = ℓ(P) - s ℓ`. -/
theorem hasDerivAt_lin (l₁ l₂ l₃ : ℝ) (t : ℝ) :
    HasDerivAt (fun s => l₁ * gy1 (ϕG c s p) + l₂ * gy2 (ϕG c s p) + l₃ * gy3 (ϕG c s p))
      (l₁ * gP1 (ϕG c t p) + l₂ * gP2 c (ϕG c t p) - gS c (ϕG c t p) *
        (l₁ * gy1 (ϕG c t p) + l₂ * gy2 (ϕG c t p) + l₃ * gy3 (ϕG c t p))) t := by
  have h := (((hasDerivAt_gy1 c p t).const_mul l₁).add ((hasDerivAt_gy2 c p t).const_mul l₂)).add
    ((hasDerivAt_gy3 c p t).const_mul l₃)
  exact h.congr_deriv (by ring)

theorem continuous_k (f : OmG → ℝ) (hf : Continuous f) :
    Continuous fun s => f (ϕG c s p) :=
  hf.comp ((ϕG c).continuous continuous_id continuous_const)

theorem hasDerivAt_gy1_lin (t : ℝ) : HasDerivAt (fun s => gy1 (ϕG c s p))
    ((gw1 (ϕG c t p) * (gy2 (ϕG c t p) - 2 * gy3 (ϕG c t p)) / 3 - gS c (ϕG c t p)) *
      gy1 (ϕG c t p)) t :=
  (hasDerivAt_gy1 c p t).congr_deriv (by simp only [gP1, fP1, gw1, gy1, gy2, gy3]; ring)

theorem gy1_pos (h : 0 < gy1 p) (t : ℝ) : 0 < gy1 (ϕG c t p) := by
  refine pos_of_linear_all (hasDerivAt_gy1_lin c p) ?_ (s₀ := 0)
    (by rwa [Flow.map_zero_apply]) t
  exact continuous_k c p _ (((continuous_gw1.mul (continuous_gy2.sub
    (continuous_const.mul continuous_gy3))).div_const 3).sub (continuous_gS c))

theorem gy1_zero (h : gy1 p = 0) (t : ℝ) : gy1 (ϕG c t p) = 0 := by
  refine eq_zero_of_linear_all (hasDerivAt_gy1_lin c p) ?_ (s₀ := 0)
    (by rwa [Flow.map_zero_apply]) t
  exact continuous_k c p _ (((continuous_gw1.mul (continuous_gy2.sub
    (continuous_const.mul continuous_gy3))).div_const 3).sub (continuous_gS c))

theorem gy1_neg (h : gy1 p < 0) (t : ℝ) : gy1 (ϕG c t p) < 0 := by
  rcases lt_trichotomy (gy1 (ϕG c t p)) 0 with h' | h' | h'
  · exact h'
  · have := gy1_zero c (ϕG c t p) h' (-t)
    rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply] at this
    linarith
  · have := gy1_pos c (ϕG c t p) h' (-t)
    rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply] at this
    linarith

theorem gy3_pos (h : 0 < gy3 p) (t : ℝ) : 0 < gy3 (ϕG c t p) :=
  pos_of_linear_all (fun s => (hasDerivAt_gy3 c p s).congr_deriv (neg_mul _ _).symm)
    (continuous_k c p _ (continuous_gS c)).neg (s₀ := 0) (by rwa [Flow.map_zero_apply]) t

theorem gy3_zero (h : gy3 p = 0) (t : ℝ) : gy3 (ϕG c t p) = 0 :=
  eq_zero_of_linear_all (fun s => (hasDerivAt_gy3 c p s).congr_deriv (neg_mul _ _).symm)
    (continuous_k c p _ (continuous_gS c)).neg (s₀ := 0) (by rwa [Flow.map_zero_apply]) t

theorem gw2_pos (h : 0 < gw2 p) (t : ℝ) : 0 < gw2 (ϕG c t p) :=
  pos_of_linear_all (hasDerivAt_gw2 c p)
    (continuous_k c p _ (continuous_gy3.mul continuous_gw1)).neg (s₀ := 0)
    (by rwa [Flow.map_zero_apply]) t

theorem gw2_zero (h : gw2 p = 0) (t : ℝ) : gw2 (ϕG c t p) = 0 :=
  eq_zero_of_linear_all (hasDerivAt_gw2 c p)
    (continuous_k c p _ (continuous_gy3.mul continuous_gw1)).neg (s₀ := 0)
    (by rwa [Flow.map_zero_apply]) t

theorem monotone_gw1 : Monotone fun s => gw1 (ϕG c s p) :=
  monotone_of_deriv_nonneg (fun s => (hasDerivAt_gw1 c p s).differentiableAt) fun s => by
    rw [(hasDerivAt_gw1 c p s).deriv]
    have h := gw1_mem (ϕG c s p)
    exact mul_nonneg (gy3_nonneg _) (by nlinarith [h.1, h.2])

end Orbit

/-! ## The reversor `S̃` -/

/-- The reversor `S̃ : (y, w) ↦ ((-y₁, y₂, y₃), (-w₁, w₂))`. -/
def revG (p : EG) : EG := (refl3 p.1, (-p.2.1, p.2.2))

theorem revG_revG (p : EG) : revG (revG p) = p := by
  simp [revG, refl3]

theorem revG_mem {p : EG} (hp : p ∈ OmG) : revG p ∈ OmG := by
  refine ⟨refl3_mem hp.1, ?_⟩
  have := hp.2
  simp only [S1, mem_ofPred_eq, revG, neg_sq] at this ⊢
  exact this

theorem fieldG_revG (c : ℝ) (p : EG) : fieldG c (revG p) = -revG (fieldG c p) := by
  refine Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_)) (Prod.ext ?_ ?_) <;>
    simp only [fieldG, revG, refl3, fieldF, fS, fP1, fP2, Prod.fst_neg, Prod.snd_neg] <;> ring

theorem continuous_revG : Continuous revG := by unfold revG refl3; fun_prop

theorem hasDerivAt_revG {f : ℝ → EG} {f' : EG} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => revG (f s)) (revG f') t := by
  have hy := hasDerivAt_fst' h
  have hw := hasDerivAt_snd' h
  exact ((hasDerivAt_fst' hy).neg.prodMk (hasDerivAt_snd' hy)).prodMk
    ((hasDerivAt_fst' hw).neg.prodMk (hasDerivAt_snd' hw))

/-- The reversor on `Ω`. -/
def revΩ (p : OmG) : OmG := ⟨revG p, revG_mem p.2⟩

theorem revΩ_revΩ (p : OmG) : revΩ (revΩ p) = p := Subtype.ext (revG_revG _)

theorem continuous_revΩ : Continuous revΩ :=
  (continuous_revG.comp continuous_subtype_val).subtype_mk _

/-- `S̃` reverses time: `ϕ_t ∘ S̃ = S̃ ∘ ϕ_{-t}`. -/
theorem ϕG_rev (c t : ℝ) (p : OmG) : ϕG c t (revΩ p) = revΩ (ϕG c (-t) p) := by
  have hsol : IsSol (bumpField (fieldG c) 2 two_pos) fun s => revG (ϕG c (-s) p : EG) := by
    intro s
    have h1 := (hasDerivAt_ϕG c p (-s)).scomp s (hasDerivAt_neg s)
    have h2 := hasDerivAt_revG h1
    have hmem : revG (ϕG c (-s) p : EG) ∈ OmG := revG_mem (ϕG c (-s) p).2
    have hb : bumpField (fieldG c) 2 two_pos (revG (ϕG c (-s) p : EG)) =
        fieldG c (revG (ϕG c (-s) p : EG)) := by
      simp only [bumpField]
      rw [show (bumpOf (E := EG) 2 two_pos : EG → ℝ) _ = 1 from bG_eq_one hmem, one_smul]
    rw [hb, fieldG_revG]
    convert h2 using 1
    · simp only [Function.comp_def]
    · simp only [neg_smul, one_smul, revG, refl3, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]
  have : flowG c t (revG (ϕG c (-0) p : EG)) = revG (ϕG c (-(t + 0)) p : EG) :=
    flowOf_eq_of_isSol _ _ hsol 0 t
  simp only [neg_zero, add_zero, Flow.map_zero_apply] at this
  exact Subtype.ext this

theorem gy1_rev (q : OmG) : gy1 (revΩ q) = -gy1 q := rfl
theorem gy2_rev (q : OmG) : gy2 (revΩ q) = gy2 q := rfl
theorem gy3_rev (q : OmG) : gy3 (revΩ q) = gy3 q := rfl
theorem gw1_rev (q : OmG) : gw1 (revΩ q) = -gw1 q := rfl
theorem gw2_rev (q : OmG) : gw2 (revΩ q) = gw2 q := rfl

end ConleyCheck.Gubser
