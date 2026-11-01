import ConleyCheck.Gubser.TCFlow
import ConleyCheck.ODE.Crossing

/-!
# The fiber flows (`lem:fiber`(ii), (iii))

The fiber `τ = const` of the Gubser flow is the planar system `(βT, βπ)`. We compactify it on
the closed upper hemisphere `HF ⊂ S² ⊂ ℝ³` (Poincaré compactification). With the homogenized
quadratic field `P = (fP1, fP2)` and `s = y₁ P₁ + y₂ P₂`, the compactified field is
`fieldF = (P₁ - s y₁, P₂ - s y₂, -s y₃)`. It is tangent to the sphere and to the equator
`y₃ = 0`, which is the circle at infinity. In the finite part, `T = y₁/y₃` and `π̄ = y₂/y₃` solve
`(βT, βπ)` after the time change `y₃ dt` (`FiberCurve.hasDerivAt_T`, `FiberCurve.hasDerivAt_P`). In
the chart `u = y₂/y₁`, `v = y₃/y₁` near `T = +∞` the field is `(Fu, Fv)` after the time change
`y₁ dt` (`FiberCurve.hasDerivAt_U`).

* `FiberCurve.tendsto_atTop`, `FiberCurve.tendsto_atBot`: for all `c ≠ 0` and `τ ≠ 0`, every
  curve in `HF` along `fieldF`, with any positive continuous time change, converges to an
  equilibrium in forward and in backward time. The proof needs no Poincaré–Bendixson theory.
  The sign of `π̄ - 2` is eventually constant (`FiberCurve.eventually_sign_g`), so `T` is
  eventually monotone. If `T` has a finite limit, `π̄` converges by one-way crossings, and if
  `T → ∞`, so does `u`.
* `lem_fiber_iii`, `lem_fiber_ii`: the strong form of `lem:fiber`(iii) for the flow `ϕF` on `HF`,
  namely every orbit converges to an equilibrium in both time directions, and hence (ii), no
  periodic orbits.
-/

open Set Filter Topology
open ConleyCheck.Conley ConleyCheck.ODE

namespace ConleyCheck.Gubser

/-! ## The compactified fiber field -/

/-- First component of the homogenized fiber field. -/
noncomputable def fP1 (τ : ℝ) (y : E3) : ℝ := τ * y.1 * (y.2.1 - 2 * y.2.2) / 3

/-- Second component of the homogenized fiber field. -/
noncomputable def fP2 (c τ : ℝ) (y : E3) : ℝ :=
  -(4 / 3) * τ * (y.2.1 ^ 2 - y.2.2 ^ 2 / 5) - y.1 * y.2.1 / c

/-- The radial part `s = ⟨(y₁, y₂), P⟩`. -/
noncomputable def fS (c τ : ℝ) (y : E3) : ℝ := y.1 * fP1 τ y + y.2.1 * fP2 c τ y

/-- The compactified fiber field. -/
noncomputable def fieldF (c τ : ℝ) (y : E3) : E3 :=
  (fP1 τ y - fS c τ y * y.1, fP2 c τ y - fS c τ y * y.2.1, -(fS c τ y * y.2.2))

/-- The closed upper hemisphere, the compactified fiber. -/
def HF : Set E3 := {y | y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 ∧ 0 ≤ y.2.2}

theorem isClosed_HF : IsClosed HF :=
  (isClosed_eq (by fun_prop : Continuous fun y : E3 => y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2)
    continuous_const).inter (isClosed_le continuous_const (by fun_prop : Continuous fun y : E3 => y.2.2))

theorem continuous_fS (c τ : ℝ) : Continuous (fS c τ) := by unfold fS fP1 fP2; fun_prop

/-- Reversing time is the same as replacing `(c, τ)` by `(-c, -τ)`. -/
theorem fieldF_neg (c τ : ℝ) (y : E3) : fieldF (-c) (-τ) y = -fieldF c τ y := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [fieldF, fS, fP1, fP2, Prod.fst_neg, Prod.snd_neg, div_neg] <;> ring

/-- The reflection `T ↦ -T`. -/
def refl3 (y : E3) : E3 := (-y.1, y.2.1, y.2.2)

theorem refl3_refl3 (y : E3) : refl3 (refl3 y) = y := by simp [refl3]

theorem continuous_refl3 : Continuous refl3 := by unfold refl3; fun_prop

theorem refl3_mem {y : E3} (hy : y ∈ HF) : refl3 y ∈ HF := by
  refine ⟨?_, hy.2⟩
  have := hy.1
  simp only [refl3, neg_sq]
  exact this

/-- The reflection `T ↦ -T` replaces `c` by `-c`. -/
theorem fieldF_refl3 (c τ : ℝ) (y : E3) : fieldF (-c) τ (refl3 y) = refl3 (fieldF c τ y) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [fieldF, fS, fP1, fP2, refl3, div_neg] <;> ring

/-- The points `P^± = (0, ±1, 0)` are equilibria. -/
theorem fieldF_pole (c τ s : ℝ) (hs : s ^ 2 = 1) : fieldF c τ (0, s, 0) = 0 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show fP1 τ (0, s, 0) - fS c τ (0, s, 0) * 0 = 0
    simp [fP1]
  · show fP2 c τ (0, s, 0) - fS c τ (0, s, 0) * s = 0
    simp only [fS, fP1, fP2]
    linear_combination (4 / 3 * τ * s ^ 2) * hs
  · show -(fS c τ (0, s, 0) * 0) = 0
    simp

theorem pole_mem {s : ℝ} (hs : s ^ 2 = 1) : ((0, s, 0) : E3) ∈ HF :=
  ⟨by simp only; linarith, le_rfl⟩

theorem fieldF_eq_zero_of_P {c τ : ℝ} {y : E3} (h1 : fP1 τ y = 0) (h2 : fP2 c τ y = 0) :
    fieldF c τ y = 0 := by
  simp [fieldF, fS, h1, h2]

/-- On the equator, `fieldF` vanishes where `P` is radial. -/
theorem fieldF_eq_zero_of_equator {c τ : ℝ} {y : E3} (h3 : y.2.2 = 0)
    (hn : y.1 ^ 2 + y.2.1 ^ 2 = 1) (hQ : y.1 * fP2 c τ y - y.2.1 * fP1 τ y = 0) :
    fieldF c τ y = 0 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show fP1 τ y - fS c τ y * y.1 = 0
    unfold fS
    linear_combination (-fP1 τ y) * hn + (-y.2.1) * hQ
  · show fP2 c τ y - fS c τ y * y.2.1 = 0
    unfold fS
    linear_combination (-fP2 c τ y) * hn + y.1 * hQ
  · show -(fS c τ y * y.2.2) = 0
    rw [h3, mul_zero, neg_zero]

/-! ## The flow on the hemisphere -/

theorem contDiff_fieldF (c τ : ℝ) : ContDiff ℝ 1 (fieldF c τ) := by
  unfold fieldF fS fP1 fP2; fun_prop

/-- The global flow of the cut-off compactified fiber field on `ℝ³`. -/
noncomputable def flowF (c τ : ℝ) : Flow ℝ E3 := bumpFlow (contDiff_fieldF c τ) 2 two_pos

/-- The cut-off, equal to `1` on the ball of radius `2`. -/
noncomputable def bF : E3 → ℝ := (bumpOf (E := E3) 2 two_pos : E3 → ℝ)

theorem continuous_bF : Continuous bF := continuous_bumpOf

theorem hasDerivAt_flowF (c τ : ℝ) (p : E3) (t : ℝ) :
    HasDerivAt (fun s => flowF c τ s p) (bF (flowF c τ t p) • fieldF c τ (flowF c τ t p)) t :=
  hasDerivAt_bumpFlow _ p t

theorem isInvariant_HF (c τ : ℝ) : IsInvariant (flowF c τ) HF := by
  intro t p hp
  have hγ := hasDerivAt_flowF c τ p
  have hcγ : Continuous fun s => flowF c τ s p :=
    (flowF c τ).continuous continuous_id continuous_const
  have hk : Continuous fun s => bF (flowF c τ s p) * fS c τ (flowF c τ s p) :=
    (continuous_bF.comp hcγ).mul ((continuous_fS c τ).comp hcγ)
  refine ⟨?_, ?_⟩
  · have hW : ∀ s, HasDerivAt (fun r => (flowF c τ r p).1 ^ 2 + (flowF c τ r p).2.1 ^ 2 +
        (flowF c τ r p).2.2 ^ 2 - 1)
        ((-2 * (bF (flowF c τ s p) * fS c τ (flowF c τ s p))) * ((flowF c τ s p).1 ^ 2 +
          (flowF c τ s p).2.1 ^ 2 + (flowF c τ s p).2.2 ^ 2 - 1)) s := by
      intro s
      have h1 := (hasDerivAt_fst' (hγ s)).pow 2
      have h2 := (hasDerivAt_fst' (hasDerivAt_snd' (hγ s))).pow 2
      have h3 := (hasDerivAt_snd' (hasDerivAt_snd' (hγ s))).pow 2
      convert ((h1.add h2).add h3).sub_const 1 using 1
      simp only [Prod.smul_fst, Prod.smul_snd, fieldF, fS, smul_eq_mul, Nat.cast_ofNat]; ring
    have h0 : (flowF c τ 0 p).1 ^ 2 + (flowF c τ 0 p).2.1 ^ 2 + (flowF c τ 0 p).2.2 ^ 2 - 1 = 0 := by
      rw [Flow.map_zero_apply]; linarith [hp.1]
    have := eq_zero_of_linear_all hW (continuous_const.mul hk) h0 t
    linarith
  · have hV : ∀ s, HasDerivAt (fun r => (flowF c τ r p).2.2)
        ((-(bF (flowF c τ s p) * fS c τ (flowF c τ s p))) * (flowF c τ s p).2.2) s := by
      intro s
      convert hasDerivAt_snd' (hasDerivAt_snd' (hγ s)) using 1
      simp only [Prod.smul_snd, fieldF, smul_eq_mul]; ring
    have h0 : 0 ≤ (flowF c τ 0 p).2.2 := by rw [Flow.map_zero_apply]; exact hp.2
    exact nonneg_of_linear_all hV hk.neg h0 t

/-- The compactified fiber flow on the closed hemisphere `HF`. -/
noncomputable def ϕF (c τ : ℝ) : Flow ℝ HF := (flowF c τ).restrict (isInvariant_HF c τ)

theorem norm_le_one_of_HF {y : E3} (hy : y ∈ HF) : ‖y‖ ≤ 1 := by
  have h := hy.1
  refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩ <;> rw [Real.norm_eq_abs] <;>
    refine (sq_le_one_iff_abs_le_one _).1 ?_ <;> nlinarith [sq_nonneg y.1, sq_nonneg y.2.1, sq_nonneg y.2.2]

theorem hasDerivAt_ϕF (c τ : ℝ) (p : HF) (t : ℝ) :
    HasDerivAt (fun s => (ϕF c τ s p : E3)) (fieldF c τ (ϕF c τ t p)) t := by
  have h := hasDerivAt_flowF c τ p t
  rw [show bF (flowF c τ t p) = 1 from
    bumpOf_eq_one ((norm_le_one_of_HF (ϕF c τ t p).2).trans one_le_two), one_smul] at h
  exact h

/-- Equilibria of `fieldF` are fixed by the flow. -/
theorem flowF_fixed {c τ : ℝ} {e : E3} (he : fieldF c τ e = 0) (t : ℝ) : flowF c τ t e = e := by
  have hsol : IsSol (bumpField (fieldF c τ) 2 two_pos) (fun _ => e) := fun s => by
    have : bumpField (fieldF c τ) 2 two_pos e = 0 := by simp [bumpField, he]
    rw [this]; exact hasDerivAt_const s e
  exact flowOf_eq_of_isSol _ _ hsol 0 t

/-! ## Curves along the fiber field -/

/-- A curve in `HF` along `fieldF`, up to a positive continuous time change `β`, which does not
leave an equilibrium it reaches. -/
structure FiberCurve (c τ : ℝ) where
  γ : ℝ → E3
  β : E3 → ℝ
  cβ : Continuous β
  pos : ∀ y ∈ HF, 0 < β y
  mem : ∀ t, γ t ∈ HF
  deriv : ∀ t, HasDerivAt γ (β (γ t) • fieldF c τ (γ t)) t
  rest : ∀ e, fieldF c τ e = 0 → ∀ t, γ t = e → ∀ s, γ s = e

namespace FiberCurve

variable {c τ : ℝ} (C : FiberCurve c τ)

theorem cont : Continuous C.γ := continuous_iff_continuousAt.2 fun t => (C.deriv t).continuousAt

theorem m_pos (t : ℝ) : 0 < C.β (C.γ t) := C.pos _ (C.mem t)

theorem cont_m : Continuous fun t => C.β (C.γ t) := C.cβ.comp C.cont

theorem d1 (t : ℝ) :
    HasDerivAt (fun s => (C.γ s).1) (C.β (C.γ t) * (fieldF c τ (C.γ t)).1) t := by
  have := hasDerivAt_fst' (C.deriv t)
  rwa [Prod.smul_fst, smul_eq_mul] at this

theorem d2 (t : ℝ) :
    HasDerivAt (fun s => (C.γ s).2.1) (C.β (C.γ t) * (fieldF c τ (C.γ t)).2.1) t := by
  have := hasDerivAt_fst' (hasDerivAt_snd' (C.deriv t))
  rwa [Prod.smul_snd, Prod.smul_fst, smul_eq_mul] at this

theorem d3 (t : ℝ) :
    HasDerivAt (fun s => (C.γ s).2.2) (C.β (C.γ t) * (fieldF c τ (C.γ t)).2.2) t := by
  have := hasDerivAt_snd' (hasDerivAt_snd' (C.deriv t))
  rwa [Prod.smul_snd, Prod.smul_snd, smul_eq_mul] at this

theorem d1_lin (t : ℝ) : HasDerivAt (fun s => (C.γ s).1)
    ((C.β (C.γ t) * (τ * ((C.γ t).2.1 - 2 * (C.γ t).2.2) / 3 - fS c τ (C.γ t)))
      * (C.γ t).1) t :=
  (C.d1 t).congr_deriv (by simp only [fieldF, fP1]; ring)

theorem d3_lin (t : ℝ) : HasDerivAt (fun s => (C.γ s).2.2)
    ((-(C.β (C.γ t) * fS c τ (C.γ t))) * (C.γ t).2.2) t :=
  (C.d3 t).congr_deriv (by simp only [fieldF]; ring)

theorem cont_k1 : Continuous fun t =>
    C.β (C.γ t) * (τ * ((C.γ t).2.1 - 2 * (C.γ t).2.2) / 3 - fS c τ (C.γ t)) :=
  C.cont_m.mul (((by fun_prop : Continuous fun y : E3 => τ * (y.2.1 - 2 * y.2.2) / 3).comp
    C.cont).sub ((continuous_fS c τ).comp C.cont))

theorem cont_k3 : Continuous fun t => -(C.β (C.γ t) * fS c τ (C.γ t)) :=
  (C.cont_m.mul ((continuous_fS c τ).comp C.cont)).neg

theorem y1_pos (h : 0 < (C.γ 0).1) (t : ℝ) : 0 < (C.γ t).1 :=
  pos_of_linear_all C.d1_lin C.cont_k1 h t

theorem y1_zero (h : (C.γ 0).1 = 0) (t : ℝ) : (C.γ t).1 = 0 :=
  eq_zero_of_linear_all C.d1_lin C.cont_k1 h t

theorem y3_pos (h : 0 < (C.γ 0).2.2) (t : ℝ) : 0 < (C.γ t).2.2 :=
  pos_of_linear_all C.d3_lin C.cont_k3 h t

theorem y3_zero (h : (C.γ 0).2.2 = 0) (t : ℝ) : (C.γ t).2.2 = 0 :=
  eq_zero_of_linear_all C.d3_lin C.cont_k3 h t

/-! ### The finite chart `T = y₁/y₃`, `π̄ = y₂/y₃` -/

theorem hasDerivAt_T (h3 : ∀ t, 0 < (C.γ t).2.2) (t : ℝ) :
    HasDerivAt (fun s => (C.γ s).1 / (C.γ s).2.2) (C.β (C.γ t) * (C.γ t).2.2 *
      βT ((C.γ t).1 / (C.γ t).2.2) ((C.γ t).2.1 / (C.γ t).2.2) τ) t := by
  have h3t := (h3 t).ne'
  convert (C.d1 t).div (C.d3 t) h3t using 1
  simp only [fieldF, fS, fP1, βT]
  field_simp
  ring

theorem hasDerivAt_P (h3 : ∀ t, 0 < (C.γ t).2.2) (t : ℝ) :
    HasDerivAt (fun s => (C.γ s).2.1 / (C.γ s).2.2) (C.β (C.γ t) * (C.γ t).2.2 *
      βπ c ((C.γ t).1 / (C.γ t).2.2) ((C.γ t).2.1 / (C.γ t).2.2) τ) t := by
  have h3t := (h3 t).ne'
  convert (C.d2 t).div (C.d3 t) h3t using 1
  simp only [fieldF, fS, fP2, βπ]
  field_simp
  ring

theorem norm_T (h3 : ∀ t, 0 < (C.γ t).2.2) (t : ℝ) : (C.γ t).2.2 ^ 2 *
    (1 + ((C.γ t).1 / (C.γ t).2.2) ^ 2 + ((C.γ t).2.1 / (C.γ t).2.2) ^ 2) = 1 := by
  have h3t := (h3 t).ne'
  have := (C.mem t).1
  field_simp
  linarith

/-! ### The chart `u = y₂/y₁`, `v = y₃/y₁` near `T = +∞` -/

theorem hasDerivAt_U (h1 : ∀ t, 0 < (C.γ t).1) (t : ℝ) :
    HasDerivAt (fun s => (C.γ s).2.1 / (C.γ s).1) (C.β (C.γ t) * (C.γ t).1 *
      Fu c ((C.γ t).2.1 / (C.γ t).1) ((C.γ t).2.2 / (C.γ t).1) τ) t := by
  have h1t := (h1 t).ne'
  convert (C.d2 t).div (C.d1 t) h1t using 1
  simp only [fieldF, fS, fP1, fP2, Fu]
  field_simp
  ring

theorem norm_U (h1 : ∀ t, 0 < (C.γ t).1) (t : ℝ) : (C.γ t).1 ^ 2 *
    (1 + ((C.γ t).2.2 / (C.γ t).1) ^ 2 + ((C.γ t).2.1 / (C.γ t).1) ^ 2) = 1 := by
  have h1t := (h1 t).ne'
  have := (C.mem t).1
  field_simp
  linarith

end FiberCurve

/-! ## Two chart limits -/

theorem chart_tendsto_finite {a r₁ r₂ : ℝ → ℝ} (ha : ∀ t, 0 < a t)
    (hn : ∀ t, a t ^ 2 * (1 + r₁ t ^ 2 + r₂ t ^ 2) = 1) {R₁ R₂ : ℝ}
    (h₁ : Tendsto r₁ atTop (𝓝 R₁)) (h₂ : Tendsto r₂ atTop (𝓝 R₂)) :
    Tendsto a atTop (𝓝 (1 / √(1 + R₁ ^ 2 + R₂ ^ 2))) := by
  have heq : ∀ t, a t = 1 / √(1 + r₁ t ^ 2 + r₂ t ^ 2) := fun t => by
    have hat := ha t
    have ha2 : a t ^ 2 ≠ 0 := by positivity
    have : 1 + r₁ t ^ 2 + r₂ t ^ 2 = (1 / a t) ^ 2 := by
      rw [div_pow, one_pow, eq_div_iff ha2]; linear_combination hn t
    rw [this, Real.sqrt_sq (by positivity), one_div_one_div]
  have hlim := ((tendsto_const_nhds (x := (1 : ℝ)).add (h₁.pow 2)).add (h₂.pow 2)).sqrt
  exact (tendsto_const_nhds.div hlim (Real.sqrt_pos.2 (by positivity)).ne').congr
    fun t => (heq t).symm

theorem chart_tendsto_infty {a r₁ r₂ : ℝ → ℝ} (ha : ∀ t, 0 < a t)
    (hn : ∀ t, a t ^ 2 * (1 + r₁ t ^ 2 + r₂ t ^ 2) = 1) {R₁ : ℝ}
    (h₁ : Tendsto r₁ atTop (𝓝 R₁)) (h₂ : Tendsto r₂ atTop atTop) :
    Tendsto a atTop (𝓝 0) ∧ Tendsto (fun t => a t * r₂ t) atTop (𝓝 1) := by
  have hsq : Tendsto (fun t => a t ^ 2) atTop (𝓝 0) := by
    have hinv : Tendsto (fun t => (r₂ t)⁻¹ ^ 2) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp h₂).pow 2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv
      (Eventually.of_forall fun t => sq_nonneg _) ?_
    filter_upwards [h₂.eventually (eventually_gt_atTop 0)] with t ht
    have : a t ^ 2 * r₂ t ^ 2 ≤ 1 := by
      nlinarith [hn t, mul_nonneg (sq_nonneg (a t)) (sq_nonneg (r₁ t)), sq_nonneg (a t)]
    rw [inv_pow, ← one_div, le_div_iff₀ (by positivity)]
    exact this
  have ha0 : Tendsto a atTop (𝓝 0) := by
    have := hsq.sqrt
    rw [Real.sqrt_zero] at this
    exact this.congr fun t => Real.sqrt_sq (ha t).le
  refine ⟨ha0, ?_⟩
  have hlim : Tendsto (fun t => 1 - a t ^ 2 * (1 + r₁ t ^ 2)) atTop (𝓝 1) := by
    have := tendsto_const_nhds (x := (1 : ℝ)).sub
      (hsq.mul (tendsto_const_nhds (x := (1 : ℝ)).add (h₁.pow 2)))
    rwa [zero_mul, sub_zero] at this
  have := hlim.sqrt
  rw [Real.sqrt_one] at this
  refine this.congr' ?_
  filter_upwards [h₂.eventually (eventually_gt_atTop 0)] with t ht
  have heq : 1 - a t ^ 2 * (1 + r₁ t ^ 2) = (a t * r₂ t) ^ 2 := by
    linear_combination (-1 : ℝ) * hn t
  rw [heq, Real.sqrt_sq (mul_pos (ha t) ht).le]

namespace FiberCurve

variable {c τ : ℝ} (C : FiberCurve c τ)

/-- Convergence when the curve stays in the finite part and `T` has a finite limit. -/
theorem tendsto_of_T (hτ : τ ≠ 0) (h3 : ∀ t, 0 < (C.γ t).2.2) {ℓ : ℝ}
    (hT : Tendsto (fun t => (C.γ t).1 / (C.γ t).2.2) atTop (𝓝 ℓ)) :
    ∃ e ∈ HF, fieldF c τ e = 0 ∧ Tendsto C.γ atTop (𝓝 e) := by
  have hm : ∀ t, 0 < C.β (C.γ t) * (C.γ t).2.2 := fun t => mul_pos (C.m_pos t) (h3 t)
  have hcross : ∀ lv ∉ {ℓ' : ℝ | -(4 / 3) * τ * ℓ' ^ 2 + -(ℓ / c) * ℓ' + 4 / 15 * τ = 0},
      ∃ t₀, (∀ t, t₀ ≤ t → (C.γ t).2.1 / (C.γ t).2.2 = lv →
        0 < C.β (C.γ t) * (C.γ t).2.2 *
          βπ c ((C.γ t).1 / (C.γ t).2.2) ((C.γ t).2.1 / (C.γ t).2.2) τ) ∨
      (∀ t, t₀ ≤ t → (C.γ t).2.1 / (C.γ t).2.2 = lv →
        C.β (C.γ t) * (C.γ t).2.2 *
          βπ c ((C.γ t).1 / (C.γ t).2.2) ((C.γ t).2.1 / (C.γ t).2.2) τ < 0) := by
    intro lv hlv
    refine cross_of_tendsto hm (k := fun t => βπ c ((C.γ t).1 / (C.γ t).2.2) lv τ)
      (fun t ht => by rw [ht]) (K := βπ c ℓ lv τ) ?_ ?_
    · simp only [βπ]
      exact tendsto_const_nhds.sub ((hT.mul_const lv).div_const c)
    · intro h
      apply hlv
      show -(4 / 3) * τ * lv ^ 2 + -(ℓ / c) * lv + 4 / 15 * τ = 0
      unfold βπ at h
      linear_combination h
  have hγ_of : ∀ {e : E3}, Tendsto (fun t => (C.γ t).1) atTop (𝓝 e.1) →
      Tendsto (fun t => (C.γ t).2.1) atTop (𝓝 e.2.1) →
      Tendsto (fun t => (C.γ t).2.2) atTop (𝓝 e.2.2) → Tendsto C.γ atTop (𝓝 e) :=
    fun h1 h2 h3 => h1.prodMk_nhds (h2.prodMk_nhds h3)
  have hy1 : ∀ t, (C.γ t).1 = (C.γ t).2.2 * ((C.γ t).1 / (C.γ t).2.2) := fun t => by
    field_simp [(h3 t).ne']
  have hy2 : ∀ t, (C.γ t).2.1 = (C.γ t).2.2 * ((C.γ t).2.1 / (C.γ t).2.2) := fun t => by
    field_simp [(h3 t).ne']
  rcases tendsto_trichotomy (C.hasDerivAt_P h3) (dense_compl_quadratic (by
      have : (4 / 3 : ℝ) ≠ 0 := by norm_num
      simpa using mul_ne_zero this hτ)) hcross with hP | hP | ⟨L, hP⟩
  · obtain ⟨ha, hap⟩ := chart_tendsto_infty h3 (C.norm_T h3) hT hP
    refine ⟨(0, 1, 0), pole_mem (by norm_num), fieldF_pole c τ 1 (by norm_num), hγ_of ?_ ?_ ha⟩
    · have := ha.mul hT
      rw [zero_mul] at this
      exact this.congr fun t => (hy1 t).symm
    · exact hap.congr fun t => (hy2 t).symm
  · obtain ⟨ha, hap⟩ := chart_tendsto_infty (r₂ := fun t => -((C.γ t).2.1 / (C.γ t).2.2)) h3
      (fun t => by rw [neg_sq]; exact C.norm_T h3 t) hT (tendsto_neg_atBot_atTop.comp hP)
    refine ⟨(0, -1, 0), pole_mem (by norm_num), fieldF_pole c τ (-1) (by norm_num),
      hγ_of ?_ ?_ ha⟩
    · have := ha.mul hT
      rw [zero_mul] at this
      exact this.congr fun t => (hy1 t).symm
    · have := hap.neg
      exact this.congr fun t => by simp only [mul_neg, neg_neg]; exact (hy2 t).symm
  · have ha := chart_tendsto_finite h3 (C.norm_T h3) hT hP
    set a := 1 / √(1 + ℓ ^ 2 + L ^ 2)
    have hapos : 0 < a := by positivity
    set e : E3 := (a * ℓ, a * L, a)
    have hγ : Tendsto C.γ atTop (𝓝 e) := hγ_of
      ((ha.mul hT).congr fun t => (hy1 t).symm) ((ha.mul hP).congr fun t => (hy2 t).symm) ha
    have he : e ∈ HF := isClosed_HF.mem_of_tendsto hγ (Eventually.of_forall C.mem)
    have hβ : Tendsto (fun t => C.β (C.γ t)) atTop (𝓝 (C.β e)) := (C.cβ.tendsto e).comp hγ
    have hπ0 : βπ c ℓ L τ = 0 := by
      have hlim : Tendsto (fun t => C.β (C.γ t) * (C.γ t).2.2 *
          βπ c ((C.γ t).1 / (C.γ t).2.2) ((C.γ t).2.1 / (C.γ t).2.2) τ) atTop
          (𝓝 (C.β e * a * βπ c ℓ L τ)) := by
        refine (hβ.mul ha).mul ?_
        simp only [βπ]
        exact ((tendsto_const_nhds.mul ((hP.pow 2).sub tendsto_const_nhds)).mul
          tendsto_const_nhds).sub ((hT.mul hP).div_const c)
      have := deriv_tendsto_zero (C.hasDerivAt_P h3) hP hlim
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (mul_pos (C.pos e he) hapos).ne'
      · exact h
    have hT0 : βT ℓ L τ = 0 := by
      have hlim : Tendsto (fun t => C.β (C.γ t) * (C.γ t).2.2 *
          βT ((C.γ t).1 / (C.γ t).2.2) ((C.γ t).2.1 / (C.γ t).2.2) τ) atTop
          (𝓝 (C.β e * a * βT ℓ L τ)) := by
        refine (hβ.mul ha).mul ?_
        simp only [βT]
        exact ((hT.div_const 3).mul (hP.sub tendsto_const_nhds)).mul tendsto_const_nhds
      have := deriv_tendsto_zero (C.hasDerivAt_T h3) hT hlim
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (mul_pos (C.pos e he) hapos).ne'
      · exact h
    refine ⟨e, he, fieldF_eq_zero_of_P ?_ ?_, hγ⟩
    · have : fP1 τ e = a ^ 2 * βT ℓ L τ := by simp only [e, fP1, βT]; ring
      rw [this, hT0, mul_zero]
    · have : fP2 c τ e = a ^ 2 * βπ c ℓ L τ := by simp only [e, fP2, βπ]; ring
      rw [this, hπ0, mul_zero]

/-- Convergence when `y₁ > 0` along the curve and `v = y₃/y₁ → 0`. -/
theorem tendsto_of_v (hτ : τ ≠ 0) (h1 : ∀ t, 0 < (C.γ t).1)
    (hv : Tendsto (fun t => (C.γ t).2.2 / (C.γ t).1) atTop (𝓝 0)) :
    ∃ e ∈ HF, fieldF c τ e = 0 ∧ Tendsto C.γ atTop (𝓝 e) := by
  have hm : ∀ t, 0 < C.β (C.γ t) * (C.γ t).1 := fun t => mul_pos (C.m_pos t) (h1 t)
  have hFu : ∀ lv, Continuous fun v => Fu c lv v τ := fun lv => by unfold Fu; fun_prop
  have hcross : ∀ lv ∉ {ℓ' : ℝ | -(5 / 3) * τ * ℓ' ^ 2 + -(1 / c) * ℓ' + 0 = 0},
      ∃ t₀, (∀ t, t₀ ≤ t → (C.γ t).2.1 / (C.γ t).1 = lv →
        0 < C.β (C.γ t) * (C.γ t).1 *
          Fu c ((C.γ t).2.1 / (C.γ t).1) ((C.γ t).2.2 / (C.γ t).1) τ) ∨
      (∀ t, t₀ ≤ t → (C.γ t).2.1 / (C.γ t).1 = lv →
        C.β (C.γ t) * (C.γ t).1 *
          Fu c ((C.γ t).2.1 / (C.γ t).1) ((C.γ t).2.2 / (C.γ t).1) τ < 0) := by
    intro lv hlv
    refine cross_of_tendsto hm (k := fun t => Fu c lv ((C.γ t).2.2 / (C.γ t).1) τ)
      (fun t ht => by rw [ht]) (K := Fu c lv 0 τ) (((hFu lv).tendsto 0).comp hv) ?_
    intro h
    apply hlv
    show -(5 / 3) * τ * lv ^ 2 + -(1 / c) * lv + 0 = 0
    unfold Fu at h
    linear_combination h
  have hγ_of : ∀ {e : E3}, Tendsto (fun t => (C.γ t).1) atTop (𝓝 e.1) →
      Tendsto (fun t => (C.γ t).2.1) atTop (𝓝 e.2.1) →
      Tendsto (fun t => (C.γ t).2.2) atTop (𝓝 e.2.2) → Tendsto C.γ atTop (𝓝 e) :=
    fun h1 h2 h3 => h1.prodMk_nhds (h2.prodMk_nhds h3)
  have hy2 : ∀ t, (C.γ t).2.1 = (C.γ t).1 * ((C.γ t).2.1 / (C.γ t).1) := fun t => by
    field_simp [(h1 t).ne']
  have hy3 : ∀ t, (C.γ t).2.2 = (C.γ t).1 * ((C.γ t).2.2 / (C.γ t).1) := fun t => by
    field_simp [(h1 t).ne']
  rcases tendsto_trichotomy (C.hasDerivAt_U h1) (dense_compl_quadratic (by
      have : (5 / 3 : ℝ) ≠ 0 := by norm_num
      simpa using mul_ne_zero this hτ)) hcross with hU | hU | ⟨L, hU⟩
  · obtain ⟨ha, hap⟩ := chart_tendsto_infty h1 (C.norm_U h1) hv hU
    refine ⟨(0, 1, 0), pole_mem (by norm_num), fieldF_pole c τ 1 (by norm_num),
      hγ_of ha (hap.congr fun t => (hy2 t).symm) ?_⟩
    have := ha.mul hv
    rw [zero_mul] at this
    exact this.congr fun t => (hy3 t).symm
  · obtain ⟨ha, hap⟩ := chart_tendsto_infty (r₂ := fun t => -((C.γ t).2.1 / (C.γ t).1)) h1
      (fun t => by rw [neg_sq]; exact C.norm_U h1 t) hv (tendsto_neg_atBot_atTop.comp hU)
    refine ⟨(0, -1, 0), pole_mem (by norm_num), fieldF_pole c τ (-1) (by norm_num),
      hγ_of ha ?_ ?_⟩
    · have := hap.neg
      exact this.congr fun t => by simp only [mul_neg, neg_neg]; exact (hy2 t).symm
    · have := ha.mul hv
      rw [zero_mul] at this
      exact this.congr fun t => (hy3 t).symm
  · have ha := chart_tendsto_finite h1 (C.norm_U h1) hv hU
    set a := 1 / √(1 + (0 : ℝ) ^ 2 + L ^ 2)
    have hapos : 0 < a := by positivity
    set e : E3 := (a, a * L, a * 0)
    have hγ : Tendsto C.γ atTop (𝓝 e) := hγ_of ha
      ((ha.mul hU).congr fun t => (hy2 t).symm) ((ha.mul hv).congr fun t => (hy3 t).symm)
    have he : e ∈ HF := isClosed_HF.mem_of_tendsto hγ (Eventually.of_forall C.mem)
    have hβ : Tendsto (fun t => C.β (C.γ t)) atTop (𝓝 (C.β e)) := (C.cβ.tendsto e).comp hγ
    have hF0 : Fu c L 0 τ = 0 := by
      have hlim : Tendsto (fun t => C.β (C.γ t) * (C.γ t).1 *
          Fu c ((C.γ t).2.1 / (C.γ t).1) ((C.γ t).2.2 / (C.γ t).1) τ) atTop
          (𝓝 (C.β e * a * Fu c L 0 τ)) := by
        refine (hβ.mul ha).mul ?_
        have hcF : Continuous fun p : ℝ × ℝ => Fu c p.1 p.2 τ := by unfold Fu; fun_prop
        have h2 := hU.prodMk_nhds hv
        have := (hcF.tendsto (L, 0)).comp h2
        simpa only [Function.comp_def] using this
      have := deriv_tendsto_zero (C.hasDerivAt_U h1) hU hlim
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (mul_pos (C.pos e he) hapos).ne'
      · exact h
    refine ⟨e, he, fieldF_eq_zero_of_equator (by simp [e]) ?_ ?_, hγ⟩
    · have := he.1
      simp only [e, mul_zero] at this ⊢
      linarith
    · have : e.1 * fP2 c τ e - e.2.1 * fP1 τ e = a ^ 3 * Fu c L 0 τ := by
        simp only [e, fP1, fP2, Fu]; ring
      rw [this, hF0, mul_zero]

/-! ### The sign of `π̄ - 2` -/

/-- In the finite part, the sign of `π̄ - 2` is eventually constant. -/
theorem eventually_sign_g (hc : c ≠ 0) (hτ : τ ≠ 0) (hne : ∀ t, fieldF c τ (C.γ t) ≠ 0)
    (h3 : ∀ t, 0 < (C.γ t).2.2) :
    ∃ t₁, (∀ t, t₁ ≤ t → 0 < (C.γ t).2.1 / (C.γ t).2.2 - 2) ∨
      (∀ t, t₁ ≤ t → (C.γ t).2.1 / (C.γ t).2.2 - 2 < 0) := by
  set T : ℝ → ℝ := fun t => (C.γ t).1 / (C.γ t).2.2
  set g : ℝ → ℝ := fun t => (C.γ t).2.1 / (C.γ t).2.2 - 2
  set M : ℝ → ℝ := fun t => C.β (C.γ t) * (C.γ t).2.2
  have hM : ∀ t, 0 < M t := fun t => mul_pos (C.m_pos t) (h3 t)
  have hdT : ∀ t, HasDerivAt T (M t * βT (T t) (g t + 2) τ) t := fun t => by
    have := C.hasDerivAt_T h3 t
    simp only [T, g, sub_add_cancel]
    exact this
  have hdg : ∀ t, HasDerivAt g (M t * βπ c (T t) (g t + 2) τ) t := fun t => by
    have := (C.hasDerivAt_P h3 t).sub_const 2
    simp only [T, g, sub_add_cancel]
    exact this
  have heq_of : ∀ t, g t = 0 → T t = -(38 * c * τ / 15) → False := fun t hg hT => by
    apply hne t
    have h3t := (h3 t).ne'
    have hP : (C.γ t).2.1 / (C.γ t).2.2 = 2 := by simp only [g] at hg; linarith
    refine fieldF_eq_zero_of_P ?_ ?_
    · have : fP1 τ (C.γ t) = (C.γ t).2.2 ^ 2 * βT (T t) (g t + 2) τ := by
        simp only [T, g, sub_add_cancel, fP1, βT]; field_simp
      rw [this, hg]; simp [βT]
    · have : fP2 c τ (C.γ t) = (C.γ t).2.2 ^ 2 * βπ c (T t) (g t + 2) τ := by
        simp only [T, g, sub_add_cancel, fP2, βπ]; field_simp
      rw [this, hg, hT]; simp only [βπ]; field_simp; ring
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun t => (hdg t).continuousAt
  by_cases hz : ∃ t₀, g t₀ = 0
  · obtain ⟨t₀, hg0⟩ := hz
    set k₀ := T t₀ + 38 * c * τ / 15
    have hk₀ : k₀ ≠ 0 := fun h => heq_of t₀ hg0 (by simp only [k₀] at h; linarith)
    set G : ℝ → ℝ := fun t => -c * k₀ * g t
    set K : ℝ → ℝ := fun t => k₀ * (T t + 38 * c * τ / 15)
    have hdG : ∀ t, HasDerivAt G (-c * k₀ * (M t * βπ c (T t) (g t + 2) τ)) t :=
      fun t => (hdg t).const_mul _
    have hdK : ∀ t, HasDerivAt K (k₀ * (M t * βT (T t) (g t + 2) τ)) t :=
      fun t => ((hdT t).add_const _).const_mul _
    have hGd : ∀ t, g t = 0 → -c * k₀ * (M t * βπ c (T t) (g t + 2) τ) = 2 * M t * K t :=
      fun t hg => by simp only [K, hg, βπ]; field_simp; ring
    have hKd : ∀ t, T t + 38 * c * τ / 15 = 0 →
        k₀ * (M t * βT (T t) (g t + 2) τ) = M t * (38 * τ ^ 2 / 45) * G t := fun t hT => by
      have hT' : T t = -(38 * c * τ / 15) := by linarith
      simp only [G, βT, hT']; field_simp; ring
    have hK0 : 0 < K t₀ := by
      exact mul_self_pos.2 hk₀
    have hG' : 0 < -c * k₀ * (M t₀ * βπ c (T t₀) (g t₀ + 2) τ) := by
      rw [hGd t₀ hg0]; exact mul_pos (mul_pos two_pos (hM t₀)) hK0
    obtain ⟨t₁, ⟨hGt₁, hKt₁⟩, ht₁⟩ := ((((eventually_sign (hdG t₀).neg (neg_lt_zero.2 hG')).1).and
      (nhdsWithin_le_nhds ((hdK t₀).continuousAt.eventually (Ioi_mem_nhds hK0)))).and
      self_mem_nhdsWithin).exists
    have hGt₁' : 0 < G t₁ := by
      have h0 : G t₀ = 0 := by simp only [G, hg0, mul_zero]
      have : -G t₁ < -G t₀ := hGt₁
      linarith
    have hquad : ∀ t, t₁ ≤ t → 0 < G t := fun t ht =>
      (quadrant_forward hdG hdK hGt₁' hKt₁
        (fun s _ hGs hKs => by
          have hgs : g s = 0 := by
            simp only [G] at hGs
            rcases mul_eq_zero.1 hGs with h | h
            · exact absurd h (mul_ne_zero (neg_ne_zero.2 hc) hk₀)
            · exact h
          rw [hGd s hgs]; exact mul_pos (mul_pos two_pos (hM s)) hKs)
        (fun s _ hKs hGs => by
          have hTs : T s + 38 * c * τ / 15 = 0 := by
            simp only [K] at hKs
            rcases mul_eq_zero.1 hKs with h | h
            · exact absurd h hk₀
            · exact h
          rw [hKd s hTs]
          have hτ2 : 0 < 38 * τ ^ 2 / 45 := by
            have := lt_of_le_of_ne (sq_nonneg τ) (Ne.symm (pow_ne_zero 2 hτ))
            positivity
          exact mul_pos (mul_pos (hM s) hτ2) hGs)
        (fun s _ ⟨hGs, hKs⟩ => by
          have hgs : g s = 0 := by
            rcases mul_eq_zero.1 hGs with h | h
            · exact absurd h (mul_ne_zero (neg_ne_zero.2 hc) hk₀)
            · exact h
          have hTs : T s + 38 * c * τ / 15 = 0 := by
            rcases mul_eq_zero.1 hKs with h | h
            · exact absurd h hk₀
            · exact h
          exact heq_of s hgs (by linarith)) ht).1
    refine ⟨t₁, ?_⟩
    rcases lt_or_gt_of_ne (mul_ne_zero (neg_ne_zero.2 hc) hk₀) with hs | hs
    · exact Or.inr fun t ht => by
        have := hquad t ht
        simp only [G] at this
        exact neg_of_mul_pos_right this hs.le
    · exact Or.inl fun t ht => by
        have := hquad t ht
        simp only [G] at this
        exact pos_of_mul_pos_right this hs.le
  · push Not at hz
    refine ⟨0, ?_⟩
    rcases lt_or_gt_of_ne (hz 0) with h0 | h0
    · refine Or.inr fun t _ => lt_of_not_ge fun ht => ?_
      obtain ⟨s, hs⟩ := intermediate_value_univ 0 t hgc ⟨h0.le, ht⟩
      exact hz s hs
    · refine Or.inl fun t _ => lt_of_not_ge fun ht => ?_
      obtain ⟨s, hs⟩ := intermediate_value_univ t 0 hgc ⟨ht, h0.le⟩
      exact hz s hs

/-- In the finite part with `T > 0`, `T` is eventually monotone, so it tends to `+∞` or to a
finite limit. -/
theorem tendsto_T (hc : c ≠ 0) (hτ : τ ≠ 0) (hne : ∀ t, fieldF c τ (C.γ t) ≠ 0)
    (h1 : ∀ t, 0 < (C.γ t).1) (h3 : ∀ t, 0 < (C.γ t).2.2) :
    Tendsto (fun t => (C.γ t).1 / (C.γ t).2.2) atTop atTop ∨
      ∃ ℓ, Tendsto (fun t => (C.γ t).1 / (C.γ t).2.2) atTop (𝓝 ℓ) := by
  obtain ⟨t₁, hg⟩ := C.eventually_sign_g hc hτ hne h3
  have hTpos : ∀ t, 0 < (C.γ t).1 / (C.γ t).2.2 := fun t => div_pos (h1 t) (h3 t)
  have hsign : (∀ t, t₁ ≤ t → 0 < ((C.γ t).2.1 / (C.γ t).2.2 - 2) * τ) ∨
      (∀ t, t₁ ≤ t → ((C.γ t).2.1 / (C.γ t).2.2 - 2) * τ < 0) := by
    rcases hg with hg | hg <;> rcases lt_or_gt_of_ne hτ with hτ' | hτ'
    · exact Or.inr fun t ht => mul_neg_of_pos_of_neg (hg t ht) hτ'
    · exact Or.inl fun t ht => mul_pos (hg t ht) hτ'
    · exact Or.inl fun t ht => mul_pos_of_neg_of_neg (hg t ht) hτ'
    · exact Or.inr fun t ht => mul_neg_of_neg_of_pos (hg t ht) hτ'
  have hfac : ∀ t, C.β (C.γ t) * (C.γ t).2.2 *
      βT ((C.γ t).1 / (C.γ t).2.2) ((C.γ t).2.1 / (C.γ t).2.2) τ =
      C.β (C.γ t) * (C.γ t).2.2 * ((C.γ t).1 / (C.γ t).2.2) / 3 *
        (((C.γ t).2.1 / (C.γ t).2.2 - 2) * τ) := fun t => by simp only [βT]; ring
  have hpos : ∀ t, 0 < C.β (C.γ t) * (C.γ t).2.2 * ((C.γ t).1 / (C.γ t).2.2) / 3 := fun t => by
    have := C.m_pos t; have := h3 t; have := hTpos t; positivity
  rcases hsign with hs | hs
  · exact tendsto_of_monotoneOn_Ici (monotoneOn_Ici_of_deriv (C.hasDerivAt_T h3) fun t ht => by
      rw [hfac t]; exact (mul_pos (hpos t) (hs t ht)).le)
  · obtain ⟨ℓ, hℓ⟩ := tendsto_of_antitoneOn_Ici (antitoneOn_Ici_of_deriv (C.hasDerivAt_T h3)
      fun t ht => by rw [hfac t]; exact (mul_neg_of_pos_of_neg (hpos t) (hs t ht)).le)
      fun t => (hTpos t).le
    exact Or.inr ⟨ℓ, hℓ⟩

/-- Forward convergence to an equilibrium when the curve starts in `T ≥ 0`. -/
theorem tendsto_core (hc : c ≠ 0) (hτ : τ ≠ 0) (h10 : 0 ≤ (C.γ 0).1) :
    ∃ e ∈ HF, fieldF c τ e = 0 ∧ Tendsto C.γ atTop (𝓝 e) := by
  by_cases hne : ∃ t, fieldF c τ (C.γ t) = 0
  · obtain ⟨t, he⟩ := hne
    exact ⟨C.γ t, C.mem t, he,
      tendsto_const_nhds.congr fun s => (C.rest (C.γ t) he t rfl s).symm⟩
  push Not at hne
  rcases (C.mem 0).2.lt_or_eq with h3 | h3
  · have h3' := C.y3_pos h3
    rcases h10.lt_or_eq with h1 | h1
    · rcases C.tendsto_T hc hτ hne (C.y1_pos h1) h3' with hT | ⟨ℓ, hT⟩
      · refine C.tendsto_of_v hτ (C.y1_pos h1) ?_
        exact (tendsto_inv_atTop_zero.comp hT).congr fun t => by
          simp only [Function.comp_apply, inv_div]
      · exact C.tendsto_of_T hτ h3' hT
    · exact C.tendsto_of_T hτ h3' (ℓ := 0)
        (tendsto_const_nhds.congr fun t => by rw [C.y1_zero h1.symm t, zero_div])
  · rcases h10.lt_or_eq with h1 | h1
    · exact C.tendsto_of_v hτ (C.y1_pos h1)
        (tendsto_const_nhds.congr fun t => by rw [C.y3_zero h3.symm t, zero_div])
    · have hγ0 : C.γ 0 = (0, (C.γ 0).2.1, 0) := Prod.ext h1.symm (Prod.ext rfl h3.symm)
      have hs : (C.γ 0).2.1 ^ 2 = 1 := by
        have := (C.mem 0).1
        rw [← h1, ← h3] at this
        linarith
      exact absurd (by rw [hγ0]; exact fieldF_pole c τ _ hs) (hne 0)

/-- The reflection `T ↦ -T` maps curves of `fieldF c τ` to curves of `fieldF (-c) τ`. -/
def reflect : FiberCurve (-c) τ where
  γ t := refl3 (C.γ t)
  β y := C.β (refl3 y)
  cβ := C.cβ.comp continuous_refl3
  pos y hy := C.pos _ (refl3_mem hy)
  mem t := refl3_mem (C.mem t)
  deriv t := by
    rw [refl3_refl3, fieldF_refl3]
    show HasDerivAt (fun t => ((-(C.γ t).1, (C.γ t).2.1, (C.γ t).2.2) : E3)) _ t
    refine ((C.d1 t).neg.prodMk ((C.d2 t).prodMk (C.d3 t))).congr_deriv ?_
    simp only [refl3, Prod.smul_mk, smul_eq_mul, mul_neg]
  rest e he t ht s := by
    have h1 : fieldF c τ (refl3 e) = 0 := by
      have := fieldF_refl3 (-c) τ e
      rw [neg_neg, he] at this
      rw [this]; simp [refl3]
    have := C.rest (refl3 e) h1 t (by rw [← ht]; exact (refl3_refl3 _).symm)
    show refl3 (C.γ s) = e
    rw [this, refl3_refl3]

/-- Time reversal maps curves of `fieldF c τ` to curves of `fieldF (-c) (-τ)`. -/
def reverse : FiberCurve (-c) (-τ) where
  γ t := C.γ (-t)
  β := C.β
  cβ := C.cβ
  pos := C.pos
  mem t := C.mem (-t)
  deriv t := by
    rw [fieldF_neg]
    refine ((C.deriv (-t)).scomp t (hasDerivAt_neg t)).congr_deriv ?_
    rw [neg_one_smul, smul_neg]
  rest e he t ht s := by
    rw [fieldF_neg, neg_eq_zero] at he
    exact C.rest e he (-t) ht (-s)

/-- Every curve converges to an equilibrium in forward time. -/
theorem tendsto_atTop (hc : c ≠ 0) (hτ : τ ≠ 0) :
    ∃ e ∈ HF, fieldF c τ e = 0 ∧ Tendsto C.γ atTop (𝓝 e) := by
  rcases le_or_gt 0 (C.γ 0).1 with h | h
  · exact C.tendsto_core hc hτ h
  · obtain ⟨e, he, hf, ht⟩ := C.reflect.tendsto_core (neg_ne_zero.2 hc) hτ
      (by show 0 ≤ -(C.γ 0).1; linarith)
    refine ⟨refl3 e, refl3_mem he, ?_, ?_⟩
    · have := fieldF_refl3 (-c) τ e
      rw [neg_neg, hf] at this
      rw [this]; simp [refl3]
    · exact ((continuous_refl3.tendsto e).comp ht).congr fun t => refl3_refl3 (C.γ t)

/-- Every curve converges to an equilibrium in backward time. -/
theorem tendsto_atBot (hc : c ≠ 0) (hτ : τ ≠ 0) :
    ∃ e ∈ HF, fieldF c τ e = 0 ∧ Tendsto C.γ atBot (𝓝 e) := by
  obtain ⟨e, he, hf, ht⟩ := C.reverse.tendsto_atTop (neg_ne_zero.2 hc) (neg_ne_zero.2 hτ)
  refine ⟨e, he, by rwa [fieldF_neg, neg_eq_zero] at hf, ?_⟩
  exact (ht.comp tendsto_neg_atBot_atTop).congr fun t => by
    show C.γ (-(-t)) = C.γ t
    rw [neg_neg]

end FiberCurve

/-- The orbit of `p` under the fiber flow, as a curve along `fieldF`. -/
noncomputable def curveF (c τ : ℝ) (p : HF) : FiberCurve c τ where
  γ t := (ϕF c τ t p : E3)
  β _ := 1
  cβ := continuous_const
  pos _ _ := one_pos
  mem t := (ϕF c τ t p).2
  deriv t := by rw [one_smul]; exact hasDerivAt_ϕF c τ p t
  rest e he t ht s := by
    have ht' : flowF c τ t p = e := ht
    show flowF c τ s p = e
    rw [show s = (s - t) + t by ring, Flow.map_add, ht', flowF_fixed he]

/-- `lem:fiber` (iii), strengthened: for `c ≠ 0` and `τ ≠ 0`, every orbit of the fiber flow
on the closed hemisphere converges to a single equilibrium in both time directions. -/
theorem lem_fiber_iii {c τ : ℝ} (hc : c ≠ 0) (hτ : τ ≠ 0) (p : HF) :
    (∃ e ∈ HF, fieldF c τ e = 0 ∧ Tendsto (fun t => (ϕF c τ t p : E3)) atTop (𝓝 e)) ∧
      ∃ e ∈ HF, fieldF c τ e = 0 ∧ Tendsto (fun t => (ϕF c τ t p : E3)) atBot (𝓝 e) :=
  ⟨(curveF c τ p).tendsto_atTop hc hτ, (curveF c τ p).tendsto_atBot hc hτ⟩

/-- `lem:fiber` (ii): for `c ≠ 0` and `τ ≠ 0`, the fiber flow has no nonconstant periodic
orbits. -/
theorem lem_fiber_ii {c τ : ℝ} (hc : c ≠ 0) (hτ : τ ≠ 0) (p : HF) {P : ℝ} (hP : 0 < P)
    (hper : ϕF c τ P p = p) : fieldF c τ p = 0 := by
  obtain ⟨e, -, he, hte⟩ := (lem_fiber_iii hc hτ p).1
  have hn : ∀ n : ℕ, ϕF c τ (n * P) p = p := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, Flow.map_add, hper, ih]
  have hseq : Tendsto (fun n : ℕ => (ϕF c τ (n * P) p : E3)) atTop (𝓝 e) :=
    hte.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hP)
  have : (p : E3) = e :=
    tendsto_nhds_unique (tendsto_const_nhds.congr fun n => by rw [hn n]) hseq
  rw [this]; exact he

end ConleyCheck.Gubser
