import ConleyCheck.Conley.Rate
import ConleyCheck.Gubser.TCFlow
import ConleyCheck.ODE.Crossing
import ConleyCheck.ON.Limits

/-!
# The torus compactification of the reduced Gubser flow (`prop:torus`)

The reduced system on `T = 0` is `π̄' = -(4/3)(π̄² - a²) τ`, `τ' = 1 - τ²`. We take any `a > 0`.

* The base. `τ(t) = θ_t(τ) = (τ cosh t + sinh t)/(cosh t + τ sinh t)` (`baseFlow`), and
  `σ(t, τ) = log (cosh t + τ sinh t) = ∫₀ᵗ τ` satisfies the cocycle identity `sigma_add`.
* The fiber `ℝP¹`, modeled by the unit circle `S1` through the doubled angle
  `z = (cos 2φ, sin 2φ)` with `π̄ = tan φ`. The Riccati equation becomes the flow `ψR` of
  `fieldR`, whose charts `π̄ = z₂/(1 + z₁)` and `w = 1/π̄ = z₂/(1 - z₁)` satisfy
  `π̄' = -(4/3)(π̄² - a²)` and `w' = (4/3)(1 - a² w²)` (`hasDerivAt_chartP`, `hasDerivAt_chartW`).
  Every orbit other than `B` converges to `A` in forward time, and every orbit other than `A`
  converges to `B` in backward time (`tendsto_ψR_atTop`, `tendsto_ψR_atBot`).
* Since the fiber equation is the autonomous Riccati equation in the time `σ`, the flows are
  `Φ_t(z, τ) = (ψ_{σ(t, τ)} z, θ_t τ)` on `S1 × [-1, 1]`, and on the torus `S1 × S1`
  `Ψ_t(z, w) = (ψ_{σ(t, w₁)} z, B_t w)`, where `B` is the flow of `ϑ' = -sin ϑ` in the coordinates
  `w = (cos ϑ, sin ϑ)`, so that `τ = cos ϑ = w₁`.

## Main results

* `prop_torus_equilibria`, `prop_torus_i`, `hasFDerivAt_chartField`: Proposition `prop:torus`(i).
* `torus_connect`: every non-stationary orbit of the torus and its limits.
* `prop_torus_ii`: Proposition `prop:torus`(ii), `CH_*(T²) ≅ H_*(T²)`, and
  `eq_zero_of_finrank_homology` for the vanishing of the connection matrix.
* `prop_torus_iii`, `prop_torus_iii_chains`: Proposition `prop:torus`(iii).
-/

open Set Filter Topology
open ConleyCheck.Conley ConleyCheck.ODE

namespace ConleyCheck.Gubser

/-! ## The base flow `τ' = 1 - τ²` -/

/-- `D(t, τ) = cosh t + τ sinh t`. -/
noncomputable def Dt (t τ : ℝ) : ℝ := Real.cosh t + τ * Real.sinh t

theorem Dt_eq (t τ : ℝ) : Dt t τ = ((1 + τ) * Real.exp t + (1 - τ) * Real.exp (-t)) / 2 := by
  rw [Dt, Real.cosh_eq, Real.sinh_eq]; ring

theorem Dt_pos {τ : ℝ} (hτ : τ ∈ Icc (-1 : ℝ) 1) (t : ℝ) : 0 < Dt t τ := by
  rw [Dt_eq]
  have h1 := Real.exp_pos t
  have h2 := Real.exp_pos (-t)
  have hA : 0 ≤ (1 + τ) * Real.exp t := mul_nonneg (by linarith [hτ.1]) h1.le
  have hB : 0 ≤ (1 - τ) * Real.exp (-t) := mul_nonneg (by linarith [hτ.2]) h2.le
  rcases le_total 0 τ with h | h
  · have : 0 < (1 + τ) * Real.exp t := mul_pos (by linarith) h1
    linarith
  · have : 0 < (1 - τ) * Real.exp (-t) := mul_pos (by linarith) h2
    linarith

/-- The base flow `θ_t(τ)` of `τ' = 1 - τ²`. -/
noncomputable def thetaF (t τ : ℝ) : ℝ := (τ * Real.cosh t + Real.sinh t) / Dt t τ

theorem one_sub_thetaF {τ : ℝ} (hτ : τ ∈ Icc (-1 : ℝ) 1) (t : ℝ) :
    1 - thetaF t τ = (1 - τ) * Real.exp (-t) / Dt t τ := by
  have hD := (Dt_pos hτ t).ne'
  have key : Dt t τ - (τ * Real.cosh t + Real.sinh t) = (1 - τ) * Real.exp (-t) := by
    rw [Dt, Real.cosh_eq, Real.sinh_eq]; ring
  rw [thetaF, ← key, sub_div, div_self hD]

theorem one_add_thetaF {τ : ℝ} (hτ : τ ∈ Icc (-1 : ℝ) 1) (t : ℝ) :
    1 + thetaF t τ = (1 + τ) * Real.exp t / Dt t τ := by
  have hD := (Dt_pos hτ t).ne'
  have key : Dt t τ + (τ * Real.cosh t + Real.sinh t) = (1 + τ) * Real.exp t := by
    rw [Dt, Real.cosh_eq, Real.sinh_eq]; ring
  rw [thetaF, ← key]
  field_simp

theorem thetaF_mem {τ : ℝ} (hτ : τ ∈ Icc (-1 : ℝ) 1) (t : ℝ) : thetaF t τ ∈ Icc (-1 : ℝ) 1 := by
  have h1 := one_sub_thetaF hτ t
  have h2 := one_add_thetaF hτ t
  have hD := Dt_pos hτ t
  have e1 : 0 ≤ (1 - τ) * Real.exp (-t) / Dt t τ :=
    div_nonneg (mul_nonneg (by linarith [hτ.2]) (Real.exp_pos _).le) hD.le
  have e2 : 0 ≤ (1 + τ) * Real.exp t / Dt t τ :=
    div_nonneg (mul_nonneg (by linarith [hτ.1]) (Real.exp_pos _).le) hD.le
  constructor <;> linarith

theorem Dt_mul {τ : ℝ} (hτ : τ ∈ Icc (-1 : ℝ) 1) (t s : ℝ) :
    Dt t (thetaF s τ) * Dt s τ = Dt (t + s) τ := by
  have hD := (Dt_pos hτ s).ne'
  simp only [Dt, thetaF] at hD ⊢
  rw [Real.cosh_add, Real.sinh_add]
  field_simp
  ring

theorem thetaF_add {τ : ℝ} (hτ : τ ∈ Icc (-1 : ℝ) 1) (t s : ℝ) :
    thetaF t (thetaF s τ) = thetaF (t + s) τ := by
  have hD := (Dt_pos hτ s).ne'
  have key : (thetaF s τ * Real.cosh t + Real.sinh t) * Dt s τ =
      τ * Real.cosh (t + s) + Real.sinh (t + s) := by
    simp only [Dt, thetaF] at hD ⊢
    rw [Real.cosh_add, Real.sinh_add]
    field_simp
    ring
  show (thetaF s τ * Real.cosh t + Real.sinh t) / Dt t (thetaF s τ) =
    (τ * Real.cosh (t + s) + Real.sinh (t + s)) / Dt (t + s) τ
  rw [← Dt_mul hτ t s, ← key, mul_div_mul_right _ _ hD]

theorem continuous_thetaF : Continuous fun p : ℝ × Tau => thetaF p.1 p.2 := by
  refine Continuous.div ?_ ?_ fun p => (Dt_pos p.2.2 p.1).ne'
  · exact ((continuous_subtype_val.comp continuous_snd).mul
      (Real.continuous_cosh.comp continuous_fst)).add (Real.continuous_sinh.comp continuous_fst)
  · exact (Real.continuous_cosh.comp continuous_fst).add
      ((continuous_subtype_val.comp continuous_snd).mul (Real.continuous_sinh.comp continuous_fst))

/-- The base flow on `[-1, 1]`. -/
noncomputable def baseFlow : Flow ℝ Tau where
  toFun t τ := ⟨thetaF t τ, thetaF_mem τ.2 t⟩
  cont' := continuous_thetaF.subtype_mk _
  map_add' t s τ := Subtype.ext (thetaF_add τ.2 t s).symm
  map_zero' τ := Subtype.ext (by simp [thetaF, Dt])

theorem baseFlow_apply (t : ℝ) (τ : Tau) : (baseFlow t τ : ℝ) = thetaF t τ := rfl

theorem thetaF_sub {τ : ℝ} (hτ : τ ∈ Icc (-1 : ℝ) 1) (t : ℝ) :
    thetaF t τ - τ = Real.sinh t * (1 - τ ^ 2) / Dt t τ := by
  have hD := (Dt_pos hτ t).ne'
  rw [thetaF, eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD, Dt]
  ring

/-- `τ` is a height function for the base flow. -/
theorem isHeight_baseFlow : IsHeight baseFlow (fun b => (b : ℝ)) where
  continuous := continuous_subtype_val
  mem b := b.2
  fix b hb t := by
    show thetaF t b = b
    rcases hb with h | h
    · have := one_sub_thetaF b.2 t
      rw [h] at this ⊢
      rw [sub_self, zero_mul, zero_div] at this
      linarith
    · have := one_add_thetaF b.2 t
      rw [h] at this ⊢
      rw [add_neg_cancel, zero_mul, zero_div] at this
      linarith
  strict b h1 h2 t ht := by
    show (b : ℝ) < thetaF t b
    have := thetaF_sub b.2 t
    have hs : 0 < Real.sinh t := Real.sinh_pos_iff.2 ht
    have hb : 0 < 1 - (b : ℝ) ^ 2 := by nlinarith
    have : 0 < Real.sinh t * (1 - (b : ℝ) ^ 2) / Dt t b := div_pos (mul_pos hs hb) (Dt_pos b.2 t)
    linarith

/-! ## The time change `σ(t, τ) = ∫₀ᵗ τ` -/

/-- `σ(t, τ) = log (cosh t + τ sinh t)`, the integral of `τ` along the base orbit. -/
noncomputable def sigma (t τ : ℝ) : ℝ := Real.log (Dt t τ)

theorem sigma_add {τ : ℝ} (hτ : τ ∈ Icc (-1 : ℝ) 1) (t s : ℝ) :
    sigma (t + s) τ = sigma t (thetaF s τ) + sigma s τ := by
  rw [sigma, sigma, sigma, ← Dt_mul hτ t s,
    Real.log_mul (Dt_pos (thetaF_mem hτ s) t).ne' (Dt_pos hτ s).ne']

theorem sigma_zero (τ : ℝ) : sigma 0 τ = 0 := by simp [sigma, Dt]

theorem sigma_one (t : ℝ) : sigma t 1 = t := by
  have : Dt t 1 = Real.exp t := by rw [Dt_eq]; ring
  rw [sigma, this, Real.log_exp]

theorem sigma_neg_one (t : ℝ) : sigma t (-1) = -t := by
  have : Dt t (-1) = Real.exp (-t) := by rw [Dt_eq]; ring
  rw [sigma, this, Real.log_exp]

theorem continuous_sigma : Continuous fun p : ℝ × Tau => sigma p.1 p.2 := by
  refine Continuous.log ?_ fun p => (Dt_pos p.2.2 p.1).ne'
  exact (Real.continuous_cosh.comp continuous_fst).add
    ((continuous_subtype_val.comp continuous_snd).mul (Real.continuous_sinh.comp continuous_fst))

theorem hasDerivAt_sigma {τ : ℝ} (hτ : τ ∈ Icc (-1 : ℝ) 1) (t : ℝ) :
    HasDerivAt (fun s => sigma s τ) (thetaF t τ) t := by
  have hD : HasDerivAt (fun s => Dt s τ) (Real.sinh t + τ * Real.cosh t) t :=
    (Real.hasDerivAt_cosh t).add ((Real.hasDerivAt_sinh t).const_mul τ)
  refine (hD.log (Dt_pos hτ t).ne').congr_deriv ?_
  unfold thetaF; ring

theorem tendsto_sigma_atTop {τ : ℝ} (h1 : -1 < τ) (h2 : τ ≤ 1) :
    Tendsto (fun t => sigma t τ) atTop atTop := by
  have hlow : ∀ t, (1 + τ) / 2 * Real.exp t ≤ Dt t τ := fun t => by
    rw [Dt_eq]
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - τ) (Real.exp_pos (-t)).le
    linarith
  exact Real.tendsto_log_atTop.comp (tendsto_atTop_mono hlow
    (Real.tendsto_exp_atTop.const_mul_atTop (by linarith)))

theorem tendsto_sigma_atBot {τ : ℝ} (h1 : -1 ≤ τ) (h2 : τ < 1) :
    Tendsto (fun t => sigma t τ) atBot atTop := by
  have hlow : ∀ t, (1 - τ) / 2 * Real.exp (-t) ≤ Dt t τ := fun t => by
    rw [Dt_eq]
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + τ) (Real.exp_pos t).le
    linarith
  exact Real.tendsto_log_atTop.comp (tendsto_atTop_mono hlow
    ((Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop).const_mul_atTop (by linarith)))

/-! ## The fiber `ℝP¹` and the Riccati flow -/

/-- The unit circle, the model of `ℝP¹` through `z = (cos 2φ, sin 2φ)`, `π̄ = tan φ`. -/
def S1 : Set (ℝ × ℝ) := {z | z.1 ^ 2 + z.2 ^ 2 = 1}

theorem isClosed_S1 : IsClosed S1 := isClosed_eq (by fun_prop) continuous_const

theorem norm_le_one_of_S1 {z : ℝ × ℝ} (hz : z ∈ S1) : ‖z‖ ≤ 1 := by
  have h : z.1 ^ 2 + z.2 ^ 2 = 1 := hz
  refine norm_prod_le_iff.2 ⟨?_, ?_⟩ <;> rw [Real.norm_eq_abs] <;>
    refine (sq_le_one_iff_abs_le_one _).1 ?_ <;> nlinarith [sq_nonneg z.1, sq_nonneg z.2]

theorem isCompact_S1 : IsCompact S1 :=
  (isCompact_closedBall (0 : ℝ × ℝ) 1).of_isClosed_subset isClosed_S1 fun z hz => by
    rw [mem_closedBall_zero_iff]; exact norm_le_one_of_S1 hz

instance : CompactSpace S1 := isCompact_iff_compactSpace.1 isCompact_S1

theorem fst_mem_Icc_of_S1 {z : ℝ × ℝ} (hz : z ∈ S1) : z.1 ∈ Icc (-1 : ℝ) 1 := by
  have h : z.1 ^ 2 + z.2 ^ 2 = 1 := hz
  have : |z.1| ≤ 1 := (sq_le_one_iff_abs_le_one _).1 (by nlinarith [sq_nonneg z.2])
  exact abs_le.1 this

variable (a : ℝ)

/-- The angular speed `dα/ds` of the doubled angle `α = 2φ`. -/
noncomputable def kap (z : ℝ × ℝ) : ℝ := 4 / 3 * ((1 + a ^ 2) * z.1 - (1 - a ^ 2))

/-- The Riccati field on the circle. -/
noncomputable def fieldR (z : ℝ × ℝ) : ℝ × ℝ := (-(kap a z * z.2), kap a z * z.1)

theorem contDiff_fieldR : ContDiff ℝ 1 (fieldR a) := by unfold fieldR kap; fun_prop

/-- The global flow of the cut-off Riccati field on `ℝ²`. -/
noncomputable def flowR : Flow ℝ (ℝ × ℝ) := bumpFlow (contDiff_fieldR a) 2 two_pos

/-- The cut-off, equal to `1` on the ball of radius `2`. -/
noncomputable def bR : ℝ × ℝ → ℝ := (bumpOf (E := ℝ × ℝ) 2 two_pos : ℝ × ℝ → ℝ)

theorem hasDerivAt_flowR (p : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun s => flowR a s p) (bR (flowR a t p) • fieldR a (flowR a t p)) t :=
  hasDerivAt_bumpFlow _ p t

theorem isInvariant_S1 : IsInvariant (flowR a) S1 := by
  intro t p hp
  have hγ := hasDerivAt_flowR a p
  have hW : ∀ s, HasDerivAt (fun r => (flowR a r p).1 ^ 2 + (flowR a r p).2 ^ 2 - 1)
      (0 * ((flowR a s p).1 ^ 2 + (flowR a s p).2 ^ 2 - 1)) s := by
    intro s
    have h1 := (hasDerivAt_fst' (hγ s)).pow 2
    have h2 := (hasDerivAt_snd' (hγ s)).pow 2
    convert (h1.add h2).sub_const 1 using 1
    simp only [Prod.smul_fst, Prod.smul_snd, fieldR, smul_eq_mul, Nat.cast_ofNat]; ring
  have h0 : (flowR a 0 p).1 ^ 2 + (flowR a 0 p).2 ^ 2 - 1 = 0 := by
    rw [Flow.map_zero_apply]
    have : p.1 ^ 2 + p.2 ^ 2 = 1 := hp
    linarith
  have := eq_zero_of_linear_all hW continuous_const h0 t
  show (flowR a t p).1 ^ 2 + (flowR a t p).2 ^ 2 = 1
  linarith

/-- The Riccati flow on `ℝP¹ ≅ S1`. -/
noncomputable def ψR : Flow ℝ S1 := (flowR a).restrict (isInvariant_S1 a)

theorem ψR_apply (t : ℝ) (p : S1) : (ψR a t p : ℝ × ℝ) = flowR a t p := rfl

theorem hasDerivAt_ψR (p : S1) (t : ℝ) :
    HasDerivAt (fun s => (ψR a s p : ℝ × ℝ)) (fieldR a (ψR a t p)) t := by
  have h := hasDerivAt_flowR a p t
  rw [show bR (flowR a t p) = 1 from
    bumpOf_eq_one ((norm_le_one_of_S1 (ψR a t p).2).trans one_le_two), one_smul] at h
  exact h

/-! ### The two equilibria -/

/-- `z₁` at the equilibria, `cos 2φ` with `tan φ = ±a`. -/
noncomputable def xs : ℝ := (1 - a ^ 2) / (1 + a ^ 2)

/-- `|z₂|` at the equilibria. -/
noncomputable def ys : ℝ := 2 * a / (1 + a ^ 2)

/-- The point `π̄ = a`. -/
noncomputable def zA : ℝ × ℝ := (xs a, ys a)

/-- The point `π̄ = -a`. -/
noncomputable def zB : ℝ × ℝ := (xs a, -ys a)

theorem xs_sq_add : xs a ^ 2 + ys a ^ 2 = 1 := by
  have : (0 : ℝ) < 1 + a ^ 2 := by positivity
  unfold xs ys; field_simp; ring

theorem zA_mem : zA a ∈ S1 := xs_sq_add a

theorem zB_mem : zB a ∈ S1 := by
  show xs a ^ 2 + (-ys a) ^ 2 = 1
  rw [neg_sq]; exact xs_sq_add a

theorem kap_xs (y : ℝ) : kap a (xs a, y) = 0 := by
  have : (0 : ℝ) < 1 + a ^ 2 := by positivity
  simp only [kap, xs]; field_simp; ring

theorem fieldR_zA : fieldR a (zA a) = 0 := by simp [fieldR, zA, kap_xs]

theorem fieldR_zB : fieldR a (zB a) = 0 := by simp [fieldR, zB, kap_xs]

variable {a}

theorem zA_ne_zB (ha : 0 < a) : zA a ≠ zB a := by
  intro h
  have h2 : ys a = -ys a := congrArg Prod.snd h
  have : 0 < ys a := by unfold ys; positivity
  linarith

theorem eq_of_kap_eq_zero (ha : 0 < a) {z : ℝ × ℝ} (hz : z ∈ S1) (hk : kap a z = 0) :
    z = zA a ∨ z = zB a := by
  have hpos : (0 : ℝ) < 1 + a ^ 2 := by positivity
  have h1 : z.1 = xs a := by
    unfold kap at hk; unfold xs; rw [eq_div_iff hpos.ne']; linarith
  have h2 : z.2 ^ 2 = ys a ^ 2 := by
    have : z.1 ^ 2 + z.2 ^ 2 = 1 := hz
    have := xs_sq_add a
    rw [h1] at *; linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
  · exact Or.inl (Prod.ext h1 h)
  · exact Or.inr (Prod.ext h1 h)

theorem flowR_fixed {e : ℝ × ℝ} (he : fieldR a e = 0) (t : ℝ) : flowR a t e = e := by
  have hsol : IsSol (bumpField (fieldR a) 2 two_pos) (fun _ => e) := fun s => by
    have : bumpField (fieldR a) 2 two_pos e = 0 := by simp [bumpField, he]
    rw [this]; exact hasDerivAt_const s e
  exact flowOf_eq_of_isSol _ _ hsol 0 t

/-! ### Charts and limits -/

/-- A solution of `f' = g(f)` in an interval `(p, q)` on which `g > 0` increases from `p` to `q`. -/
theorem tendsto_Ioo_of_deriv {f g : ℝ → ℝ} (hf : ∀ s, HasDerivAt f (g (f s)) s)
    (hg : Continuous g) {p q : ℝ} (hpos : ∀ x ∈ Ioo p q, 0 < g x)
    (hI : ∀ s, f s ∈ Ioo p q) : Tendsto f atTop (𝓝 q) ∧ Tendsto f atBot (𝓝 p) := by
  have hmono : Monotone f := monotone_of_deriv_nonneg (fun s => (hf s).differentiableAt)
    fun s => by rw [(hf s).deriv]; exact (hpos _ (hI s)).le
  have hbA : BddAbove (range f) := ⟨q, by rintro _ ⟨s, rfl⟩; exact (hI s).2.le⟩
  have hbB : BddBelow (range f) := ⟨p, by rintro _ ⟨s, rfl⟩; exact (hI s).1.le⟩
  have hT := tendsto_atTop_ciSup hmono hbA
  have hB := tendsto_atBot_ciInf hmono hbB
  have hLq : ⨆ i, f i ≤ q := ciSup_le fun s => (hI s).2.le
  have hL0 : f 0 ≤ ⨆ i, f i := le_ciSup hbA 0
  have hgL : g (⨆ i, f i) = 0 := deriv_tendsto_zero hf hT ((hg.tendsto _).comp hT)
  have hL'p : p ≤ ⨅ i, f i := le_ciInf fun s => (hI s).1.le
  have hL'0 : ⨅ i, f i ≤ f 0 := ciInf_le hbB 0
  have hgL' : g (⨅ i, f i) = 0 := by
    have hneg : ∀ s, HasDerivAt (fun r => f (-r)) (-g (f (-s))) s := fun s => by
      have := (hf (-s)).scomp s (hasDerivAt_neg s)
      simpa [Function.comp_def] using this
    have h1 : Tendsto (fun r => f (-r)) atTop (𝓝 (⨅ i, f i)) := hB.comp tendsto_neg_atTop_atBot
    have := deriv_tendsto_zero hneg h1 ((hg.tendsto _).comp h1).neg
    linarith
  refine ⟨?_, ?_⟩
  · have : ⨆ i, f i = q := by
      by_contra hne
      have := hpos _ ⟨(hI 0).1.trans_le hL0, lt_of_le_of_ne hLq hne⟩
      linarith
    rwa [this] at hT
  · have : ⨅ i, f i = p := by
      by_contra hne
      have := hpos _ ⟨lt_of_le_of_ne hL'p (Ne.symm hne), hL'0.trans_lt (hI 0).2⟩
      linarith
    rwa [this] at hB

theorem chartP_sq {x y : ℝ} (hm : x ^ 2 + y ^ 2 = 1) (h1 : -1 < x) :
    (y / (1 + x)) ^ 2 = (1 - x) / (1 + x) := by
  have hne : 1 + x ≠ 0 := by linarith
  rw [div_pow, div_eq_div_iff (pow_ne_zero 2 hne) hne]
  linear_combination (1 + x) * hm

theorem chartW_sq {x y : ℝ} (hm : x ^ 2 + y ^ 2 = 1) (h1 : x < 1) :
    (y / (1 - x)) ^ 2 = (1 + x) / (1 - x) := by
  have hne : 1 - x ≠ 0 := by linarith
  rw [div_pow, div_eq_div_iff (pow_ne_zero 2 hne) hne]
  linear_combination (1 - x) * hm

/-- In the chart `π̄ = z₂/(1 + z₁)`, the Riccati equation `π̄' = -(4/3)(π̄² - a²)`. -/
theorem hasDerivAt_chartP {γ : ℝ → ℝ × ℝ} {s : ℝ} (hγ : HasDerivAt γ (fieldR a (γ s)) s)
    (hm : (γ s).1 ^ 2 + (γ s).2 ^ 2 = 1) (h1 : -1 < (γ s).1) :
    HasDerivAt (fun r => (γ r).2 / (1 + (γ r).1))
      (-(4 / 3) * (((γ s).2 / (1 + (γ s).1)) ^ 2 - a ^ 2)) s := by
  have hne : 1 + (γ s).1 ≠ 0 := by linarith
  have h := (hasDerivAt_snd' hγ).div ((hasDerivAt_fst' hγ).const_add 1) hne
  convert h using 1
  rw [chartP_sq hm h1]
  simp only [fieldR, kap]
  field_simp
  linear_combination ((1 - a ^ 2) - (1 + a ^ 2) * (γ s).1) * hm

/-- In the chart `w = 1/π̄ = z₂/(1 - z₁)`, `w' = (4/3)(1 - a² w²)`. -/
theorem hasDerivAt_chartW {γ : ℝ → ℝ × ℝ} {s : ℝ} (hγ : HasDerivAt γ (fieldR a (γ s)) s)
    (hm : (γ s).1 ^ 2 + (γ s).2 ^ 2 = 1) (h1 : (γ s).1 < 1) :
    HasDerivAt (fun r => (γ r).2 / (1 - (γ r).1))
      (4 / 3 * (1 - a ^ 2 * ((γ s).2 / (1 - (γ s).1)) ^ 2)) s := by
  have hne : 1 - (γ s).1 ≠ 0 := by linarith
  have h := (hasDerivAt_snd' hγ).div ((hasDerivAt_fst' hγ).const_sub 1) hne
  convert h using 1
  rw [chartW_sq hm h1]
  simp only [fieldR, kap]
  field_simp
  linear_combination ((1 + a ^ 2) * (γ s).1 - (1 - a ^ 2)) * hm

/-- The inverse of the chart `π̄`. -/
noncomputable def invP (P : ℝ) : ℝ × ℝ := ((1 - P ^ 2) / (1 + P ^ 2), 2 * P / (1 + P ^ 2))

/-- The inverse of the chart `w`. -/
noncomputable def invW (W : ℝ) : ℝ × ℝ := ((W ^ 2 - 1) / (W ^ 2 + 1), 2 * W / (W ^ 2 + 1))

theorem continuous_invP : Continuous invP :=
  Continuous.prodMk (Continuous.div (by fun_prop) (by fun_prop) fun P => by positivity)
    (Continuous.div (by fun_prop) (by fun_prop) fun P => by positivity)

theorem continuous_invW : Continuous invW :=
  Continuous.prodMk (Continuous.div (by fun_prop) (by fun_prop) fun P => by positivity)
    (Continuous.div (by fun_prop) (by fun_prop) fun P => by positivity)

theorem invP_chart {z : ℝ × ℝ} (hm : z.1 ^ 2 + z.2 ^ 2 = 1) (h1 : -1 < z.1) :
    invP (z.2 / (1 + z.1)) = z := by
  have hP := chartP_sq hm h1
  have hne : 1 + z.1 ≠ 0 := by linarith
  unfold invP
  rw [hP]
  refine Prod.ext ?_ ?_
  · field_simp; ring
  · field_simp; ring

theorem invW_chart {z : ℝ × ℝ} (hm : z.1 ^ 2 + z.2 ^ 2 = 1) (h1 : z.1 < 1) :
    invW (z.2 / (1 - z.1)) = z := by
  have hW := chartW_sq hm h1
  have hne : 1 - z.1 ≠ 0 := by linarith
  unfold invW
  rw [hW]
  refine Prod.ext ?_ ?_
  · field_simp; ring
  · field_simp; ring

theorem invP_pos : invP a = zA a := rfl

theorem invP_neg : invP (-a) = zB a := by
  simp only [invP, zB, xs, ys, neg_sq, mul_neg, neg_div]

theorem invW_pos (ha : 0 < a) : invW (1 / a) = zA a := by
  have := ha.ne'
  simp only [invW, zA, xs, ys]
  refine Prod.ext ?_ ?_ <;> field_simp

theorem invW_neg (ha : 0 < a) : invW (-(1 / a)) = zB a := by
  have := ha.ne'
  simp only [invW, zB, xs, ys, neg_sq]
  refine Prod.ext ?_ ?_ <;> field_simp

theorem ψR_fixed_A (t : ℝ) : ψR a t ⟨zA a, zA_mem a⟩ = ⟨zA a, zA_mem a⟩ :=
  Subtype.ext (flowR_fixed (fieldR_zA a) t)

theorem ψR_fixed_B (t : ℝ) : ψR a t ⟨zB a, zB_mem a⟩ = ⟨zB a, zB_mem a⟩ :=
  Subtype.ext (flowR_fixed (fieldR_zB a) t)

theorem continuous_ψR_orbit (p : S1) : Continuous fun s => (ψR a s p : ℝ × ℝ) :=
  continuous_subtype_val.comp ((ψR a).continuous continuous_id continuous_const)

/-- Every Riccati orbit other than the equilibria runs from `B` to `A`. -/
theorem tendsto_ψR (ha : 0 < a) (p : S1) (hA : (p : ℝ × ℝ) ≠ zA a) (hB : (p : ℝ × ℝ) ≠ zB a) :
    Tendsto (fun s => (ψR a s p : ℝ × ℝ)) atTop (𝓝 (zA a)) ∧
      Tendsto (fun s => (ψR a s p : ℝ × ℝ)) atBot (𝓝 (zB a)) := by
  have hpos : (0 : ℝ) < 1 + a ^ 2 := by positivity
  have ha2 : 0 < a ^ 2 := by positivity
  have hd : ∀ s, HasDerivAt (fun s => (ψR a s p : ℝ × ℝ)) (fieldR a (ψR a s p)) s :=
    hasDerivAt_ψR a p
  have hm : ∀ s, (ψR a s p : ℝ × ℝ).1 ^ 2 + (ψR a s p : ℝ × ℝ).2 ^ 2 = 1 := fun s => (ψR a s p).2
  have hne : ∀ s, kap a (ψR a s p) ≠ 0 := by
    intro s hk
    have e : p = ψR a (-s) (ψR a s p) := by
      rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
    rcases eq_of_kap_eq_zero ha (ψR a s p).2 hk with h | h
    · apply hA
      rw [e, show ψR a s p = ⟨zA a, zA_mem a⟩ from Subtype.ext h, ψR_fixed_A]
    · apply hB
      rw [e, show ψR a s p = ⟨zB a, zB_mem a⟩ from Subtype.ext h, ψR_fixed_B]
  have hkc : Continuous fun s => kap a (ψR a s p) :=
    (by unfold kap; fun_prop : Continuous (kap a)).comp (continuous_ψR_orbit p)
  have hsign : (∀ s, 0 < kap a (ψR a s p)) ∨ (∀ s, kap a (ψR a s p) < 0) := by
    rcases lt_or_gt_of_ne (hne 0) with h0 | h0
    · refine Or.inr fun s => lt_of_not_ge fun hs => ?_
      obtain ⟨r, hr⟩ := intermediate_value_univ 0 s hkc ⟨h0.le, hs⟩
      exact hne r hr
    · refine Or.inl fun s => lt_of_not_ge fun hs => ?_
      obtain ⟨r, hr⟩ := intermediate_value_univ s 0 hkc ⟨hs, h0.le⟩
      exact hne r hr
  rcases hsign with hk | hk
  · have hx : ∀ s, xs a < (ψR a s p : ℝ × ℝ).1 := fun s => by
      have := hk s; unfold kap at this; unfold xs; rw [div_lt_iff₀ hpos]; linarith
    have hxs : -1 < xs a := by unfold xs; rw [lt_div_iff₀ hpos]; linarith
    have h1 : ∀ s, -1 < (ψR a s p : ℝ × ℝ).1 := fun s => hxs.trans (hx s)
    set P : ℝ → ℝ := fun s => (ψR a s p : ℝ × ℝ).2 / (1 + (ψR a s p : ℝ × ℝ).1) with hPdef
    have hPd : ∀ s, HasDerivAt P (-(4 / 3) * (P s ^ 2 - a ^ 2)) s := fun s =>
      hasDerivAt_chartP (hd s) (hm s) (h1 s)
    have hPI : ∀ s, P s ∈ Ioo (-a) a := fun s => by
      have hsq : P s ^ 2 < a ^ 2 := by
        rw [hPdef]; dsimp only
        rw [chartP_sq (hm s) (h1 s), div_lt_iff₀ (by linarith [h1 s])]
        have := hk s; unfold kap at this; linarith
      exact abs_lt.1 (abs_lt_of_sq_lt_sq hsq ha.le)
    obtain ⟨hT, hBt⟩ := tendsto_Ioo_of_deriv (g := fun u => -(4 / 3) * (u ^ 2 - a ^ 2)) hPd
      (by fun_prop) (fun u hu => by have := sq_lt_sq' hu.1 hu.2; nlinarith) hPI
    have hγ : ∀ s, invP (P s) = (ψR a s p : ℝ × ℝ) := fun s => invP_chart (hm s) (h1 s)
    refine ⟨?_, ?_⟩
    · rw [← invP_pos]; exact ((continuous_invP.tendsto a).comp hT).congr hγ
    · rw [← invP_neg]; exact ((continuous_invP.tendsto (-a)).comp hBt).congr hγ
  · have hx : ∀ s, (ψR a s p : ℝ × ℝ).1 < xs a := fun s => by
      have := hk s; unfold kap at this; unfold xs; rw [lt_div_iff₀ hpos]; linarith
    have hxs : xs a < 1 := by unfold xs; rw [div_lt_iff₀ hpos]; linarith
    have h1 : ∀ s, (ψR a s p : ℝ × ℝ).1 < 1 := fun s => (hx s).trans hxs
    set W : ℝ → ℝ := fun s => (ψR a s p : ℝ × ℝ).2 / (1 - (ψR a s p : ℝ × ℝ).1) with hWdef
    have hWd : ∀ s, HasDerivAt W (4 / 3 * (1 - a ^ 2 * W s ^ 2)) s := fun s =>
      hasDerivAt_chartW (hd s) (hm s) (h1 s)
    have hWI : ∀ s, W s ∈ Ioo (-(1 / a)) (1 / a) := fun s => by
      have hsq : W s ^ 2 < (1 / a) ^ 2 := by
        rw [hWdef]; dsimp only
        rw [chartW_sq (hm s) (h1 s), div_lt_iff₀ (by linarith [h1 s]), one_div_pow,
          div_mul_eq_mul_div, one_mul, lt_div_iff₀ ha2]
        have := hk s; unfold kap at this; linarith
      exact abs_lt.1 (abs_lt_of_sq_lt_sq hsq (by positivity))
    obtain ⟨hT, hBt⟩ := tendsto_Ioo_of_deriv (g := fun u => 4 / 3 * (1 - a ^ 2 * u ^ 2)) hWd
      (by fun_prop) (fun u hu => by
        have h := sq_lt_sq' hu.1 hu.2
        rw [one_div_pow, lt_div_iff₀ ha2] at h
        nlinarith) hWI
    have hγ : ∀ s, invW (W s) = (ψR a s p : ℝ × ℝ) := fun s => invW_chart (hm s) (h1 s)
    refine ⟨?_, ?_⟩
    · rw [← invW_pos ha]; exact ((continuous_invW.tendsto _).comp hT).congr hγ
    · rw [← invW_neg ha]; exact ((continuous_invW.tendsto _).comp hBt).congr hγ

theorem tendsto_ψR_atTop (ha : 0 < a) (p : S1) (hB : (p : ℝ × ℝ) ≠ zB a) :
    Tendsto (fun s => (ψR a s p : ℝ × ℝ)) atTop (𝓝 (zA a)) := by
  by_cases hA : (p : ℝ × ℝ) = zA a
  · have hp : p = ⟨zA a, zA_mem a⟩ := Subtype.ext hA
    subst hp
    simp only [ψR_fixed_A]
    exact tendsto_const_nhds
  · exact (tendsto_ψR ha p hA hB).1

theorem tendsto_ψR_atBot (ha : 0 < a) (p : S1) (hA : (p : ℝ × ℝ) ≠ zA a) :
    Tendsto (fun s => (ψR a s p : ℝ × ℝ)) atBot (𝓝 (zB a)) := by
  by_cases hB : (p : ℝ × ℝ) = zB a
  · have hp : p = ⟨zB a, zB_mem a⟩ := Subtype.ext hB
    subst hp
    simp only [ψR_fixed_B]
    exact tendsto_const_nhds
  · exact (tendsto_ψR ha p hA hB).2

/-! ## The circle `ϑ' = -sin ϑ` -/

theorem tendsto_Dt_atTop {τ : ℝ} (h1 : -1 < τ) (h2 : τ ≤ 1) :
    Tendsto (fun t => Dt t τ) atTop atTop := by
  refine tendsto_atTop_mono (fun t => ?_) (Real.tendsto_exp_atTop.const_mul_atTop
    (by linarith : 0 < (1 + τ) / 2))
  rw [Dt_eq]
  have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - τ) (Real.exp_pos (-t)).le
  linarith

theorem tendsto_Dt_atBot {τ : ℝ} (h1 : -1 ≤ τ) (h2 : τ < 1) :
    Tendsto (fun t => Dt t τ) atBot atTop := by
  refine tendsto_atTop_mono (fun t => ?_) ((Real.tendsto_exp_atTop.comp
    tendsto_neg_atBot_atTop).const_mul_atTop (by linarith : 0 < (1 - τ) / 2))
  rw [Dt_eq]
  have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + τ) (Real.exp_pos t).le
  show (1 - τ) / 2 * Real.exp (-t) ≤ _
  linarith

/-- The first coordinate of a point of the circle, as a point of `[-1, 1]`. -/
def toTau (w : S1) : Tau := ⟨(w : ℝ × ℝ).1, fst_mem_Icc_of_S1 w.2⟩

theorem continuous_toTau : Continuous toTau :=
  (continuous_fst.comp continuous_subtype_val).subtype_mk _

theorem circ_mem (w : S1) (t : ℝ) :
    (thetaF t (w : ℝ × ℝ).1, (w : ℝ × ℝ).2 / Dt t (w : ℝ × ℝ).1) ∈ S1 := by
  have h : (w : ℝ × ℝ).1 ^ 2 + (w : ℝ × ℝ).2 ^ 2 = 1 := w.2
  have hD := (Dt_pos (fst_mem_Icc_of_S1 w.2) t).ne'
  show thetaF t (w : ℝ × ℝ).1 ^ 2 + ((w : ℝ × ℝ).2 / Dt t (w : ℝ × ℝ).1) ^ 2 = 1
  rw [thetaF, div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hD), Dt]
  linear_combination ((w : ℝ × ℝ).1 ^ 2 - 1) * Real.cosh_sq_sub_sinh_sq t + h

/-- The flow of `ϑ' = -sin ϑ` on the circle `w = (cos ϑ, sin ϑ)`, with `τ = w₁`. -/
noncomputable def circFlow : Flow ℝ S1 where
  toFun t w := ⟨(thetaF t (w : ℝ × ℝ).1, (w : ℝ × ℝ).2 / Dt t (w : ℝ × ℝ).1), circ_mem w t⟩
  cont' := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · exact continuous_thetaF.comp (continuous_fst.prodMk (continuous_toTau.comp continuous_snd))
    · refine Continuous.div ((continuous_snd.comp continuous_subtype_val).comp continuous_snd) ?_
        fun p => (Dt_pos (fst_mem_Icc_of_S1 p.2.2) p.1).ne'
      exact (Real.continuous_cosh.comp continuous_fst).add
        (((continuous_fst.comp continuous_subtype_val).comp continuous_snd).mul
          (Real.continuous_sinh.comp continuous_fst))
  map_add' t s w := Subtype.ext (Prod.ext (thetaF_add (fst_mem_Icc_of_S1 w.2) t s).symm (by
    show (w : ℝ × ℝ).2 / Dt (t + s) (w : ℝ × ℝ).1 =
      (w : ℝ × ℝ).2 / Dt s (w : ℝ × ℝ).1 / Dt t (thetaF s (w : ℝ × ℝ).1)
    rw [div_div, mul_comm (Dt s _), Dt_mul (fst_mem_Icc_of_S1 w.2)]))
  map_zero' w := Subtype.ext (Prod.ext (by simp [thetaF, Dt]) (by simp [Dt]))

theorem circFlow_coe (t : ℝ) (w : S1) :
    (circFlow t w : ℝ × ℝ) = (thetaF t (w : ℝ × ℝ).1, (w : ℝ × ℝ).2 / Dt t (w : ℝ × ℝ).1) := rfl

/-- `circFlow` is the flow of `ϑ' = -sin ϑ`, i.e. `(cos ϑ)' = sin² ϑ`, `(sin ϑ)' = -cos ϑ sin ϑ`. -/
theorem hasDerivAt_circFlow (w : S1) (t : ℝ) :
    HasDerivAt (fun s => (circFlow s w : ℝ × ℝ))
      (((circFlow t w : ℝ × ℝ).2) ^ 2, -((circFlow t w : ℝ × ℝ).1 * (circFlow t w : ℝ × ℝ).2)) t := by
  have hτ := fst_mem_Icc_of_S1 w.2
  have h : (w : ℝ × ℝ).1 ^ 2 + (w : ℝ × ℝ).2 ^ 2 = 1 := w.2
  have hD := (Dt_pos hτ t).ne'
  have hDd : HasDerivAt (fun s => Dt s (w : ℝ × ℝ).1)
      (Real.sinh t + (w : ℝ × ℝ).1 * Real.cosh t) t :=
    (Real.hasDerivAt_cosh t).add ((Real.hasDerivAt_sinh t).const_mul _)
  have hNd : HasDerivAt (fun s => (w : ℝ × ℝ).1 * Real.cosh s + Real.sinh s)
      ((w : ℝ × ℝ).1 * Real.sinh t + Real.cosh t) t :=
    ((Real.hasDerivAt_cosh t).const_mul _).add (Real.hasDerivAt_sinh t)
  refine (hNd.div hDd hD).prodMk ((hasDerivAt_const t (w : ℝ × ℝ).2).div hDd hD) |>.congr_deriv ?_
  simp only [circFlow_coe, thetaF]
  refine Prod.ext ?_ ?_
  · simp only [Dt] at hD ⊢
    field_simp
    linear_combination (-(1 : ℝ)) * h + (-(w : ℝ × ℝ).1 ^ 2 + 1) * Real.cosh_sq_sub_sinh_sq t
  · simp only [Dt] at hD ⊢
    field_simp
    ring

theorem thetaF_one (t : ℝ) : thetaF t 1 = 1 := by
  have := one_sub_thetaF (τ := 1) (by norm_num) t
  rw [sub_self, zero_mul, zero_div] at this
  linarith

theorem thetaF_neg_one (t : ℝ) : thetaF t (-1) = -1 := by
  have := one_add_thetaF (τ := -1) (by norm_num) t
  rw [add_neg_cancel, zero_mul, zero_div] at this
  linarith

/-- The infrared point `ϑ = 0`, i.e. `τ = 1`. -/
def wI : S1 := ⟨(1, 0), show (1 : ℝ) ^ 2 + 0 ^ 2 = 1 by norm_num⟩

/-- The ultraviolet point `ϑ = π`, i.e. `τ = -1`. -/
def wU : S1 := ⟨(-1, 0), show (-1 : ℝ) ^ 2 + 0 ^ 2 = 1 by norm_num⟩

theorem circFlow_wI (t : ℝ) : circFlow t wI = wI :=
  Subtype.ext (Prod.ext (thetaF_one t) (zero_div _))

theorem circFlow_wU (t : ℝ) : circFlow t wU = wU :=
  Subtype.ext (Prod.ext (thetaF_neg_one t) (zero_div _))

theorem eq_wI {w : S1} (h : (w : ℝ × ℝ).1 = 1) : w = wI := by
  have hw : (w : ℝ × ℝ).1 ^ 2 + (w : ℝ × ℝ).2 ^ 2 = 1 := w.2
  rw [h] at hw
  exact Subtype.ext (Prod.ext h (show (w : ℝ × ℝ).2 = 0 by nlinarith))

theorem eq_wU {w : S1} (h : (w : ℝ × ℝ).1 = -1) : w = wU := by
  have hw : (w : ℝ × ℝ).1 ^ 2 + (w : ℝ × ℝ).2 ^ 2 = 1 := w.2
  rw [h] at hw
  exact Subtype.ext (Prod.ext h (show (w : ℝ × ℝ).2 = 0 by nlinarith))

theorem tendsto_thetaF_atTop {τ : ℝ} (h1 : -1 < τ) (h2 : τ ≤ 1) :
    Tendsto (fun t => thetaF t τ) atTop (𝓝 1) := by
  have hinv := tendsto_inv_atTop_zero.comp (tendsto_Dt_atTop h1 h2)
  have := tendsto_const_nhds (x := (1 : ℝ)).sub
    ((tendsto_const_nhds (x := 1 - τ)).mul Real.tendsto_exp_neg_atTop_nhds_zero |>.mul hinv)
  simp only [mul_zero, sub_zero] at this
  refine this.congr fun t => ?_
  have := one_sub_thetaF ⟨h1.le, h2⟩ t
  simp only [Function.comp_apply]
  rw [← div_eq_mul_inv]
  linarith

theorem tendsto_thetaF_atBot {τ : ℝ} (h1 : -1 ≤ τ) (h2 : τ < 1) :
    Tendsto (fun t => thetaF t τ) atBot (𝓝 (-1)) := by
  have hinv := tendsto_inv_atTop_zero.comp (tendsto_Dt_atBot h1 h2)
  have := tendsto_const_nhds (x := (-1 : ℝ)).add
    ((tendsto_const_nhds (x := 1 + τ)).mul Real.tendsto_exp_atBot |>.mul hinv)
  simp only [mul_zero, add_zero] at this
  refine this.congr fun t => ?_
  have := one_add_thetaF ⟨h1, h2.le⟩ t
  simp only [Function.comp_apply]
  rw [← div_eq_mul_inv]
  linarith

theorem tendsto_circFlow_atTop (w : S1) (h : -1 < (w : ℝ × ℝ).1) :
    Tendsto (fun t => circFlow t w) atTop (𝓝 wI) := by
  have hτ := fst_mem_Icc_of_S1 w.2
  have hinv := tendsto_inv_atTop_zero.comp (tendsto_Dt_atTop h hτ.2)
  refine tendsto_subtype_rng.2 (Tendsto.prodMk_nhds (tendsto_thetaF_atTop h hτ.2) ?_)
  have := (tendsto_const_nhds (x := (w : ℝ × ℝ).2)).mul hinv
  rw [mul_zero] at this
  exact this.congr fun t => by simp only [Function.comp_apply, div_eq_mul_inv]

theorem tendsto_circFlow_atBot (w : S1) (h : (w : ℝ × ℝ).1 < 1) :
    Tendsto (fun t => circFlow t w) atBot (𝓝 wU) := by
  have hτ := fst_mem_Icc_of_S1 w.2
  have hinv := tendsto_inv_atTop_zero.comp (tendsto_Dt_atBot hτ.1 h)
  refine tendsto_subtype_rng.2 (Tendsto.prodMk_nhds (tendsto_thetaF_atBot hτ.1 h) ?_)
  have := (tendsto_const_nhds (x := (w : ℝ × ℝ).2)).mul hinv
  rw [mul_zero] at this
  exact this.congr fun t => by simp only [Function.comp_apply, div_eq_mul_inv]

/-! ## The torus flow -/

variable (a) in
/-- The reduced doubled flow on the torus `ℝP¹ × S¹`. -/
noncomputable def torusFlow : Flow ℝ (S1 × S1) where
  toFun t p := (ψR a (sigma t (p.2 : ℝ × ℝ).1) p.1, circFlow t p.2)
  cont' := by
    refine Continuous.prodMk ?_ ?_
    · exact (ψR a).continuous (continuous_sigma.comp (continuous_fst.prodMk
        (continuous_toTau.comp (continuous_snd.comp continuous_snd))))
        (continuous_fst.comp continuous_snd)
    · exact circFlow.continuous continuous_fst (continuous_snd.comp continuous_snd)
  map_add' t s p := Prod.ext (by
      show ψR a (sigma (t + s) (p.2 : ℝ × ℝ).1) p.1 =
        ψR a (sigma t (thetaF s (p.2 : ℝ × ℝ).1)) (ψR a (sigma s (p.2 : ℝ × ℝ).1) p.1)
      rw [sigma_add (fst_mem_Icc_of_S1 p.2.2), Flow.map_add]) (circFlow.map_add t s p.2)
  map_zero' p := Prod.ext (by
      show ψR a (sigma 0 (p.2 : ℝ × ℝ).1) p.1 = p.1
      rw [sigma_zero, Flow.map_zero_apply]) (circFlow.map_zero_apply p.2)

theorem torusFlow_apply (t : ℝ) (p : S1 × S1) :
    torusFlow a t p = (ψR a (sigma t (p.2 : ℝ × ℝ).1) p.1, circFlow t p.2) := rfl

/-- `torusFlow` is the flow of the reduced doubled system: `z' = cos ϑ · fieldR(z)` in the
fiber, i.e. `π̄' = -(4/3)(π̄² - a²) cos ϑ` in the chart `π̄`, and `ϑ' = -sin ϑ`. -/
theorem hasDerivAt_torusFlow_fst (p : S1 × S1) (t : ℝ) :
    HasDerivAt (fun s => ((torusFlow a s p).1 : ℝ × ℝ))
      (((torusFlow a t p).2 : ℝ × ℝ).1 • fieldR a ((torusFlow a t p).1 : ℝ × ℝ)) t :=
  (hasDerivAt_ψR a p.1 _).scomp t (hasDerivAt_sigma (fst_mem_Icc_of_S1 p.2.2) t)

variable (a) in
/-- The two fiber points as points of `S1`. -/
noncomputable def zAp : S1 := ⟨zA a, zA_mem a⟩

variable (a) in
noncomputable def zBp : S1 := ⟨zB a, zB_mem a⟩

variable (a) in
/-- The four equilibria `Σ_I(A), Σ_I(B), Σ_U(B), Σ_U(A)`, of Morse indices `0, 1, 1, 2`. -/
noncomputable def tpts : Fin 4 → S1 × S1 := ![(zAp a, wI), (zBp a, wI), (zBp a, wU), (zAp a, wU)]

theorem torusFlow_tpts (i : Fin 4) (t : ℝ) : torusFlow a t (tpts a i) = tpts a i := by
  fin_cases i <;>
  simp [tpts, torusFlow_apply, zAp, zBp, ψR_fixed_A, ψR_fixed_B, circFlow_wI, circFlow_wU]

theorem tpts_injective (ha : 0 < a) : Function.Injective (tpts a) := by
  have hAB : zAp a ≠ zBp a := fun h => zA_ne_zB ha (congrArg Subtype.val h)
  have hIU : wI ≠ wU := fun h => by
    have := congrArg (fun w : S1 => (w : ℝ × ℝ).1) h
    norm_num [wI, wU] at this
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [tpts, Prod.ext_iff, eq_comm]

theorem tendsto_ψR_top_ite (ha : 0 < a) (z : S1) :
    Tendsto (fun s => ψR a s z) atTop
      (𝓝 (if (z : ℝ × ℝ) = zB a then zBp a else zAp a)) := by
  split_ifs with h
  · have : z = zBp a := Subtype.ext h
    subst this
    simp only [zBp, ψR_fixed_B]
    exact tendsto_const_nhds
  · exact tendsto_subtype_rng.2 (tendsto_ψR_atTop ha z h)

/-- Every orbit of the torus that is not an equilibrium runs from `tpts j` to `tpts i` with
`i < j`. Off the fixed circles `ϑ = 0, π` it runs from `Σ_U(A)` to `Σ_I(A)` or along the
separatrix from `Σ_U(B)` to `Σ_I(B)`. On `ϑ = π` it runs from `Σ_U(A)` to `Σ_U(B)`, and on
`ϑ = 0` from `Σ_I(B)` to `Σ_I(A)`. -/
theorem torus_connect (ha : 0 < a) (p : S1 × S1) (hp : ∀ i, p ≠ tpts a i) :
    ∃ i j, i < j ∧ Tendsto (fun t => torusFlow a t p) atTop (𝓝 (tpts a i)) ∧
      Tendsto (fun t => torusFlow a t p) atBot (𝓝 (tpts a j)) := by
  obtain ⟨z, w⟩ := p
  obtain ⟨hw1, hw2⟩ := fst_mem_Icc_of_S1 w.2
  have hz := tendsto_ψR_top_ite ha z
  rcases hw2.lt_or_eq with hw2 | hw2
  · rcases hw1.lt_or_eq with hw1 | hw1
    · have hT : Tendsto (fun t => torusFlow a t (z, w)) atTop
          (𝓝 (if (z : ℝ × ℝ) = zB a then zBp a else zAp a, wI)) :=
        (hz.comp (tendsto_sigma_atTop hw1 hw2.le)).prodMk_nhds (tendsto_circFlow_atTop w hw1)
      have hB : Tendsto (fun t => torusFlow a t (z, w)) atBot
          (𝓝 (if (z : ℝ × ℝ) = zB a then zBp a else zAp a, wU)) :=
        (hz.comp (tendsto_sigma_atBot hw1.le hw2)).prodMk_nhds (tendsto_circFlow_atBot w hw2)
      by_cases hzB : (z : ℝ × ℝ) = zB a
      · simp only [hzB, ↓reduceIte] at hT hB
        exact ⟨1, 2, by decide, hT, hB⟩
      · simp only [hzB, ↓reduceIte] at hT hB
        exact ⟨0, 3, by decide, hT, hB⟩
    · have hw : w = wU := eq_wU hw1.symm
      subst hw
      have hA : (z : ℝ × ℝ) ≠ zA a := fun h => hp 3 (by
        rw [show z = zAp a from Subtype.ext h]; rfl)
      have hB : (z : ℝ × ℝ) ≠ zB a := fun h => hp 2 (by
        rw [show z = zBp a from Subtype.ext h]; rfl)
      have e : (fun t => torusFlow a t (z, wU)) = fun t => (ψR a (-t) z, wU) := funext fun t =>
        Prod.ext (by show ψR a (sigma t (-1)) z = _; rw [sigma_neg_one]) (circFlow_wU t)
      obtain ⟨h1, h2⟩ := tendsto_ψR ha z hA hB
      refine ⟨2, 3, by decide, ?_, ?_⟩ <;> rw [e]
      · exact (tendsto_subtype_rng.2 (h2.comp tendsto_neg_atTop_atBot)).prodMk_nhds
          tendsto_const_nhds
      · exact (tendsto_subtype_rng.2 (h1.comp tendsto_neg_atBot_atTop)).prodMk_nhds
          tendsto_const_nhds
  · have hw : w = wI := eq_wI hw2
    subst hw
    have hA : (z : ℝ × ℝ) ≠ zA a := fun h => hp 0 (by
      rw [show z = zAp a from Subtype.ext h]; rfl)
    have hB : (z : ℝ × ℝ) ≠ zB a := fun h => hp 1 (by
      rw [show z = zBp a from Subtype.ext h]; rfl)
    have e : (fun t => torusFlow a t (z, wI)) = fun t => (ψR a t z, wI) := funext fun t =>
      Prod.ext (by show ψR a (sigma t 1) z = _; rw [sigma_one]) (circFlow_wI t)
    obtain ⟨h1, h2⟩ := tendsto_ψR ha z hA hB
    refine ⟨0, 1, by decide, ?_, ?_⟩ <;> rw [e]
    · exact (tendsto_subtype_rng.2 h1).prodMk_nhds tendsto_const_nhds
    · exact (tendsto_subtype_rng.2 h2).prodMk_nhds tendsto_const_nhds

/-! ## Gradient-like flows with finitely many equilibria -/

section Gradient

variable {X : Type*} [MetricSpace X] {n : ℕ} {ϕ : Flow ℝ X} {q : Fin n → X}

theorem eq_of_tendsto_omegaLim {x p z : X} (hp : Tendsto (fun t => ϕ t x) atTop (𝓝 p))
    (hz : z ∈ omegaLim ϕ x) : z = p := by
  have hc := (mem_omegaLimit_singleton_iff_mapClusterPt (f := atTop) (ϕ := ϕ.toFun) x z).1 hz
  exact eq_of_nhds_neBot (hc.clusterPt.mono hp)

theorem eq_of_tendsto_alphaLim {x p z : X} (hp : Tendsto (fun t => ϕ t x) atBot (𝓝 p))
    (hz : z ∈ alphaLim ϕ x) : z = p := by
  have hc := (mem_omegaLimit_singleton_iff_mapClusterPt (f := atBot) (ϕ := ϕ.toFun) x z).1 hz
  exact eq_of_nhds_neBot (hc.clusterPt.mono hp)

variable [CompactSpace X]

open Metric in
/-- If every orbit other than the equilibria `q i` runs from some `q j` to some `q i` with
`i < j`, then each `{q i}` is an isolated invariant set. -/
theorem isIsolated_of_connect (hq : Function.Injective q) (hfix : ∀ i t, ϕ t (q i) = q i)
    (hcon : ∀ x, (∀ i, x ≠ q i) → ∃ i j, i < j ∧ Tendsto (fun t => ϕ t x) atTop (𝓝 (q i)) ∧
      Tendsto (fun t => ϕ t x) atBot (𝓝 (q j))) (k : Fin n) :
    IsIsolatedInvariantSet ϕ {q k} := by
  obtain ⟨r, hr0, hr⟩ : ∃ r > 0, ∀ i, i ≠ k → r < dist (q i) (q k) := by
    have : ∀ i, ∀ᶠ r in 𝓝[>] (0 : ℝ), i ≠ k → r < dist (q i) (q k) := fun i => by
      by_cases hik : i = k
      · exact Eventually.of_forall fun _ h => absurd hik h
      · exact nhdsWithin_le_nhds ((eventually_lt_nhds (dist_pos.2 (hq.ne hik))).mono
          fun _ h _ => h)
    obtain ⟨r, hr, hr0⟩ := ((Filter.eventually_all.2 this).and self_mem_nhdsWithin).exists
    exact ⟨r, hr0, hr⟩
  have heq : ∀ i, q i ∈ closedBall (q k) r → i = k := fun i hi => by
    by_contra h
    exact absurd (mem_closedBall.1 hi) (not_le.2 (hr i h))
  have hInv : Inv ϕ (closedBall (q k) r) = {q k} := by
    ext x
    constructor
    · intro hx
      have hx0 : x ∈ closedBall (q k) r := by
        have := hx 0
        rwa [Flow.map_zero_apply] at this
      by_cases hxq : ∃ i, x = q i
      · obtain ⟨i, rfl⟩ := hxq
        rw [heq i hx0]
        rfl
      · push Not at hxq
        obtain ⟨i, j, hij, hi, hj⟩ := hcon x hxq
        have hi' := heq i (isClosed_closedBall.mem_of_tendsto hi
          (Eventually.of_forall fun t => hx t))
        have hj' := heq j (isClosed_closedBall.mem_of_tendsto hj
          (Eventually.of_forall fun t => hx t))
        exact absurd hij (by rw [hi', hj']; exact lt_irrefl k)
    · rintro rfl t
      rw [hfix]
      exact mem_closedBall_self hr0.le
  refine ⟨closedBall (q k) r, ⟨isClosed_closedBall.isCompact, ?_⟩, hInv⟩
  rw [hInv]
  exact singleton_subset_iff.2 (mem_interior_iff_mem_nhds.2 (closedBall_mem_nhds _ hr0))

theorem isIsolated_univ : IsIsolatedInvariantSet ϕ univ :=
  ⟨univ, ⟨isCompact_univ, by rw [interior_univ]; exact subset_univ _⟩,
    eq_univ_of_forall fun _ _ => mem_univ _⟩

theorem isMorseDecomp_of_connect (hq : Function.Injective q) (hfix : ∀ i t, ϕ t (q i) = q i)
    (hcon : ∀ x, (∀ i, x ≠ q i) → ∃ i j, i < j ∧ Tendsto (fun t => ϕ t x) atTop (𝓝 (q i)) ∧
      Tendsto (fun t => ϕ t x) atBot (𝓝 (q j))) :
    IsMorseDecomp ϕ univ (fun i => {q i}) (· < ·) where
  isolated := isIsolated_univ
  isolated_M := isIsolated_of_connect hq hfix hcon
  subset _ := subset_univ _
  disjoint i j hij := disjoint_singleton.2 fun h => hij (hq h)
  irrefl := lt_irrefl
  trans _ _ _ := lt_trans
  connecting x _ hM := by
    obtain ⟨i, j, hij, hi, hj⟩ := hcon x fun i h => hM i h
    exact ⟨i, j, hij, fun z hz => eq_of_tendsto_omegaLim hi hz,
      fun z hz => eq_of_tendsto_alphaLim hj hz⟩

theorem isBlock_univ (ϕ : Flow ℝ X) : IsBlock ϕ (univ : Set X) ∅ :=
  ⟨isCompact_univ, isClosed_empty, empty_subset _, fun _ h => h.elim,
    fun x _ hx => absurd (by rw [interior_univ]; exact mem_univ x) hx⟩

end Gradient

theorem isDeformCollared_univ_empty {X : Type*} [TopologicalSpace X] :
    IsDeformCollared (univ : Set X) ∅ :=
  ⟨∅, ∅, ⟨fun p => p.2, continuous_snd⟩, isOpen_empty, subset_refl _, by simp, empty_subset _,
    fun _ => rfl, fun _ _ h => h.elim, fun _ _ h => h.elim, fun _ h => h.elim⟩

/-- On a compact space the whole space is isolated with empty exit set, so its homology index is
the singular homology of the space. -/
theorem homologyIndex_univ {X : Type} [MetricSpace X] [CompactSpace X] (K : Type) [Ring K]
    (ϕ : Flow ℝ X) (n : ℕ) :
    Nonempty (homologyIndex K ϕ (isIsolated_univ (ϕ := ϕ)) n ≃ₗ[K]
      singH K X (Int.ofNat n) univ ∅) := by
  have hI : Inv ϕ (univ : Set X) = univ := eq_univ_of_forall fun _ _ => mem_univ _
  have hP := (isBlock_univ ϕ).isIndexPair
  rw [hI] at hP
  exact homologyIndex_equiv_of_deformCollared K _ hP isDeformCollared_univ_empty n

/-- A complex `Δ` on `Kⁿ` whose homology has dimension `n` vanishes. -/
theorem eq_zero_of_finrank_homology {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι K) (h : Module.finrank K (LinearMap.ker (Matrix.toLin' D)) =
      Module.finrank K (LinearMap.range (Matrix.toLin' D)) + Fintype.card ι) : D = 0 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' D)
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have h0 : Module.finrank K (LinearMap.range (Matrix.toLin' D)) = 0 := by
    have := Submodule.finrank_le (LinearMap.ker (Matrix.toLin' D))
    rw [Module.finrank_fintype_fun_eq_card] at this
    omega
  have : LinearMap.range (Matrix.toLin' D) = ⊥ := Submodule.finrank_eq_zero.1 h0
  exact Matrix.toLin'.map_eq_zero_iff.1 (LinearMap.range_eq_bot.1 this)

/-! ## Proposition `prop:torus` -/

/-- Proposition `prop:torus`(i), equilibria: the torus flow has exactly the four equilibria
`Σ_I(A), Σ_I(B), Σ_U(B), Σ_U(A)`. -/
theorem prop_torus_equilibria (ha : 0 < a) (p : S1 × S1) :
    (∀ t, torusFlow a t p = p) ↔ ∃ i, p = tpts a i := by
  refine ⟨fun hp => ?_, fun ⟨i, hi⟩ t => hi ▸ torusFlow_tpts i t⟩
  by_contra h
  push Not at h
  obtain ⟨i, -, -, hT, -⟩ := torus_connect ha p h
  have : Tendsto (fun t => torusFlow a t p) atTop (𝓝 p) := by
    simp only [hp]
    exact tendsto_const_nhds
  exact h i (tendsto_nhds_unique this hT)

/-- Proposition `prop:torus`(i): for every `a > 0` the four equilibria, ordered as
`Σ_I(A) < Σ_I(B) < Σ_U(B) < Σ_U(A)`, form a Morse decomposition of the torus. -/
theorem prop_torus_i (ha : 0 < a) :
    IsMorseDecomp (torusFlow a) univ (fun i => {tpts a i}) (· < ·) :=
  isMorseDecomp_of_connect (tpts_injective ha) (fun i t => torusFlow_tpts i t) (torus_connect ha)

theorem chartP_zA (a : ℝ) : (zA a).2 / (1 + (zA a).1) = a := by
  have : (1 : ℝ) + a ^ 2 ≠ 0 := by positivity
  simp only [zA, xs, ys]
  field_simp
  ring

theorem chartP_zB (a : ℝ) : (zB a).2 / (1 + (zB a).1) = -a := by
  have : (1 : ℝ) + a ^ 2 ≠ 0 := by positivity
  simp only [zB, xs, ys]
  field_simp
  ring

/-- In the chart `π̄ = z₂ / (1 + z₁)` the torus flow is the reduced doubled system
`π̄' = -(4/3)(π̄² - a²) cos ϑ`. -/
theorem hasDerivAt_torus_chartP (p : S1 × S1) (t : ℝ)
    (h1 : -1 < ((torusFlow a t p).1 : ℝ × ℝ).1) :
    HasDerivAt (fun r => ((torusFlow a r p).1 : ℝ × ℝ).2 / (1 + ((torusFlow a r p).1 : ℝ × ℝ).1))
      (-(4 / 3) * ((((torusFlow a t p).1 : ℝ × ℝ).2 / (1 + ((torusFlow a t p).1 : ℝ × ℝ).1)) ^ 2
        - a ^ 2) * ((torusFlow a t p).2 : ℝ × ℝ).1) t := by
  have hτ := fst_mem_Icc_of_S1 p.2.2
  have h := (hasDerivAt_chartP (a := a) (hasDerivAt_ψR a p.1 (sigma t (p.2 : ℝ × ℝ).1))
    (ψR a _ p.1).2 h1).comp t (hasDerivAt_sigma hτ t)
  exact h

/-- In the chart `w = z₂ / (1 - z₁) = 1/π̄` the torus flow is `w' = (4/3)(1 - a² w²) cos ϑ`, so
the Riccati equation extends smoothly to `π̄ = ∞`. -/
theorem hasDerivAt_torus_chartW (p : S1 × S1) (t : ℝ)
    (h1 : ((torusFlow a t p).1 : ℝ × ℝ).1 < 1) :
    HasDerivAt (fun r => ((torusFlow a r p).1 : ℝ × ℝ).2 / (1 - ((torusFlow a r p).1 : ℝ × ℝ).1))
      (4 / 3 * (1 - a ^ 2 * (((torusFlow a t p).1 : ℝ × ℝ).2 /
        (1 - ((torusFlow a t p).1 : ℝ × ℝ).1)) ^ 2) * ((torusFlow a t p).2 : ℝ × ℝ).1) t := by
  have hτ := fst_mem_Icc_of_S1 p.2.2
  have h := (hasDerivAt_chartW (a := a) (hasDerivAt_ψR a p.1 (sigma t (p.2 : ℝ × ℝ).1))
    (ψR a _ p.1).2 h1).comp t (hasDerivAt_sigma hτ t)
  exact h

variable (a) in
/-- The reduced doubled field `(π̄, ϑ) ↦ (-(4/3)(π̄² - a²) cos ϑ, -sin ϑ)`. -/
noncomputable def chartField (x : ℝ × ℝ) : ℝ × ℝ :=
  (-(4 / 3) * (x.1 ^ 2 - a ^ 2) * Real.cos x.2, -Real.sin x.2)

/-- Hyperbolicity: at an equilibrium `π̄ = ±a`, `sin ϑ = 0`, the linearization is
`diag(-(8/3) π̄ cos ϑ, -cos ϑ)`. With `cos ϑ = 1` at `Σ_I` and `cos ϑ = -1` at `Σ_U`, the
number of positive eigenvalues is `0, 1, 1, 2` at `Σ_I(A), Σ_I(B), Σ_U(B), Σ_U(A)`. -/
theorem hasFDerivAt_chartField {x : ℝ × ℝ} (h1 : x.1 ^ 2 = a ^ 2) (h2 : Real.sin x.2 = 0) :
    HasFDerivAt (chartField a)
      (((-(8 / 3) * x.1 * Real.cos x.2) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        ((-Real.cos x.2) • ContinuousLinearMap.snd ℝ ℝ ℝ)) x := by
  have hf : HasFDerivAt (fun y : ℝ × ℝ => y.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) x :=
    hasFDerivAt_fst
  have hs : HasFDerivAt (fun y : ℝ × ℝ => y.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    hasFDerivAt_snd
  have hc := (Real.hasDerivAt_cos x.2).comp_hasFDerivAt x hs
  have hsn := (Real.hasDerivAt_sin x.2).comp_hasFDerivAt x hs
  have h1' := (((hf.pow 2).sub_const (a ^ 2)).const_mul (-(4 / 3))).mul hc
  refine (h1'.prodMk hsn.neg).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp [h1, h2]
  ring

/-- Proposition `prop:torus`(ii): `CH_*(T²) ≅ H_*(T²)`, the whole torus being isolated with
empty exit set. -/
theorem prop_torus_ii (K : Type) [Ring K] (n : ℕ) :
    Nonempty (homologyIndex K (torusFlow a) (isIsolated_univ (ϕ := torusFlow a)) n ≃ₗ[K]
      singH K (S1 × S1) (Int.ofNat n) univ ∅) :=
  homologyIndex_univ K (torusFlow a) n

/-! ### The one-sided extension `ℝP¹ × [-1, 1]` -/

variable (a) in
/-- The reduced flow on the compactified extended phase space `ℝP¹ × [-1, 1]`. -/
noncomputable def skewFlow : Flow ℝ (S1 × Tau) where
  toFun t p := (ψR a (sigma t (p.2 : ℝ)) p.1, baseFlow t p.2)
  cont' := by
    refine Continuous.prodMk ?_ ?_
    · exact (ψR a).continuous (continuous_sigma.comp (continuous_fst.prodMk
        (continuous_snd.comp continuous_snd))) (continuous_fst.comp continuous_snd)
    · exact baseFlow.continuous continuous_fst (continuous_snd.comp continuous_snd)
  map_add' t s p := Prod.ext (by
      show ψR a (sigma (t + s) (p.2 : ℝ)) p.1 =
        ψR a (sigma t (thetaF s (p.2 : ℝ))) (ψR a (sigma s (p.2 : ℝ)) p.1)
      rw [sigma_add p.2.2, Flow.map_add]) (baseFlow.map_add t s p.2)
  map_zero' p := Prod.ext (by
      show ψR a (sigma 0 (p.2 : ℝ)) p.1 = p.1
      rw [sigma_zero, Flow.map_zero_apply]) (baseFlow.map_zero_apply p.2)

theorem isSkew_skewFlow : IsSkew (skewFlow a) baseFlow := fun _ _ => rfl

theorem isUniformBlock_univ : IsUniformBlock (skewFlow a) univ ∅ :=
  ⟨isCompact_univ, isClosed_empty, empty_subset _, fun _ h => h.elim,
    fun x _ hx => absurd (by rw [interior_univ]; exact mem_univ x) hx⟩

/-- Proposition `prop:torus`(iii): Theorem `thm:rate` with `N = ℝP¹` gives `CH_* = 0` for the
one-sided extension and an isomorphism `Ψ : CH_*(K₋) → CH_*(K₊)`. -/
theorem prop_torus_iii (K : Type) [Ring K] :
    ∃ (hSn : IsIsolatedInvariantSet (dblΦ (isSkew_skewFlow (a := a)) isHeight_baseFlow)
        (snat (Inv (skewFlow a) (univ ×ˢ univ))))
      (hKp : IsIsolatedInvariantSet
        (fiberFlow (isSkew_skewFlow (a := a)) Tau.top (base_top isHeight_baseFlow))
        {x | (x, Tau.top) ∈ Inv (skewFlow a) (univ ×ˢ univ)})
      (hKm : IsIsolatedInvariantSet
        (fiberFlow (isSkew_skewFlow (a := a)) Tau.bot (base_bot isHeight_baseFlow))
        {x | (x, Tau.bot) ∈ Inv (skewFlow a) (univ ×ˢ univ)})
      (Ψ : ∀ k, homologyIndex K _ hKm k →ₗ[K] homologyIndex K _ hKp k),
      (∀ k, Subsingleton (homologyIndex K _ hSn k)) ∧ ∀ k, Function.Bijective (Ψ k) := by
  obtain ⟨hSn, hKp, hKm, Ψ, -, -, -, -, -, hz, hb⟩ :=
    rate_transport isSkew_skewFlow isHeight_baseFlow K (isUniformBlock_univ (a := a))
  exact ⟨hSn, hKp, hKm, Ψ, hz, hb⟩

theorem baseFlow_top (t : ℝ) : baseFlow t Tau.top = Tau.top := Subtype.ext (thetaF_one t)

theorem baseFlow_bot (t : ℝ) : baseFlow t Tau.bot = Tau.bot := Subtype.ext (thetaF_neg_one t)

/-- Proposition `prop:torus`(iii), the heteroclinic orbits realizing the connection matrix:
`Σ_U(A) → Σ_U(B)` in the fiber `τ = -1`, `Σ_U(B) → Σ_I(B)` along the separatrix `π̄ = -a`, and
`Σ_I(B) → Σ_I(A)` in the fiber `τ = 1`. -/
theorem prop_torus_iii_chains (ha : 0 < a) :
    (∀ z : S1, (z : ℝ × ℝ) ≠ zA a → (z : ℝ × ℝ) ≠ zB a →
      Tendsto (fun t => skewFlow a t (z, Tau.bot)) atTop (𝓝 (zBp a, Tau.bot)) ∧
      Tendsto (fun t => skewFlow a t (z, Tau.bot)) atBot (𝓝 (zAp a, Tau.bot))) ∧
    (∀ τ : Tau, -1 < (τ : ℝ) → (τ : ℝ) < 1 →
      Tendsto (fun t => skewFlow a t (zBp a, τ)) atTop (𝓝 (zBp a, Tau.top)) ∧
      Tendsto (fun t => skewFlow a t (zBp a, τ)) atBot (𝓝 (zBp a, Tau.bot))) ∧
    (∀ z : S1, (z : ℝ × ℝ) ≠ zA a → (z : ℝ × ℝ) ≠ zB a →
      Tendsto (fun t => skewFlow a t (z, Tau.top)) atTop (𝓝 (zAp a, Tau.top)) ∧
      Tendsto (fun t => skewFlow a t (z, Tau.top)) atBot (𝓝 (zBp a, Tau.top))) := by
  refine ⟨fun z hA hB => ?_, fun τ h1 h2 => ?_, fun z hA hB => ?_⟩
  · have e : (fun t => skewFlow a t (z, Tau.bot)) = fun t => (ψR a (-t) z, Tau.bot) :=
      funext fun t => Prod.ext (by show ψR a (sigma t (-1)) z = _; rw [sigma_neg_one])
        (baseFlow_bot t)
    obtain ⟨h1, h2⟩ := tendsto_ψR ha z hA hB
    rw [e]
    exact ⟨(tendsto_subtype_rng.2 (h2.comp tendsto_neg_atTop_atBot)).prodMk_nhds
      tendsto_const_nhds, (tendsto_subtype_rng.2 (h1.comp tendsto_neg_atBot_atTop)).prodMk_nhds
      tendsto_const_nhds⟩
  · have e : (fun t => skewFlow a t (zBp a, τ)) = fun t => (zBp a, baseFlow t τ) :=
      funext fun t => Prod.ext (by simp only [zBp]; exact ψR_fixed_B _) rfl
    rw [e]
    exact ⟨tendsto_const_nhds.prodMk_nhds (tendsto_subtype_rng.2 (tendsto_thetaF_atTop h1 τ.2.2)),
      tendsto_const_nhds.prodMk_nhds (tendsto_subtype_rng.2 (tendsto_thetaF_atBot τ.2.1 h2))⟩
  · have e : (fun t => skewFlow a t (z, Tau.top)) = fun t => (ψR a t z, Tau.top) :=
      funext fun t => Prod.ext (by show ψR a (sigma t 1) z = _; rw [sigma_one]) (baseFlow_top t)
    obtain ⟨h1, h2⟩ := tendsto_ψR ha z hA hB
    rw [e]
    exact ⟨(tendsto_subtype_rng.2 h1).prodMk_nhds tendsto_const_nhds,
      (tendsto_subtype_rng.2 h2).prodMk_nhds tendsto_const_nhds⟩

end ConleyCheck.Gubser
