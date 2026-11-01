import ConleyCheck.Palmer.Planar
import ConleyCheck.Palmer.Scalar
import ConleyCheck.Gubser.Separatrix

/-!
# Proposition `prop:transversal`: the separatrix is transversal

Along `γ_B` the linearization in `(δT, δπ)` is `A(t) = τ(t) A₁ + A₂` with
`A₁ = diag(-k, 8a/3)`, `k = (2 + a)/3`, `A₂ δT = (0, (a/c) δT)` and `τ(t) = θ_t b → ±1`. The limits
`±A₁ + A₂` are lower-triangular with one positive eigenvalue each, so `L` has index `1 - 1 = 0`
by Palmer's theorem. Together with `ker L = 0` (`prop_transversal`) this shows that the connection
is transversal and that `L : C¹_b → C⁰_b` is invertible (`prop_transversal_palmer`).

In the reduced system `T = 0` the linearization is `δπ' = (8a/3) τ δπ`, with limits `∓8a/3`, so
`L` has index `0 - 1 = -1` (`reduced_index`).
-/

namespace ConleyCheck.Gubser.Sep

open Set Filter Topology Matrix BoundedContinuousFunction ConleyCheck.Conley ConleyCheck.Palmer

/-- `diag(-k, 8a/3)`. -/
noncomputable def linB₁ : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  matCLM !![-((2 + a) / 3), 0; 0, 8 * a / 3]

/-- `δT ↦ (0, (a/c) δT)`. -/
noncomputable def linB₂ (c : ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := matCLM !![0, 0; a / c, 0]

/-- The linearization along `γ_B`: `δT' = -k τ δT`, `δπ' = (8a/3) τ δπ + (a/c) δT`. -/
noncomputable def linB (c : ℝ) (τ : ℝ → ℝ) (t : ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  τ t • linB₁ + linB₂ c

variable {c : ℝ} {τ : ℝ → ℝ}

theorem linB_apply_zero (t : ℝ) (v : Fin 2 → ℝ) :
    linB c τ t v 0 = -((2 + a) / 3) * τ t * v 0 := by
  simp [linB, linB₁, linB₂, dotProduct, Fin.sum_univ_two]; ring

theorem linB_apply_one (t : ℝ) (v : Fin 2 → ℝ) :
    linB c τ t v 1 = 8 * a / 3 * τ t * v 1 + a / c * v 0 := by
  simp [linB, linB₁, linB₂, dotProduct, Fin.sum_univ_two]; ring

theorem smul_add_linB (s : ℝ) :
    s • linB₁ + linB₂ c = matCLM !![-((2 + a) / 3) * s, 0; a / c, 8 * a / 3 * s] := by
  ext v i
  fin_cases i <;> simp [linB₁, linB₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem exists_dichotomy_linB {s : ℝ} (hs : s ≠ 0) :
    ∃ d : Dichotomy (s • linB₁ + linB₂ c), d.μ = 1 := by
  have ha := a_pos
  have hk : 0 < (2 + a) / 3 := by positivity
  have hpq : -((2 + a) / 3) * s ≠ 8 * a / 3 * s := fun h => by
    have : s * ((2 + a) / 3 + 8 * a / 3) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · exact hs h1
    · linarith
  rw [smul_add_linB]
  obtain ⟨d, hd⟩ := exists_dichotomy_tri (Or.inl hpq) (mul_ne_zero (by linarith) hs)
    (mul_ne_zero (by positivity) hs)
  refine ⟨d, hd.trans ?_⟩
  rcases hs.lt_or_gt with h | h
  · have h1 : 0 < -((2 + a) / 3) * s := by nlinarith
    have h2 : ¬ 0 < 8 * a / 3 * s := by nlinarith
    simp only [h1, h2, ↓reduceIte]
  · have h1 : ¬ 0 < -((2 + a) / 3) * s := by nlinarith
    have h2 : 0 < 8 * a / 3 * s := by nlinarith
    simp only [h1, h2, ↓reduceIte]

theorem continuous_linB (c : ℝ) (hτ : Continuous τ) : Continuous (linB c τ) :=
  (hτ.smul continuous_const).add continuous_const

theorem tendsto_linB {l : Filter ℝ} {s : ℝ} (hτ : Tendsto τ l (𝓝 s)) :
    Tendsto (linB c τ) l (𝓝 (s • linB₁ + linB₂ c)) :=
  (hτ.smul_const _).add_const _

variable {θ : Flow ℝ Tau}

theorem continuous_base_orbit (b : Tau) : Continuous fun t => (θ t b : ℝ) :=
  continuous_subtype_val.comp (θ.continuous continuous_id continuous_const)

theorem tendsto_base_top (hθ : IsHeight θ (fun b => (b : ℝ))) {b : Tau} (hb : -1 < (b : ℝ)) :
    Tendsto (fun t => (θ t b : ℝ)) atTop (𝓝 1) :=
  Metric.tendsto_nhds.2 fun ε hε => by
    obtain ⟨T, hT⟩ := base_tendsto_top hθ hb hε
    refine eventually_atTop.2 ⟨T, fun t ht => ?_⟩
    have h1 := hT t ht
    have h2 := (θ t b).2.2
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith

theorem tendsto_base_bot (hθ : IsHeight θ (fun b => (b : ℝ))) {b : Tau} (hb : (b : ℝ) < 1) :
    Tendsto (fun t => (θ t b : ℝ)) atBot (𝓝 (-1)) :=
  Metric.tendsto_nhds.2 fun ε hε => by
    obtain ⟨T, hT⟩ := base_tendsto_bot hθ hb hε
    refine eventually_atBot.2 ⟨T, fun t ht => ?_⟩
    have h1 := hT t ht
    have h2 := (θ t b).2.1
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith

theorem exists_bound_linB (c : ℝ) (hθ : IsHeight θ (fun b => (b : ℝ))) {b : Tau}
    (hb1 : -1 < (b : ℝ)) (hb2 : (b : ℝ) < 1) :
    ∃ M, ∀ t, ‖linB c (fun t => (θ t b : ℝ)) t‖ ≤ M :=
  exists_bound_of_tendsto (continuous_linB c (continuous_base_orbit b))
    (tendsto_linB (tendsto_base_bot hθ hb2)) (tendsto_linB (tendsto_base_top hθ hb1))

/-- Proposition `prop:transversal`. For `c ≠ 0`, the connection `γ_B` from `Σ_U(B)` to `Σ_I(B)`
is transversal: `L = d/dt - A(t) : C¹_b → C⁰_b` has index `μ(Σ_U(B)) - μ(Σ_I(B)) = 1 - 1 = 0`,
and it is invertible. -/
theorem prop_transversal_palmer (hc : c ≠ 0) (hθ : IsHeight θ (fun b => (b : ℝ))) {b : Tau}
    (hb1 : -1 < (b : ℝ)) (hb2 : (b : ℝ) < 1) {M : ℝ}
    (hM : ∀ t, ‖linB c (fun t => (θ t b : ℝ)) t‖ ≤ M) :
    Transversal (linB c fun t => (θ t b : ℝ)) ∧
      (palmerL (continuous_linB c (continuous_base_orbit b)) hM).index = 0 ∧
      ∃ e : C1b (Fin 2 → ℝ) ≃L[ℝ] (ℝ →ᵇ (Fin 2 → ℝ)),
        ∀ p, e p = palmerL (continuous_linB c (continuous_base_orbit b)) hM p := by
  obtain ⟨dm, hdm⟩ := exists_dichotomy_linB (c := c) (s := -1) (by norm_num)
  obtain ⟨dp, hdp⟩ := exists_dichotomy_linB (c := c) (s := 1) one_ne_zero
  have hlimp := tendsto_linB (c := c) (tendsto_base_top hθ hb1)
  have hlimm := tendsto_linB (c := c) (tendsto_base_bot hθ hb2)
  have hA := continuous_linB c (continuous_base_orbit (θ := θ) b)
  have h0 : ∀ y : ℝ → Fin 2 → ℝ, IsLinSol (linB c fun t => (θ t b : ℝ)) 0 y →
      (∃ C, ∀ t, ‖y t‖ ≤ C) → y = 0 := by
    rintro y hy ⟨C, hC⟩
    have hT : ∀ t, HasDerivAt (fun s => y s 0) (-((2 + a) / 3) * (θ t b : ℝ) * y t 0) t :=
      fun t => by simpa [linB_apply_zero] using hasDerivAt_pi.1 (hy t) 0
    have hπ : ∀ t, HasDerivAt (fun s => y s 1)
        (8 * a / 3 * (θ t b : ℝ) * y t 1 + a / c * y t 0) t :=
      fun t => by simpa [linB_apply_one] using hasDerivAt_pi.1 (hy t) 1
    have hb : ∀ t, |y t 1| ≤ C := fun t => by
      rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm (y t) 1).trans (hC t)
    funext t i
    have := prop_transversal hc hθ hb1 hb2 hT hπ hb t
    fin_cases i
    · exact this.1
    · exact this.2
  obtain ⟨hT, e, he⟩ := transversal_of_bdd_eq_zero hA hM dm dp hlimm hlimp
    (hdm.trans hdp.symm) h0
  obtain ⟨-, hi, -⟩ := palmer hA hM dm dp hlimm hlimp
  exact ⟨hT, by rw [hi, hdm, hdp]; rfl, e, he⟩

/-- The linearization `δπ' = (8a/3) τ δπ` along `γ_B` in the reduced system `T = 0`. -/
noncomputable def linR (τ : ℝ → ℝ) (t : ℝ) : ℝ →L[ℝ] ℝ := (8 * a / 3 * τ t) • (1 : ℝ →L[ℝ] ℝ)

theorem continuous_linR (hτ : Continuous τ) : Continuous (linR τ) :=
  continuous_scal (continuous_const.mul hτ)

/-- The reduced system `T = 0`: along `γ_B` the operator `L` is Fredholm of index
`μ(Σ_U(B)) - μ(Σ_I(B)) = 0 - 1 = -1`. -/
theorem reduced_index (hθ : IsHeight θ (fun b => (b : ℝ))) {b : Tau} (hb1 : -1 < (b : ℝ))
    (hb2 : (b : ℝ) < 1) {M : ℝ} (hM : ∀ t, ‖linR (fun t => (θ t b : ℝ)) t‖ ≤ M) :
    (palmerL (continuous_linR (continuous_base_orbit b)) hM).IsFredholm ∧
      (palmerL (continuous_linR (continuous_base_orbit b)) hM).index = -1 := by
  have ha := a_pos
  have hlimm := tendsto_scal ((tendsto_base_bot hθ hb2).const_mul (8 * a / 3))
  have hlimp := tendsto_scal ((tendsto_base_top hθ hb1).const_mul (8 * a / 3))
  have hm : 8 * a / 3 * (-1) < 0 := by nlinarith
  have hp : 0 < 8 * a / 3 * 1 := by nlinarith
  obtain ⟨dm, hdm⟩ := exists_dichotomy_scalar hm.ne
  obtain ⟨dp, hdp⟩ := exists_dichotomy_scalar hp.ne'
  simp only [not_lt.2 hm.le, hp, ↓reduceIte] at hdm hdp
  obtain ⟨hF, hi, -⟩ := palmer (continuous_linR (continuous_base_orbit b)) hM dm dp hlimm hlimp
  exact ⟨hF, by rw [hi, hdm, hdp]; rfl⟩

theorem exists_bound_linR (hθ : IsHeight θ (fun b => (b : ℝ))) {b : Tau} (hb1 : -1 < (b : ℝ))
    (hb2 : (b : ℝ) < 1) : ∃ M, ∀ t, ‖linR (fun t => (θ t b : ℝ)) t‖ ≤ M :=
  exists_bound_of_tendsto (continuous_linR (continuous_base_orbit b))
    (tendsto_scal ((tendsto_base_bot hθ hb2).const_mul (8 * a / 3)))
    (tendsto_scal ((tendsto_base_top hθ hb1).const_mul (8 * a / 3)))

end ConleyCheck.Gubser.Sep
