import ConleyCheck.Palmer.Scalar
import ConleyCheck.Palmer.Planar
import ConleyCheck.BjorkenFlow

/-!
# Proposition `prop:bjorken`: the attractor solution is hyperbolic

Along an orbit of `S` from `(c^-, -1)` to `(0, 1)`, the linearization `y' = a(t) y` with
`a = ∂F/∂c` has `a(t) → ∂F/∂c(c^-, -1) < -1` as `t → -∞` and `a(t) → -k` as `t → ∞`. Both limits
are negative, so `L` has index `0 - 0 = 0` by Palmer's theorem, and with `ker L = 0`
(`prop_bjorken_ker`) it is an isomorphism `C¹_b → C⁰_b` (`prop_bjorken_invertible`).
-/

namespace ConleyCheck.Bjorken.Flow

open Set Filter Topology BoundedContinuousFunction ConleyCheck.Conley ConleyCheck.Palmer

variable (D : Data)

/-- The linearization `y ↦ (∂F/∂c)(c(t), τ(t)) y` along the orbit of `p`. -/
noncomputable def linBj (p : ℝ × Tau) (t : ℝ) : ℝ →L[ℝ] ℝ :=
  Fc D.k ((Pb D).Φ t p).1 ((Pb D).θ t p.2) • (1 : ℝ →L[ℝ] ℝ)

variable {D}

theorem continuous_Fc_orbit {p : ℝ × Tau} (hp : p ∈ S D) :
    Continuous fun s => Fc D.k ((Pb D).Φ s p).1 ((Pb D).θ s p.2) := by
  have hcc : Continuous fun s => ((Pb D).Φ s p).1 := (Pb D).continuous_Φ_fst p
  have hτc : Continuous fun s => ((Pb D).θ s p.2 : ℝ) := (Pb D).continuous_θ p.2
  unfold Fc num P
  exact Continuous.div (by fun_prop) (by fun_prop)
    fun s => pow_ne_zero 2 (den_pos D (mem_N_of_S D hp s)).ne'

theorem continuous_linBj {p : ℝ × Tau} (hp : p ∈ S D) : Continuous (linBj D p) :=
  continuous_scal (continuous_Fc_orbit hp)

theorem Fc_top (k : ℝ) : Fc k 0 1 = -k := by
  unfold Fc num P; norm_num

theorem Fc_cont_top (k : ℝ) : ContinuousAt (fun q : ℝ × ℝ => Fc k q.1 q.2) (0, 1) := by
  unfold Fc num P
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)

theorem tendsto_Fc_of {k : ℝ} {f : ℝ → ℝ × Tau} {l : Filter ℝ} {c₀ : ℝ} {b₀ : Tau}
    (hl : Tendsto f l (𝓝 (c₀, b₀)))
    (hF : ContinuousAt (fun q : ℝ × ℝ => Fc k q.1 q.2) (c₀, b₀)) :
    Tendsto (fun t => Fc k (f t).1 (f t).2) l (𝓝 (Fc k c₀ b₀)) := by
  have h1 : Tendsto (fun t => (f t).1) l (𝓝 c₀) := (continuous_fst.tendsto _).comp hl
  have h2 : Tendsto (fun t => ((f t).2 : ℝ)) l (𝓝 (b₀ : ℝ)) :=
    (continuous_subtype_val.tendsto _).comp ((continuous_snd.tendsto (c₀, b₀)).comp hl)
  have h3 := hF.tendsto.comp (h1.prodMk_nhds h2)
  exact h3

theorem tendsto_Fc_orbit {p : ℝ × Tau} {l : Filter ℝ} {c₀ : ℝ} {b₀ : Tau}
    (hl : Tendsto (fun t => (Pb D).Φ t p) l (𝓝 (c₀, b₀)))
    (hF : ContinuousAt (fun q : ℝ × ℝ => Fc D.k q.1 q.2) (c₀, b₀)) :
    Tendsto (fun t => Fc D.k ((Pb D).Φ t p).1 ((Pb D).θ t p.2)) l
      (𝓝 (Fc D.k c₀ b₀)) := by
  simpa only [ODE.SkewODE.Φ_snd] using tendsto_Fc_of hl hF

/-- Proposition `prop:bjorken`, hyperbolicity. Along an orbit of `S` from `(c^-, -1)` to `(0, 1)`,
the linearized operator `L y = y' - (∂F/∂c) y : C¹_b → C⁰_b` is Fredholm of index `0 - 0 = 0`,
the connection is transversal, and `L` is an isomorphism. -/
theorem prop_bjorken_invertible {p : ℝ × Tau} (hp : p ∈ S D) (hb : (p.2 : ℝ) ∈ Ioo (-1) 1)
    (hm : Tendsto (fun t => (Pb D).Φ t p) atBot (𝓝 (cminus, Tau.bot)))
    (hpl : Tendsto (fun t => (Pb D).Φ t p) atTop (𝓝 (0, Tau.top))) {M : ℝ}
    (hM : ∀ t, ‖linBj D p t‖ ≤ M) :
    (palmerL (continuous_linBj hp) hM).IsFredholm ∧
      (palmerL (continuous_linBj hp) hM).index = 0 ∧ Transversal (linBj D p) ∧
      ∃ e : C1b ℝ ≃L[ℝ] (ℝ →ᵇ ℝ), ∀ q, e q = palmerL (continuous_linBj hp) hM q := by
  have hlm := tendsto_scal (tendsto_Fc_orbit hm (by
    show ContinuousAt _ (cminus, -1); exact Fc_cont D.k))
  have hlp := tendsto_scal (tendsto_Fc_orbit hpl (by
    show ContinuousAt _ (0, 1); exact Fc_cont_top D.k))
  have hneg_m : Fc D.k cminus (Tau.bot : ℝ) < 0 := by
    show Fc D.k cminus (-1) < 0; linarith [Fc_cm_lt D.k]
  have hneg_p : Fc D.k 0 (Tau.top : ℝ) < 0 := by
    show Fc D.k 0 1 < 0; rw [Fc_top]; linarith [D.hk]
  obtain ⟨dm, hdm⟩ := exists_dichotomy_scalar hneg_m.ne
  obtain ⟨dp, hdp⟩ := exists_dichotomy_scalar hneg_p.ne
  simp only [not_lt.2 hneg_m.le, ↓reduceIte] at hdm
  simp only [not_lt.2 hneg_p.le, ↓reduceIte] at hdp
  have hc : Tendsto (fun t => ((Pb D).Φ t p).1) atBot (𝓝 cminus) :=
    (continuous_fst.tendsto _).comp hm
  have h0 : ∀ y : ℝ → ℝ, IsLinSol (linBj D p) 0 y → (∃ C, ∀ t, ‖y t‖ ≤ C) → y = 0 := by
    rintro y hy ⟨C, hC⟩
    funext t
    refine prop_bjorken_ker D hp hb.2 hc (B := C) (fun s => ?_) (fun s => ?_) t
    · simpa [linBj, IsLinSol] using hy s
    · rw [← Real.norm_eq_abs]; exact hC s
  obtain ⟨hF, hi, -⟩ := palmer (continuous_linBj hp) hM dm dp hlm hlp
  obtain ⟨hT, e, he⟩ := transversal_of_bdd_eq_zero (continuous_linBj hp) hM dm dp hlm hlp
    (hdm.trans hdp.symm) h0
  exact ⟨hF, by rw [hi, hdm, hdp]; rfl, hT, e, he⟩

theorem exists_bound_linBj {p : ℝ × Tau} (hp : p ∈ S D)
    (hm : Tendsto (fun t => (Pb D).Φ t p) atBot (𝓝 (cminus, Tau.bot)))
    (hpl : Tendsto (fun t => (Pb D).Φ t p) atTop (𝓝 (0, Tau.top))) :
    ∃ M, ∀ t, ‖linBj D p t‖ ≤ M :=
  exists_bound_of_tendsto (continuous_linBj hp)
    (tendsto_scal (tendsto_Fc_orbit hm (by show ContinuousAt _ (cminus, -1); exact Fc_cont D.k)))
    (tendsto_scal (tendsto_Fc_orbit hpl (by show ContinuousAt _ (0, 1); exact Fc_cont_top D.k)))

end ConleyCheck.Bjorken.Flow
