import ConleyCheck.Palmer.Hyperbolic
import ConleyCheck.Conley.Continuation
import ConleyCheck.Analysis.LemG
import ConleyCheck.ODE.Cutoff

/-!
# Proposition `prop:palmer`(i): the end points are hyperbolic in the double

The double of a non-autonomous system `ẋ = F(σ, x)` is the vector field
`V(x, θ) = (F(cos θ, x), G(θ))` on `E × ℝ` (`dblField`), with `G` the function of Lemma `lem:G`.
At `p₊ = (e₊, 0)` and `p₋ = (e₋, π)`, where `sin θ = 0`, the `θ`-derivative of `F(cos θ, x)`
vanishes, so `DV(p±) = Df±(e±) × G'(θ±)` is block diagonal (`hasFDerivAt_dblField`).

* `Dichotomy.prod`: dichotomies of block-diagonal maps, with `μ` additive (`Dichotomy.prod_μ`).
* `Dichotomy.scalar`: the dichotomy of `c ≠ 0` on `ℝ`, with `μ = 1` if `c > 0` and `0` if `c < 0`.
* `Dichotomy.isHyperbolicEquilibrium`: a dichotomy of the linearization `Df(e)` at a zero `e` of a
  `C¹` generator makes `e` a hyperbolic equilibrium of the flow in the sense of
  `Conley.IsHyperbolicEquilibrium`, with `k = μ`. This is the link with `hasIndex_sphere`.
* `prop_palmer_i`: if `e±` are hyperbolic equilibria of `f± = F(±1, ·)` with Morse indices `μ±` and
  `g'(-1) > 0 > g'(1)`, then `p₊` and `p₋` are hyperbolic equilibria of every global flow of the
  double, with Morse indices `μ₊` and `μ₋ + 1`.
* `dblCutFlow`, `prop_palmer_i_flow`: the flow of the double, constructed. For a general `C¹` field
  `F` solutions may blow up in finite time, so `V` is cut off outside a ball of radius `R`
  containing `p±`; the cut-off field is bounded and globally Lipschitz, and its flow agrees with the
  double on the ball (`hasDerivAt_dblCutFlow`, `dblCutFlow_eq_of_sol`).
-/

namespace ConleyCheck.Palmer

open NormedSpace Set Filter Topology Module

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Block-diagonal dichotomies -/

theorem norm_prodMap_le (f : E →L[ℝ] E) (g : F →L[ℝ] F) : ‖f.prodMap g‖ ≤ max ‖f‖ ‖g‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (le_max_of_le_left (norm_nonneg _)) fun v => ?_
  show ‖(f v.1, g v.2)‖ ≤ _
  rw [Prod.norm_def, Prod.norm_def]
  refine max_le ((f.le_opNorm _).trans ?_) ((g.le_opNorm _).trans ?_)
  · exact mul_le_mul (le_max_left _ _) (le_max_left _ _) (norm_nonneg _)
      (le_max_of_le_left (norm_nonneg _))
  · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (norm_nonneg _)
      (le_max_of_le_left (norm_nonneg _))

theorem prodMap_mul (f f' : E →L[ℝ] E) (g g' : F →L[ℝ] F) :
    f.prodMap g * f'.prodMap g' = (f * f').prodMap (g * g') := rfl

theorem one_sub_prodMap (f : E →L[ℝ] E) (g : F →L[ℝ] F) :
    1 - f.prodMap g = (1 - f).prodMap (1 - g) := by
  ext v <;> simp

variable [CompleteSpace E] [CompleteSpace F]

theorem exp_smul_prodMap (A : E →L[ℝ] E) (B : F →L[ℝ] F) (t : ℝ) :
    exp (t • A.prodMap B) = (exp (t • A)).prodMap (exp (t • B)) := by
  refine ContinuousLinearMap.ext fun v => ?_
  have h1 : IsLinSol (fun _ => A.prodMap B) 0 fun s => exp (s • A.prodMap B) v := fun s => by
    simpa using hasDerivAt_exp_smul_apply (A.prodMap B) v s
  have h2 : IsLinSol (fun _ => A.prodMap B) 0 fun s => (exp (s • A) v.1, exp (s • B) v.2) :=
    fun s => by
      have := (hasDerivAt_exp_smul_apply A v.1 s).prodMk (hasDerivAt_exp_smul_apply B v.2 s)
      simpa using this
  have := h1.eq_of_eq (M := ‖A.prodMap B‖) (fun _ => le_rfl) h2 (t₀ := 0) (by simp)
  exact congrFun this t

theorem le_max_mul_exp {K K' α α' t : ℝ} (hK : 0 < K) (ht : 0 ≤ t) (hα : min α α' ≤ α) :
    K * Real.exp (-(α * t)) ≤ max K K' * Real.exp (-(min α α' * t)) :=
  mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le
    (hK.le.trans (le_max_left _ _))

namespace Dichotomy

variable {A : E →L[ℝ] E} {B : F →L[ℝ] F}

/-- The dichotomy of a block-diagonal map. -/
noncomputable def prod (d : Dichotomy A) (d' : Dichotomy B) : Dichotomy (A.prodMap B) where
  P := d.P.prodMap d'.P
  K := max d.K d'.K
  α := min d.α d'.α
  hK := lt_max_of_lt_left d.hK
  hα := lt_min d.hα d'.hα
  idem := by rw [prodMap_mul, d.idem, d'.idem]
  comm := by
    show A.prodMap B * d.P.prodMap d'.P = d.P.prodMap d'.P * A.prodMap B
    rw [prodMap_mul, prodMap_mul, d.comm.eq, d'.comm.eq]
  stable t ht := by
    rw [exp_smul_prodMap, prodMap_mul]
    refine (norm_prodMap_le _ _).trans (max_le ?_ ?_)
    · exact (d.stable t ht).trans (le_max_mul_exp d.hK ht (min_le_left _ _))
    · refine (d'.stable t ht).trans ?_
      rw [max_comm, min_comm]
      exact le_max_mul_exp d'.hK ht (min_le_left _ _)
  unstable t ht := by
    rw [exp_smul_prodMap, one_sub_prodMap, prodMap_mul]
    refine (norm_prodMap_le _ _).trans (max_le ?_ ?_)
    · exact (d.unstable t ht).trans (le_max_mul_exp d.hK ht (min_le_left _ _))
    · refine (d'.unstable t ht).trans ?_
      rw [max_comm, min_comm]
      exact le_max_mul_exp d'.hK ht (min_le_left _ _)

theorem prod_μ [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] (d : Dichotomy A)
    (d' : Dichotomy B) : (d.prod d').μ = d.μ + d'.μ := by
  rw [μ, μ, μ]
  show finrank ℝ (LinearMap.range ((1 - d.P.prodMap d'.P : E × F →L[ℝ] E × F) : E × F →ₗ[ℝ] E × F)) = _
  rw [one_sub_prodMap]
  show finrank ℝ (LinearMap.range (((1 - d.P : E →L[ℝ] E) : E →ₗ[ℝ] E).prodMap
    ((1 - d'.P : F →L[ℝ] F) : F →ₗ[ℝ] F))) = _
  rw [LinearMap.range_prodMap, (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]

end Dichotomy

/-- The dichotomy of multiplication by `c ≠ 0` on `ℝ`. -/
noncomputable def Dichotomy.scalar {c : ℝ} (hc : c ≠ 0) :
    Dichotomy (ContinuousLinearMap.toSpanSingleton ℝ c) :=
  Dichotomy.ofBasis (b := Basis.singleton (Fin 1) ℝ) (l := fun _ => c)
    (fun i => by simp) (fun _ => hc)

theorem Dichotomy.scalar_μ {c : ℝ} (hc : c ≠ 0) :
    (Dichotomy.scalar hc).μ = if 0 < c then 1 else 0 := by
  rw [Dichotomy.scalar, Dichotomy.ofBasis_μ]
  split_ifs with h <;> simp [h]

/-! ### Hyperbolic equilibria of flows -/

omit [CompleteSpace E] in
/-- A flow of a `C¹` vector field fixes the zeros of the field. -/
theorem fixed_of_gen_zero {ϕ : Flow ℝ E} {f : E → E} {e : E} (hf : ContDiff ℝ 1 f)
    (hgen : ∀ x t, HasDerivAt (fun s => ϕ s x) (f (ϕ t x)) t) (he : f e = 0) (t : ℝ) :
    ϕ t e = e := by
  set T := {t : ℝ | ϕ t e = e}
  have hcont : Continuous fun s => ϕ s e :=
    continuous_iff_continuousAt.2 fun s => (hgen e s).continuousAt
  have hcl : IsClosed T := isClosed_eq hcont continuous_const
  have hop : IsOpen T := by
    refine isOpen_iff_mem_nhds.2 fun t₀ ht₀ => ?_
    obtain ⟨K, u, hu, hL⟩ := (hf.contDiffAt (x := e)).exists_lipschitzOnWith
    have hev : ∀ᶠ s in 𝓝 t₀, ϕ s e ∈ u := by
      have := hcont.continuousAt (x := t₀)
      rw [ContinuousAt, show ϕ t₀ e = e from ht₀] at this
      exact this hu
    have := ODE_solution_unique_of_eventually (v := fun _ => f) (s := fun _ => u) (t₀ := t₀)
      (f := fun s => ϕ s e) (g := fun _ => e) (Eventually.of_forall fun _ => hL)
      (hev.mono fun s hs => ⟨hgen e s, hs⟩)
      (Eventually.of_forall fun _ => ⟨by rw [he]; exact hasDerivAt_const _ _,
        mem_of_mem_nhds hu⟩) ht₀
    exact this
  have h0 : (0 : ℝ) ∈ T := by simp [T]
  have := (IsClopen.eq_univ ⟨hcl, hop⟩ ⟨0, h0⟩)
  exact (this ▸ mem_univ t : t ∈ T)

/-- A dichotomy of the linearization at a zero of a `C¹` generator makes the zero a hyperbolic
equilibrium of its flow, with `k` the Morse index `μ`. -/
theorem Dichotomy.isHyperbolicEquilibrium [FiniteDimensional ℝ E] {ϕ : Flow ℝ E} {f : E → E}
    {e : E} (hf : ContDiff ℝ 1 f) (hgen : ∀ x t, HasDerivAt (fun s => ϕ s x) (f (ϕ t x)) t)
    (he : f e = 0) {A : E →L[ℝ] E} (hA : HasFDerivAt f A e)
    (d : Dichotomy A) : Conley.IsHyperbolicEquilibrium ϕ e d.μ := by
  have hfix := fixed_of_gen_zero hf hgen he
  have hL : ∀ t, fderiv ℝ (ϕ t) e = exp (t • A) := Conley.fderiv_flow_eq_exp hgen hfix hA
  set Eu := LinearMap.range ((1 - d.P : E →L[ℝ] E) : E →ₗ[ℝ] E)
  set Es := LinearMap.range (d.P : E →ₗ[ℝ] E)
  have hidem : IsIdempotentElem (d.P : E →ₗ[ℝ] E) := by
    unfold IsIdempotentElem
    rw [← ContinuousLinearMap.toLinearMap_mul, d.idem]
  have hu : ∀ v ∈ Eu, d.P v = 0 := by
    rintro _ ⟨w, rfl⟩
    show d.P ((1 - d.P) w) = 0
    simpa using d.P_Q w
  have hs : ∀ v ∈ Es, d.P v = v := by
    rintro _ ⟨w, rfl⟩
    exact d.P_apply_P w
  refine ⟨⟨f, hf, hgen⟩, hfix, Eu, Es, ?_, rfl, ?_, ?_, ?_⟩
  · rw [show Eu = LinearMap.ker (d.P : E →ₗ[ℝ] E) from d.range_one_sub_eq_ker]
    exact (LinearMap.IsIdempotentElem.isCompl hidem).symm
  · intro t v hv
    rw [hL]
    refine ⟨exp (t • A) v, ?_⟩
    show (1 - d.P) (exp (t • A) v) = _
    rw [clm_one_sub_apply, ← d.exp_P, hu v hv, map_zero, sub_zero]
  · intro t v hv
    rw [hL, ← hs v hv, d.exp_P]
    exact ⟨_, rfl⟩
  · refine ⟨d.K, d.α, d.hα, fun t ht => ⟨fun v hv => ?_, fun v hv => ?_⟩⟩
    · rw [hL]
      have := d.norm_exp_P_le ht v
      rwa [hs v hv] at this
    · rw [hL]
      have := d.norm_exp_Q_le ht v
      rwa [hu v hv, sub_zero] at this

/-- A zero `e` of a `C¹` field `f` in the open ball of radius `R`, with a dichotomy of `Df(e)`, is a
hyperbolic equilibrium of the flow of `f` cut off outside the closed ball. -/
theorem Dichotomy.isHyperbolicEquilibrium_bumpFlow [FiniteDimensional ℝ E] {f : E → E}
    (hf : ContDiff ℝ 1 f) {R : ℝ} (hR : 0 < R) {e : E} (he : f e = 0) (heR : ‖e‖ < R)
    {A : E →L[ℝ] E} (hA : HasFDerivAt f A e) (d : Dichotomy A) :
    Conley.IsHyperbolicEquilibrium (ODE.bumpFlow hf R hR) e d.μ := by
  have hβ : ContDiff ℝ 1 (ODE.bumpField f R hR) := (ODE.bumpOf R hR).contDiff.smul hf
  have heq : ODE.bumpField f R hR =ᶠ[𝓝 e] f := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds heR] with p hp
    simp [ODE.bumpField, ODE.bumpOf_eq_one (hR := hR) (le_of_lt hp)]
  exact d.isHyperbolicEquilibrium hβ (fun x t => ODE.hasDerivAt_bumpFlow hf x t)
    (by simp [ODE.bumpField, he]) (hA.congr_of_eventuallyEq heq)

/-! ### The vector field of the double -/

/-- The vector field `(F(cos θ, x), G(θ))` of the double, with `F(τ, x) = f_τ(x)`. -/
noncomputable def dblField (F : ℝ × E → E) (G : ℝ → ℝ) (p : E × ℝ) : E × ℝ := (F (Real.cos p.2, p.1), G p.2)

omit [CompleteSpace E] in
theorem contDiff_dblField {F : ℝ × E → E} {G : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G) : ContDiff ℝ 1 (dblField F G) :=
  (hF.comp ((Real.contDiff_cos.comp contDiff_snd).prodMk contDiff_fst)).prodMk
    (hG.comp contDiff_snd)

/-- The fiber linearization `D_x F(τ, x)`. -/
noncomputable def fiberDeriv (F : ℝ × E → E) (τ : ℝ) (x : E) : E →L[ℝ] E :=
  (fderiv ℝ F (τ, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)

omit [CompleteSpace E] in
/-- Where `sin θ₀ = 0`, the linearization of the double is block diagonal. -/
theorem hasFDerivAt_dblField {F : ℝ × E → E} {G : ℝ → ℝ} {e : E} {θ₀ : ℝ}
    (hF : DifferentiableAt ℝ F (Real.cos θ₀, e)) (hG : DifferentiableAt ℝ G θ₀)
    (hs : Real.sin θ₀ = 0) :
    HasFDerivAt (dblField F G) ((fiberDeriv F (Real.cos θ₀) e).prodMap
      (ContinuousLinearMap.toSpanSingleton ℝ (deriv G θ₀))) (e, θ₀) := by
  have hin : HasFDerivAt (fun p : E × ℝ => (Real.cos p.2, p.1))
      (((ContinuousLinearMap.toSpanSingleton ℝ (-Real.sin θ₀)).comp
        (ContinuousLinearMap.snd ℝ E ℝ)).prod (ContinuousLinearMap.fst ℝ E ℝ)) (e, θ₀) := by
    have hc : HasFDerivAt (fun p : E × ℝ => Real.cos p.2)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-Real.sin θ₀)).comp
          (ContinuousLinearMap.snd ℝ E ℝ)) (e, θ₀) := by
      have := (Real.hasDerivAt_cos θ₀).hasFDerivAt.comp (e, θ₀)
        (hasFDerivAt_snd (𝕜 := ℝ) (p := (e, θ₀)))
      exact this
    exact hc.prodMk hasFDerivAt_fst
  have h1 := hF.hasFDerivAt.comp (e, θ₀) hin
  have h2 := hG.hasDerivAt.hasFDerivAt.comp (e, θ₀) (hasFDerivAt_snd (𝕜 := ℝ) (p := (e, θ₀)))
  refine (h1.prodMk h2).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => Prod.ext ?_ ?_
  · simp [fiberDeriv, hs]
  · simp

/-- Proposition `prop:palmer`(i), for any `G` with the properties of Lemma `lem:G` used here. -/
theorem prop_palmer_i_of [FiniteDimensional ℝ E] {F : ℝ × E → E} (hF : ContDiff ℝ 1 F)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) (hG0 : G 0 = 0) (hGπ : G Real.pi = 0)
    (hG'0 : deriv G 0 < 0) (hG'π : 0 < deriv G Real.pi)
    {ϕ : Flow ℝ (E × ℝ)} (hgen : ∀ x t, HasDerivAt (fun s => ϕ s x) (dblField F G (ϕ t x)) t)
    {ep em : E} (hep : F (1, ep) = 0) (hem : F (-1, em) = 0)
    (dp : Dichotomy (fiberDeriv F 1 ep)) (dm : Dichotomy (fiberDeriv F (-1) em)) :
    Conley.IsHyperbolicEquilibrium ϕ (ep, 0) dp.μ ∧
      Conley.IsHyperbolicEquilibrium ϕ (em, Real.pi) (dm.μ + 1) := by
  have hV := contDiff_dblField hF hG
  have hFd : ∀ p, DifferentiableAt ℝ F p := fun p => hF.differentiable one_ne_zero p
  have hGd : ∀ θ, DifferentiableAt ℝ G θ := fun θ => hG.differentiable one_ne_zero θ
  constructor
  · have hA := hasFDerivAt_dblField (e := ep) (hFd _) (hGd 0) Real.sin_zero
    rw [Real.cos_zero] at hA
    have h := (dp.prod (Dichotomy.scalar hG'0.ne)).isHyperbolicEquilibrium hV hgen
      (by simp [dblField, hep, hG0]) hA
    have hn : ¬ (0 < deriv G 0) := not_lt.2 hG'0.le
    simpa [Dichotomy.prod_μ, Dichotomy.scalar_μ, hn] using h
  · have hA := hasFDerivAt_dblField (e := em) (hFd _) (hGd Real.pi) Real.sin_pi
    rw [Real.cos_pi] at hA
    have h := (dm.prod (Dichotomy.scalar hG'π.ne')).isHyperbolicEquilibrium hV hgen
      (by simp [dblField, hem, hGπ]) hA
    simpa [Dichotomy.prod_μ, Dichotomy.scalar_μ, hG'π] using h

/-- Proposition `prop:palmer`(i). Let `g ∈ C³` with `g(±1) = 0`, `g > 0` on `(-1, 1)` and
`g'(-1) > 0 > g'(1)`, and let `G` be the function of Lemma `lem:G`. If `e±` are hyperbolic
equilibria of `f± = F(±1, ·)` with Morse indices `μ±`, then `(e₊, 0)` and `(e₋, π)` are hyperbolic
equilibria of every global flow of the double, with Morse indices `μ₊` and `μ₋ + 1`. A global
flow need not exist; `prop_palmer_i_flow` constructs one that agrees with the double on a ball. -/
theorem prop_palmer_i [FiniteDimensional ℝ E] {F : ℝ × E → E} (hF : ContDiff ℝ 1 F)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 3 g) (h1 : g 1 = 0) (hm1 : g (-1) = 0)
    (hpos : ∀ τ ∈ Ioo (-1 : ℝ) 1, 0 < g τ) (hg1 : deriv g 1 < 0) (hgm1 : 0 < deriv g (-1)) :
    ∃ G : ℝ → ℝ, (∀ θ, Real.sin θ ≠ 0 → G θ = -g (Real.cos θ) / Real.sin θ) ∧
      ContDiff ℝ 1 G ∧ ∀ (ϕ : Flow ℝ (E × ℝ)),
        (∀ x t, HasDerivAt (fun s => ϕ s x) (dblField F G (ϕ t x)) t) →
        ∀ {ep em : E}, F (1, ep) = 0 → F (-1, em) = 0 →
        ∀ (dp : Dichotomy (fiberDeriv F 1 ep)) (dm : Dichotomy (fiberDeriv F (-1) em)),
          Conley.IsHyperbolicEquilibrium ϕ (ep, 0) dp.μ ∧
            Conley.IsHyperbolicEquilibrium ϕ (em, Real.pi) (dm.μ + 1) := by
  obtain ⟨G, hG, -, -, hform, -, -, hG0, hGπ, hG'0, hG'π⟩ := lem_G hg h1 hm1 hpos
  refine ⟨G, hform, hG, fun ϕ hgen ep em hep hem dp dm => ?_⟩
  exact prop_palmer_i_of hF hG hG0 hGπ (by rw [hG'0]; linarith) (by rw [hG'π]; linarith)
    hgen hep hem dp dm

/-! ### The flow of the double -/

/-- The flow of the double cut off outside the closed ball of radius `R` in `E × ℝ`. It is the
global flow of the bounded, globally Lipschitz field `β • dblField F G` with `β = 1` on the ball. -/
noncomputable def dblCutFlow [FiniteDimensional ℝ E] {F : ℝ × E → E} (hF : ContDiff ℝ 1 F)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) (R : ℝ) (hR : 0 < R) : Flow ℝ (E × ℝ) :=
  ODE.bumpFlow (contDiff_dblField hF hG) R hR

section CutFlow

variable [FiniteDimensional ℝ E] {F : ℝ × E → E} (hF : ContDiff ℝ 1 F) {G : ℝ → ℝ}
  (hG : ContDiff ℝ 1 G) {R : ℝ} (hR : 0 < R)

/-- While it stays in the closed ball, an orbit of `dblCutFlow` solves the double. -/
theorem hasDerivAt_dblCutFlow (x : E × ℝ) (t : ℝ) (h : ‖dblCutFlow hF hG R hR t x‖ ≤ R) :
    HasDerivAt (fun s => dblCutFlow hF hG R hR s x)
      (dblField F G (dblCutFlow hF hG R hR t x)) t := by
  unfold dblCutFlow at h ⊢
  have := ODE.hasDerivAt_bumpFlow (contDiff_dblField hF hG) (R := R) (hR := hR) x t
  rwa [ODE.bumpOf_eq_one (hR := hR) h, one_smul] at this

/-- A solution of the double that stays in the closed ball is an orbit of `dblCutFlow`. -/
theorem dblCutFlow_eq_of_sol {γ : ℝ → E × ℝ} (hγ : ∀ t, HasDerivAt γ (dblField F G (γ t)) t)
    (hγR : ∀ t, ‖γ t‖ ≤ R) (t₀ t : ℝ) : dblCutFlow hF hG R hR t (γ t₀) = γ (t + t₀) := by
  unfold dblCutFlow ODE.bumpFlow
  refine ODE.flowOf_eq_of_isSol _ _ (fun s => ?_) t₀ t
  have hb := ODE.bumpOf_eq_one (E := E × ℝ) (hR := hR) (hγR s)
  simpa [ODE.bumpField, hb] using hγ s

end CutFlow

/-- Proposition `prop:palmer`(i) for `dblCutFlow`, for any `G` with the properties of Lemma `lem:G`
used here, if `p₊ = (e₊, 0)` and `p₋ = (e₋, π)` lie in the open ball of radius `R`. -/
theorem prop_palmer_i_flow_of [FiniteDimensional ℝ E] {F : ℝ × E → E} (hF : ContDiff ℝ 1 F)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) (hG0 : G 0 = 0) (hGπ : G Real.pi = 0)
    (hG'0 : deriv G 0 < 0) (hG'π : 0 < deriv G Real.pi)
    {ep em : E} (hep : F (1, ep) = 0) (hem : F (-1, em) = 0)
    (dp : Dichotomy (fiberDeriv F 1 ep)) (dm : Dichotomy (fiberDeriv F (-1) em))
    {R : ℝ} (hR : 0 < R) (hRp : ‖ep‖ < R) (hRm : ‖em‖ < R) (hRπ : Real.pi < R) :
    Conley.IsHyperbolicEquilibrium (dblCutFlow hF hG R hR) (ep, 0) dp.μ ∧
      Conley.IsHyperbolicEquilibrium (dblCutFlow hF hG R hR) (em, Real.pi) (dm.μ + 1) := by
  unfold dblCutFlow
  have hV := contDiff_dblField hF hG
  have hFd : ∀ p, DifferentiableAt ℝ F p := fun p => hF.differentiable one_ne_zero p
  have hGd : ∀ θ, DifferentiableAt ℝ G θ := fun θ => hG.differentiable one_ne_zero θ
  constructor
  · have hA := hasFDerivAt_dblField (e := ep) (hFd _) (hGd 0) Real.sin_zero
    rw [Real.cos_zero] at hA
    have hn : ‖((ep, 0) : E × ℝ)‖ < R := by
      rw [Prod.norm_def]; exact max_lt hRp (by simpa using hR)
    have h := (dp.prod (Dichotomy.scalar hG'0.ne)).isHyperbolicEquilibrium_bumpFlow hV hR
      (by simp [dblField, hep, hG0]) hn hA
    have hn : ¬ (0 < deriv G 0) := not_lt.2 hG'0.le
    simpa [Dichotomy.prod_μ, Dichotomy.scalar_μ, hn] using h
  · have hA := hasFDerivAt_dblField (e := em) (hFd _) (hGd Real.pi) Real.sin_pi
    rw [Real.cos_pi] at hA
    have hn : ‖((em, Real.pi) : E × ℝ)‖ < R := by
      rw [Prod.norm_def, Real.norm_eq_abs, abs_of_pos Real.pi_pos]; exact max_lt hRm hRπ
    have h := (dm.prod (Dichotomy.scalar hG'π.ne')).isHyperbolicEquilibrium_bumpFlow hV hR
      (by simp [dblField, hem, hGπ]) hn hA
    simpa [Dichotomy.prod_μ, Dichotomy.scalar_μ, hG'π] using h

/-- Proposition `prop:palmer`(i), with the flow of the double constructed. Let `g ∈ C³` with
`g(±1) = 0`, `g > 0` on `(-1, 1)` and `g'(-1) > 0 > g'(1)`, let `G` be the function of Lemma
`lem:G`, and let `e±` be hyperbolic equilibria of `f± = F(±1, ·)` with Morse indices `μ±`. For
every `R > max(‖e₊‖, ‖e₋‖, π)` there is a global flow `ϕ` on `E × ℝ` that agrees with the double on
the closed ball of radius `R`: its orbits solve the double while in the ball, and solutions of the
double that stay in the ball are its orbits. `(e₊, 0)` and `(e₋, π)` are hyperbolic equilibria
of `ϕ` with Morse indices `μ₊` and `μ₋ + 1`. -/
theorem prop_palmer_i_flow [FiniteDimensional ℝ E] {F : ℝ × E → E} (hF : ContDiff ℝ 1 F)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 3 g) (h1 : g 1 = 0) (hm1 : g (-1) = 0)
    (hpos : ∀ τ ∈ Ioo (-1 : ℝ) 1, 0 < g τ) (hg1 : deriv g 1 < 0) (hgm1 : 0 < deriv g (-1)) :
    ∃ G : ℝ → ℝ, (∀ θ, Real.sin θ ≠ 0 → G θ = -g (Real.cos θ) / Real.sin θ) ∧
      ContDiff ℝ 1 G ∧ ∀ {ep em : E}, F (1, ep) = 0 → F (-1, em) = 0 →
        ∀ (dp : Dichotomy (fiberDeriv F 1 ep)) (dm : Dichotomy (fiberDeriv F (-1) em)),
        ∀ {R : ℝ}, ‖ep‖ < R → ‖em‖ < R → Real.pi < R →
        ∃ ϕ : Flow ℝ (E × ℝ),
          (∀ x t, ‖ϕ t x‖ ≤ R → HasDerivAt (fun s => ϕ s x) (dblField F G (ϕ t x)) t) ∧
          (∀ γ : ℝ → E × ℝ, (∀ t, HasDerivAt γ (dblField F G (γ t)) t) → (∀ t, ‖γ t‖ ≤ R) →
            ∀ t₀ t, ϕ t (γ t₀) = γ (t + t₀)) ∧
          Conley.IsHyperbolicEquilibrium ϕ (ep, 0) dp.μ ∧
          Conley.IsHyperbolicEquilibrium ϕ (em, Real.pi) (dm.μ + 1) := by
  obtain ⟨G, hG, -, -, hform, -, -, hG0, hGπ, hG'0, hG'π⟩ := lem_G hg h1 hm1 hpos
  refine ⟨G, hform, hG, fun {ep em} hep hem dp dm {R} hRp hRm hRπ => ?_⟩
  have hR : 0 < R := Real.pi_pos.trans hRπ
  exact ⟨dblCutFlow hF hG R hR, hasDerivAt_dblCutFlow hF hG hR,
    fun γ hγ hγR => dblCutFlow_eq_of_sol hF hG hR hγ hγR,
    prop_palmer_i_flow_of hF hG hG0 hGπ (by rw [hG'0]; linarith) (by rw [hG'π]; linarith)
      hep hem dp dm hR hRp hRm hRπ⟩

end ConleyCheck.Palmer
