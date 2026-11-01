import ConleyCheck.Conley.Saddle
import ConleyCheck.Conley.Radial
import ConleyCheck.Conley.Linearization
import ConleyCheck.Conley.Lyapunov
import ConleyCheck.Conley.Family

/-!
# Conley index theory, Stage 3: continuation and hyperbolic equilibria

* `continuation` (Conley 1978, Salamon 1985 Sec. 6): the index is constant along a family of
  flows with a common isolating neighborhood. Proved in `ConleyCheck.Conley.Family`.
* `hasIndex_sphere` : a hyperbolic equilibrium with `k` unstable directions has index `S^k`.
  Proved. In coordinates adapted to `Eᵘ ⊕ Eˢ` the linearized flow is `exp(tA)`
  (`ConleyCheck.Conley.Linearization`), quadratic Lyapunov forms on the two factors
  (`ConleyCheck.Conley.Lyapunov`) cut out an isolating block (`ConleyCheck.Conley.Block`), and the
  block quotient is `S^k` by radial rescaling onto `(D^k × D^m)/(S^{k-1} × D^m)`
  (`ConleyCheck.Conley.Radial`, `ConleyCheck.Conley.Sphere`). The index is transported back along
  the conjugacy (`ConleyCheck.Conley.Conjugacy`).
-/

namespace ConleyCheck.Conley

open Set unitInterval Filter Topology

section Hyperbolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `e` is a hyperbolic equilibrium, with `k`-dimensional unstable space, of the flow of a `C¹`
vector field: the linearized flow `L t = D(ϕ t)(e)` has an invariant splitting `E = Eᵘ ⊕ Eˢ`,
`dim Eᵘ = k`, with exponential contraction on `Eˢ` forward in time and on `Eᵘ` backward in time. -/
structure IsHyperbolicEquilibrium (ϕ : Flow ℝ E) (e : E) (k : ℕ) : Prop where
  generator : ∃ f : E → E, ContDiff ℝ 1 f ∧ ∀ x t, HasDerivAt (fun s => ϕ s x) (f (ϕ t x)) t
  fixed : ∀ t, ϕ t e = e
  splitting : ∃ Eu Es : Submodule ℝ E, IsCompl Eu Es ∧ Module.finrank ℝ Eu = k ∧
    (∀ t, ∀ v ∈ Eu, fderiv ℝ (ϕ t) e v ∈ Eu) ∧ (∀ t, ∀ v ∈ Es, fderiv ℝ (ϕ t) e v ∈ Es) ∧
    ∃ C c : ℝ, 0 < c ∧ ∀ t, 0 ≤ t →
      (∀ v ∈ Es, ‖fderiv ℝ (ϕ t) e v‖ ≤ C * Real.exp (-(c * t)) * ‖v‖) ∧
      (∀ v ∈ Eu, ‖fderiv ℝ (ϕ (-t)) e v‖ ≤ C * Real.exp (-(c * t)) * ‖v‖)

set_option maxHeartbeats 1000000 in
/-- A hyperbolic equilibrium with `k` unstable directions has Conley index `S^k`. -/
theorem hasIndex_sphere [FiniteDimensional ℝ E] {ϕ : Flow ℝ E} {e : E} {k : ℕ}
    (h : IsHyperbolicEquilibrium ϕ e k) : HasIndex ϕ {e} (Sphere k) (Sphere.pt k) := by
  obtain ⟨f, hf, hgen⟩ := h.generator
  obtain ⟨Eu, Es, hcompl, hk, hinvu, hinvs, C, c, hc, hest⟩ := h.splitting
  set A := fderiv ℝ f e with hAdef
  have hd : HasFDerivAt f A e := (hf.differentiable one_ne_zero e).hasFDerivAt
  have hf0 := gen_fixed hgen h.fixed
  have hL : ∀ t, fderiv ℝ (ϕ t) e = NormedSpace.exp (t • A) := fderiv_flow_eq_exp hgen h.fixed hd
  set m := Module.finrank ℝ Es
  -- linear coordinates adapted to the splitting
  let Ju : Eu ≃ₗ[ℝ] EuclideanSpace ℝ (Fin k) := LinearEquiv.ofFinrankEq _ _ (by simp [hk])
  let Js : Es ≃ₗ[ℝ] EuclideanSpace ℝ (Fin m) := LinearEquiv.ofFinrankEq _ _ (by simp [m])
  let J₀ : E ≃ₗ[ℝ] SaddleSpace k m :=
    (Submodule.prodEquivOfIsCompl Eu Es hcompl).symm ≪≫ₗ Ju.prodCongr Js
  haveI : ContinuousSMul ℝ (SaddleSpace k m) := Prod.continuousSMul
  let J : E ≃L[ℝ] SaddleSpace k m := J₀.toContinuousLinearEquiv
  have hJsymm : ∀ z : SaddleSpace k m, J.symm z = ((Ju.symm z.1 : Eu) : E) + (Js.symm z.2 : E) :=
    fun z => rfl
  have hJ1 : ∀ u ∈ Eu, (J u).2 = 0 := by
    intro u hu
    have h1 : (Submodule.prodEquivOfIsCompl Eu Es hcompl).symm u = ((⟨u, hu⟩ : Eu), 0) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left Eu Es hcompl (⟨u, hu⟩ : Eu)
    show Js ((Submodule.prodEquivOfIsCompl Eu Es hcompl).symm u).2 = 0
    rw [h1, map_zero]
  have hJ2 : ∀ v ∈ Es, (J v).1 = 0 := by
    intro v hv
    have h1 : (Submodule.prodEquivOfIsCompl Eu Es hcompl).symm v = (0, (⟨v, hv⟩ : Es)) :=
      Submodule.prodEquivOfIsCompl_symm_apply_right Eu Es hcompl (⟨v, hv⟩ : Es)
    show Ju ((Submodule.prodEquivOfIsCompl Eu Es hcompl).symm v).1 = 0
    rw [h1, map_zero]
  have hJ3 : ∀ a, J.symm (a, 0) ∈ Eu := fun a => by
    rw [hJsymm]; simp only [map_zero, ZeroMemClass.coe_zero, add_zero]; exact (Ju.symm a).2
  have hJ4 : ∀ b, J.symm (0, b) ∈ Es := fun b => by
    rw [hJsymm]; simp only [map_zero, ZeroMemClass.coe_zero, zero_add]; exact (Js.symm b).2
  -- the conjugated flow on `ℝᵏ × ℝᵐ`
  let hφ : E ≃ₜ SaddleSpace k m :=
    { toFun := fun x => J (x - e)
      invFun := fun z => J.symm z + e
      left_inv := fun x => by simp
      right_inv := fun z => by simp
      continuous_toFun := J.continuous.comp (continuous_id.sub continuous_const)
      continuous_invFun := J.symm.continuous.add continuous_const }
  let ψ := conjFlow ϕ hφ
  have hconj : ∀ t x, hφ (ϕ t x) = ψ t (hφ x) := fun t x => by
    simp [ψ, conjFlow_apply]
  have hpre : hφ ⁻¹' {0} = {e} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff]
    show J (x - e) = 0 ↔ x = e
    rw [map_eq_zero_iff J J.injective, sub_eq_zero]
  rw [← hpre]
  refine HasIndex.preimage hconj ?_
  -- generator and linear part of `ψ`
  let F : SaddleSpace k m → SaddleSpace k m := fun z => J (f (J.symm z + e))
  have hψ : ∀ s z, ψ s z = J (ϕ s (J.symm z + e) - e) := fun s z => rfl
  have hgenψ : ∀ z t, HasDerivAt (fun s => ψ s z) (F (ψ t z)) t := by
    intro z t
    have := J.hasFDerivAt.comp_hasDerivAt t ((hgen (J.symm z + e) t).sub_const e)
    convert this using 1
    · exact funext fun s => hψ s z
    · show J (f (J.symm (ψ t z) + e)) = _
      rw [hψ]
      simp
  have hfixψ : ∀ t, ψ t 0 = 0 := fun t => by
    rw [hψ, map_zero, zero_add, h.fixed, sub_self, map_zero]
  let B : SaddleSpace k m →L[ℝ] SaddleSpace k m :=
    (J : E →L[ℝ] SaddleSpace k m).comp (A.comp (J.symm : SaddleSpace k m →L[ℝ] E))
  have hB : ∀ z, B z = J (A (J.symm z)) := fun z => rfl
  let Λ : ℝ → SaddleSpace k m →L[ℝ] SaddleSpace k m := fun s =>
    (J : E →L[ℝ] SaddleSpace k m).comp
      ((NormedSpace.exp (s • A)).comp (J.symm : SaddleSpace k m →L[ℝ] E))
  have hΛ : ∀ s z, Λ s z = J (NormedSpace.exp (s • A) (J.symm z)) := fun s z => rfl
  have hexpc : Continuous fun s : ℝ => NormedSpace.exp (s • A) :=
    continuous_iff_continuousAt.2 fun s => (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A s).continuousAt
  have hΛc : Continuous Λ := continuous_const.clm_comp (hexpc.clm_comp continuous_const)
  have hΛ0 : ∀ z, Λ 0 z = z := fun z => by
    rw [hΛ, zero_smul, NormedSpace.exp_zero, ContinuousLinearMap.one_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  have hΛ' : ∀ s z, HasDerivAt (fun s => Λ s z) (Λ s (B z)) s := by
    intro s z
    have h1 := (ContinuousLinearMap.apply ℝ E (J.symm z)).hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) A s)
    have h2 := J.hasFDerivAt.comp_hasDerivAt s h1
    convert h2 using 1
    · rfl
    · show J (NormedSpace.exp (s • A) (J.symm (J (A (J.symm z))))) = _
      rw [ContinuousLinearEquiv.symm_apply_apply]
      rfl
  have hexpu : ∀ s, ∀ u ∈ Eu, NormedSpace.exp (s • A) u ∈ Eu := fun s u hu => by
    rw [← hL]; exact hinvu s u hu
  have hexps : ∀ s, ∀ v ∈ Es, NormedSpace.exp (s • A) v ∈ Es := fun s v hv => by
    rw [← hL]; exact hinvs s v hv
  have hΛu : ∀ s a, (Λ s (a, 0)).2 = 0 := fun s a => hJ1 _ (hexpu s _ (hJ3 a))
  have hΛs : ∀ s b, (Λ s (0, b)).1 = 0 := fun s b => hJ2 _ (hexps s _ (hJ4 b))
  have hBu : ∀ a, (B (a, 0)).2 = 0 := fun a => by
    have h1 := (hasFDerivAt_snd (p := Λ 0 (a, 0))).comp_hasDerivAt 0 (hΛ' 0 (a, 0))
    have h2 : (Prod.snd ∘ fun s => Λ s (a, 0)) = fun _ => (0 : EuclideanSpace ℝ (Fin m)) :=
      funext fun s => hΛu s a
    rw [h2] at h1
    have := h1.unique (hasDerivAt_const _ _)
    simpa [hΛ0] using this
  have hBs : ∀ b, (B (0, b)).1 = 0 := fun b => by
    have h1 := (hasFDerivAt_fst (p := Λ 0 (0, b))).comp_hasDerivAt 0 (hΛ' 0 (0, b))
    have h2 : (Prod.fst ∘ fun s => Λ s (0, b)) = fun _ => (0 : EuclideanSpace ℝ (Fin k)) :=
      funext fun s => hΛs s b
    rw [h2] at h1
    have := h1.unique (hasDerivAt_const _ _)
    simpa [hΛ0] using this
  let B₁ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    (ContinuousLinearMap.fst ℝ _ _).comp (B.comp (ContinuousLinearMap.inl ℝ _ _))
  let B₂ : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (ContinuousLinearMap.snd ℝ _ _).comp (B.comp (ContinuousLinearMap.inr ℝ _ _))
  have hB₁ : ∀ a, B (a, 0) = (B₁ a, 0) := fun a => Prod.ext rfl (hBu a)
  have hB₂ : ∀ b, B (0, b) = (0, B₂ b) := fun b => Prod.ext (hBs b) rfl
  have hBz : ∀ z : SaddleSpace k m, B z = (B₁ z.1, B₂ z.2) := fun z => by
    have : z = (z.1, 0) + (0, z.2) := by simp
    rw [this, map_add, hB₁, hB₂]
    simp
  -- smallness of the nonlinearity
  have hsmall : ∀ ε > 0, ∀ᶠ z in 𝓝 (0 : SaddleSpace k m),
      ‖(F z).1 - B₁ z.1‖ ≤ ε * ‖z‖ ∧ ‖(F z).2 - B₂ z.2‖ ≤ ε * ‖z‖ := by
    intro ε hε
    set ε' := ε / ((‖(J : E →L[ℝ] SaddleSpace k m)‖ + 1) *
      (‖(J.symm : SaddleSpace k m →L[ℝ] E)‖ + 1)) with hε'
    have hε'0 : 0 < ε' := by positivity
    have hT : Tendsto (fun z : SaddleSpace k m => J.symm z + e) (𝓝 0) (𝓝 e) := by
      have hcont : Continuous fun z : SaddleSpace k m => J.symm z + e :=
        J.symm.continuous.add continuous_const
      simpa using hcont.tendsto (0 : SaddleSpace k m)
    filter_upwards [hT.eventually (eventually_norm_sub_le hd hf0 hε'0)] with z hz
    have hz' : ‖F z - B z‖ ≤ ε * ‖z‖ := by
      have e1 : F z - B z = J (f (J.symm z + e) - A (J.symm z + e - e)) := by
        simp [F, hB, map_sub]
      rw [e1]
      simp only [add_sub_cancel_right] at hz ⊢
      have h1 := (J : E →L[ℝ] SaddleSpace k m).le_opNorm (f (J.symm z + e) - A (J.symm z))
      have h2 := (J.symm : SaddleSpace k m →L[ℝ] E).le_opNorm z
      set a := ‖(J : E →L[ℝ] SaddleSpace k m)‖
      set b := ‖(J.symm : SaddleSpace k m →L[ℝ] E)‖
      have ha : 0 ≤ a := norm_nonneg _
      have hb : 0 ≤ b := norm_nonneg _
      have key : ε' * (a + 1) * (b + 1) = ε := by
        rw [hε', mul_assoc]; exact div_mul_cancel₀ _ (by positivity)
      calc ‖J (f (J.symm z + e) - A (J.symm z))‖
          ≤ a * ‖f (J.symm z + e) - A (J.symm z)‖ := h1
        _ ≤ a * (ε' * ‖J.symm z‖) := mul_le_mul_of_nonneg_left hz ha
        _ ≤ (a + 1) * (ε' * ((b + 1) * ‖z‖)) := by
            gcongr
            · linarith
            · exact h2.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
        _ = ε * ‖z‖ := by rw [← key]; ring
    rw [hBz] at hz'
    exact ⟨(norm_fst_le _).trans hz', (norm_snd_le _).trans hz'⟩
  -- Lyapunov forms on the two factors
  have hnorm_inl : ∀ a : EuclideanSpace ℝ (Fin k), ‖((a, 0) : SaddleSpace k m)‖ = ‖a‖ := fun a => by
    simp [Prod.norm_def]
  have hnorm_inr : ∀ b : EuclideanSpace ℝ (Fin m), ‖((0, b) : SaddleSpace k m)‖ = ‖b‖ := fun b => by
    simp [Prod.norm_def]
  set CJ := ‖(J : E →L[ℝ] SaddleSpace k m)‖ * |C| * ‖(J.symm : SaddleSpace k m →L[ℝ] E)‖
  let Λ₂ : ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) := fun s =>
    (ContinuousLinearMap.snd ℝ _ _).comp ((Λ s).comp (ContinuousLinearMap.inr ℝ _ _))
  have hΛ₂ : ∀ s b, Λ s (0, b) = (0, Λ₂ s b) := fun s b => Prod.ext (hΛs s b) rfl
  obtain ⟨P₂, τ₂, hτ₂, hP₂⟩ := exists_lyapunov (Λ := Λ₂) (B := B₂)
    ((continuous_const.clm_comp (hΛc.clm_comp continuous_const)))
    (fun b => by
      show (Λ 0 (0, b)).2 = b
      rw [hΛ0])
    (fun s b => by
      have h1 := (hasFDerivAt_snd (p := Λ s (0, b))).comp_hasDerivAt s (hΛ' s (0, b))
      convert h1 using 1
      · rfl
      · show Λ₂ s (B₂ b) = (Λ s (B (0, b))).2
        rw [hB₂, hΛ₂])
    hc (C := CJ) (fun s hs b => by
      have hw := hJ4 b
      have h1 := (hest s hs).1 _ hw
      rw [hL] at h1
      have h2 : ‖Λ₂ s b‖ ≤ ‖Λ s (0, b)‖ := by rw [hΛ₂]; exact norm_snd_le ((0, Λ₂ s b) : SaddleSpace k m)
      rw [hΛ] at h2
      have h3 := (J : E →L[ℝ] SaddleSpace k m).le_opNorm (NormedSpace.exp (s • A) (J.symm (0, b)))
      have h4 := (J.symm : SaddleSpace k m →L[ℝ] E).le_opNorm ((0, b) : SaddleSpace k m)
      rw [hnorm_inr] at h4
      have h5 : C * Real.exp (-(c * s)) * ‖J.symm (0, b)‖ ≤
          |C| * Real.exp (-(c * s)) * ‖J.symm (0, b)‖ := by
        gcongr; exact le_abs_self C
      calc ‖Λ₂ s b‖ ≤ ‖(J : E →L[ℝ] SaddleSpace k m)‖ *
            ‖NormedSpace.exp (s • A) (J.symm (0, b))‖ := h2.trans h3
        _ ≤ ‖(J : E →L[ℝ] SaddleSpace k m)‖ * (|C| * Real.exp (-(c * s)) * ‖J.symm (0, b)‖) :=
            mul_le_mul_of_nonneg_left (h1.trans h5) (norm_nonneg _)
        _ ≤ ‖(J : E →L[ℝ] SaddleSpace k m)‖ * (|C| * Real.exp (-(c * s)) *
            (‖(J.symm : SaddleSpace k m →L[ℝ] E)‖ * ‖b‖)) := by gcongr; exact h4
        _ = CJ * Real.exp (-(c * s)) * ‖b‖ := by ring)
  let Λ₁ : ℝ → EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) := fun s =>
    (ContinuousLinearMap.fst ℝ _ _).comp ((Λ (-s)).comp (ContinuousLinearMap.inl ℝ _ _))
  have hΛ₁ : ∀ s a, Λ (-s) (a, 0) = (Λ₁ s a, 0) := fun s a => Prod.ext rfl (hΛu (-s) a)
  have hΛnc : Continuous fun s => Λ (-s) := hΛc.comp continuous_neg
  obtain ⟨P₁, τ₁, hτ₁, hP₁⟩ := exists_lyapunov (Λ := Λ₁) (B := -B₁)
    ((continuous_const.clm_comp (hΛnc.clm_comp continuous_const)))
    (fun a => by
      show (Λ (-0) (a, 0)).1 = a
      rw [neg_zero, hΛ0])
    (fun s a => by
      have h0 := (hΛ' (-s) (a, 0)).scomp s (hasDerivAt_neg s)
      have h1 := (hasFDerivAt_fst (p := Λ (-s) (a, 0))).comp_hasDerivAt s h0
      convert h1 using 1
      · rfl
      · show Λ₁ s ((-B₁) a) = ((-1 : ℝ) • Λ (-s) (B (a, 0))).1
        rw [hB₁, neg_apply, map_neg, Prod.smul_fst, neg_one_smul]
        show -(Λ (-s) (B₁ a, 0)).1 = -(Λ (-s) (B₁ a, 0)).1
        rfl)
    hc (C := CJ) (fun s hs a => by
      have hw := hJ3 a
      have h1 := (hest s hs).2 _ hw
      rw [hL] at h1
      have h2 : ‖Λ₁ s a‖ ≤ ‖Λ (-s) (a, 0)‖ := by rw [hΛ₁]; exact norm_fst_le ((Λ₁ s a, 0) : SaddleSpace k m)
      rw [hΛ] at h2
      have h3 := (J : E →L[ℝ] SaddleSpace k m).le_opNorm
        (NormedSpace.exp ((-s) • A) (J.symm (a, 0)))
      have h4 := (J.symm : SaddleSpace k m →L[ℝ] E).le_opNorm ((a, 0) : SaddleSpace k m)
      rw [hnorm_inl] at h4
      have h5 : C * Real.exp (-(c * s)) * ‖J.symm (a, 0)‖ ≤
          |C| * Real.exp (-(c * s)) * ‖J.symm (a, 0)‖ := by
        gcongr; exact le_abs_self C
      calc ‖Λ₁ s a‖ ≤ ‖(J : E →L[ℝ] SaddleSpace k m)‖ *
            ‖NormedSpace.exp ((-s) • A) (J.symm (a, 0))‖ := h2.trans h3
        _ ≤ ‖(J : E →L[ℝ] SaddleSpace k m)‖ * (|C| * Real.exp (-(c * s)) * ‖J.symm (a, 0)‖) :=
            mul_le_mul_of_nonneg_left (h1.trans h5) (norm_nonneg _)
        _ ≤ ‖(J : E →L[ℝ] SaddleSpace k m)‖ * (|C| * Real.exp (-(c * s)) *
            (‖(J.symm : SaddleSpace k m →L[ℝ] E)‖ * ‖a‖)) := by gcongr; exact h4
        _ = CJ * Real.exp (-(c * s)) * ‖a‖ := by ring)
  -- the block
  have hP₁' : ∀ a, τ₁ * ‖a‖ ^ 2 ≤ qf P₁ a ∧ 1 / 2 * ‖a‖ ^ 2 ≤ dq P₁ a (B₁ a) := fun a => by
    obtain ⟨h1, h2⟩ := hP₁ a
    refine ⟨h1, ?_⟩
    simp only [neg_apply, map_neg, inner_neg_left, inner_neg_right] at h2
    unfold dq
    linarith
  have hP₂' : ∀ b, τ₂ * ‖b‖ ^ 2 ≤ qf P₂ b ∧ dq P₂ b (B₂ b) ≤ -(1 / 2) * ‖b‖ ^ 2 := hP₂
  obtain ⟨δ, hδ, hpair⟩ := exists_block hgenψ hfixψ hsmall hτ₁ hτ₂ hP₁' hP₂'
  exact ⟨_, _, hpair, ⟨blockEquiv hτ₁ hτ₂ hδ (fun a => (hP₁' a).1) (fun b => (hP₂' b).1)⟩⟩

theorem IsHyperbolicEquilibrium.isIsolatedInvariantSet [FiniteDimensional ℝ E] {ϕ : Flow ℝ E}
    {e : E} {k : ℕ} (h : IsHyperbolicEquilibrium ϕ e k) : IsIsolatedInvariantSet ϕ {e} := by
  obtain ⟨N, L, hP, -⟩ := hasIndex_sphere h
  exact hP.isIsolatedInvariantSet

end Hyperbolic

end ConleyCheck.Conley
