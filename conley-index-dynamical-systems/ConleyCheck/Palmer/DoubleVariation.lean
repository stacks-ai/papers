import ConleyCheck.Palmer.DoubleEnds
import ConleyCheck.Palmer.Fredholm

/-!
# Remark `rem:palmergeom`: variations of the double along a connecting orbit

Let `γ = (x*, θ*)` be an orbit of the double in the upper sheet, and `D(t) = DV(γ(t))` the
linearization of the double along `γ`. `D(t)` is block upper triangular: `D(t)(y, 0) = (A(t) y, 0)`
with `A(t) = D_x F(cos θ*(t), x*(t))`, and `D(t)(0, 1) = (b(t), a(t))` with `a(t) = G'(θ*(t))`.

* `bddSub_double`: if `(v, w)` is a bounded solution of `ζ' = D(t) ζ` with `w(t) ≠ 0` for all `t`
  (the tangent `γ̇`), then for every set of times `S` the initial values of the solutions bounded on
  `S` are `⟨(v 0, w 0)⟩ ⊕ (E_S × {0})`, where `E_S` are those of `y' = A(t) y`
  (`disjoint_span_map_inl`). For `S = (-∞, 0]` and `[0, ∞)` this is
  `E^u_D = ⟨γ̇(0)⟩ ⊕ (E^u × 0)` and `E^s_D = ⟨γ̇(0)⟩ ⊕ (E^s × 0)`.
* `transversal_double_iff`: `D` is transversal iff `A` is.
* `rem_palmergeom`: the same for the derivative of `dblField F G` along an orbit `γ` with
  `θ* ∈ (0, π)` and bounded range, where `γ̇ = V(γ)` and `w = G(θ*) < 0`.

The identification of `E^u_D`, `E^s_D` with the tangent spaces of `W^u(p₋)`, `W^s(p₊)` at `γ(0)` is the
stable manifold theorem, which is not formalized.
-/

namespace ConleyCheck.Palmer

open Set Filter Topology Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section Linear

omit [CompleteSpace E]

variable {A : ℝ → E →L[ℝ] E} {D : ℝ → E × ℝ →L[ℝ] E × ℝ} {v : ℝ → E} {w : ℝ → ℝ} {M : ℝ}

theorem D_apply (hD : ∀ t y, D t (y, 0) = (A t y, 0)) (t : ℝ) (y : E) (s : ℝ) :
    D t (y, s) = (A t y + s • (D t (0, 1)).1, s * (D t (0, 1)).2) := by
  have : (y, s) = (y, (0 : ℝ)) + s • ((0 : E), (1 : ℝ)) := by ext <;> simp
  rw [this, map_add, map_smul, hD]
  ext <;> simp

/-- The scalar equation `s' = a(t) s` as a linear system on `ℝ`. -/
noncomputable def scalarA (D : ℝ → E × ℝ →L[ℝ] E × ℝ) (t : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.toSpanSingleton ℝ (D t (0, 1)).2

theorem norm_scalarA_le (hM : ∀ t, ‖D t‖ ≤ M) (t : ℝ) : ‖scalarA D t‖ ≤ M := by
  rw [scalarA, ContinuousLinearMap.norm_toSpanSingleton]
  refine (norm_snd_le _).trans (((D t).le_opNorm _).trans ?_)
  have : ‖((0 : E), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  rw [this, mul_one]
  exact hM t

/-- The components of a solution of the double variational equation. -/
theorem isLinSol_components (hD : ∀ t y, D t (y, 0) = (A t y, 0)) {y : ℝ → E} {s : ℝ → ℝ}
    (h : IsLinSol D 0 fun t => (y t, s t)) :
    IsLinSol (scalarA D) 0 s ∧ ∀ t, HasDerivAt y (A t (y t) + s t • (D t (0, 1)).1) t := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have := (hasFDerivAt_snd (𝕜 := ℝ) (p := (y t, s t))).comp_hasDerivAt t (h t)
    rw [Pi.zero_apply, add_zero, D_apply hD] at this
    simp only [scalarA, ContinuousLinearMap.toSpanSingleton_apply, Pi.zero_apply, add_zero,
      smul_eq_mul]
    exact this
  · have := (hasFDerivAt_fst (𝕜 := ℝ) (p := (y t, s t))).comp_hasDerivAt t (h t)
    rw [Pi.zero_apply, add_zero, D_apply hD] at this
    exact this

variable (hD : ∀ t y, D t (y, 0) = (A t y, 0)) (hM : ∀ t, ‖D t‖ ≤ M)
  (hγ : IsLinSol D 0 fun t => (v t, w t)) (hw : ∀ t, w t ≠ 0)
include hD hM hγ hw

/-- Every solution of the double variational equation is `c (v, w) + (z, 0)` with `z' = A z`. -/
theorem eq_smul_add_of_isLinSol {y : ℝ → E} {s : ℝ → ℝ} (h : IsLinSol D 0 fun t => (y t, s t)) :
    s = (s 0 / w 0) • w ∧ IsLinSol A 0 fun t => y t - (s 0 / w 0) • v t := by
  set c := s 0 / w 0
  have h1 := isLinSol_components hD h
  have h2 := isLinSol_components hD hγ
  have hs : s = c • w := h1.1.eq_of_eq (norm_scalarA_le hM) (by simpa using h2.1.smul c)
    (t₀ := 0) (by simp [c, div_mul_cancel₀ _ (hw 0)])
  refine ⟨hs, fun t => ?_⟩
  have := (h1.2 t).sub ((h2.2 t).const_smul c)
  convert this using 1
  have hst : s t = c * w t := congrFun hs t
  simp only [Pi.zero_apply, add_zero, map_sub, map_smul, hst, smul_add, mul_smul]
  abel

/-- The bounded solutions of the double variational equation on `S` are `⟨(v 0, w 0)⟩ ⊕ (E_S × 0)`. -/
theorem bddSub_double (hvb : ∃ C, ∀ t, ‖v t‖ ≤ C) (hwb : ∃ C, ∀ t, |w t| ≤ C) (S : Set ℝ) :
    bddSub D S = Submodule.span ℝ {(v 0, w 0)} ⊔ (bddSub A S).map (LinearMap.inl ℝ E ℝ) := by
  obtain ⟨Cv, hCv⟩ := hvb
  obtain ⟨Cw, hCw⟩ := hwb
  apply le_antisymm
  · rintro _ ⟨Y, hY, rfl, C, hC⟩
    have hY' : IsLinSol D 0 fun t => ((Y t).1, (Y t).2) := by simpa using hY
    obtain ⟨hs, hz⟩ := eq_smul_add_of_isLinSol hD hM hγ hw hY'
    set c := (Y 0).2 / w 0
    refine Submodule.mem_sup.2 ⟨c • (v 0, w 0), Submodule.mem_span_singleton.2 ⟨c, rfl⟩,
      ((Y 0).1 - c • v 0, 0), ⟨(Y 0).1 - c • v 0, ⟨_, hz, rfl, C + |c| * Cv, fun t ht => ?_⟩, rfl⟩,
      ?_⟩
    · refine (norm_sub_le _ _).trans (add_le_add ((norm_fst_le _).trans (hC t ht)) ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hCv t) (abs_nonneg _)
    · have h0 : (Y 0).2 = c * w 0 := by simp [c, div_mul_cancel₀ _ (hw 0)]
      ext <;> simp [h0]
  · rw [sup_le_iff, Submodule.span_le, singleton_subset_iff]
    refine ⟨⟨fun t => (v t, w t), hγ, rfl, Cv + Cw, fun t _ => ?_⟩, ?_⟩
    · rw [Prod.norm_def, Real.norm_eq_abs]
      exact max_le ((hCv t).trans (le_add_of_nonneg_right ((abs_nonneg _).trans (hCw t))))
        ((hCw t).trans (le_add_of_nonneg_left ((norm_nonneg _).trans (hCv t))))
    · rintro _ ⟨_, ⟨z, hz, rfl, C, hC⟩, rfl⟩
      refine ⟨fun t => (z t, 0), fun t => ?_, rfl, C, fun t ht => ?_⟩
      · rw [Pi.zero_apply, add_zero, hD]
        simpa using (hz t).prodMk (hasDerivAt_const t (0 : ℝ))
      · simpa [Prod.norm_def] using hC t ht

omit hD hM hγ in
theorem disjoint_span_map_inl (X : Submodule ℝ E) :
    Disjoint (Submodule.span ℝ {(v 0, w 0)}) (X.map (LinearMap.inl ℝ E ℝ)) := by
  rw [Submodule.disjoint_def]
  intro p hp hX
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hp
  obtain ⟨x, -, hx⟩ := hX
  have h2 := congrArg Prod.snd hx
  simp only [LinearMap.inl_apply, Prod.smul_mk, smul_eq_mul] at h2
  have hc : c = 0 := by
    rcases mul_eq_zero.1 h2.symm with h | h
    · exact h
    · exact absurd h (hw 0)
  simp [hc]

/-- The double variational equation is transversal iff `y' = A(t) y` is. -/
theorem transversal_double_iff (hvb : ∃ C, ∀ t, ‖v t‖ ≤ C) (hwb : ∃ C, ∀ t, |w t| ≤ C) :
    Transversal D ↔ Transversal A := by
  show bddSub D (Iic 0) ⊔ bddSub D (Ici 0) = ⊤ ↔ bddSub A (Iic 0) ⊔ bddSub A (Ici 0) = ⊤
  rw [bddSub_double hD hM hγ hw hvb hwb, bddSub_double hD hM hγ hw hvb hwb,
    sup_sup_sup_comm, sup_idem, ← Submodule.map_sup]
  set X := bddSub A (Iic 0) ⊔ bddSub A (Ici 0)
  constructor
  · intro h
    rw [eq_top_iff]
    intro x _
    have hx : (x, (0 : ℝ)) ∈ Submodule.span ℝ {(v 0, w 0)} ⊔ X.map (LinearMap.inl ℝ E ℝ) :=
      h ▸ Submodule.mem_top
    obtain ⟨p, hp, q, ⟨u, hu, rfl⟩, hpq⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hp
    have h2 := congrArg Prod.snd hpq
    simp only [Prod.smul_mk, smul_eq_mul, LinearMap.inl_apply, Prod.mk_add_mk, add_zero] at h2
    have hc : c = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · exact h
      · exact absurd h (hw 0)
    have h1 := congrArg Prod.fst hpq
    simp only [hc, zero_smul, LinearMap.inl_apply, zero_add] at h1
    exact h1 ▸ hu
  · intro h
    rw [eq_top_iff]
    rintro ⟨x, s⟩ -
    set c := s / w 0
    refine Submodule.mem_sup.2 ⟨c • (v 0, w 0), Submodule.mem_span_singleton.2 ⟨c, rfl⟩,
      (x - c • v 0, 0), ⟨x - c • v 0, h ▸ Submodule.mem_top, rfl⟩, ?_⟩
    have : c * w 0 = s := by simp [c, div_mul_cancel₀ _ (hw 0)]
    ext <;> simp [this]

end Linear

/-! ### The double along an orbit -/

/-- The linearization of the double at `(x, θ)`. -/
noncomputable def dblDeriv (F : ℝ × E → E) (G : ℝ → ℝ) (p : E × ℝ) : E × ℝ →L[ℝ] E × ℝ :=
  ((fderiv ℝ F (Real.cos p.2, p.1)).comp
    (((ContinuousLinearMap.toSpanSingleton ℝ (-Real.sin p.2)).comp
      (ContinuousLinearMap.snd ℝ E ℝ)).prod (ContinuousLinearMap.fst ℝ E ℝ))).prod
    ((ContinuousLinearMap.toSpanSingleton ℝ (deriv G p.2)).comp (ContinuousLinearMap.snd ℝ E ℝ))

omit [CompleteSpace E] in
theorem hasFDerivAt_dblField' {F : ℝ × E → E} {G : ℝ → ℝ} (p : E × ℝ)
    (hF : DifferentiableAt ℝ F (Real.cos p.2, p.1)) (hG : DifferentiableAt ℝ G p.2) :
    HasFDerivAt (dblField F G) (dblDeriv F G p) p := by
  have hc : HasFDerivAt (fun p : E × ℝ => Real.cos p.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-Real.sin p.2)).comp
        (ContinuousLinearMap.snd ℝ E ℝ)) p := by
    have := (Real.hasDerivAt_cos p.2).hasFDerivAt.comp p (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
    exact this
  have h1 := hF.hasFDerivAt.comp p (hc.prodMk hasFDerivAt_fst)
  have h2 := hG.hasDerivAt.hasFDerivAt.comp p (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  exact h1.prodMk h2

omit [CompleteSpace E] in
theorem dblDeriv_inl (F : ℝ × E → E) (G : ℝ → ℝ) (p : E × ℝ) (y : E) :
    dblDeriv F G p (y, 0) = (fiberDeriv F (Real.cos p.2) p.1 y, 0) := by
  simp [dblDeriv, fiberDeriv]

omit [CompleteSpace E] in
/-- Remark `rem:palmergeom`, linear part. Let `γ = (x*, θ*)` be an orbit of the double with `θ*`
in `(0, π)` (the upper sheet) and bounded range, and `A(t) = D_x F(cos θ*(t), x*(t))`. Then the
initial values of the variations of `γ` bounded on `(-∞, 0]` resp. `[0, ∞)` are
`⟨γ̇(0)⟩ ⊕ (E^u × 0)` resp. `⟨γ̇(0)⟩ ⊕ (E^s × 0)`, and the variational equation of the double is
transversal iff `A` is. -/
theorem rem_palmergeom [FiniteDimensional ℝ E] {F : ℝ × E → E} {G : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) (hGneg : ∀ θ ∈ Ioo 0 Real.pi, G θ < 0)
    {γ : ℝ → E × ℝ} (hγ : ∀ t, HasDerivAt γ (dblField F G (γ t)) t)
    (hup : ∀ t, (γ t).2 ∈ Ioo 0 Real.pi) (hbdd : ∃ C, ∀ t, ‖γ t‖ ≤ C) :
    let D := fun t => dblDeriv F G (γ t)
    let A := fun t => fiberDeriv F (Real.cos (γ t).2) (γ t).1
    unstableSub D = Submodule.span ℝ {dblField F G (γ 0)} ⊔
        (unstableSub A).map (LinearMap.inl ℝ E ℝ) ∧
      stableSub D = Submodule.span ℝ {dblField F G (γ 0)} ⊔
        (stableSub A).map (LinearMap.inl ℝ E ℝ) ∧
      (Transversal D ↔ Transversal A) := by
  intro D A
  obtain ⟨C, hC⟩ := hbdd
  have hK : IsCompact (Metric.closedBall (0 : E × ℝ) C) := isCompact_closedBall _ _
  have hmem : ∀ t, γ t ∈ Metric.closedBall (0 : E × ℝ) C := fun t => by simpa using hC t
  have hV := contDiff_dblField hF hG
  have hFd : ∀ p, DifferentiableAt ℝ F p := fun p => hF.differentiable one_ne_zero p
  have hGd : ∀ θ, DifferentiableAt ℝ G θ := fun θ => hG.differentiable one_ne_zero θ
  have hDV : ∀ p, HasFDerivAt (dblField F G) (dblDeriv F G p) p := fun p =>
    hasFDerivAt_dblField' p (hFd _) (hGd _)
  have hcontD : Continuous (dblDeriv F G) := by
    have : dblDeriv F G = fderiv ℝ (dblField F G) := funext fun p => (hDV p).fderiv.symm
    rw [this]
    exact hV.continuous_fderiv one_ne_zero
  obtain ⟨M, hM⟩ : ∃ M, ∀ t, ‖D t‖ ≤ M := by
    obtain ⟨M, hM⟩ := (hK.image hcontD.norm).isBounded.bddAbove
    exact ⟨M, fun t => hM ⟨γ t, hmem t, rfl⟩⟩
  obtain ⟨B, hB⟩ : ∃ B, ∀ t, ‖dblField F G (γ t)‖ ≤ B := by
    obtain ⟨B, hB⟩ := (hK.image hV.continuous.norm).isBounded.bddAbove
    exact ⟨B, fun t => hB ⟨γ t, hmem t, rfl⟩⟩
  have hvar : IsLinSol D 0 fun t => ((dblField F G (γ t)).1, (dblField F G (γ t)).2) := by
    intro t
    have := (hDV (γ t)).comp_hasDerivAt t (hγ t)
    rw [Pi.zero_apply, add_zero]
    exact this
  have hw : ∀ t, (dblField F G (γ t)).2 ≠ 0 := fun t => (hGneg _ (hup t)).ne
  have hvb : ∃ C, ∀ t, ‖(dblField F G (γ t)).1‖ ≤ C := ⟨B, fun t => (norm_fst_le _).trans (hB t)⟩
  have hwb : ∃ C, ∀ t, |(dblField F G (γ t)).2| ≤ C :=
    ⟨B, fun t => (show |_| = ‖_‖ from rfl).le.trans ((norm_snd_le _).trans (hB t))⟩
  have hD : ∀ t y, D t (y, 0) = (A t y, 0) := fun t y => dblDeriv_inl F G (γ t) y
  have key := bddSub_double hD hM hvar hw hvb hwb
  refine ⟨?_, ?_, transversal_double_iff hD hM hvar hw hvb hwb⟩
  · simpa using key (Iic 0)
  · simpa using key (Ici 0)

end ConleyCheck.Palmer
