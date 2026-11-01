import ConleyCheck.Palmer.Planar
import ConleyCheck.ON.Diagonal

/-!
# Proposition `prop:ONramp`(ii): transversality and the Fredholm index

* `transversal_G`, `transversal_I`: the linearizations along the constant solutions `y ≡ Σ_G` and
  `y ≡ Σ_I` are `-I` and `diag(1, -1/3)` for every `N` (`J_G`, `J_I`), so the connections
  `Σ_G^- → Σ_G^+` and `Σ_I^- → Σ_I^+` are transversal and `L` is invertible.
* `diagonal_index`: along the diagonal solution `y₁ = y₂ = -1/p_*` with `h = N ∘ σ + 8`, the
  linearization `J(N(σ(s)), y(s))` tends to `J(N_∓, Σ_H)`, whose eigenvectors are `(1, 1)` and
  `(N - 1, -3)` with eigenvalues `1` and `(4 - N)/(N + 8)`. For `N_- > 4` and `1 < N_+ < 4`, `L` is
  Fredholm of index `μ(Σ_H^-) - μ(Σ_H^+) = 1 - 2 = -1`.
-/

namespace ConleyCheck.ON

open Set Filter Topology Matrix BoundedContinuousFunction ConleyCheck.Palmer

/-- Proposition `prop:ONramp`(ii): `y ≡ Σ_G` is a transversal connection, and `L` is invertible. -/
theorem transversal_G (Ns : ℝ → ℝ) :
    Transversal (fun s => matCLM (J (Ns s) ptG.1 ptG.2)) ∧
      ∃ e : C1b (Fin 2 → ℝ) ≃L[ℝ] (ℝ →ᵇ (Fin 2 → ℝ)), ∀ p, e p =
        palmerL (A := fun _ => matCLM !![-1, 0; 0, -1]) continuous_const (fun _ => le_rfl) p := by
  have : (fun s => matCLM (J (Ns s) ptG.1 ptG.2)) = fun _ => matCLM !![-1, 0; 0, -1] :=
    funext fun s => by rw [J_G]
  rw [this]
  obtain ⟨d, -⟩ := exists_dichotomy_tri (p := -1) (r := 0) (q := -1) (Or.inr rfl) (by norm_num)
    (by norm_num)
  exact transversal_const d

/-- Proposition `prop:ONramp`(ii): `y ≡ Σ_I` is a transversal connection, and `L` is invertible. -/
theorem transversal_I (Ns : ℝ → ℝ) :
    Transversal (fun s => matCLM (J (Ns s) ptI.1 ptI.2)) ∧
      ∃ e : C1b (Fin 2 → ℝ) ≃L[ℝ] (ℝ →ᵇ (Fin 2 → ℝ)), ∀ p, e p =
        palmerL (A := fun _ => matCLM !![1, 0; 0, -1 / 3]) continuous_const (fun _ => le_rfl)
          p := by
  have : (fun s => matCLM (J (Ns s) ptI.1 ptI.2)) = fun _ => matCLM !![1, 0; 0, -1 / 3] :=
    funext fun s => by rw [J_I]
  rw [this]
  obtain ⟨d, -⟩ := exists_dichotomy_tri (p := 1) (r := 0) (q := -1 / 3) (Or.inr rfl)
    (by norm_num) (by norm_num)
  exact transversal_const d

theorem continuous_J : Continuous fun q : ℝ × ℝ => J q.1 q.2 q.2 :=
  continuous_matrix fun i j => by fin_cases i <;> fin_cases j <;> simp [J] <;> fun_prop

/-- The dichotomy at `Σ_H` for `N > 1`, `N ≠ 4`. -/
theorem exists_dichotomy_H {N : ℝ} (h1 : 1 < N) (h4 : N ≠ 4) :
    ∃ d : Dichotomy (matCLM (J N (-1 / (N + 8)) (-1 / (N + 8)))),
      d.μ = 1 + (if 0 < (4 - N) / (N + 8) then 1 else 0) := by
  have h8 : N + 8 ≠ 0 := by linarith
  have hli : LinearIndependent ℝ ![![(1 : ℝ), 1], ![N - 1, -3]] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h0 := congrFun h 0
    have h1' := congrFun h 1
    simp at h0 h1'
    have ht : t * (N + 2) = 0 := by linarith
    rcases mul_eq_zero.1 ht with ht | ht
    · subst ht; exact ⟨by linarith, rfl⟩
    · exact absurd ht (by linarith)
  have hv : J N (-1 / (N + 8)) (-1 / (N + 8)) *ᵥ ![1, 1] = (1 : ℝ) • ![1, 1] := by
    ext i; fin_cases i <;> simp [J, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      field_simp <;> ring
  have hw : J N (-1 / (N + 8)) (-1 / (N + 8)) *ᵥ ![N - 1, -3] =
      ((4 - N) / (N + 8)) • ![N - 1, -3] := by
    ext i; fin_cases i <;> simp [J, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      field_simp <;> ring
  obtain ⟨d, hd⟩ := exists_dichotomy_pair hli hv hw one_ne_zero
    (div_ne_zero (sub_ne_zero.2 (Ne.symm h4)) h8)
  exact ⟨d, hd.trans (by simp only [zero_lt_one, ↓reduceIte])⟩

variable {h : ℝ → ℝ} {B : ℝ}

/-- The linearization `J(N(s), y(s), y(s))` along the diagonal solution, `N = h - 8`,
`y = -1/p_*`. -/
noncomputable def Adiag (h : ℝ → ℝ) (s : ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  matCLM (J (h s - 8) (-1 / pstar h s) (-1 / pstar h s))

theorem continuous_pstar (hc : Continuous h) (hb : ∀ r, |h r| ≤ B) : Continuous (pstar h) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_pstar hc hb s).continuousAt

theorem continuous_Adiag (hc : Continuous h) (hb : ∀ r, |h r| ≤ B) {m : ℝ} (hm9 : 9 < m)
    (hm : ∀ r, m ≤ h r) : Continuous (Adiag h) := by
  have hp : ∀ s, pstar h s ≠ 0 := fun s => by
    have := (diagonal_solution hc hb hm9 hm s).2.2.1; linarith
  have hy : Continuous fun s => -1 / pstar h s := continuous_const.div (continuous_pstar hc hb) hp
  exact matCLM.continuous.comp (continuous_J.comp ((hc.sub continuous_const).prodMk hy))

theorem tendsto_Adiag {l : Filter ℝ} {N : ℝ} (hN : Tendsto h l (𝓝 (N + 8)))
    (hp : Tendsto (pstar h) l (𝓝 (N + 8))) (hN8 : N + 8 ≠ 0) :
    Tendsto (Adiag h) l (𝓝 (matCLM (J N (-1 / (N + 8)) (-1 / (N + 8))))) := by
  have h1 : Tendsto (fun s => h s - 8) l (𝓝 N) := by
    have := hN.sub_const 8
    rwa [add_sub_cancel_right] at this
  have h2 : Tendsto (fun s => -1 / pstar h s) l (𝓝 (-1 / (N + 8))) :=
    tendsto_const_nhds.div hp hN8
  have hJ : Tendsto (fun q : ℝ × ℝ => matCLM (J q.1 q.2 q.2)) (𝓝 (N, -1 / (N + 8)))
      (𝓝 (matCLM (J N (-1 / (N + 8)) (-1 / (N + 8))))) :=
    (matCLM.continuous.comp continuous_J).tendsto (N, -1 / (N + 8))
  have h3 := hJ.comp (h1.prodMk_nhds h2)
  unfold Adiag
  exact h3

theorem exists_bound_Adiag (hc : Continuous h) (hb : ∀ r, |h r| ≤ B) {m : ℝ} (hm9 : 9 < m)
    (hm : ∀ r, m ≤ h r) {Nm Np : ℝ} (hNm : Tendsto h atBot (𝓝 (Nm + 8)))
    (hNp : Tendsto h atTop (𝓝 (Np + 8))) (h8m : Nm + 8 ≠ 0) (h8p : Np + 8 ≠ 0) :
    ∃ M, ∀ s, ‖Adiag h s‖ ≤ M :=
  exists_bound_of_tendsto (continuous_Adiag hc hb hm9 hm)
    (tendsto_Adiag hNm (tendsto_pstar_atBot hc hb hNm) h8m)
    (tendsto_Adiag hNp (tendsto_pstar_atTop hc hb hNp) h8p)

/-- Proposition `prop:ONramp`(ii). For `N_- > 4` and `1 < N_+ < 4`, the linearized operator along
the diagonal solution `eq:ONdiag` is Fredholm of index `μ(Σ_H^-) - μ(Σ_H^+) = 1 - 2 = -1`. -/
theorem diagonal_index (hc : Continuous h) (hb : ∀ r, |h r| ≤ B) {m : ℝ} (hm9 : 9 < m)
    (hm : ∀ r, m ≤ h r) {Nm Np : ℝ} (hNm : Tendsto h atBot (𝓝 (Nm + 8)))
    (hNp : Tendsto h atTop (𝓝 (Np + 8))) (h4m : 4 < Nm) (h1p : 1 < Np) (h4p : Np < 4)
    {M : ℝ} (hM : ∀ s, ‖Adiag h s‖ ≤ M) :
    (palmerL (continuous_Adiag hc hb hm9 hm) hM).IsFredholm ∧
      (palmerL (continuous_Adiag hc hb hm9 hm) hM).index = -1 := by
  obtain ⟨dm, hdm⟩ := exists_dichotomy_H (N := Nm) (by linarith) h4m.ne'
  obtain ⟨dp, hdp⟩ := exists_dichotomy_H (N := Np) h1p h4p.ne
  have hlimm := tendsto_Adiag hNm (tendsto_pstar_atBot hc hb hNm) (by linarith)
  have hlimp := tendsto_Adiag hNp (tendsto_pstar_atTop hc hb hNp) (by linarith)
  obtain ⟨hF, hi, -⟩ := palmer (continuous_Adiag hc hb hm9 hm) hM dm dp hlimm hlimp
  refine ⟨hF, ?_⟩
  have h1 : ¬ 0 < (4 - Nm) / (Nm + 8) :=
    not_lt.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
  have h2 : 0 < (4 - Np) / (Np + 8) := div_pos (by linarith) (by linarith)
  rw [hi, hdm, hdp]
  simp only [h1, h2, ↓reduceIte]
  norm_num

end ConleyCheck.ON
