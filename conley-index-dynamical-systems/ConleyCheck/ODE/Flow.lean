import Mathlib

/-!
# The flow of a bounded, globally Lipschitz vector field

A bounded, globally Lipschitz vector field `v` on a Banach space has a unique global solution
through every point, and these solutions form a continuous flow `Flow ℝ E`.
-/

open Set Filter Topology Metric
open scoped NNReal

namespace ConleyCheck.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `γ` is an integral curve of `v` defined on all of `ℝ`. -/
def IsSol (v : E → E) (γ : ℝ → E) : Prop := ∀ t, HasDerivAt γ (v (γ t)) t

theorem IsSol.comp_add_const {v : E → E} {γ : ℝ → E} (h : IsSol v γ) (s : ℝ) :
    IsSol v fun t => γ (t + s) := fun t => (h (t + s)).comp_add_const t s

theorem IsSol.unique {v : E → E} {K : ℝ≥0} (hv : LipschitzWith K v) {γ δ : ℝ → E}
    (hγ : IsSol v γ) (hδ : IsSol v δ) {t₀ : ℝ} (h : γ t₀ = δ t₀) : γ = δ :=
  ODE_solution_unique_univ (v := fun _ => v) (s := fun _ => univ)
    (fun _ => hv.lipschitzOnWith) (fun t => ⟨hγ t, trivial⟩) (fun t => ⟨hδ t, trivial⟩) h

variable [CompleteSpace E] {v : E → E} {K L : ℝ≥0}

theorem exists_sol_Icc (hv : LipschitzWith K v) (hb : ∀ x, ‖v x‖ ≤ L) (x : E) (T : ℝ≥0) :
    ∃ α : ℝ → E, α 0 = x ∧
      ∀ t ∈ Icc (-(T : ℝ)) T, HasDerivWithinAt α (v (α t)) (Icc (-(T : ℝ)) T) t := by
  have h0 : (0 : ℝ) ∈ Icc (-(T : ℝ)) T := ⟨by simp, T.2⟩
  have hPL : IsPicardLindelof (fun _ => v) (⟨0, h0⟩ : Icc (-(T : ℝ)) T) x (L * T) 0 L K :=
    { lipschitzOnWith := fun _ _ => hv.lipschitzOnWith
      continuousOn := fun _ _ => continuousOn_const
      norm_le := fun _ _ y _ => hb y
      mul_max_le := by simp }
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

theorem exists_sol (hv : LipschitzWith K v) (hb : ∀ x, ‖v x‖ ≤ L) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ IsSol v γ := by
  choose α hα0 hα using fun n : ℕ => exists_sol_Icc hv hb x ⟨(n : ℝ) + 1, by positivity⟩
  have hα' : ∀ n : ℕ, ∀ t ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
      HasDerivWithinAt (α n) (v (α n t)) (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) t := hα
  have hαd : ∀ n : ℕ, ∀ t ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1), HasDerivAt (α n) (v (α n t)) t :=
    fun n t ht => (hα' n t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hαc : ∀ n : ℕ, ContinuousOn (α n) (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) :=
    fun n t ht => (hα' n t ht).continuousWithinAt
  have hcons : ∀ n m : ℕ, n ≤ m → EqOn (α n) (α m) (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) := by
    intro n m hnm
    have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
    have hsub : Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) ⊆ Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1) :=
      Ioo_subset_Ioo (by linarith) hnm'
    refine ODE_solution_unique_of_mem_Icc (v := fun _ => v) (s := fun _ => univ) (K := K)
      (fun _ _ => hv.lipschitzOnWith) (t₀ := 0) ⟨by linarith [n.cast_nonneg (α := ℝ)],
        by linarith [n.cast_nonneg (α := ℝ)]⟩ (hαc n) (fun t ht => hαd n t ht)
      (fun _ _ => trivial) ((hαc m).mono (Icc_subset_Icc (by linarith) hnm'))
      (fun t ht => hαd m t (hsub ht)) (fun _ _ => trivial) (by rw [hα0, hα0])
  have hagree : ∀ n m : ℕ, ∀ t ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
      t ∈ Icc (-((m : ℝ) + 1)) ((m : ℝ) + 1) → α n t = α m t := by
    intro n m t hn hm
    rcases le_total n m with h | h
    · exact hcons n m h hn
    · exact (hcons m n h hm).symm
  have hmem : ∀ t : ℝ, t ∈ Ioo (-((⌈|t|⌉₊ : ℝ) + 1)) ((⌈|t|⌉₊ : ℝ) + 1) := by
    intro t
    have h1 := Nat.le_ceil |t|
    constructor <;> linarith [neg_abs_le t, le_abs_self t]
  refine ⟨fun t => α ⌈|t|⌉₊ t, by simp [hα0], fun t => ?_⟩
  refine (hαd _ t (hmem t)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (hmem t).1 (hmem t).2] with s hs
  exact hagree _ _ s (Ioo_subset_Icc_self (hmem s)) (Ioo_subset_Icc_self hs)

/-- The solution through `x`. -/
noncomputable def sol (hv : LipschitzWith K v) (hb : ∀ x, ‖v x‖ ≤ L) (x : E) : ℝ → E :=
  (exists_sol hv hb x).choose

theorem sol_zero (hv : LipschitzWith K v) (hb : ∀ x, ‖v x‖ ≤ L) (x : E) : sol hv hb x 0 = x :=
  (exists_sol hv hb x).choose_spec.1

theorem isSol_sol (hv : LipschitzWith K v) (hb : ∀ x, ‖v x‖ ≤ L) (x : E) :
    IsSol v (sol hv hb x) :=
  (exists_sol hv hb x).choose_spec.2

theorem sol_eq_of_isSol (hv : LipschitzWith K v) (hb : ∀ x, ‖v x‖ ≤ L) {γ : ℝ → E}
    (hγ : IsSol v γ) (t₀ : ℝ) : sol hv hb (γ t₀) = fun t => γ (t + t₀) := by
  refine IsSol.unique hv (isSol_sol hv hb _) (hγ.comp_add_const t₀) (t₀ := 0) ?_
  simp [sol_zero]

theorem dist_sol_le_of_nonneg (hv : LipschitzWith K v) (hb : ∀ x, ‖v x‖ ≤ L) (x y : E) {t : ℝ}
    (ht : 0 ≤ t) : dist (sol hv hb x t) (sol hv hb y t) ≤ dist x y * Real.exp (K * t) := by
  have := dist_le_of_trajectories_ODE (v := fun _ => v) (K := K) (a := 0) (b := t)
    (fun _ => hv) (fun s _ => (isSol_sol hv hb x s).continuousAt.continuousWithinAt)
    (fun s _ => (isSol_sol hv hb x s).hasDerivWithinAt)
    (fun s _ => (isSol_sol hv hb y s).continuousAt.continuousWithinAt)
    (fun s _ => (isSol_sol hv hb y s).hasDerivWithinAt)
    (by rw [sol_zero, sol_zero]) t ⟨ht, le_rfl⟩
  simpa using this

theorem dist_sol_le (hv : LipschitzWith K v) (hb : ∀ x, ‖v x‖ ≤ L) (x y : E) (t : ℝ) :
    dist (sol hv hb x t) (sol hv hb y t) ≤ dist x y * Real.exp (K * |t|) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]; exact dist_sol_le_of_nonneg hv hb x y ht
  · have hrev : ∀ z, IsSol (fun w => -v w) fun s => sol hv hb z (-s) := fun z s => by
      have := (isSol_sol hv hb z (-s)).scomp s (hasDerivAt_neg s)
      simp only [neg_one_smul] at this
      exact this
    have hv' : LipschitzWith K fun w => -v w := by
      have := LipschitzWith.id.neg.comp hv
      simp only [one_mul] at this
      exact this
    have := dist_le_of_trajectories_ODE (v := fun _ w => -v w) (K := K) (a := 0) (b := -t)
      (δ := dist x y)
      (fun _ => hv') (fun s _ => (hrev x s).continuousAt.continuousWithinAt)
      (fun s _ => (hrev x s).hasDerivWithinAt)
      (fun s _ => (hrev y s).continuousAt.continuousWithinAt)
      (fun s _ => (hrev y s).hasDerivWithinAt)
      (by simp [sol_zero]) (-t) ⟨by linarith, le_rfl⟩
    rw [abs_of_nonpos ht]
    simpa using this

theorem lipschitzWith_sol (hv : LipschitzWith K v) (hb : ∀ x, ‖v x‖ ≤ L) (x : E) :
    LipschitzWith L (sol hv hb x) :=
  lipschitzWith_of_nnnorm_deriv_le (fun t => (isSol_sol hv hb x t).differentiableAt)
    fun t => by
      rw [(isSol_sol hv hb x t).deriv, ← NNReal.coe_le_coe, coe_nnnorm]
      exact hb _

/-- The flow of a bounded, globally Lipschitz vector field. -/
noncomputable def flowOf (hv : LipschitzWith K v) (hb : ∀ x, ‖v x‖ ≤ L) : Flow ℝ E where
  toFun t x := sol hv hb x t
  cont' := by
    refine continuous_prod_of_continuous_lipschitzWith _ L (fun t => ?_)
      (fun x => lipschitzWith_sol hv hb x)
    refine Metric.continuous_iff.2 fun x ε hε => ⟨ε / Real.exp (K * |t|), by positivity,
      fun y hy => ?_⟩
    calc dist (sol hv hb y t) (sol hv hb x t) ≤ dist y x * Real.exp (K * |t|) :=
          dist_sol_le hv hb y x t
      _ < ε / Real.exp (K * |t|) * Real.exp (K * |t|) :=
          mul_lt_mul_of_pos_right hy (Real.exp_pos _)
      _ = ε := div_mul_cancel₀ _ (Real.exp_pos _).ne'
  map_add' t₁ t₂ x := by
    have := sol_eq_of_isSol hv hb (isSol_sol hv hb x) t₂
    exact (congrFun this t₁).symm
  map_zero' x := sol_zero hv hb x

theorem flowOf_apply (hv : LipschitzWith K v) (hb : ∀ x, ‖v x‖ ≤ L) (t : ℝ) (x : E) :
    flowOf hv hb t x = sol hv hb x t := rfl

/-- The orbits of `flowOf` are the solutions of `v`. -/
theorem hasDerivAt_flowOf (hv : LipschitzWith K v) (hb : ∀ x, ‖v x‖ ≤ L) (x : E) (t : ℝ) :
    HasDerivAt (fun s => flowOf hv hb s x) (v (flowOf hv hb t x)) t :=
  isSol_sol hv hb x t

theorem flowOf_eq_of_isSol (hv : LipschitzWith K v) (hb : ∀ x, ‖v x‖ ≤ L) {γ : ℝ → E}
    (hγ : IsSol v γ) (t₀ t : ℝ) : flowOf hv hb t (γ t₀) = γ (t + t₀) :=
  congrFun (sol_eq_of_isSol hv hb hγ t₀) t

end ConleyCheck.ODE
