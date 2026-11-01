import ConleyCheck.Conley.Index
import ConleyCheck.Conley.Sphere

/-!
# The linear saddle

The flow `ϕ t (u, s) = (eᵗ u, e⁻ᵗ s)` on `ℝᵏ × ℝᵐ` has the box `(D^k × D^m, S^{k-1} × D^m)` as an
index pair for the equilibrium `0`, so its Conley index is `S^k`. This is the model case of
`hasIndex_sphere`.
-/

namespace ConleyCheck.Conley

open Set Metric

variable (k m : ℕ)

abbrev SaddleSpace := EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)

/-- The linear saddle `(u, s) ↦ (eᵗ u, e⁻ᵗ s)`. -/
noncomputable def saddleFlow : Flow ℝ (SaddleSpace k m) where
  toFun t z := (Real.exp t • z.1, Real.exp (-t) • z.2)
  cont' := by
    show Continuous fun p : ℝ × SaddleSpace k m => (Real.exp p.1 • p.2.1, Real.exp (-p.1) • p.2.2)
    fun_prop
  map_add' t₁ t₂ z := Prod.ext
    (show Real.exp (t₁ + t₂) • z.1 = Real.exp t₁ • Real.exp t₂ • z.1 by
      rw [Real.exp_add, mul_smul])
    (show Real.exp (-(t₁ + t₂)) • z.2 = Real.exp (-t₁) • Real.exp (-t₂) • z.2 by
      rw [neg_add, Real.exp_add, mul_smul])
  map_zero' z := by simp

variable {k m}

theorem saddle_norm_fst (t : ℝ) (z : SaddleSpace k m) :
    ‖(saddleFlow k m t z).1‖ = Real.exp t * ‖z.1‖ := by
  show ‖Real.exp t • z.1‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]

theorem saddle_norm_snd (t : ℝ) (z : SaddleSpace k m) :
    ‖(saddleFlow k m t z).2‖ = Real.exp (-t) * ‖z.2‖ := by
  show ‖Real.exp (-t) • z.2‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem saddle_fixed (t : ℝ) : saddleFlow k m t 0 = 0 :=
  Prod.ext (smul_zero _) (smul_zero _)

theorem saddle_snd_le {t : ℝ} (ht : 0 ≤ t) {z : SaddleSpace k m} (hz : ‖z.2‖ ≤ 1) :
    ‖(saddleFlow k m t z).2‖ ≤ 1 := by
  rw [saddle_norm_snd]
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  nlinarith [Real.exp_pos (-t), norm_nonneg z.2]

theorem saddle_Inv_box : Inv (saddleFlow k m) (boxN k m) ⊆ {0} := by
  intro z hz
  have h1 : ∀ t, Real.exp t * ‖z.1‖ ≤ 1 := fun t => by
    have := (hz t).1
    rwa [mem_closedBall_zero_iff, saddle_norm_fst] at this
  have h2 : ∀ t, Real.exp (-t) * ‖z.2‖ ≤ 1 := fun t => by
    have := (hz t).2
    rwa [mem_closedBall_zero_iff, saddle_norm_snd] at this
  have key : ∀ a : ℝ, 0 ≤ a → (∀ r : ℝ, 0 < r → r * a ≤ 1) → a = 0 := by
    intro a ha h
    by_contra hne
    have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm hne)
    have := h (2 / a) (by positivity)
    rw [div_mul_cancel₀ _ hpos.ne'] at this
    norm_num at this
  have hu := key _ (norm_nonneg _) fun r hr => by
    have := h1 (Real.log r)
    rwa [Real.exp_log hr] at this
  have hs := key _ (norm_nonneg _) fun r hr => by
    have := h2 (-Real.log r)
    rwa [neg_neg, Real.exp_log hr] at this
  exact Prod.ext (norm_eq_zero.1 hu) (norm_eq_zero.1 hs)

theorem saddle_zero_mem_interior : (0 : SaddleSpace k m) ∈ interior (boxN k m \ boxL k m) := by
  refine interior_maximal (s := boxN k m \ boxL k m) (t := ball 0 1 ×ˢ ball 0 1) (fun z hz => ⟨⟨ball_subset_closedBall hz.1,
    ball_subset_closedBall hz.2⟩, fun hL => ?_⟩) (isOpen_ball.prod isOpen_ball)
    ⟨mem_ball_self one_pos, mem_ball_self one_pos⟩
  have h1 := mem_sphere_zero_iff_norm.1 hL.1
  have h2 := mem_ball_zero_iff.1 hz.1
  linarith

variable (k m) in
/-- The box is an index pair for the equilibrium of the linear saddle. -/
theorem saddle_isIndexPair : IsIndexPair (saddleFlow k m) {0} (boxN k m) (boxL k m) := by
  have hN : IsCompact (boxN k m) := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hcl : closure (boxN k m \ boxL k m) ⊆ boxN k m := closure_minimal sdiff_subset hN.isClosed
  have hinv : Inv (saddleFlow k m) (closure (boxN k m \ boxL k m)) = {0} := by
    refine subset_antisymm ((Inv_mono hcl).trans saddle_Inv_box) ?_
    rintro _ rfl t
    rw [saddle_fixed]
    exact subset_closure (interior_subset saddle_zero_mem_interior)
  exact
    { isCompact_N := hN
      isCompact_L := (isCompact_sphere _ _).prod (isCompact_closedBall _ _)
      subset := prod_mono sphere_subset_closedBall subset_rfl
      isolating := ⟨hN.of_isClosed_subset isClosed_closure hcl, by
        rw [hinv]
        rintro _ rfl
        exact interior_mono subset_closure saddle_zero_mem_interior⟩
      inv_eq := hinv
      nhds := by
        rintro _ rfl
        exact saddle_zero_mem_interior
      posInv := by
        intro x hx t ht hseg
        have h1 := (hseg t ⟨ht, le_rfl⟩).1
        rw [mem_closedBall_zero_iff, saddle_norm_fst, mem_sphere_zero_iff_norm.1 hx.1,
          mul_one, Real.exp_le_one_iff] at h1
        rw [le_antisymm h1 ht, (saddleFlow k m).map_zero_apply]
        exact hx
      exit := by
        intro x hx t ht hout
        have hu1 : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.1 hx.1
        have hs1 : ‖x.2‖ ≤ 1 := mem_closedBall_zero_iff.1 hx.2
        have hlt : 1 < Real.exp t * ‖x.1‖ := by
          by_contra hc
          push Not at hc
          apply hout
          refine ⟨?_, ?_⟩
          · rw [mem_closedBall_zero_iff, saddle_norm_fst]
            exact hc
          · exact mem_closedBall_zero_iff.2 (saddle_snd_le ht hs1)
        have hpos : 0 < ‖x.1‖ := by
          by_contra hc
          push Not at hc
          nlinarith [Real.exp_pos t, norm_nonneg x.1]
        set s₀ := -Real.log ‖x.1‖
        have hs₀e : Real.exp s₀ * ‖x.1‖ = 1 := by
          rw [Real.exp_neg, Real.exp_log hpos, inv_mul_cancel₀ hpos.ne']
        have hs₀0 : 0 ≤ s₀ := neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) hu1)
        have hs₀t : s₀ ≤ t := by
          have h : Real.exp s₀ * ‖x.1‖ < Real.exp t * ‖x.1‖ := by rw [hs₀e]; exact hlt
          exact (Real.exp_lt_exp.1 (lt_of_mul_lt_mul_right h hpos.le)).le
        refine ⟨s₀, ⟨hs₀0, hs₀t⟩, fun r hr => ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · rw [mem_closedBall_zero_iff, saddle_norm_fst, ← hs₀e]
          exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hr.2) (norm_nonneg _)
        · exact mem_closedBall_zero_iff.2 (saddle_snd_le hr.1 hs1)
        · rw [mem_sphere_zero_iff_norm, saddle_norm_fst]
          exact hs₀e
        · exact mem_closedBall_zero_iff.2 (saddle_snd_le hs₀0 hs1) }

variable (k m) in
/-- The equilibrium of the linear saddle with `k` unstable directions has Conley index `S^k`. -/
theorem saddle_hasIndex : HasIndex (saddleFlow k m) {0} (Sphere k) (Sphere.pt k) :=
  ⟨_, _, saddle_isIndexPair k m, ⟨boxEquiv k m⟩⟩

end ConleyCheck.Conley
