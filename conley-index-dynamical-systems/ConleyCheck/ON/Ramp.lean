import ConleyCheck.ON.Flow
import ConleyCheck.Conley.Rate

/-!
# A parameter shift through `N = 4`: the time-dependent system

The control parameter of `eq:ONy` is made time-dependent, `N = N(σ(s))`, where `σ' = g(σ)` is the
compactified time of Hypothesis `hyp:H`. Here `N` and `g` are only assumed Lipschitz on `[-1, 1]`,
with `N > 1`, `g(±1) = 0` and `g > 0` on `(-1, 1)`.

The system is the autonomous field `(β(y) ψ(N(τ)) F(N(τ), y), g(τ))` on `ℝ² × ℝ`, with `N` and `g`
extended to `ℝ` as constants outside `[-1, 1]`, `β` the bump of `flowON` and `ψ` a bump equal to
`1` on the range of `N`. It is bounded and globally Lipschitz, so it has a global flow, and its
restriction to `ℝ² × [-1, 1]` is a skew product `Φ` over the flow `θ` of `σ' = g(σ)`.

* `isHeight_θ`: `τ` is a height function for `θ`.
* `fiber_top`, `fiber_bot`: the frozen systems at `τ = ±1` are `flowON N(±1)`.
* `isUniformBlock_R`: `R` is a common block with exit set `L`, so Theorem `thm:rate` applies.
-/

open Set Filter Topology Metric Function
open scoped NNReal

namespace ConleyCheck.ON

open ConleyCheck.Conley ConleyCheck.ODE

/-- A real flow preserves the order of the line. -/
theorem flow_mono_real (ϕ : Flow ℝ ℝ) {x y : ℝ} (h : x ≤ y) (t : ℝ) : ϕ t x ≤ ϕ t y := by
  by_contra hlt
  push Not at hlt
  have hc : Continuous fun s => ϕ s y - ϕ s x :=
    (ϕ.continuous continuous_id continuous_const).sub (ϕ.continuous continuous_id continuous_const)
  have h0 : (0 : ℝ) ∈ uIcc (ϕ 0 y - ϕ 0 x) (ϕ t y - ϕ t x) := by
    rw [Flow.map_zero_apply, Flow.map_zero_apply]
    exact mem_uIcc.2 (Or.inr ⟨by linarith, by linarith⟩)
  obtain ⟨s, -, hs⟩ := intermediate_value_uIcc hc.continuousOn h0
  have heq : ϕ s y = ϕ s x := by simp only at hs; linarith
  have := congrArg (ϕ (-s)) heq
  rw [← Flow.map_add, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply,
    Flow.map_zero_apply] at this
  rw [this] at hlt
  exact lt_irrefl _ hlt

/-- The data of a parameter shift: `N` and `g` Lipschitz on `[-1, 1]`, `N > 1`, `g(±1) = 0`
and `g > 0` on `(-1, 1)`. -/
structure Ramp where
  N : ℝ → ℝ
  g : ℝ → ℝ
  KN : ℝ≥0
  Kg : ℝ≥0
  lipN : LipschitzOnWith KN N (Icc (-1) 1)
  lipg : LipschitzOnWith Kg g (Icc (-1) 1)
  one_lt : ∀ τ ∈ Icc (-1 : ℝ) 1, 1 < N τ
  g_one : g 1 = 0
  g_neg_one : g (-1) = 0
  g_pos : ∀ τ ∈ Ioo (-1 : ℝ) 1, 0 < g τ

namespace Ramp

variable (P : Ramp)

/-- The retraction of `ℝ` onto `[-1, 1]`. -/
noncomputable def clamp (τ : ℝ) : ℝ := (projIcc (-1) 1 (by norm_num) τ : ℝ)

theorem clamp_of_mem {τ : ℝ} (h : τ ∈ Icc (-1 : ℝ) 1) : clamp τ = τ := by
  simp [clamp, projIcc_of_mem _ h]

theorem clamp_mem (τ : ℝ) : clamp τ ∈ Icc (-1 : ℝ) 1 := (projIcc (-1) 1 (by norm_num) τ).2

/-- `N`, extended to `ℝ` as constants outside `[-1, 1]`. -/
noncomputable def Nc (τ : ℝ) : ℝ := P.N (clamp τ)

/-- `g`, extended to `ℝ` as constants outside `[-1, 1]`. -/
noncomputable def gc (τ : ℝ) : ℝ := P.g (clamp τ)

theorem lipschitz_Nc : LipschitzWith P.KN P.Nc := by
  have h := P.lipN.to_restrict.comp (LipschitzWith.projIcc (a := -1) (b := 1) (by norm_num))
  rw [mul_one] at h
  exact h

theorem lipschitz_gc : LipschitzWith P.Kg P.gc := by
  have h := P.lipg.to_restrict.comp (LipschitzWith.projIcc (a := -1) (b := 1) (by norm_num))
  rw [mul_one] at h
  exact h

theorem gc_one : P.gc 1 = 0 := by rw [gc, clamp_of_mem (by norm_num), P.g_one]

theorem gc_neg_one : P.gc (-1) = 0 := by rw [gc, clamp_of_mem (by norm_num), P.g_neg_one]

/-- A bound for `|N|` on `[-1, 1]`. -/
noncomputable def bN : ℝ := |P.N 1| + 2 * P.KN

theorem bN_nonneg : 0 ≤ P.bN := by unfold bN; positivity

theorem abs_N_le {τ : ℝ} (h : τ ∈ Icc (-1 : ℝ) 1) : |P.N τ| ≤ P.bN := by
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hd := P.lipN.dist_le_mul τ h 1 h1
  rw [Real.dist_eq, Real.dist_eq] at hd
  have : |τ - 1| ≤ 2 := by rw [abs_le]; constructor <;> linarith [h.1, h.2]
  have hK : (P.KN : ℝ) * |τ - 1| ≤ P.KN * 2 := mul_le_mul_of_nonneg_left this P.KN.2
  unfold bN
  have := abs_sub_abs_le_abs_sub (P.N τ) (P.N 1)
  linarith

theorem abs_Nc_le (τ : ℝ) : |P.Nc τ| ≤ P.bN := P.abs_N_le (clamp_mem τ)

theorem abs_gc_le (τ : ℝ) : |P.gc τ| ≤ 2 * P.Kg := by
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hd := P.lipg.dist_le_mul _ (clamp_mem τ) 1 h1
  rw [Real.dist_eq, Real.dist_eq, P.g_one, sub_zero] at hd
  have : |clamp τ - 1| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith [(clamp_mem τ).1, (clamp_mem τ).2]
  have hK : (P.Kg : ℝ) * |clamp τ - 1| ≤ P.Kg * 2 := mul_le_mul_of_nonneg_left this P.Kg.2
  show |P.g (clamp τ)| ≤ _
  linarith

/-- A bump on `ℝ` equal to `1` on `[-bN, bN] ⊇ N([-1, 1])`. -/
noncomputable def bumpN : ContDiffBump (0 : ℝ) := ⟨P.bN + 1, P.bN + 2, by linarith [P.bN_nonneg],
  by linarith⟩

theorem bumpN_eq_one (τ : ℝ) : P.bumpN (P.Nc τ) = 1 :=
  P.bumpN.one_of_mem_closedBall (by
    rw [mem_closedBall, Real.dist_eq, sub_zero]
    exact (P.abs_Nc_le τ).trans (by show P.bN ≤ P.bN + 1; linarith))

/-- The fiber part `β(y) ψ(n) F(n, y)` of the field, as a function of `(y, n)`. -/
noncomputable def fieldA (q : (ℝ × ℝ) × ℝ) : ℝ × ℝ := (bump q.1 * P.bumpN q.2) • field q.2 q.1

theorem contDiff_fieldA : ContDiff ℝ 1 P.fieldA := by
  have hF : ContDiff ℝ 1 fun q : (ℝ × ℝ) × ℝ => field q.2 q.1 := by
    unfold field f₁ f₂
    fun_prop
  exact ((bump.contDiff.comp contDiff_fst).mul (P.bumpN.contDiff.comp contDiff_snd)).smul hF

theorem hasCompactSupport_fieldA : HasCompactSupport P.fieldA := by
  refine HasCompactSupport.intro ((isCompact_closedBall (0 : ℝ × ℝ) 2).prod
    (isCompact_closedBall (0 : ℝ) (P.bN + 2))) fun q hq => ?_
  simp only [fieldA]
  rcases not_and_or.1 hq with h | h
  · rw [bump.zero_of_le_dist (by
      rw [mem_closedBall] at h
      exact (show bump.rOut = 2 from rfl) ▸ (not_le.1 h).le), zero_mul, zero_smul]
  · rw [P.bumpN.zero_of_le_dist (by
      rw [mem_closedBall] at h
      exact (show P.bumpN.rOut = P.bN + 2 from rfl) ▸ (not_le.1 h).le), mul_zero, zero_smul]

theorem fieldA_eq {x : ℝ × ℝ} (hx : ‖x‖ ≤ 1) (τ : ℝ) :
    P.fieldA (x, P.Nc τ) = field (P.Nc τ) x := by
  have : bump x = 1 := bump.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hx)
  simp [fieldA, this, P.bumpN_eq_one]

theorem fieldA_eq_cutField (x : ℝ × ℝ) (τ : ℝ) :
    P.fieldA (x, P.Nc τ) = cutField (P.Nc τ) x := by
  simp [fieldA, cutField, P.bumpN_eq_one]

/-- The autonomous field on `ℝ² × ℝ`. -/
noncomputable def V (p : (ℝ × ℝ) × ℝ) : (ℝ × ℝ) × ℝ := (P.fieldA (p.1, P.Nc p.2), P.gc p.2)

theorem exists_lipschitz_V : ∃ K : ℝ≥0, LipschitzWith K P.V := by
  obtain ⟨KA, hA⟩ := ContDiff.lipschitzWith_of_hasCompactSupport P.hasCompactSupport_fieldA
    P.contDiff_fieldA one_ne_zero
  have hin : LipschitzWith (max 1 P.KN) fun p : (ℝ × ℝ) × ℝ => (p.1, P.Nc p.2) :=
    LipschitzWith.prod_fst.prodMk (P.lipschitz_Nc.comp LipschitzWith.prod_snd |>.weaken
      (by simp))
  exact ⟨_, (hA.comp hin).prodMk (P.lipschitz_gc.comp LipschitzWith.prod_snd)⟩

theorem exists_bound_V : ∃ L : ℝ≥0, ∀ p, ‖P.V p‖ ≤ L := by
  obtain ⟨C, hC⟩ := P.hasCompactSupport_fieldA.exists_bound_of_continuous
    P.contDiff_fieldA.continuous
  refine ⟨⟨max (max C 0) (2 * P.Kg), le_max_of_le_left (le_max_right _ _)⟩, fun p => ?_⟩
  refine norm_prod_le_iff.2 ⟨(hC _).trans ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · rw [Real.norm_eq_abs]
    exact (P.abs_gc_le _).trans (le_max_right _ _)

/-- The flow of the autonomous field on `ℝ² × ℝ`. -/
noncomputable def Ψ : Flow ℝ ((ℝ × ℝ) × ℝ) :=
  flowOf P.exists_lipschitz_V.choose_spec P.exists_bound_V.choose_spec

theorem hasDerivAt_Ψ (p : (ℝ × ℝ) × ℝ) (t : ℝ) :
    HasDerivAt (fun s => P.Ψ s p) (P.V (P.Ψ t p)) t :=
  hasDerivAt_flowOf _ _ p t

theorem exists_bound_gc : ∃ L : ℝ≥0, ∀ τ, ‖P.gc τ‖ ≤ L :=
  ⟨⟨2 * P.Kg, by positivity⟩, fun τ => by rw [Real.norm_eq_abs]; exact P.abs_gc_le τ⟩

/-- The flow of `σ' = g(σ)` on `ℝ`. -/
noncomputable def β : Flow ℝ ℝ := flowOf P.lipschitz_gc P.exists_bound_gc.choose_spec

theorem hasDerivAt_β (τ t : ℝ) : HasDerivAt (fun s => P.β s τ) (P.gc (P.β t τ)) t :=
  hasDerivAt_flowOf _ _ τ t

theorem Ψ_snd (t : ℝ) (p : (ℝ × ℝ) × ℝ) : (P.Ψ t p).2 = P.β t p.2 := by
  have hγ : IsSol P.gc fun s => (P.Ψ s p).2 := fun s => by
    have h := hasFDerivAt_snd.comp_hasDerivAt s (P.hasDerivAt_Ψ p s)
    exact h
  have := flowOf_eq_of_isSol P.lipschitz_gc P.exists_bound_gc.choose_spec hγ 0 t
  rw [add_zero, Flow.map_zero_apply] at this
  exact this.symm

theorem β_one (t : ℝ) : P.β t 1 = 1 := by
  have hγ : IsSol P.gc fun _ => (1 : ℝ) := fun s => by
    simpa [P.gc_one] using hasDerivAt_const s (1 : ℝ)
  have h := flowOf_eq_of_isSol P.lipschitz_gc P.exists_bound_gc.choose_spec hγ 0 t
  exact h

theorem β_neg_one (t : ℝ) : P.β t (-1) = -1 := by
  have hγ : IsSol P.gc fun _ => (-1 : ℝ) := fun s => by
    simpa [P.gc_neg_one] using hasDerivAt_const s (-1 : ℝ)
  have h := flowOf_eq_of_isSol P.lipschitz_gc P.exists_bound_gc.choose_spec hγ 0 t
  exact h

theorem β_mem {τ : ℝ} (h : τ ∈ Icc (-1 : ℝ) 1) (t : ℝ) : P.β t τ ∈ Icc (-1 : ℝ) 1 :=
  ⟨P.β_neg_one t ▸ flow_mono_real _ h.1 t, P.β_one t ▸ flow_mono_real _ h.2 t⟩

theorem β_mem_Ioo {τ : ℝ} (h : τ ∈ Ioo (-1 : ℝ) 1) (t : ℝ) : P.β t τ ∈ Ioo (-1 : ℝ) 1 := by
  have hm := P.β_mem (Ioo_subset_Icc_self h) t
  have back : ∀ c, P.β (-t) c = c → P.β t τ = c → τ = c := fun c hc he => by
    rw [← hc, ← he, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  refine ⟨lt_of_le_of_ne hm.1 fun he => ?_, lt_of_le_of_ne hm.2 fun he => ?_⟩
  · exact h.1.ne (back _ (P.β_neg_one _) he.symm).symm
  · exact h.2.ne (back _ (P.β_one _) he)

/-- The base flow `θ` of `σ' = g(σ)` on `[-1, 1]`. -/
noncomputable def θ : Flow ℝ Tau where
  toFun t b := ⟨P.β t b, P.β_mem b.2 t⟩
  cont' := (P.β.continuous continuous_fst (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  map_add' t s b := Subtype.ext (P.β.map_add t s b)
  map_zero' b := Subtype.ext (P.β.map_zero_apply b)

theorem θ_apply (t : ℝ) (b : Tau) : (P.θ t b : ℝ) = P.β t b := rfl

theorem isHeight_θ : IsHeight P.θ (fun b => (b : ℝ)) where
  continuous := continuous_subtype_val
  mem b := b.2
  fix b hb t := by
    show P.β t b = b
    rcases hb with h | h <;> rw [h]
    · exact P.β_one t
    · exact P.β_neg_one t
  strict b h1 h2 t ht := by
    show (b : ℝ) < P.β t b
    have hmono : StrictMono fun s => P.β s b :=
      strictMono_of_hasDerivAt_pos (fun s => P.hasDerivAt_β b s) fun s => by
        have hm := P.β_mem_Ioo ⟨h1, h2⟩ s
        rw [gc, clamp_of_mem (Ioo_subset_Icc_self hm)]
        exact P.g_pos _ hm
    have := hmono ht
    simpa using this

/-- The skew-product flow on `ℝ² × [-1, 1]`. -/
noncomputable def Φ : Flow ℝ ((ℝ × ℝ) × Tau) where
  toFun t p := ((P.Ψ t (p.1, (p.2 : ℝ))).1, P.θ t p.2)
  cont' := (continuous_fst.comp (P.Ψ.continuous continuous_fst
    ((continuous_fst.comp continuous_snd).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))).prodMk
    (P.θ.continuous continuous_fst (continuous_snd.comp continuous_snd))
  map_add' t s p := by
    have e : P.Ψ s (p.1, (p.2 : ℝ)) = ((P.Ψ s (p.1, (p.2 : ℝ))).1, ((P.θ s p.2 : Tau) : ℝ)) :=
      Prod.ext rfl (P.Ψ_snd s _)
    show ((P.Ψ (t + s) (p.1, (p.2 : ℝ))).1, P.θ (t + s) p.2) =
      ((P.Ψ t ((P.Ψ s (p.1, (p.2 : ℝ))).1, ((P.θ s p.2 : Tau) : ℝ))).1, P.θ t (P.θ s p.2))
    rw [← e, ← Flow.map_add, ← Flow.map_add]
  map_zero' p := by
    show ((P.Ψ 0 (p.1, (p.2 : ℝ))).1, P.θ 0 p.2) = p
    rw [Flow.map_zero_apply, Flow.map_zero_apply]

theorem Φ_fst (t : ℝ) (p : (ℝ × ℝ) × Tau) : (P.Φ t p).1 = (P.Ψ t (p.1, (p.2 : ℝ))).1 := rfl

theorem isSkew_Φ : IsSkew P.Φ P.θ := fun _ _ => rfl

/-- The `y`-component of a solution of the shifted system solves `y' = F(N(σ), y)` in the
cut-off form. -/
theorem hasDerivAt_Φ_fst (p : (ℝ × ℝ) × Tau) (t : ℝ) :
    HasDerivAt (fun s => (P.Φ s p).1)
      (cutField (P.Nc (P.β t p.2)) (P.Φ t p).1) t := by
  have h := hasFDerivAt_fst.comp_hasDerivAt t (P.hasDerivAt_Ψ (p.1, (p.2 : ℝ)) t)
  have e : (P.V (P.Ψ t (p.1, (p.2 : ℝ)))).1 = cutField (P.Nc (P.β t p.2)) (P.Φ t p).1 := by
    simp only [V]
    rw [P.Ψ_snd, P.fieldA_eq_cutField]
    rfl
  exact e ▸ h

theorem Nc_of_tau (b : Tau) : P.Nc b = P.N b := by rw [Nc, clamp_of_mem b.2]

theorem fiber_eq (b : Tau) (hb : ∀ t, P.θ t b = b) (t : ℝ) (x : ℝ × ℝ) :
    fiberFlow P.isSkew_Φ b hb t x = flowON (P.N b) t x := by
  have hfix : ∀ s, P.β s b = b := fun s => congrArg Subtype.val (hb s)
  have hγ : IsSol (cutField (P.N b)) fun s => (P.Φ s (x, b)).1 := fun s => by
    have h := P.hasDerivAt_Φ_fst (x, b) s
    rwa [hfix, P.Nc_of_tau] at h
  have := flowON_eq_of_isSol (P.N b) hγ 0 t
  rw [add_zero] at this
  rw [show (P.Φ 0 (x, b)).1 = x from congrArg Prod.fst (P.Φ.map_zero_apply _)] at this
  exact this.symm

/-- The frozen system at the IR end `τ = 1` is `flowON N(1)`. -/
theorem fiber_top : fiberFlow P.isSkew_Φ Tau.top (base_top P.isHeight_θ) = flowON (P.N 1) :=
  Flow.ext fun t x => P.fiber_eq _ _ t x

/-- The frozen system at the UV end `τ = -1` is `flowON N(-1)`. -/
theorem fiber_bot : fiberFlow P.isSkew_Φ Tau.bot (base_bot P.isHeight_θ) = flowON (P.N (-1)) :=
  Flow.ext fun t x => P.fiber_eq _ _ t x

theorem hasDerivAt_fst_zero {x : ℝ × ℝ} (hx : ‖x‖ ≤ 1) (b : Tau) :
    HasDerivAt (fun s => ((P.Φ s (x, b)).1).1) (f₁ (P.N b) x.1 x.2) 0 := by
  have h := hasFDerivAt_fst.comp_hasDerivAt 0 (P.hasDerivAt_Φ_fst (x, b) 0)
  rw [show (P.Φ 0 (x, b)).1 = x from congrArg Prod.fst (P.Φ.map_zero_apply _),
    Flow.map_zero_apply, P.Nc_of_tau, cutField_eq hx] at h
  exact h

theorem hasDerivAt_snd_zero {x : ℝ × ℝ} (hx : ‖x‖ ≤ 1) (b : Tau) :
    HasDerivAt (fun s => ((P.Φ s (x, b)).1).2) (f₂ (P.N b) x.1 x.2) 0 := by
  have h := hasFDerivAt_snd.comp_hasDerivAt 0 (P.hasDerivAt_Φ_fst (x, b) 0)
  rw [show (P.Φ 0 (x, b)).1 = x from congrArg Prod.fst (P.Φ.map_zero_apply _),
    Flow.map_zero_apply, P.Nc_of_tau, cutField_eq hx] at h
  exact h

/-- `R` is a common block with exit set `L`: the face inequalities of Proposition `prop:ON`(a)
hold for every `N > 1`. -/
theorem isUniformBlock_R : IsUniformBlock P.Φ blockR blockL where
  isCompact := isCompact_Icc.prod isCompact_Icc
  isClosed_out := isClosed_L
  out_subset _ := mem_R_of_mem_L
  exit x hx b := by
    have hn := norm_le_one_of_mem_R (mem_R_of_mem_L hx)
    exact R_exit (P.one_lt b b.2) hx (congrArg Prod.fst (P.Φ.map_zero_apply _))
      (P.hasDerivAt_fst_zero hn b) (P.hasDerivAt_snd_zero hn b)
  entrance x hxR hint hL b := by
    have hn := norm_le_one_of_mem_R hxR
    exact R_entrance (P.one_lt b b.2) hxR hint hL (congrArg Prod.fst (P.Φ.map_zero_apply _))
      (P.hasDerivAt_fst_zero hn b) (P.hasDerivAt_snd_zero hn b)

/-- `S = Inv(R × [-1, 1])`. -/
abbrev S : Set ((ℝ × ℝ) × Tau) := Inv P.Φ (blockR ×ˢ univ)

/-- The flow of the double. -/
noncomputable abbrev D : Flow ℝ ((ℝ × ℝ) × Dbl) := dblΦ P.isSkew_Φ P.isHeight_θ

/-- `K_+ = B_{N(1)}`. -/
theorem Kp_eq : {x | (x, Tau.top) ∈ P.S} = boundedOrbits (P.N 1) := by
  rw [S, ← Inv_fiber_block P.isSkew_Φ Tau.top (base_top P.isHeight_θ), fiber_top,
    Inv_R_eq (P.one_lt 1 (by norm_num))]

/-- `K_- = B_{N(-1)}`. -/
theorem Km_eq : {x | (x, Tau.bot) ∈ P.S} = boundedOrbits (P.N (-1)) := by
  rw [S, ← Inv_fiber_block P.isSkew_Φ Tau.bot (base_bot P.isHeight_θ), fiber_bot,
    Inv_R_eq (P.one_lt (-1) (by norm_num))]

/-- Proposition `prop:ONramp`(i), index part: `S♮` is an isolated invariant set of the double with
`CH_*(S♮) = 0`, `K_± = B_{N(±1)}` have trivial homology index, and the transport map `Ψ` of the
exact sequence of Theorem `thm:transport` is zero. -/
theorem prop_ONramp_i_index (K : Type) [Ring K] :
    ∃ (hSn : IsIsolatedInvariantSet P.D (snat P.S))
      (hKp : IsIsolatedInvariantSet (fiberFlow P.isSkew_Φ Tau.top (base_top P.isHeight_θ))
        {x | (x, Tau.top) ∈ P.S})
      (hKm : IsIsolatedInvariantSet (fiberFlow P.isSkew_Φ Tau.bot (base_bot P.isHeight_θ))
        {x | (x, Tau.bot) ∈ P.S})
      (Ψ : ∀ k, homologyIndex K _ hKm k →ₗ[K] homologyIndex K _ hKp k)
      (i : ∀ k, homologyIndex K _ hKp k →ₗ[K] homologyIndex K _ hSn k)
      (p : ∀ k, homologyIndex K _ hSn (k + 1) →ₗ[K] homologyIndex K _ hKm k),
      (∀ k, Exact (Ψ k) (i k)) ∧ (∀ k, Exact (i (k + 1)) (p k)) ∧ (∀ k, Exact (p k) (Ψ k)) ∧
        (∀ k, Subsingleton (homologyIndex K _ hSn k)) ∧
        (∀ k, Subsingleton (homologyIndex K _ hKp k)) ∧
        (∀ k, Subsingleton (homologyIndex K _ hKm k)) ∧ ∀ k, Ψ k = 0 := by
  obtain ⟨hSn, hKp, hKm, Ψ, i, p, h1, h2, h3, hz, -⟩ :=
    rate_transport P.isSkew_Φ P.isHeight_θ K P.isUniformBlock_R
  obtain ⟨-, hKp', hKm', -, -, hiso⟩ := rate_index P.isSkew_Φ P.isHeight_θ K P.isUniformBlock_R
  have hR := redH_subsingleton K pointedContractible_R
  have hp : ∀ k, Subsingleton (homologyIndex K _ hKp k) := fun k => by
    have := hR k
    exact (hiso k).1.some.toEquiv.subsingleton
  have hm : ∀ k, Subsingleton (homologyIndex K _ hKm k) := fun k => by
    have := hR k
    exact (hiso k).2.some.toEquiv.subsingleton
  exact ⟨hSn, hKp, hKm, Ψ, i, p, h1, h2, h3, hz, hp, hm, fun k => by
    have := hm k
    ext x
    rw [Subsingleton.elim x 0]
    simp⟩

end Ramp

end ConleyCheck.ON
