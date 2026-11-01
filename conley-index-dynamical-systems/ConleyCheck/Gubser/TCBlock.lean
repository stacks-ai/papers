import ConleyCheck.Gubser.TCInv
import ConleyCheck.Conley.IsolatingBlock
import ConleyCheck.ODE.TimeChange

/-!
# Lemma `lem:TC`: the blocks `N^±`

We work with an abstract model `TCModel c X` of the chart `eq:flowTp` near a `T`-axis curve,
namely a flow on a space `X` with continuous coordinates `u`, `v ≥ 0` and `τ ∈ [-1, 1]` along
whose orbits `(u, v, τ)` solves `b · eq:flowTp`, `dτ/ds = b v (1 - τ²)` on `{|u|, v < 1/c}`, for a
continuous time change `b` that is positive there, and for which `TC = {u = v = 0}` is invariant.
The doubled base `θ ∈ S¹` (with `τ = cos θ`), the interval `τ ∈ [-1, 1]` of part (iii)
(`ConleyCheck.Gubser.TCFlow`) and the doubled compactified flow near `TC^+`
(`ConleyCheck.Gubser.GlobalTC`) are such models.

* `isBlock_N`: `N = {|u| ≤ δ, v ≤ δ'}` is an isolating block with exit set
  `L = {v = δ', τ ≥ 0}` (part (i)), including the external tangency at `τ = 0`.
* `isBlock_N_reverse`: for the time-reversed flow, `N` is an isolating block with exit set
  `E = {|u| = δ} ∪ {v = δ', τ ≤ 0}`. Under the reversor `S̃` this is the block `N^-` of part (ii)
  with exit set `L^-` (`ConleyCheck.Gubser.TCFlow`).
* `Inv_N`: `Inv(N) = TC = {u = v = 0}` for both time directions.
-/

open Set Filter Topology Real

namespace ConleyCheck.Gubser

open ConleyCheck.ODE ConleyCheck.Conley

/-- A flow whose orbits solve a positive time change of `eq:flowTp` near `TC`, see the module
docstring. -/
structure TCModel (c : ℝ) (X : Type*) [TopologicalSpace X] where
  ϕ : Flow ℝ X
  u : X → ℝ
  v : X → ℝ
  τ : X → ℝ
  b : X → ℝ
  cu : Continuous u
  cv : Continuous v
  cτ : Continuous τ
  cb : Continuous b
  v_nonneg : ∀ p, 0 ≤ v p
  τ_ge : ∀ p, -1 ≤ τ p
  τ_le : ∀ p, τ p ≤ 1
  b_pos : ∀ p, |u p| < 1 / c → v p < 1 / c → 0 < b p
  du : ∀ p t, |u (ϕ t p)| < 1 / c → v (ϕ t p) < 1 / c → HasDerivAt (fun s => u (ϕ s p))
    (b (ϕ t p) * Fu c (u (ϕ t p)) (v (ϕ t p)) (τ (ϕ t p))) t
  dv : ∀ p t, |u (ϕ t p)| < 1 / c → v (ϕ t p) < 1 / c → HasDerivAt (fun s => v (ϕ s p))
    (b (ϕ t p) * Fv (u (ϕ t p)) (v (ϕ t p)) (τ (ϕ t p))) t
  dτ : ∀ p t, |u (ϕ t p)| < 1 / c → v (ϕ t p) < 1 / c → HasDerivAt (fun s => τ (ϕ s p))
    (b (ϕ t p) * (v (ϕ t p) * (1 - τ (ϕ t p) ^ 2))) t
  tc_inv : ∀ p, u p = 0 → v p = 0 → ∀ t, u (ϕ t p) = 0 ∧ v (ϕ t p) = 0
  compact : ∀ a a', IsCompact {p | |u p| ≤ a ∧ v p ≤ a'}

/-- The field `tc_inv` for coordinates that solve the cut-off equations everywhere. -/
theorem tc_inv_of_global {X : Type*} [TopologicalSpace X] {c : ℝ} {ϕ : Flow ℝ X}
    {u v τ b : X → ℝ} (cu : Continuous u) (cv : Continuous v) (cτ : Continuous τ)
    (cb : Continuous b)
    (du : ∀ p t, HasDerivAt (fun s => u (ϕ s p)) (b (ϕ t p) * Fu c (u (ϕ t p)) (v (ϕ t p)) (τ (ϕ t p))) t)
    (dv : ∀ p t, HasDerivAt (fun s => v (ϕ s p)) (b (ϕ t p) * Fv (u (ϕ t p)) (v (ϕ t p)) (τ (ϕ t p))) t)
    (p : X) (hu : u p = 0) (hv : v p = 0) (t : ℝ) : u (ϕ t p) = 0 ∧ v (ϕ t p) = 0 := by
  have hγ : Continuous fun s => ϕ s p := ϕ.continuous continuous_id continuous_const
  have hv' : ∀ s, v (ϕ s p) = 0 := fun s =>
    eq_zero_of_linear_all (T := fun s => v (ϕ s p))
      (k := fun s => b (ϕ s p) * (τ (ϕ s p) * (2 * v (ϕ s p) - u (ϕ s p)) / 3))
      (fun s => (dv p s).congr_deriv (by simp only [Fv]; ring))
      ((cb.comp hγ).mul (((cτ.comp hγ).mul (((cv.comp hγ).const_mul 2).sub
        (cu.comp hγ))).div_const 3))
      (s₀ := 0) (by simpa [Flow.map_zero_apply] using hv) s
  have hu' : ∀ s, u (ϕ s p) = 0 := fun s =>
    eq_zero_of_linear_all (T := fun s => u (ϕ s p))
      (k := fun s => -(b (ϕ s p) * (1 / c + 5 / 3 * u (ϕ s p) * τ (ϕ s p))))
      (fun s => (du p s).congr_deriv (by
        rw [hv' s, (circle_at_infinity c _ _).1]; ring))
      ((cb.comp hγ).mul (continuous_const.add
        ((continuous_const.mul (cu.comp hγ)).mul (cτ.comp hγ)))).neg
      (s₀ := 0) (by simpa [Flow.map_zero_apply] using hu) s
  exact ⟨hu' t, hv' t⟩

/-! ## Assembling blocks from one-sided statements -/

theorem isBlock_of_eventually {X : Type*} [TopologicalSpace X] {ϕ : Flow ℝ X} {N L : Set X}
    (hN : IsCompact N) (hL : IsClosed L) (hLN : L ⊆ N)
    (hexit : ∀ p ∈ L, ∀ᶠ t in 𝓝[>] (0 : ℝ), ϕ t p ∉ N)
    (hent : ∀ p ∈ N, p ∉ interior N → p ∉ L →
      (∀ᶠ t in 𝓝[<] (0 : ℝ), ϕ t p ∉ N) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ϕ t p ∈ N) :
    IsBlock ϕ N L where
  isCompact := hN
  isClosed_L := hL
  subset := hLN
  exit p hp := by
    obtain ⟨ε, hε, h⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hexit p hp)
    exact ⟨ε, hε, fun t ht => h ht⟩
  entrance p hp hint hpL := by
    obtain ⟨h1, h2⟩ := hent p hp hint hpL
    exact exists_eps h1 h2

theorem eventually_neg_gt {P : ℝ → Prop} (h : ∀ᶠ t in 𝓝[<] (0 : ℝ), P t) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), P (-t) := by
  have := tendsto_neg_nhdsGT (a := (0 : ℝ))
  rw [neg_zero] at this
  exact this.eventually h

theorem eventually_neg_lt {P : ℝ → Prop} (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), P t) :
    ∀ᶠ t in 𝓝[<] (0 : ℝ), P (-t) := by
  have := tendsto_neg_nhdsLT (a := (0 : ℝ))
  rw [neg_zero] at this
  exact this.eventually h

/-- The reversed flow version of `isBlock_of_eventually`. -/
theorem isBlock_reverse_of_eventually {X : Type*} [TopologicalSpace X] {ϕ : Flow ℝ X}
    {N L : Set X} (hN : IsCompact N) (hL : IsClosed L) (hLN : L ⊆ N)
    (hexit : ∀ p ∈ L, ∀ᶠ t in 𝓝[<] (0 : ℝ), ϕ t p ∉ N)
    (hent : ∀ p ∈ N, p ∉ interior N → p ∉ L →
      (∀ᶠ t in 𝓝[>] (0 : ℝ), ϕ t p ∉ N) ∧ ∀ᶠ t in 𝓝[<] (0 : ℝ), ϕ t p ∈ N) :
    IsBlock ϕ.reverse N L :=
  isBlock_of_eventually hN hL hLN (fun p hp => eventually_neg_gt (hexit p hp))
    fun p hp hint hpL => ⟨eventually_neg_lt (hent p hp hint hpL).1,
      eventually_neg_gt (hent p hp hint hpL).2⟩

theorem Inv_reverse {X : Type*} [TopologicalSpace X] (ϕ : Flow ℝ X) (N : Set X) :
    Inv ϕ.reverse N = Inv ϕ N := by
  ext p
  exact ⟨fun h t => by simpa using h (-t), fun h t => h (-t)⟩

namespace TCModel

variable {c δ δ' : ℝ} {X : Type*} [TopologicalSpace X] (M : TCModel c X)

/-- The block `N^+ = {|u| ≤ δ, v ≤ δ'}`. -/
def N (δ δ' : ℝ) : Set X := {p | |M.u p| ≤ δ ∧ M.v p ≤ δ'}

/-- Its exit set `L^+ = {v = δ', τ ≥ 0}`. -/
def L (δ δ' : ℝ) : Set X := {p | |M.u p| ≤ δ ∧ M.v p = δ' ∧ 0 ≤ M.τ p}

/-- The exit set `{|u| = δ} ∪ {v = δ', τ ≤ 0}` of `N` for the reversed flow. -/
def E (δ δ' : ℝ) : Set X :=
  {p | |M.u p| ≤ δ ∧ M.v p ≤ δ' ∧ (|M.u p| = δ ∨ (M.v p = δ' ∧ M.τ p ≤ 0))}

/-- The `T`-axis curve `TC = {u = v = 0}`. -/
def TC : Set X := {p | M.u p = 0 ∧ M.v p = 0}

theorem L_subset : M.L δ δ' ⊆ M.N δ δ' := fun _ h => ⟨h.1, h.2.1.le⟩

theorem E_subset : M.E δ δ' ⊆ M.N δ δ' := fun _ h => ⟨h.1, h.2.1⟩

theorem isClosed_L : IsClosed (M.L δ δ') :=
  (isClosed_le (continuous_abs.comp M.cu) continuous_const).inter
    ((isClosed_eq M.cv continuous_const).inter (isClosed_le continuous_const M.cτ))

theorem isClosed_E : IsClosed (M.E δ δ') :=
  (isClosed_le (continuous_abs.comp M.cu) continuous_const).inter
    ((isClosed_le M.cv continuous_const).inter
      ((isClosed_eq (continuous_abs.comp M.cu) continuous_const).union
        ((isClosed_eq M.cv continuous_const).inter (isClosed_le M.cτ continuous_const))))

theorem isCompact_N : IsCompact (M.N δ δ') := M.compact δ δ'

theorem not_interior {p : X} (hp : p ∉ interior (M.N δ δ')) : ¬(|M.u p| < δ ∧ M.v p < δ') := by
  intro h
  have ho : IsOpen {q | |M.u q| < δ ∧ M.v q < δ'} :=
    (isOpen_lt (continuous_abs.comp M.cu) continuous_const).inter
      (isOpen_lt M.cv continuous_const)
  exact hp (interior_maximal (fun q (hq : q ∈ {q | |M.u q| < δ ∧ M.v q < δ'}) =>
    (⟨hq.1.le, hq.2.le⟩ : q ∈ M.N δ δ')) ho h)

/-! ## The field near `N` -/

section Local

variable (H : TCHyp c δ δ')
include H

theorem delta'_lt : δ' < 1 / c := by
  have hc := H.hc
  have : 15 / (16 * c) < 1 / c := by
    rw [div_lt_div_iff₀ (by positivity) hc]; nlinarith
  linarith [H.h2]

theorem mem_W {p : X} (hp : p ∈ M.N δ δ') : |M.u p| < 1 / c ∧ M.v p < 1 / c :=
  ⟨hp.1.trans_lt (H.h1.trans (delta'_lt H)), hp.2.trans_lt (delta'_lt H)⟩

theorem b_pos_of {p : X} (hp : p ∈ M.N δ δ') : 0 < M.b p :=
  M.b_pos p (mem_W M H hp).1 (mem_W M H hp).2

omit H in
theorem du_of {p : X} {t : ℝ} (h1 : |M.u (M.ϕ t p)| < 1 / c) (h2 : M.v (M.ϕ t p) < 1 / c) :
    HasDerivAt (fun s => M.u (M.ϕ s p))
      (M.b (M.ϕ t p) * Fu c (M.u (M.ϕ t p)) (M.v (M.ϕ t p)) (M.τ (M.ϕ t p))) t :=
  M.du p t h1 h2

omit H in
theorem dv_of {p : X} {t : ℝ} (h1 : |M.u (M.ϕ t p)| < 1 / c) (h2 : M.v (M.ϕ t p) < 1 / c) :
    HasDerivAt (fun s => M.v (M.ϕ s p))
      (M.b (M.ϕ t p) * Fv (M.u (M.ϕ t p)) (M.v (M.ϕ t p)) (M.τ (M.ϕ t p))) t :=
  M.dv p t h1 h2

omit H in
theorem dτ_of {p : X} {t : ℝ} (h1 : |M.u (M.ϕ t p)| < 1 / c) (h2 : M.v (M.ϕ t p) < 1 / c) :
    HasDerivAt (fun s => M.τ (M.ϕ s p))
      (M.b (M.ϕ t p) * (M.v (M.ϕ t p) * (1 - M.τ (M.ϕ t p) ^ 2))) t :=
  M.dτ p t h1 h2

theorem du0 {p : X} (hp : p ∈ M.N δ δ') :
    HasDerivAt (fun s => M.u (M.ϕ s p)) (M.b p * Fu c (M.u p) (M.v p) (M.τ p)) 0 := by
  have h := mem_W M H hp
  have := du_of M (p := p) (t := 0) (by rw [Flow.map_zero_apply]; exact h.1)
    (by rw [Flow.map_zero_apply]; exact h.2)
  rwa [Flow.map_zero_apply] at this

theorem dv0 {p : X} (hp : p ∈ M.N δ δ') :
    HasDerivAt (fun s => M.v (M.ϕ s p)) (M.b p * Fv (M.u p) (M.v p) (M.τ p)) 0 := by
  have h := mem_W M H hp
  have := dv_of M (p := p) (t := 0) (by rw [Flow.map_zero_apply]; exact h.1)
    (by rw [Flow.map_zero_apply]; exact h.2)
  rwa [Flow.map_zero_apply] at this

/-- Near a point of `N` the orbit stays in the region where `b > 0`. -/
theorem eventually_W {p : X} (hp : p ∈ M.N δ δ') :
    ∀ᶠ t in 𝓝 (0 : ℝ), |M.u (M.ϕ t p)| < 1 / c ∧ M.v (M.ϕ t p) < 1 / c := by
  have ho : IsOpen {q | |M.u q| < 1 / c ∧ M.v q < 1 / c} :=
    (isOpen_lt (continuous_abs.comp M.cu) continuous_const).inter
      (isOpen_lt M.cv continuous_const)
  have hc : ContinuousAt (fun t => M.ϕ t p) 0 :=
    (M.ϕ.continuous continuous_id continuous_const).continuousAt
  have := hc.eventually_mem (ho.mem_nhds (by rw [Flow.map_zero_apply]; exact mem_W M H hp))
  exact this

omit M H in
/-- The derivative of `Fv` along a curve at a point with `τ = 0`. -/
theorem hasDerivAt_Fv_tangency {u v τ : ℝ → ℝ} {u' v' τ' s : ℝ} (hu : HasDerivAt u u' s)
    (hv : HasDerivAt v v' s) (hτ : HasDerivAt τ τ' s) (h0 : τ s = 0) :
    HasDerivAt (fun r => Fv (u r) (v r) (τ r)) (v s / 3 * (2 * v s - u s) * τ') s := by
  have h := ((hv.mul hτ).div_const 3).mul ((hv.const_mul 2).sub hu)
  convert h using 1
  · funext r; simp only [Fv, Pi.mul_apply, Pi.sub_apply]
  · simp only [Pi.mul_apply, Pi.sub_apply, h0]; ring

/-- The external tangency on the top face: at `v = δ'`, `τ = 0` the coordinate `v` has a strict
local minimum along the orbit. -/
theorem tangency {p : X} (hp : p ∈ M.N δ δ') (hv : M.v p = δ') (hτ : M.τ p = 0) :
    (∀ᶠ t in 𝓝[>] (0 : ℝ), δ' < M.v (M.ϕ t p)) ∧ ∀ᶠ t in 𝓝[<] (0 : ℝ), δ' < M.v (M.ϕ t p) := by
  have hW := eventually_W M H hp
  set g := fun s => M.v (M.ϕ s p)
  set h := fun s => Fv (M.u (M.ϕ s p)) (M.v (M.ϕ s p)) (M.τ (M.ϕ s p))
  have hW0 := mem_W M H hp
  have h0' : |M.u (M.ϕ 0 p)| < 1 / c := by rw [Flow.map_zero_apply]; exact hW0.1
  have h0'' : M.v (M.ϕ 0 p) < 1 / c := by rw [Flow.map_zero_apply]; exact hW0.2
  have hτ0 : M.τ (M.ϕ 0 p) = 0 := by rw [Flow.map_zero_apply]; exact hτ
  have hD := hasDerivAt_Fv_tangency (du_of M h0' h0'') (dv_of M h0' h0'') (dτ_of M h0' h0'') hτ0
  simp only [Flow.map_zero_apply, hv, hτ] at hD
  have hb := b_pos_of M H hp
  have hD0 : 0 < δ' / 3 * (2 * δ' - M.u p) * (M.b p * (δ' * (1 - 0 ^ 2))) := by
    have := (H.top_face (τ := M.τ p) hp.1).1
    have := H.hδ'
    positivity
  have hh0 : h 0 = 0 := by simp only [h, Flow.map_zero_apply, hτ]; simp [Fv]
  obtain ⟨hpos, hneg⟩ := eventually_sign hD.neg (neg_lt_zero.2 hD0)
  have hg0 : g 0 = δ' := by simp [g, Flow.map_zero_apply, hv]
  have hderiv : ∀ s, |M.u (M.ϕ s p)| < 1 / c ∧ M.v (M.ϕ s p) < 1 / c →
      HasDerivAt g (M.b (M.ϕ s p) * h s) s := fun s hs => dv_of M hs.1 hs.2
  have hgc : Continuous g := M.cv.comp (M.ϕ.continuous continuous_id continuous_const)
  constructor
  · have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), (|M.u (M.ϕ s p)| < 1 / c ∧ M.v (M.ϕ s p) < 1 / c) ∧
        0 < h s := by
      filter_upwards [nhdsWithin_le_nhds hW, hpos] with s hs1 hs2
      refine ⟨hs1, ?_⟩
      have : -h s < -h 0 := hs2
      linarith
    obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    refine mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨ε, hε, fun t ht => ?_⟩
    have hmono : StrictMonoOn g (Icc 0 t) :=
      strictMonoOn_of_deriv_pos (convex_Icc 0 t) hgc.continuousOn fun x hx => by
        rw [interior_Icc] at hx
        have hx' := hsub ⟨hx.1, hx.2.trans ht.2⟩
        rw [(hderiv x hx'.1).deriv]
        exact mul_pos (M.b_pos _ hx'.1.1 hx'.1.2) hx'.2
    have := hmono ⟨le_rfl, ht.1.le⟩ ⟨ht.1.le, le_rfl⟩ ht.1
    rw [hg0] at this
    exact this
  · have hev : ∀ᶠ s in 𝓝[<] (0 : ℝ), (|M.u (M.ϕ s p)| < 1 / c ∧ M.v (M.ϕ s p) < 1 / c) ∧
        h s < 0 := by
      filter_upwards [nhdsWithin_le_nhds hW, hneg] with s hs1 hs2
      refine ⟨hs1, ?_⟩
      have : -h 0 < -h s := hs2
      linarith
    obtain ⟨ε, hε, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
    refine mem_nhdsLT_iff_exists_Ioo_subset.2 ⟨ε, hε, fun t ht => ?_⟩
    have hanti : StrictAntiOn g (Icc t 0) :=
      strictAntiOn_of_deriv_neg (convex_Icc t 0) hgc.continuousOn fun x hx => by
        rw [interior_Icc] at hx
        have hx' := hsub ⟨ht.1.trans hx.1, hx.2⟩
        rw [(hderiv x hx'.1).deriv]
        exact mul_neg_of_pos_of_neg (M.b_pos _ hx'.1.1 hx'.1.2) hx'.2
    have := hanti ⟨le_rfl, ht.2.le⟩ ⟨ht.2.le, le_rfl⟩ ht.2
    rw [hg0] at this
    exact this

/-- On the top face with `τ > 0` the orbit exits forward. -/
theorem top_exit_fwd {p : X} (hp : p ∈ M.N δ δ') (hv : M.v p = δ') (hτ : 0 < M.τ p) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), δ' < M.v (M.ϕ t p) := by
  have hd : 0 < M.b p * Fv (M.u p) (M.v p) (M.τ p) := by
    refine mul_pos (b_pos_of M H hp) ?_
    rw [hv, (H.top_face (τ := M.τ p) hp.1).2]
    exact mul_pos (div_pos (mul_pos H.hδ' hτ) (by norm_num)) (H.top_face (τ := M.τ p) hp.1).1
  have := (eventually_sign (dv0 M H hp).neg (neg_lt_zero.2 hd)).1
  filter_upwards [this] with s hs
  simp only [Pi.neg_apply, Flow.map_zero_apply, neg_lt_neg_iff] at hs
  rw [hv] at hs; exact hs

/-- On the top face with `τ < 0` the orbit exits backward. -/
theorem top_exit_bwd {p : X} (hp : p ∈ M.N δ δ') (hv : M.v p = δ') (hτ : M.τ p < 0) :
    ∀ᶠ t in 𝓝[<] (0 : ℝ), δ' < M.v (M.ϕ t p) := by
  have hd : M.b p * Fv (M.u p) (M.v p) (M.τ p) < 0 := by
    refine mul_neg_of_pos_of_neg (b_pos_of M H hp) ?_
    rw [hv, (H.top_face (τ := M.τ p) hp.1).2]
    exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg H.hδ' hτ)
      (by norm_num)) (H.top_face (τ := M.τ p) hp.1).1
  have := (eventually_sign (dv0 M H hp) hd).2
  filter_upwards [this] with s hs
  simp only [Flow.map_zero_apply] at hs
  rw [hv] at hs; exact hs

/-- On the faces `|u| = δ` the orbit exits backward. -/
theorem side_exit_bwd {p : X} (hp : p ∈ M.N δ δ') (hu : |M.u p| = δ) :
    ∀ᶠ t in 𝓝[<] (0 : ℝ), δ < |M.u (M.ϕ t p)| := by
  obtain ⟨hf1, hf2⟩ := H.face_entrance (M.v_nonneg p) hp.2 (M.τ_ge p) (M.τ_le p)
  rcases abs_eq H.hδ.le |>.1 hu with h | h
  · have hd : M.b p * Fu c (M.u p) (M.v p) (M.τ p) < 0 := by
      rw [h]; exact mul_neg_of_pos_of_neg (b_pos_of M H hp) hf1
    filter_upwards [(eventually_sign (du0 M H hp) hd).2] with s hs
    simp only [Flow.map_zero_apply] at hs
    rw [h] at hs
    exact hs.trans_le (le_abs_self _)
  · have hd : -(M.b p * Fu c (M.u p) (M.v p) (M.τ p)) < 0 := by
      rw [h]; linarith [mul_pos (b_pos_of M H hp) hf2]
    filter_upwards [(eventually_sign (du0 M H hp).neg hd).2] with s hs
    simp only [Pi.neg_apply, Flow.map_zero_apply] at hs
    rw [h, neg_neg] at hs
    exact hs.trans_le (neg_le_abs _)

end Local

/-! ## Part (i): `N` is a block with exit set `L` -/

theorem isBlock_N (H : TCHyp c δ δ') : IsBlock M.ϕ (M.N δ δ') (M.L δ δ') := by
  refine isBlock_of_eventually M.isCompact_N M.isClosed_L M.L_subset (fun p hp => ?_)
    fun p hp hint hpL => ?_
  · have hpN := M.L_subset hp
    obtain ⟨-, hv, hτ⟩ := hp
    have key : ∀ᶠ t in 𝓝[>] (0 : ℝ), δ' < M.v (M.ϕ t p) := by
      rcases hτ.lt_or_eq with hτ | hτ
      · exact top_exit_fwd M H hpN hv hτ
      · exact (tangency M H hpN hv hτ.symm).1
    filter_upwards [key] with t ht hN using absurd hN.2 (not_le.2 ht)
  · have hni := M.not_interior hint
    have hτ : M.v p = δ' → M.τ p < 0 := fun hv => by
      by_contra h; push Not at h; exact hpL ⟨hp.1, hv, h⟩
    refine ⟨?_, ?_⟩
    · by_cases hu : |M.u p| = δ
      · filter_upwards [side_exit_bwd M H hp hu] with t ht hN using absurd hN.1 (not_le.2 ht)
      · have hv : M.v p = δ' := by
          by_contra hv
          exact hni ⟨lt_of_le_of_ne hp.1 hu, lt_of_le_of_ne hp.2 hv⟩
        filter_upwards [top_exit_bwd M H hp hv (hτ hv)] with t ht hN
        exact absurd hN.2 (not_le.2 ht)
    · obtain ⟨hf1, hf2⟩ := H.face_entrance (M.v_nonneg p) hp.2 (M.τ_ge p) (M.τ_le p)
      have hb := b_pos_of M H hp
      have e1 := eventually_le_right (b := δ) (du0 M H hp) (by
          rw [Flow.map_zero_apply]; exact (abs_le.1 hp.1).2)
        (fun h => by
          rw [Flow.map_zero_apply] at h; rw [h]; exact mul_neg_of_pos_of_neg hb hf1)
      have e2 := eventually_le_right (b := δ) (du0 M H hp).neg (by
          simp only [Pi.neg_apply, Flow.map_zero_apply]; linarith [(abs_le.1 hp.1).1])
        (fun h => by
          simp only [Pi.neg_apply, Flow.map_zero_apply] at h
          rw [show M.u p = -δ by linarith]; linarith [mul_pos hb hf2])
      have e3 := eventually_le_right (b := δ') (dv0 M H hp) (by
          rw [Flow.map_zero_apply]; exact hp.2)
        (fun h => by
          rw [Flow.map_zero_apply] at h
          have hτ' := hτ h
          refine mul_neg_of_pos_of_neg hb ?_
          rw [h, (H.top_face (τ := M.τ p) hp.1).2]
          exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg H.hδ' hτ')
            (by norm_num)) (H.top_face (τ := M.τ p) hp.1).1)
      filter_upwards [e1, e2, e3] with t h1 h2 h3
      simp only [Pi.neg_apply] at h2
      exact ⟨abs_le.2 ⟨by linarith, h1⟩, h3⟩

/-! ## Part (ii): the reversed flow -/

theorem isBlock_N_reverse (H : TCHyp c δ δ') : IsBlock M.ϕ.reverse (M.N δ δ') (M.E δ δ') := by
  refine isBlock_reverse_of_eventually M.isCompact_N M.isClosed_E M.E_subset (fun p hp => ?_)
    fun p hp hint hpE => ?_
  · have hpN := M.E_subset hp
    obtain ⟨-, -, hu | ⟨hv, hτ⟩⟩ := hp
    · filter_upwards [side_exit_bwd M H hpN hu] with t ht hN using absurd hN.1 (not_le.2 ht)
    · have key : ∀ᶠ t in 𝓝[<] (0 : ℝ), δ' < M.v (M.ϕ t p) := by
        rcases hτ.lt_or_eq with hτ | hτ
        · exact top_exit_bwd M H hpN hv hτ
        · exact (tangency M H hpN hv hτ).2
      filter_upwards [key] with t ht hN using absurd hN.2 (not_le.2 ht)
  · have hni := M.not_interior hint
    have hu : |M.u p| < δ := lt_of_le_of_ne hp.1 fun h => hpE ⟨hp.1, hp.2, Or.inl h⟩
    have hv : M.v p = δ' := by
      by_contra hv; exact hni ⟨hu, lt_of_le_of_ne hp.2 hv⟩
    have hτ : 0 < M.τ p := by
      by_contra h; push Not at h; exact hpE ⟨hp.1, hp.2, Or.inr ⟨hv, h⟩⟩
    refine ⟨?_, ?_⟩
    · filter_upwards [top_exit_fwd M H hp hv hτ] with t ht hN using absurd hN.2 (not_le.2 ht)
    · have hd : 0 < M.b p * Fv (M.u p) (M.v p) (M.τ p) := by
        refine mul_pos (b_pos_of M H hp) ?_
        rw [hv, (H.top_face (τ := M.τ p) hp.1).2]
        exact mul_pos (div_pos (mul_pos H.hδ' hτ) (by norm_num)) (H.top_face (τ := M.τ p) hp.1).1
      have e1 := eventually_le_left (b := δ') (dv0 M H hp) (by
          rw [Flow.map_zero_apply]; exact hp.2) fun _ => hd
      have hcu : ContinuousAt (fun t => |M.u (M.ϕ t p)|) 0 :=
        ((continuous_abs.comp M.cu).comp
          (M.ϕ.continuous continuous_id continuous_const)).continuousAt
      have e2 : ∀ᶠ t in 𝓝 (0 : ℝ), |M.u (M.ϕ t p)| < δ :=
        hcu.eventually (gt_mem_nhds (by simpa [Flow.map_zero_apply] using hu))
      filter_upwards [e1, nhdsWithin_le_nhds e2] with t h1 h2 using ⟨h2.le, h1⟩

/-! ## `Inv(N) = TC` -/

theorem Inv_N (H : TCHyp c δ δ') : Inv M.ϕ (M.N δ δ') = M.TC := by
  ext p
  constructor
  · intro hp
    have hW : ∀ t, |M.u (M.ϕ t p)| < 1 / c ∧ M.v (M.ϕ t p) < 1 / c := fun t =>
      mem_W M H (hp t)
    have hp0 : p ∈ M.N δ δ' := by simpa [Flow.map_zero_apply] using hp 0
    obtain ⟨q, hqN, hq⟩ := (M.isCompact_N (δ := δ) (δ' := δ')).exists_isMinOn ⟨p, hp0⟩
      M.cb.continuousOn
    have hγ : Continuous fun s => M.ϕ s p := M.ϕ.continuous continuous_id continuous_const
    obtain ⟨ρ, hρ0, hρ⟩ := exists_timeChange (b := fun t => M.b (M.ϕ t p)) (M.cb.comp hγ)
      (b_pos_of M H hqN) fun t => isMinOn_iff.1 hq _ (hp t)
    have hbne : ∀ s, M.b (M.ϕ (ρ s) p) ≠ 0 := fun s => (b_pos_of M H (hp _)).ne'
    have := inv_TC H (u := fun s => M.u (M.ϕ (ρ s) p)) (v := fun s => M.v (M.ϕ (ρ s) p))
      (τ := fun s => M.τ (M.ϕ (ρ s) p))
      (fun s => hasDerivAt_timeChange (b := fun t => M.b (M.ϕ t p))
        (F := fun t => Fu c (M.u (M.ϕ t p)) (M.v (M.ϕ t p)) (M.τ (M.ϕ t p)))
        (hρ s) (du_of M (hW _).1 (hW _).2) (hbne s))
      (fun s => hasDerivAt_timeChange (b := fun t => M.b (M.ϕ t p))
        (F := fun t => Fv (M.u (M.ϕ t p)) (M.v (M.ϕ t p)) (M.τ (M.ϕ t p)))
        (hρ s) (dv_of M (hW _).1 (hW _).2) (hbne s))
      (fun s => hasDerivAt_timeChange (b := fun t => M.b (M.ϕ t p))
        (F := fun t => M.v (M.ϕ t p) * (1 - M.τ (M.ϕ t p) ^ 2))
        (hρ s) (dτ_of M (hW _).1 (hW _).2) (hbne s))
      (fun s => M.τ_ge _) (fun s => M.τ_le _) (fun s => (hp _).1) (fun s => M.v_nonneg _)
      (fun s => (hp _).2) 0
    show M.u p = 0 ∧ M.v p = 0
    simpa [hρ0, Flow.map_zero_apply] using this
  · rintro ⟨hu, hv⟩ t
    obtain ⟨hu', hv'⟩ := M.tc_inv p hu hv t
    exact ⟨by rw [hu', abs_zero]; exact H.hδ.le, by rw [hv']; exact H.hδ'.le⟩

theorem Inv_N_reverse (H : TCHyp c δ δ') : Inv M.ϕ.reverse (M.N δ δ') = M.TC := by
  rw [Inv_reverse, M.Inv_N H]

/-- Part (i): `(N, L)` is an index pair for `TC`. -/
theorem isIndexPair_L [T2Space X] (H : TCHyp c δ δ') : IsIndexPair M.ϕ M.TC (M.N δ δ') (M.L δ δ') := by
  have := (M.isBlock_N H).isIndexPair
  rwa [M.Inv_N H] at this

/-- Part (ii): `(N, E)` is an index pair for `TC` under the reversed flow. -/
theorem isIndexPair_E [T2Space X] (H : TCHyp c δ δ') :
    IsIndexPair M.ϕ.reverse M.TC (M.N δ δ') (M.E δ δ') := by
  have := (M.isBlock_N_reverse H).isIndexPair
  rwa [M.Inv_N_reverse H] at this

end TCModel

end ConleyCheck.Gubser
