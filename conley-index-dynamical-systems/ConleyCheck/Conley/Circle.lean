import ConleyCheck.Conley.Double

/-!
# The double on the circle

The double `𝒟 = X × S¹` of the paper, with `S¹ = {z ∈ ℝ² : |z| = 1}` and `z = (cos θ, sin θ)`.
The base flow `cflow` is the lift of the base flow `θ̇ = g` of the extended phase space through
`cos`: `cflow_t(c, s) = (ϑ_t c, sign(s) √(1 - (ϑ_t c)²))`, which keeps the open upper and lower
sheets `s > 0`, `s < 0` invariant and fixes `θ = 0` (`z = (1, 0)`, IR) and `θ = π` (`z = (-1, 0)`,
UV). Then

* `circΦ`, `cq_circΦ`: Lemma `lem:double`(a), `q(x, z) = (x, Re z)` is a semiconjugacy onto the
  slab;
* `cR`, `cR_circΦ`, `cq_cR`, `cR_eq_self_iff`, `cq_eq_cq_iff`: Lemma `lem:double`(b), the sheet
  exchange `R(x, z) = (x, z̄)` commutes with the flow, `Fix(R) = X × {0} ⊔ X × {π}`, and the
  fibers of `q` are the `R`-orbits;
* `circ_isolated`: Lemma `lem:isolation`(b), `S̃ = q⁻¹(S)` is isolated and `R`-invariant;
* `circ_attractorRepeller`: Lemma `lem:isolation`(c) for `S̃`;
* `IsIndexPair.preimage_semiconj`, `equivariant_i`: Theorem `thm:equivariant`(i). `(q⁻¹N, q⁻¹L)` is an
  `R`-invariant index pair of `S̃`; its fixed-point part is `(N₊, L₊) × {0} ⊔ (N₋, L₋) × {π}`
  with `(N_±, L_±)` index pairs of `K_±` for `f_±`; and `q` induces a homeomorphism
  `q⁻¹(N)/R ≅ N` carrying `q⁻¹(L)/R` onto `L` (`orbitHomeo`).
-/

namespace ConleyCheck.Conley

open Set Filter Topology

universe u

/-! ### The circle -/

/-- The circle `S¹ ⊆ ℝ²`. -/
abbrev Circ : Type := {z : ℝ × ℝ // z.1 ^ 2 + z.2 ^ 2 = 1}

namespace Circ

/-- `θ = 0`, the IR point. -/
def zero : Circ := ⟨(1, 0), by norm_num⟩

/-- `θ = π`, the UV point. -/
def pi : Circ := ⟨(-1, 0), by norm_num⟩

theorem fst_mem (z : Circ) : z.1.1 ∈ Icc (-1 : ℝ) 1 := by
  have h := z.2
  constructor <;> nlinarith [sq_nonneg z.1.2, sq_nonneg (z.1.1 - 1), sq_nonneg (z.1.1 + 1)]

/-- `cos θ`. -/
def cos (z : Circ) : Tau := ⟨z.1.1, fst_mem z⟩

/-- The reflection `θ ↦ -θ`. -/
def refl (z : Circ) : Circ := ⟨(z.1.1, -z.1.2), by rw [neg_sq]; exact z.2⟩

theorem continuous_cos : Continuous cos :=
  (continuous_fst.comp continuous_subtype_val).subtype_mk _

theorem continuous_refl : Continuous refl :=
  ((continuous_fst.comp continuous_subtype_val).prodMk
    (continuous_snd.comp continuous_subtype_val).neg).subtype_mk _

theorem refl_refl (z : Circ) : refl (refl z) = z := Subtype.ext (Prod.ext rfl (neg_neg _))

theorem cos_refl (z : Circ) : cos (refl z) = cos z := rfl

theorem snd_eq_zero_iff (z : Circ) : z.1.2 = 0 ↔ (z.1.1 = 1 ∨ z.1.1 = -1) := by
  have h := z.2
  constructor
  · intro h2
    rw [h2] at h
    have : (z.1.1 - 1) * (z.1.1 + 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  · rintro (h1 | h1) <;> rw [h1] at h <;> nlinarith [sq_nonneg z.1.2]

theorem eq_of_cos_eq {z w : Circ} (h : z.1.1 = w.1.1) : w = z ∨ w = refl z := by
  have hz := z.2
  have hw := w.2
  have : (w.1.2 - z.1.2) * (w.1.2 + z.1.2) = 0 := by rw [h] at hz; nlinarith
  rcases mul_eq_zero.1 this with h2 | h2
  · left; exact Subtype.ext (Prod.ext h.symm (by linarith))
  · right; exact Subtype.ext (Prod.ext h.symm (show w.1.2 = -z.1.2 by linarith))

theorem refl_eq_self_iff (z : Circ) : refl z = z ↔ z = zero ∨ z = pi := by
  constructor
  · intro h
    have h2 : z.1.2 = 0 := by
      have := congrArg (fun w : Circ => w.1.2) h
      simp only [refl] at this
      linarith
    rcases (snd_eq_zero_iff z).1 h2 with h1 | h1
    · left; exact Subtype.ext (Prod.ext h1 h2)
    · right; exact Subtype.ext (Prod.ext h1 h2)
  · rintro (rfl | rfl) <;> exact Subtype.ext (Prod.ext rfl (neg_zero))

theorem cos_eq_top_iff (z : Circ) : cos z = Tau.top ↔ z = zero := by
  constructor
  · intro h
    have h1 : z.1.1 = 1 := congrArg Subtype.val h
    exact Subtype.ext (Prod.ext h1 ((snd_eq_zero_iff z).2 (Or.inl h1)))
  · rintro rfl; rfl

theorem cos_eq_bot_iff (z : Circ) : cos z = Tau.bot ↔ z = pi := by
  constructor
  · intro h
    have h1 : z.1.1 = -1 := congrArg Subtype.val h
    exact Subtype.ext (Prod.ext h1 ((snd_eq_zero_iff z).2 (Or.inr h1)))
  · rintro rfl; rfl

/-- The point of the closed upper sheet over `τ`. -/
noncomputable def up (b : Tau) : Circ :=
  ⟨((b : ℝ), √(1 - (b : ℝ) ^ 2)), by
    have h := b.2
    rw [Real.sq_sqrt (by nlinarith [h.1, h.2])]; ring⟩

theorem cos_up (b : Tau) : cos (up b) = b := rfl

instance : CompactSpace Circ := by
  refine isCompact_iff_compactSpace.1 (Metric.isCompact_of_isClosed_isBounded
    (isClosed_eq (by fun_prop) continuous_const) (Metric.isBounded_closedBall (x := 0) (r := 1)
      |>.subset fun z (hz : z.1 ^ 2 + z.2 ^ 2 = 1) => ?_))
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  refine max_le (abs_le.2 ⟨?_, ?_⟩) (abs_le.2 ⟨?_, ?_⟩) <;>
    nlinarith [sq_nonneg z.1, sq_nonneg z.2, sq_nonneg (z.1 - 1), sq_nonneg (z.1 + 1),
      sq_nonneg (z.2 - 1), sq_nonneg (z.2 + 1)]

end Circ

/-! ### The base flow on the circle -/

section Base

variable {θ : Flow ℝ Tau} (hθ : IsHeight θ (fun b => (b : ℝ)))

omit hθ in
theorem one_sub_sq_nonneg (b : Tau) : 0 ≤ 1 - (b : ℝ) ^ 2 := by
  have h := b.2; nlinarith [h.1, h.2]

include hθ in
/-- The base flow keeps the end points and the open interval invariant. -/
theorem base_sq_eq_one_iff (t : ℝ) (b : Tau) : (θ t b : ℝ) ^ 2 = 1 ↔ (b : ℝ) ^ 2 = 1 := by
  have key : ∀ (s : ℝ) (b : Tau), (b : ℝ) ^ 2 = 1 → (θ s b : ℝ) ^ 2 = 1 := fun s b hb => by
    have : (b : ℝ) = 1 ∨ (b : ℝ) = -1 := by
      have : ((b : ℝ) - 1) * ((b : ℝ) + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · right; linarith
    rw [hθ.fix b this s]; exact hb
  refine ⟨fun h => ?_, key t b⟩
  have := key (-t) _ h
  rwa [base_cancel] at this

/-- The second component of the base flow, `sign(s) √(1 - (ϑ_t c)²)`. -/
noncomputable def csnd (θ : Flow ℝ Tau) (t : ℝ) (z : Circ) : ℝ :=
  Real.sign z.1.2 * √(1 - (θ t (Circ.cos z) : ℝ) ^ 2)

include hθ in
theorem csnd_eq_zero_iff (t : ℝ) (z : Circ) : csnd θ t z = 0 ↔ z.1.2 = 0 := by
  have hb := one_sub_sq_nonneg (θ t (Circ.cos z))
  constructor
  · intro h
    by_contra h2
    rcases Real.sign_apply_eq_of_ne_zero _ h2 with hs | hs <;>
    · rw [csnd, hs] at h
      have h3 : √(1 - (θ t (Circ.cos z) : ℝ) ^ 2) = 0 := by linarith
      rw [Real.sqrt_eq_zero hb] at h3
      have h4 : (θ t (Circ.cos z) : ℝ) ^ 2 = 1 := by linarith
      rw [base_sq_eq_one_iff hθ] at h4
      exact h2 ((Circ.snd_eq_zero_iff z).2 (by
        have : (z.1.1 - 1) * (z.1.1 + 1) = 0 := by
          have : (Circ.cos z : ℝ) = z.1.1 := rfl
          rw [this] at h4; nlinarith
        rcases mul_eq_zero.1 this with h | h
        · left; linarith
        · right; linarith))
  · intro h; rw [csnd, h, Real.sign_zero, zero_mul]

include hθ in
theorem sign_csnd (t : ℝ) (z : Circ) : Real.sign (csnd θ t z) = Real.sign z.1.2 := by
  rcases lt_trichotomy z.1.2 0 with h | h | h
  · have hne : csnd θ t z ≠ 0 := fun h' => h.ne ((csnd_eq_zero_iff hθ t z).1 h')
    have hle : csnd θ t z ≤ 0 := by
      rw [csnd, Real.sign_of_neg h]; nlinarith [Real.sqrt_nonneg (1 - (θ t (Circ.cos z) : ℝ) ^ 2)]
    rw [Real.sign_of_neg (lt_of_le_of_ne hle hne), Real.sign_of_neg h]
  · rw [(csnd_eq_zero_iff hθ t z).2 h, h]
  · have hne : csnd θ t z ≠ 0 := fun h' => h.ne' ((csnd_eq_zero_iff hθ t z).1 h')
    have hle : 0 ≤ csnd θ t z := by
      rw [csnd, Real.sign_of_pos h, one_mul]; exact Real.sqrt_nonneg _
    rw [Real.sign_of_pos (lt_of_le_of_ne hle hne.symm), Real.sign_of_pos h]

include hθ in
theorem cfun_mem (t : ℝ) (z : Circ) : (θ t (Circ.cos z) : ℝ) ^ 2 + csnd θ t z ^ 2 = 1 := by
  have hb := one_sub_sq_nonneg (θ t (Circ.cos z))
  rcases eq_or_ne z.1.2 0 with h | h
  · have h2 : (θ t (Circ.cos z) : ℝ) ^ 2 = 1 := by
      rw [base_sq_eq_one_iff hθ]
      have := z.2; rw [h] at this
      show z.1.1 ^ 2 = 1; linarith
    rw [(csnd_eq_zero_iff hθ t z).2 h, h2]; ring
  · rw [csnd, mul_pow, Real.sq_sqrt hb]
    rcases Real.sign_apply_eq_of_ne_zero _ h with hs | hs <;> rw [hs] <;> ring

theorem abs_csnd_le (t : ℝ) (z : Circ) :
    |csnd θ t z| ≤ √(1 - (θ t (Circ.cos z) : ℝ) ^ 2) := by
  rw [csnd, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_of_le_one_left (Real.sqrt_nonneg _) ?_
  rcases Real.sign_apply_eq z.1.2 with h | h | h <;> rw [h] <;> norm_num

omit hθ in
theorem continuous_base_cos :
    Continuous fun p : ℝ × Circ => (θ p.1 (Circ.cos p.2) : ℝ) :=
  continuous_subtype_val.comp (θ.continuous continuous_fst (Circ.continuous_cos.comp continuous_snd))

include hθ in
theorem continuous_csnd : Continuous fun p : ℝ × Circ => csnd θ p.1 p.2 := by
  have hw : Continuous fun p : ℝ × Circ => √(1 - (θ p.1 (Circ.cos p.2) : ℝ) ^ 2) :=
    (continuous_const.sub ((continuous_base_cos).pow 2)).sqrt
  have hs : Continuous fun p : ℝ × Circ => (p.2 : ℝ × ℝ).2 :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_snd)
  refine continuous_iff_continuousAt.2 fun p => ?_
  rcases lt_trichotomy (p.2 : ℝ × ℝ).2 0 with h | h | h
  · have hev : (fun q : ℝ × Circ => csnd θ q.1 q.2) =ᶠ[𝓝 p]
        fun q => -√(1 - (θ q.1 (Circ.cos q.2) : ℝ) ^ 2) := by
      filter_upwards [hs.continuousAt.eventually (gt_mem_nhds h)] with q hq
      rw [csnd, Real.sign_of_neg hq, neg_one_mul]
    exact (hw.neg.continuousAt).congr hev.symm
  · have h0 : csnd θ p.1 p.2 = 0 := (csnd_eq_zero_iff hθ p.1 p.2).2 h
    have hw0 : √(1 - (θ p.1 (Circ.cos p.2) : ℝ) ^ 2) = 0 := by
      have h2 : (θ p.1 (Circ.cos p.2) : ℝ) ^ 2 = 1 := by
        rw [base_sq_eq_one_iff hθ]
        have := (p.2).2; rw [h] at this
        show (p.2 : ℝ × ℝ).1 ^ 2 = 1; linarith
      rw [h2, sub_self, Real.sqrt_zero]
    show Tendsto _ _ (𝓝 (csnd θ p.1 p.2))
    rw [h0]
    have hw' : Tendsto (fun q : ℝ × Circ => √(1 - (θ q.1 (Circ.cos q.2) : ℝ) ^ 2)) (𝓝 p) (𝓝 0) := by
      rw [← hw0]; exact hw.continuousAt
    refine squeeze_zero_norm (fun q => ?_) hw'
    rw [Real.norm_eq_abs]; exact abs_csnd_le q.1 q.2
  · have hev : (fun q : ℝ × Circ => csnd θ q.1 q.2) =ᶠ[𝓝 p]
        fun q => √(1 - (θ q.1 (Circ.cos q.2) : ℝ) ^ 2) := by
      filter_upwards [hs.continuousAt.eventually (lt_mem_nhds h)] with q hq
      rw [csnd, Real.sign_of_pos hq, one_mul]
    exact hw.continuousAt.congr hev.symm

include hθ in
/-- The base flow `θ̇ = G(θ)` of the double, lifted from the slab through `cos`. -/
noncomputable def cflow : Flow ℝ Circ where
  toFun t z := ⟨((θ t (Circ.cos z) : ℝ), csnd θ t z), cfun_mem hθ t z⟩
  cont' := ((continuous_base_cos).prodMk (continuous_csnd hθ)).subtype_mk _
  map_add' s t z := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show (θ (s + t) (Circ.cos z) : ℝ) = (θ s (θ t (Circ.cos z)) : ℝ)
      rw [Flow.map_add]
    · show csnd θ (s + t) z =
        Real.sign (csnd θ t z) * √(1 - (θ s (θ t (Circ.cos z)) : ℝ) ^ 2)
      rw [sign_csnd hθ, ← Flow.map_add]
      rfl
  map_zero' z := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show (θ 0 (Circ.cos z) : ℝ) = z.1.1
      rw [Flow.map_zero_apply]; rfl
    · show csnd θ 0 z = z.1.2
      rw [csnd, Flow.map_zero_apply]
      have h1 : 1 - ((Circ.cos z : Tau) : ℝ) ^ 2 = z.1.2 ^ 2 := by
        have := z.2; show 1 - z.1.1 ^ 2 = _; linarith
      rw [h1, Real.sqrt_sq_eq_abs]
      rcases lt_trichotomy z.1.2 0 with h | h | h
      · rw [Real.sign_of_neg h, abs_of_neg h]; ring
      · rw [h]; simp
      · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]

theorem cos_cflow (t : ℝ) (z : Circ) : Circ.cos (cflow hθ t z) = θ t (Circ.cos z) := rfl

theorem cflow_refl (t : ℝ) (z : Circ) : cflow hθ t (Circ.refl z) = Circ.refl (cflow hθ t z) := by
  refine Subtype.ext (Prod.ext rfl ?_)
  show csnd θ t (Circ.refl z) = -csnd θ t z
  simp only [csnd, Circ.cos_refl]
  rw [show (Circ.refl z).1.2 = -z.1.2 from rfl, Real.sign_neg, neg_mul]

theorem cflow_up (t : ℝ) (b : Tau) : cflow hθ t (Circ.up b) = Circ.up (θ t b) := by
  refine Subtype.ext (Prod.ext rfl ?_)
  show Real.sign √(1 - (b : ℝ) ^ 2) * √(1 - (θ t b : ℝ) ^ 2) = √(1 - (θ t b : ℝ) ^ 2)
  rcases (Real.sqrt_nonneg (1 - (b : ℝ) ^ 2)).eq_or_lt with h | h
  · have h1 : (b : ℝ) ^ 2 = 1 := by
      have := one_sub_sq_nonneg b
      rw [eq_comm, Real.sqrt_eq_zero this] at h; linarith
    have h2 : (θ t b : ℝ) ^ 2 = 1 := (base_sq_eq_one_iff hθ t b).2 h1
    rw [h2, sub_self, Real.sqrt_zero, mul_zero]
  · rw [Real.sign_of_pos h, one_mul]

omit hθ in
theorem Circ.up_cos {z : Circ} (hz : 0 ≤ z.1.2) : Circ.up (Circ.cos z) = z := by
  refine Subtype.ext (Prod.ext rfl ?_)
  show √(1 - z.1.1 ^ 2) = z.1.2
  have := z.2
  rw [show 1 - z.1.1 ^ 2 = z.1.2 ^ 2 by linarith, Real.sqrt_sq hz]

end Base

/-! ### The double -/

section Double

variable {X : Type u} [TopologicalSpace X] {Φ : Flow ℝ (X × Tau)} {θ : Flow ℝ Tau}
  (hΦ : IsSkew Φ θ) (hθ : IsHeight θ (fun b => (b : ℝ)))

/-- `q(x, θ) = (x, cos θ)`. -/
def cq (p : X × Circ) : X × Tau := (p.1, Circ.cos p.2)

/-- The sheet exchange `R(x, θ) = (x, -θ)`. -/
def cR (p : X × Circ) : X × Circ := (p.1, Circ.refl p.2)

omit [TopologicalSpace X] in
theorem cq_cR (p : X × Circ) : cq (cR p) = cq p := rfl

omit [TopologicalSpace X] in
theorem cR_cR (p : X × Circ) : cR (cR p) = p := Prod.ext rfl (Circ.refl_refl _)

theorem continuous_cq : Continuous (cq : X × Circ → X × Tau) :=
  continuous_fst.prodMk (Circ.continuous_cos.comp continuous_snd)

theorem continuous_cR : Continuous (cR : X × Circ → X × Circ) :=
  continuous_fst.prodMk (Circ.continuous_refl.comp continuous_snd)

/-- The double `ẋ = F(cos θ, x)`, `θ̇ = G(θ)` on `X × S¹`. -/
noncomputable def circΦ : Flow ℝ (X × Circ) where
  toFun t p := ((Φ t (cq p)).1, cflow hθ t p.2)
  cont' := (continuous_fst.comp (Φ.continuous continuous_fst
    (continuous_cq.comp continuous_snd))).prodMk
    ((cflow hθ).continuous continuous_fst (continuous_snd.comp continuous_snd))
  map_add' s t p := by
    have e : ((Φ t (cq p)).1, Circ.cos (cflow hθ t p.2)) = Φ t (cq p) :=
      Prod.ext rfl (by rw [cos_cflow, hΦ]; rfl)
    show ((Φ (s + t) (cq p)).1, cflow hθ (s + t) p.2) =
      ((Φ s ((Φ t (cq p)).1, Circ.cos (cflow hθ t p.2))).1, cflow hθ s (cflow hθ t p.2))
    rw [e, Φ.map_add, Flow.map_add]
  map_zero' p := by
    show ((Φ 0 (cq p)).1, cflow hθ 0 p.2) = p
    rw [Φ.map_zero_apply, Flow.map_zero_apply]
    rfl

theorem circΦ_apply (t : ℝ) (p : X × Circ) :
    circΦ hΦ hθ t p = ((Φ t (cq p)).1, cflow hθ t p.2) := rfl

/-- Lemma `lem:double`(a) on the circle: `q ∘ Φ̃_t = Φ_t ∘ q`. -/
theorem cq_circΦ (t : ℝ) (p : X × Circ) : cq (circΦ hΦ hθ t p) = Φ t (cq p) :=
  Prod.ext rfl (by
    show Circ.cos (cflow hθ t p.2) = (Φ t (cq p)).2
    rw [cos_cflow, hΦ]; rfl)

/-- Lemma `lem:double`(b): `R` commutes with the flow. -/
theorem cR_circΦ (t : ℝ) (p : X × Circ) : cR (circΦ hΦ hθ t p) = circΦ hΦ hθ t (cR p) :=
  Prod.ext rfl (cflow_refl hθ t p.2).symm

omit [TopologicalSpace X] in
/-- Lemma `lem:double`(b): `Fix(R) = X × {0} ⊔ X × {π}`, and `R` acts freely off it. -/
theorem cR_eq_self_iff (p : X × Circ) : cR p = p ↔ p.2 = Circ.zero ∨ p.2 = Circ.pi := by
  rw [← Circ.refl_eq_self_iff]
  exact ⟨fun h => congrArg Prod.snd h, fun h => Prod.ext rfl h⟩

omit [TopologicalSpace X] in
/-- Lemma `lem:double`(b): the fibers of `q` are the `R`-orbits. -/
theorem cq_eq_cq_iff (p p' : X × Circ) : cq p' = cq p ↔ p' = p ∨ p' = cR p := by
  constructor
  · intro h
    have h1 : p'.1 = p.1 := congrArg (fun q : X × Tau => q.1) h
    have h2 : (p'.2 : ℝ × ℝ).1 = (p.2 : ℝ × ℝ).1 := congrArg (fun q => ((q.2 : Tau) : ℝ)) h
    rcases Circ.eq_of_cos_eq h2.symm with h3 | h3
    · exact Or.inl (Prod.ext h1 h3)
    · exact Or.inr (Prod.ext h1 h3)
  · rintro (rfl | rfl)
    · rfl
    · exact cq_cR p

/-- Lemma `lem:double`(a) on the circle: on the closed upper sheet `sin θ ≥ 0`, `q` is a bijection
onto the slab, with inverse `(x, τ) ↦ (x, up τ)`, conjugating the flows. -/
theorem circ_upper :
    (∀ p : X × Tau, cq (p.1, Circ.up p.2) = p) ∧
      (∀ p : X × Circ, 0 ≤ (p.2 : ℝ × ℝ).2 → ((cq p).1, Circ.up (cq p).2) = p) ∧
      (∀ p : X × Tau, 0 ≤ ((Circ.up p.2 : Circ) : ℝ × ℝ).2) ∧
      ∀ t (p : X × Tau), circΦ hΦ hθ t (p.1, Circ.up p.2) = ((Φ t p).1, Circ.up (Φ t p).2) := by
  refine ⟨fun p => rfl, fun p hp => Prod.ext rfl (Circ.up_cos hp), fun p => Real.sqrt_nonneg _,
    fun t p => Prod.ext rfl ?_⟩
  show cflow hθ t (Circ.up p.2) = Circ.up (Φ t p).2
  rw [cflow_up, hΦ]

omit [TopologicalSpace X] in
theorem cq_surjective : Function.Surjective (cq : X × Circ → X × Tau) := fun p =>
  ⟨(p.1, Circ.up p.2), rfl⟩

/-- `τ ∘ q` is a height function on the double. -/
theorem isHeight_circ : IsHeight (circΦ hΦ hθ) (fun p => ((cq p).2 : ℝ)) where
  continuous := continuous_subtype_val.comp (continuous_snd.comp continuous_cq)
  mem p := (cq p).2.2
  fix p h t := by
    show ((cq (circΦ hΦ hθ t p)).2 : ℝ) = (cq p).2
    rw [cq_circΦ, hΦ]
    exact hθ.fix _ h t
  strict p h1 h2 t ht := by
    show ((cq p).2 : ℝ) < (cq (circΦ hΦ hθ t p)).2
    rw [cq_circΦ, hΦ]
    exact hθ.strict _ h1 h2 t ht

theorem Inv_cq_preimage (N : Set (X × Tau)) :
    Inv (circΦ hΦ hθ) (cq ⁻¹' N) = cq ⁻¹' Inv Φ N := by
  ext p
  simp only [Inv, mem_ofPred_eq, mem_preimage, cq_circΦ]

variable [T2Space X]

omit [T2Space X] in
theorem isCompact_cq_preimage [T2Space X] {N : Set (X × Tau)} (hN : IsCompact N) :
    IsCompact (cq ⁻¹' N) :=
  ((hN.image continuous_fst).prod isCompact_univ).of_isClosed_subset
    (hN.isClosed.preimage continuous_cq) fun p hp => ⟨⟨cq p, hp, rfl⟩, mem_univ _⟩

/-- Lemma `lem:isolation`(b) on the circle: `q⁻¹(N)` isolates `S̃ = q⁻¹(S)`, which is
`R`-invariant. -/
theorem circ_isolated {N : Set (X × Tau)} (hN : IsIsolatingNbhd Φ N) :
    IsIsolatingNbhd (circΦ hΦ hθ) (cq ⁻¹' N) ∧
      Inv (circΦ hΦ hθ) (cq ⁻¹' N) = cq ⁻¹' Inv Φ N ∧
      cR ⁻¹' (cq ⁻¹' Inv Φ N) = cq ⁻¹' Inv Φ N := by
  refine ⟨⟨isCompact_cq_preimage hN.1, ?_⟩, Inv_cq_preimage hΦ hθ N, rfl⟩
  rw [Inv_cq_preimage]
  exact (preimage_mono hN.2).trans (preimage_interior_subset_interior_preimage continuous_cq)

omit [TopologicalSpace X] [T2Space X] in
theorem cq_preimage_inter_top (S : Set (X × Tau)) :
    cq ⁻¹' S ∩ (fun p => ((cq p).2 : ℝ)) ⁻¹' {1} = {x | (x, Tau.top) ∈ S} ×ˢ {Circ.zero} := by
  ext ⟨x, z⟩
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_prod, mem_ofPred_eq]
  constructor
  · rintro ⟨hS, h1⟩
    have hz : Circ.cos z = Tau.top := Subtype.ext h1
    rw [Circ.cos_eq_top_iff] at hz
    subst hz
    exact ⟨hS, rfl⟩
  · rintro ⟨hS, rfl⟩
    exact ⟨hS, rfl⟩

omit [TopologicalSpace X] [T2Space X] in
theorem cq_preimage_inter_bot (S : Set (X × Tau)) :
    cq ⁻¹' S ∩ (fun p => ((cq p).2 : ℝ)) ⁻¹' {-1} = {x | (x, Tau.bot) ∈ S} ×ˢ {Circ.pi} := by
  ext ⟨x, z⟩
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_prod, mem_ofPred_eq]
  constructor
  · rintro ⟨hS, h1⟩
    have hz : Circ.cos z = Tau.bot := Subtype.ext h1
    rw [Circ.cos_eq_bot_iff] at hz
    subst hz
    exact ⟨hS, rfl⟩
  · rintro ⟨hS, rfl⟩
    exact ⟨hS, rfl⟩

/-- Lemma `lem:isolation`(c) for `S̃`: `(K_+ × {0}, K_- × {π})` is an attractor–repeller pair of
`S̃ = q⁻¹(S)`. -/
theorem circ_attractorRepeller {S : Set (X × Tau)} (hS : IsIsolatedInvariantSet Φ S) :
    IsIsolatedInvariantSet (circΦ hΦ hθ) (cq ⁻¹' S) ∧
      IsAttractorRepellerPair (circΦ hΦ hθ) (cq ⁻¹' S) ({x | (x, Tau.top) ∈ S} ×ˢ {Circ.zero})
        ({x | (x, Tau.bot) ∈ S} ×ˢ {Circ.pi}) := by
  obtain ⟨N, hN, rfl⟩ := hS
  obtain ⟨hNn, hInv, -⟩ := circ_isolated hΦ hθ hN
  have hSn : IsIsolatedInvariantSet (circΦ hΦ hθ) (cq ⁻¹' Inv Φ N) := ⟨_, hNn, hInv⟩
  have h := (isHeight_circ hΦ hθ).isAttractorRepellerPair hSn
  rw [cq_preimage_inter_top, cq_preimage_inter_bot] at h
  exact ⟨hSn, h⟩

end Double

/-! ### Index pairs pull back along proper semiconjugacies -/

section Preimage

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [T2Space α]
  {ϕ : Flow ℝ α} {ψ : Flow ℝ β} {e : β → α}

/-- An index pair pulls back along a continuous semiconjugacy `e ∘ ψ_t = ϕ_t ∘ e` for which
preimages of compact sets are compact. -/
theorem IsIndexPair.preimage_semiconj (he : Continuous e) (hsc : ∀ t y, e (ψ t y) = ϕ t (e y))
    (hc : ∀ K, IsCompact K → IsCompact (e ⁻¹' K)) {S N L : Set α} (h : IsIndexPair ϕ S N L) :
    IsIndexPair ψ (e ⁻¹' S) (e ⁻¹' N) (e ⁻¹' L) := by
  have hInv : ∀ M : Set α, Inv ψ (e ⁻¹' M) = e ⁻¹' Inv ϕ M := fun M => by
    ext y; simp only [Inv, mem_ofPred_eq, mem_preimage, hsc]
  have hcl : closure (e ⁻¹' N \ e ⁻¹' L) ⊆ e ⁻¹' closure (N \ L) := by
    rw [← preimage_sdiff]; exact he.closure_preimage_subset _
  have hS : e ⁻¹' S ⊆ interior (e ⁻¹' N \ e ⁻¹' L) := by
    rw [← preimage_sdiff]
    exact (preimage_mono h.nhds).trans (preimage_interior_subset_interior_preimage he)
  have hInvS : Inv ψ (closure (e ⁻¹' N \ e ⁻¹' L)) = e ⁻¹' S := by
    refine le_antisymm ?_ ?_
    · refine (Inv_mono hcl).trans ?_
      rw [hInv, h.inv_eq]
    · intro y hy t
      have : ψ t y ∈ e ⁻¹' S := by
        show e (ψ t y) ∈ S
        rw [hsc, ← h.inv_eq]
        rw [← h.inv_eq] at hy
        exact flow_mem_Inv hy t
      exact subset_closure (interior_subset (hS this))
  refine
    { isCompact_N := hc _ h.isCompact_N
      isCompact_L := hc _ h.isCompact_L
      subset := preimage_mono h.subset
      isolating := ⟨(hc _ h.isCompact_N).of_isClosed_subset isClosed_closure
        (closure_minimal sdiff_subset (h.isCompact_N.isClosed.preimage he)), ?_⟩
      inv_eq := hInvS
      nhds := hS
      posInv := fun x hx t ht hs => ?_
      exit := fun x hx t ht hout => ?_ }
  · rw [hInvS]; exact hS.trans (interior_mono subset_closure)
  · show e (ψ t x) ∈ L
    rw [hsc]
    exact h.posInv (e x) hx t ht fun s hs' => by rw [← hsc]; exact hs s hs'
  · obtain ⟨s, hs, hseg, hL⟩ := h.exit (e x) hx t ht (by rw [← hsc]; exact hout)
    exact ⟨s, hs, fun r hr => by show e (ψ r x) ∈ N; rw [hsc]; exact hseg r hr,
      by show e (ψ s x) ∈ L; rw [hsc]; exact hL⟩

end Preimage

/-! ### Theorem `thm:equivariant`(i) -/

section Equivariant

variable {X : Type u} [TopologicalSpace X] [T2Space X] {Φ : Flow ℝ (X × Tau)} {θ : Flow ℝ Tau}
  (hΦ : IsSkew Φ θ) (hθ : IsHeight θ (fun b => (b : ℝ)))

omit [T2Space X] in
theorem isCompact_fiber_preimage (b₀ : Tau) {K : Set (X × Tau)} (hK : IsCompact K) :
    IsCompact ((fun x => (x, b₀)) ⁻¹' K) := by
  have : (fun x => (x, b₀)) ⁻¹' K = Prod.fst '' (K ∩ univ ×ˢ {b₀}) := by
    ext x
    constructor
    · intro hx; exact ⟨(x, b₀), ⟨hx, mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨p, ⟨hp, -, hp2⟩, rfl⟩
      show (p.1, b₀) ∈ K
      rw [show b₀ = p.2 from (mem_singleton_iff.1 hp2).symm]; exact hp
  rw [this]
  exact (hK.inter_right (isClosed_univ.prod isClosed_singleton)).image continuous_fst

/-- Theorem `thm:equivariant`(i). Let `(N, L)` be an index pair of `S` in the slab.
* `(q⁻¹N, q⁻¹L)` is an `R`-invariant index pair of `S̃ = q⁻¹(S)` in the circle double.
* Its fixed-point part is `(N₊ × {0}) ⊔ (N₋ × {π})`, relative to `(L₊ × {0}) ⊔ (L₋ × {π})`, with
  `N_± = {x : (x, ±1) ∈ N}`, and `(N_±, L_±)` is an index pair of `K_±` for `f_±`. Hence
  `Y^R = (N₊/L₊) ∨ (N₋/L₋)`.
* `q` identifies points of `q⁻¹N` exactly along `R`-orbits (`cq_eq_cq_iff`), and induces the
  homeomorphism `q⁻¹(N)/R ≅ N` of `orbitHomeo`, which carries `q⁻¹(L)/R` onto `L`. -/
theorem equivariant_i {S N L : Set (X × Tau)} (h : IsIndexPair Φ S N L) :
    IsIndexPair (circΦ hΦ hθ) (cq ⁻¹' S) (cq ⁻¹' N) (cq ⁻¹' L) ∧
      cR ⁻¹' (cq ⁻¹' N) = cq ⁻¹' N ∧ cR ⁻¹' (cq ⁻¹' L) = cq ⁻¹' L ∧
      {p | p ∈ cq ⁻¹' N ∧ cR p = p} =
        {x | (x, Tau.top) ∈ N} ×ˢ {Circ.zero} ∪ {x | (x, Tau.bot) ∈ N} ×ˢ {Circ.pi} ∧
      {p | p ∈ cq ⁻¹' L ∧ cR p = p} =
        {x | (x, Tau.top) ∈ L} ×ˢ {Circ.zero} ∪ {x | (x, Tau.bot) ∈ L} ×ˢ {Circ.pi} ∧
      IsIndexPair (fiberFlow hΦ Tau.top (base_top hθ)) {x | (x, Tau.top) ∈ S}
        {x | (x, Tau.top) ∈ N} {x | (x, Tau.top) ∈ L} ∧
      IsIndexPair (fiberFlow hΦ Tau.bot (base_bot hθ)) {x | (x, Tau.bot) ∈ S}
        {x | (x, Tau.bot) ∈ N} {x | (x, Tau.bot) ∈ L} := by
  have hfix : ∀ M : Set (X × Tau), {p | p ∈ cq ⁻¹' M ∧ cR p = p} =
      {x | (x, Tau.top) ∈ M} ×ˢ {Circ.zero} ∪ {x | (x, Tau.bot) ∈ M} ×ˢ {Circ.pi} := fun M => by
    ext ⟨x, z⟩
    simp only [mem_ofPred_eq, mem_preimage, mem_union, mem_prod, mem_singleton_iff]
    rw [cR_eq_self_iff]
    constructor
    · rintro ⟨hM, rfl | rfl⟩
      · exact Or.inl ⟨hM, rfl⟩
      · exact Or.inr ⟨hM, rfl⟩
    · rintro (⟨hM, rfl⟩ | ⟨hM, rfl⟩)
      · exact ⟨hM, Or.inl rfl⟩
      · exact ⟨hM, Or.inr rfl⟩
  have hfib : ∀ (b₀ : Tau) (hb₀ : ∀ t, θ t b₀ = b₀) (t : ℝ) (x : X),
      (fun x => (x, b₀)) (fiberFlow hΦ b₀ hb₀ t x) = Φ t ((fun x => (x, b₀)) x) := fun b₀ hb₀ t x =>
    Prod.ext rfl (by rw [hΦ, hb₀])
  refine ⟨h.preimage_semiconj continuous_cq (cq_circΦ hΦ hθ) (fun K hK => isCompact_cq_preimage hK),
    rfl, rfl, hfix N, hfix L, ?_, ?_⟩
  · exact h.preimage_semiconj (continuous_id.prodMk continuous_const) (hfib Tau.top (base_top hθ))
      (fun K hK => isCompact_fiber_preimage Tau.top hK)
  · exact h.preimage_semiconj (continuous_id.prodMk continuous_const) (hfib Tau.bot (base_bot hθ))
      (fun K hK => isCompact_fiber_preimage Tau.bot hK)

omit [TopologicalSpace X] [T2Space X] in
/-- On `q⁻¹(N)`, `q` identifies exactly the `R`-orbits. -/
theorem cq_restrict_eq_iff {N : Set (X × Tau)} (y y' : cq ⁻¹' N) :
    (cq (y' : X × Circ) = cq y) ↔ ((y' : X × Circ) = y ∨ (y' : X × Circ) = cR y) :=
  cq_eq_cq_iff _ _

/-- The orbit space of `R` on `q⁻¹(N)`, as the quotient by the fibers of `q`. -/
def orbitSetoid (N : Set (X × Tau)) : Setoid (cq ⁻¹' N) :=
  Setoid.ker fun y : cq ⁻¹' N => cq (y : X × Circ)

/-- Theorem `thm:equivariant`(i), orbit space: for compact `N`, `q` induces a homeomorphism
`q⁻¹(N)/R ≅ N`. -/
noncomputable def orbitHomeo {N : Set (X × Tau)} (hN : IsCompact N) :
    Quotient (orbitSetoid N) ≃ₜ N := by
  haveI : CompactSpace (cq ⁻¹' N) := isCompact_iff_compactSpace.1 (isCompact_cq_preimage hN)
  let f : cq ⁻¹' N → N := fun y => ⟨cq (y : X × Circ), y.2⟩
  have hf : Continuous f := (continuous_cq.comp continuous_subtype_val).subtype_mk _
  let g : Quotient (orbitSetoid N) → N := Quotient.lift f fun a b hab => Subtype.ext hab
  have hg : Function.Bijective g := by
    refine ⟨fun a b hab => ?_, fun p => ?_⟩
    · induction a using Quotient.inductionOn
      induction b using Quotient.inductionOn
      exact Quotient.sound (congrArg Subtype.val hab)
    · obtain ⟨y, hy⟩ := cq_surjective (X := X) (p : X × Tau)
      exact ⟨Quotient.mk _ ⟨y, show cq y ∈ N by rw [hy]; exact p.2⟩, Subtype.ext hy⟩
  exact (continuous_quot_lift _ hf : Continuous g).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective g hg)

theorem orbitHomeo_mk {N : Set (X × Tau)} (hN : IsCompact N) (y : cq ⁻¹' N) :
    (orbitHomeo hN (Quotient.mk _ y) : X × Tau) = cq (y : X × Circ) := rfl

omit [TopologicalSpace X] [T2Space X] in
/-- The relation of `orbitSetoid` is the `R`-orbit relation. -/
theorem orbitSetoid_r {N : Set (X × Tau)} (y y' : cq ⁻¹' N) :
    (orbitSetoid N) y' y ↔ ((y' : X × Circ) = y ∨ (y' : X × Circ) = cR y) :=
  cq_eq_cq_iff _ _

end Equivariant

/-! ### Theorem `thm:equivariant`(ii), the algebraic step -/

/-- The algebraic step of Theorem `thm:equivariant`(ii): if a homomorphism `d` intertwines an
action `r_R` that is `-1` on the source with an action `r_A` that is `+1` on the target, then
`2 d = 0`. Hence `d = 0` if the target has no `2`-torsion. -/
theorem two_smul_eq_zero_of_equivariant {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (d : M →+ N) (rR : M →+ M) (rA : N →+ N) (hR : ∀ m, rR m = -m) (hA : ∀ n, rA n = n)
    (hd : ∀ m, d (rR m) = rA (d m)) (m : M) : 2 • d m = 0 := by
  have h := hd m
  rw [hR, hA, map_neg] at h
  rw [two_nsmul]
  nth_rewrite 1 [← h]
  exact neg_add_cancel _

theorem eq_zero_of_equivariant {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [IsAddTorsionFree N] (d : M →+ N) (rR : M →+ M) (rA : N →+ N) (hR : ∀ m, rR m = -m)
    (hA : ∀ n, rA n = n) (hd : ∀ m, d (rR m) = rA (d m)) (m : M) : d m = 0 := by
  have h := two_smul_eq_zero_of_equivariant d rR rA hR hA hd m
  exact (nsmul_eq_zero_iff_right (n := 2) two_ne_zero).1 h

end ConleyCheck.Conley
