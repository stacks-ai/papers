import ConleyCheck.Conley.AttractorHomology
import ConleyCheck.Conley.Conjugacy
import ConleyCheck.Gubser.ThmM

/-!
# The attractors of the Gubser flow (`cor:attractors`)

* `hasIndex_SIA`: `h(Σ_I(A)) = S⁰`, from the forward invariant block `N_A`, which deforms to a
  point.
* `hasIndex_TCp`: `h(TC^+) = S¹` for the flow `ϕG` on `Ω`, by carrying the block `N^+` to the
  model block of `lem:TC` through the chart `(u, v, τ, σ)`.
* `cor_attractors`: over any commutative ring `K`, the attractors `A₁ ⊂ A₂ ⊂ A₃` of
  `{Σ_I(A), TC^+}`, `{Σ_I(A), TC^+, M^-}` and `{Σ_I(A), TC^+, M^-, M^+}` have
  `CH_*(A_j) = K[0] ⊕ K[1]`, the inclusions induce isomorphisms, and every compact positively
  invariant neighborhood `B` of `A_j` with `Inv(B) = A_j` has `H_*(B) = K[0] ⊕ K[1]`. Such
  neighborhoods exist.
-/

open Set unitInterval

namespace ConleyCheck.Conley

/-- A homeomorphism `N ≃ N'` carrying `L` onto `L'` induces `N/L ≃ N'/L'`. -/
noncomputable def IndexSpace.homeoEquiv {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {N L : Set α} {N' L' : Set β} (e : N ≃ₜ N') (he : ∀ x : N, (e x : β) ∈ L' ↔ (x : α) ∈ L) :
    PointedHomotopyEquiv (IndexSpace N L) (IndexSpace N' L') (IndexSpace.pt _ _)
      (IndexSpace.pt _ _) :=
  PointedHomotopyEquiv.ofInverse
    (descend (IndexSpace.pt N' L') ((IndexSpace.proj N' L').comp ⟨e, e.continuous⟩)
      fun y hy => IndexSpace.proj_eq_pt ((he y).2 hy))
    (descend (IndexSpace.pt N L) ((IndexSpace.proj N L).comp ⟨e.symm, e.symm.continuous⟩)
      fun y hy => IndexSpace.proj_eq_pt ((he (e.symm y)).1 (by rwa [e.apply_symm_apply])))
    rfl rfl
    (IndexSpace.hom_ext (fun y => congrArg (IndexSpace.proj N L) (e.symm_apply_apply y)) rfl)
    (IndexSpace.hom_ext (fun y => congrArg (IndexSpace.proj N' L') (e.apply_symm_apply y)) rfl)

end ConleyCheck.Conley

namespace ConleyCheck.Gubser

open ConleyCheck.Conley

instance : Finite GM :=
  Finite.of_surjective (fun i : Fin 6 => ![GM.A, .Tp, .Bm, .Bp, .Tm, .R] i) fun x => by
    cases x
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩]

/-! ## Radial normalization -/

/-- `v / |v|` on `ℝ³`. -/
noncomputable def nrm3 (v : E3) : E3 :=
  (v.1 / √(v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2), v.2.1 / √(v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2),
    v.2.2 / √(v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2))

/-- `w / |w|` on `ℝ²`. -/
noncomputable def nrm2 (w : ℝ × ℝ) : ℝ × ℝ :=
  (w.1 / √(w.1 ^ 2 + w.2 ^ 2), w.2 / √(w.1 ^ 2 + w.2 ^ 2))

theorem nrm3_pos {v : E3} (h : 0 < v.2.2) : 0 < √(v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2) :=
  Real.sqrt_pos.2 (by nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, pow_pos h 2])

theorem nrm2_pos {w : ℝ × ℝ} (h : 0 < w.1) : 0 < √(w.1 ^ 2 + w.2 ^ 2) :=
  Real.sqrt_pos.2 (by nlinarith [sq_nonneg w.2, pow_pos h 2])

theorem nrm3_sq {v : E3} (h : 0 < v.2.2) :
    (nrm3 v).1 ^ 2 + (nrm3 v).2.1 ^ 2 + (nrm3 v).2.2 ^ 2 = 1 := by
  have hs : 0 < v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 := by
    nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, pow_pos h 2]
  simp only [nrm3, div_pow, Real.sq_sqrt hs.le]
  rw [← add_div, ← add_div, div_self hs.ne']

theorem nrm2_sq {w : ℝ × ℝ} (h : 0 < w.1) : (nrm2 w).1 ^ 2 + (nrm2 w).2 ^ 2 = 1 := by
  have hs : 0 < w.1 ^ 2 + w.2 ^ 2 := by nlinarith [sq_nonneg w.2, pow_pos h 2]
  simp only [nrm2, div_pow, Real.sq_sqrt hs.le]
  rw [← add_div, div_self hs.ne']

theorem nrm3_of_sq {v : E3} (h : v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = 1) : nrm3 v = v := by
  simp only [nrm3, h, Real.sqrt_one, div_one]

theorem nrm2_of_sq {w : ℝ × ℝ} (h : w.1 ^ 2 + w.2 ^ 2 = 1) : nrm2 w = w := by
  simp only [nrm2, h, Real.sqrt_one, div_one]

theorem continuous_nrm3 {Z : Type*} [TopologicalSpace Z] {f : Z → E3} (hf : Continuous f)
    (h : ∀ z, 0 < (f z).2.2) : Continuous fun z => nrm3 (f z) := by
  have hr : Continuous fun z => √((f z).1 ^ 2 + (f z).2.1 ^ 2 + (f z).2.2 ^ 2) := by fun_prop
  have hne : ∀ z, √((f z).1 ^ 2 + (f z).2.1 ^ 2 + (f z).2.2 ^ 2) ≠ 0 := fun z => (nrm3_pos (h z)).ne'
  exact (hf.fst.div hr hne).prodMk ((hf.snd.fst.div hr hne).prodMk (hf.snd.snd.div hr hne))

theorem continuous_nrm2 {Z : Type*} [TopologicalSpace Z] {f : Z → ℝ × ℝ} (hf : Continuous f)
    (h : ∀ z, 0 < (f z).1) : Continuous fun z => nrm2 (f z) := by
  have hr : Continuous fun z => √((f z).1 ^ 2 + (f z).2 ^ 2) := by fun_prop
  have hne : ∀ z, √((f z).1 ^ 2 + (f z).2 ^ 2) ≠ 0 := fun z => (nrm2_pos (h z)).ne'
  exact (hf.fst.div hr hne).prodMk (hf.snd.div hr hne)

/-! ## `h(Σ_I(A)) = S⁰` -/

section SIA

variable {c a : ℝ}

/-- The segment from `y` to `(0, a, 1)`. -/
def segY (a t : ℝ) (q : OmG) : E3 := ((1 - t) * gy1 q, (1 - t) * gy2 q + t * a, (1 - t) * gy3 q + t)

/-- The segment from `w` to `(1, 0)`. -/
def segW (t : ℝ) (q : OmG) : ℝ × ℝ := ((1 - t) * gw1 q + t, (1 - t) * gw2 q)

/-- The deformation of `N_A` to the point `A`. -/
noncomputable def segPt (a t : ℝ) (q : OmG) : EG := (nrm3 (segY a t q), nrm2 (segW t q))

theorem segY_pos {t : ℝ} (ht0 : 0 ≤ t) {q : OmG} (hq : q ∈ NA c a) : 0 < (segY a t q).2.2 := by
  have h3 := gy3_pos_of_NA hq
  have hs := sphere_G q
  have : gy3 q ≤ 1 := by nlinarith [sq_nonneg (gy1 q), sq_nonneg (gy2 q)]
  show 0 < (1 - t) * gy3 q + t
  nlinarith [mul_nonneg ht0 (sub_nonneg.2 this)]

theorem segW_ge {t : ℝ} (ht0 : 0 ≤ t) {q : OmG} (hq : q ∈ NA c a) : 1 / 2 ≤ (segW t q).1 := by
  have hw := hq.1
  have := (gw1_mem q).2
  show 1 / 2 ≤ (1 - t) * gw1 q + t
  nlinarith [mul_nonneg ht0 (sub_nonneg.2 this)]

theorem segW_sq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (q : OmG) :
    (segW t q).1 ^ 2 + (segW t q).2 ^ 2 ≤ 1 := by
  have hc := circle_G q
  have := (gw1_mem q).2
  show ((1 - t) * gw1 q + t) ^ 2 + ((1 - t) * gw2 q) ^ 2 ≤ 1
  have e : ((1 - t) * gw1 q + t) ^ 2 + ((1 - t) * gw2 q) ^ 2 =
      (1 - t) ^ 2 * (gw1 q ^ 2 + gw2 q ^ 2) + 2 * t * (1 - t) * gw1 q + t ^ 2 := by ring
  rw [e, hc]
  nlinarith [mul_nonneg (mul_nonneg ht0 (sub_nonneg.2 ht1)) (sub_nonneg.2 this)]

theorem segPt_mem {t : ℝ} (ht0 : 0 ≤ t) {q : OmG} (hq : q ∈ NA c a) :
    segPt a t q ∈ OmG :=
  ⟨⟨nrm3_sq (segY_pos ht0 hq), div_nonneg (segY_pos ht0 hq).le (Real.sqrt_nonneg _)⟩,
    nrm2_sq (by linarith [segW_ge ht0 hq])⟩

theorem segPt_mem_NA (hc : 0 < c) (ha0 : 0 < a) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {q : OmG}
    (hq : q ∈ NA c a) : (⟨segPt a t q, segPt_mem ht0 hq⟩ : OmG) ∈ NA c a := by
  have hW := segW_ge ht0 hq
  have hr := nrm3_pos (segY_pos ht0 hq)
  have hrW := nrm2_pos (w := segW t q) (by linarith)
  have hrW1 : √((segW t q).1 ^ 2 + (segW t q).2 ^ 2) ≤ 1 :=
    Real.sqrt_le_iff.2 ⟨zero_le_one, by rw [one_pow]; exact segW_sq ht0 ht1 q⟩
  have key : ∀ l : ℝ, l ≤ 0 →
      l / √((segY a t q).1 ^ 2 + (segY a t q).2.1 ^ 2 + (segY a t q).2.2 ^ 2) ≤ 0 :=
    fun l hl => div_nonpos_iff.2 (Or.inr ⟨hl, hr.le⟩)
  have hk : 0 ≤ a * c / 2 := by positivity
  obtain ⟨-, h1, h2, h3, h4⟩ := hq
  have ht1' := sub_nonneg.2 ht1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show 1 / 2 ≤ (segW t q).1 / √((segW t q).1 ^ 2 + (segW t q).2 ^ 2)
    rw [le_div_iff₀ hrW]
    nlinarith
  · convert key ((segY a t q).1 - a * c / 2 * (segY a t q).2.2) ?_ using 1
    · show _ / _ - _ * (_ / _) = _
      ring
    · show (1 - t) * gy1 q - a * c / 2 * ((1 - t) * gy3 q + t) ≤ 0
      nlinarith [mul_nonneg ht1' (neg_nonneg.2 h1), mul_nonneg ht0 hk]
  · convert key (-(segY a t q).1 - a * c / 2 * (segY a t q).2.2) ?_ using 1
    · show -(_ / _) - _ * (_ / _) = _
      ring
    · show -((1 - t) * gy1 q) - a * c / 2 * ((1 - t) * gy3 q + t) ≤ 0
      nlinarith [mul_nonneg ht1' (neg_nonneg.2 h2), mul_nonneg ht0 hk]
  · convert key ((segY a t q).2.1 - 3 * a / 2 * (segY a t q).2.2) ?_ using 1
    · show _ / _ - _ * (_ / _) = _
      ring
    · show (1 - t) * gy2 q + t * a - 3 * a / 2 * ((1 - t) * gy3 q + t) ≤ 0
      nlinarith [mul_nonneg ht1' (neg_nonneg.2 h3), mul_nonneg ht0 ha0.le]
  · convert key (a / 2 * (segY a t q).2.2 - (segY a t q).2.1) ?_ using 1
    · show _ * (_ / _) - _ / _ = _
      ring
    · show a / 2 * ((1 - t) * gy3 q + t) - ((1 - t) * gy2 q + t * a) ≤ 0
      nlinarith [mul_nonneg ht1' (neg_nonneg.2 h4), mul_nonneg ht0 ha0.le]

/-- The deformation of `N_A` to a point. -/
noncomputable def deformNA (hc : 0 < c) (ha0 : 0 < a) : C(I × NA c a, NA c a) where
  toFun p := ⟨⟨segPt a p.1 p.2, segPt_mem p.1.2.1 p.2.2⟩,
    segPt_mem_NA hc ha0 p.1.2.1 p.1.2.2 p.2.2⟩
  continuous_toFun := by
    have hq : Continuous fun p : I × NA c a => ((p.2 : OmG)) :=
      continuous_subtype_val.comp continuous_snd
    have ht : Continuous fun p : I × NA c a => ((p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have h1 := continuous_gy1.comp hq
    have h2 := continuous_gy2.comp hq
    have h3 := continuous_gy3.comp hq
    have h4 := continuous_gw1.comp hq
    have h5 := continuous_gw2.comp hq
    have hY : Continuous fun p : I × NA c a => segY a p.1 p.2 := by
      unfold segY
      exact ((continuous_const.sub ht).mul h1).prodMk ((((continuous_const.sub ht).mul h2).add
        (ht.mul continuous_const)).prodMk (((continuous_const.sub ht).mul h3).add ht))
    have hW : Continuous fun p : I × NA c a => segW p.1 p.2 := by
      unfold segW
      exact (((continuous_const.sub ht).mul h4).add ht).prodMk ((continuous_const.sub ht).mul h5)
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact (continuous_nrm3 hY fun p => segY_pos p.1.2.1 p.2.2).prodMk
      (continuous_nrm2 hW fun p => by linarith [segW_ge (t := p.1) p.1.2.1 p.2.2])

/-- The point `A`. -/
noncomputable def ptA (a : ℝ) : EG := (nrm3 (0, a, 1), nrm2 (1, 0))

theorem segPt_one (q : OmG) : segPt a 1 q = ptA a := by
  simp only [segPt, segY, segW, ptA, sub_self, zero_mul, zero_add, one_mul]

theorem segPt_zero (q : OmG) : segPt a 0 q = (q : EG) := by
  simp only [segPt, segY, segW, sub_zero, one_mul, zero_mul, add_zero]
  rw [nrm3_of_sq (v := (gy1 q, gy2 q, gy3 q)) (sphere_G q),
    nrm2_of_sq (w := (gw1 q, gw2 q)) (circle_G q)]
  rfl

theorem ptA_mem : ptA a ∈ OmG :=
  ⟨⟨nrm3_sq one_pos, div_nonneg zero_le_one (Real.sqrt_nonneg _)⟩, nrm2_sq one_pos⟩

theorem ptA_mem_NA (hc : 0 < c) (ha0 : 0 < a) : (⟨ptA a, ptA_mem⟩ : OmG) ∈ NA c a := by
  have hr := nrm3_pos (v := ((0 : ℝ), a, (1 : ℝ))) one_pos
  set r := √((0 : ℝ) ^ 2 + a ^ 2 + 1 ^ 2)
  have hk : 0 ≤ a * c / 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show 1 / 2 ≤ 1 / √(1 ^ 2 + 0 ^ 2)
    norm_num
  · show 0 / r - a * c / 2 * (1 / r) ≤ 0
    have : 0 ≤ a * c / 2 * (1 / r) := by positivity
    linarith [zero_div r]
  · show -(0 / r) - a * c / 2 * (1 / r) ≤ 0
    have : 0 ≤ a * c / 2 * (1 / r) := by positivity
    linarith [zero_div r]
  · show a / r - 3 * a / 2 * (1 / r) ≤ 0
    have : a / r - 3 * a / 2 * (1 / r) = -(a / 2 / r) := by ring
    rw [this, neg_nonpos]
    positivity
  · show a / 2 * (1 / r) - a / r ≤ 0
    have : a / 2 * (1 / r) - a / r = -(a / 2 / r) := by ring
    rw [this, neg_nonpos]
    positivity

/-- `h(Σ_I(A)) = S⁰`. -/
theorem hasIndex_SIA (hc : 0 < c) (ha : a ^ 2 = 1 / 5) (ha0 : 0 < a) :
    HasIndex (ϕG c) (SIA c a) (Sphere 0) (Sphere.pt 0) := by
  have hN := isConvexNbhd_NA hc ha ha0
  have hP : IsIndexPair (ϕG c) (SIA c a) (NA c a) ∅ :=
    indexPair_of_fwd (isClosed_NA c a).isCompact (fun _ hx _ ht => NA_fwd hc ha ha0 hx ht) rfl
      hN.subset_interior
  refine hasIndex_sphere_zero_of_deform (ptA_mem_NA hc ha0) hP (deformNA hc ha0)
    (fun x => Subtype.ext (Subtype.ext (segPt_zero _))) (fun x => Subtype.ext (segPt_one _))

end SIA

/-! ## `h(TC^+) = S¹` -/

section TC

variable {c δ δ' : ℝ}

/-- `√(1 + u² + v²)` on the model space. -/
noncomputable def rhoS (p : XS) : ℝ := √(1 + uS p ^ 2 + vS p ^ 2)

theorem rhoS_pos (p : XS) : 0 < rhoS p := Real.sqrt_pos.2 (by positivity)

/-- The inverse chart `(u, v, x, y) ↦ ((1, u, v) / √(1 + u² + v²), (x, y))`. -/
noncomputable def chartInv (p : XS) : EG :=
  ((1 / rhoS p, uS p / rhoS p, vS p / rhoS p), (xS p, yS p))

theorem chartInv_mem (p : XS) : chartInv p ∈ OmG := by
  have hr := rhoS_pos p
  refine ⟨⟨?_, div_nonneg p.2.1 hr.le⟩, p.2.2⟩
  show (1 / rhoS p) ^ 2 + (uS p / rhoS p) ^ 2 + (vS p / rhoS p) ^ 2 = 1
  rw [div_pow, div_pow, div_pow, rhoS, Real.sq_sqrt (by positivity), ← add_div, ← add_div,
    one_pow, div_self (by positivity)]

theorem kapG_le_chartInv (H : TCHyp c δ δ') {p : XS} (hp : p ∈ NS δ δ') :
    kapG c ≤ gy1 ⟨chartInv p, chartInv_mem p⟩ := by
  show kapG c ≤ 1 / rhoS p
  have hc := H.hc
  have hk := kapG_pos hc
  have hkc := kapG_le_c c
  have hkh := kapG_le_half c
  have hv := p.2.1
  obtain ⟨hu, hv'⟩ := hp
  have hρ : rhoS p ≤ 1 + |uS p| + vS p := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    nlinarith [sq_abs (uS p), abs_nonneg (uS p), mul_nonneg (abs_nonneg (uS p)) hv]
  have h3 : c * (5 / 3 * δ + 14 / 15 * δ') < 1 / 2 := by
    have := mul_lt_mul_of_pos_left H.h3 hc
    rwa [show c * (1 / (2 * c)) = 1 / 2 by field_simp] at this
  have hcδ : 0 ≤ c * δ := mul_nonneg hc.le H.hδ.le
  have hku : kapG c * |uS p| ≤ c / 2 * δ :=
    mul_le_mul hkc hu (abs_nonneg _) (by positivity)
  have hkv : kapG c * vS p ≤ c / 2 * δ' := mul_le_mul hkc hv' hv (by positivity)
  rw [le_div_iff₀ (rhoS_pos p)]
  nlinarith [mul_le_mul_of_nonneg_left hρ hk.le]

theorem gu_chartInv (H : TCHyp c δ δ') {p : XS} (hp : p ∈ NS δ δ') :
    gu c ⟨chartInv p, chartInv_mem p⟩ = uS p := by
  rw [gu_eq _ (kapG_le_chartInv H hp)]
  show uS p / rhoS p / (1 / rhoS p) = uS p
  field_simp [(rhoS_pos p).ne']

theorem gv_chartInv (H : TCHyp c δ δ') {p : XS} (hp : p ∈ NS δ δ') :
    gv c ⟨chartInv p, chartInv_mem p⟩ = vS p := by
  rw [gv_eq _ (kapG_le_chartInv H hp)]
  show vS p / rhoS p / (1 / rhoS p) = vS p
  field_simp [(rhoS_pos p).ne']

/-- The chart `N^+ ≃ N_S`, `q ↦ (u, v, τ, σ)`. -/
noncomputable def chartG (H : TCHyp c δ δ') : NG c δ δ' ≃ₜ NS δ δ' where
  toFun q := ⟨⟨(gu c q, gv c q, gw1 q, gw2 q), gv_nonneg H.hc q, circle_G q⟩, q.2⟩
  invFun p := ⟨⟨chartInv p, chartInv_mem p⟩, by
    show |gu c _| ≤ δ ∧ gv c _ ≤ δ'
    rw [gu_chartInv H p.2, gv_chartInv H p.2]
    exact p.2⟩
  left_inv q := by
    have hk := kapG_lt_of_NG H q.2
    have h1 : 0 < gy1 q := (kapG_pos H.hc).trans hk
    have hs := sphere_G q
    have hρ : √(1 + (gy2 q / gy1 q) ^ 2 + (gy3 q / gy1 q) ^ 2) = 1 / gy1 q := by
      rw [show 1 + (gy2 q / gy1 q) ^ 2 + (gy3 q / gy1 q) ^ 2 = (1 / gy1 q) ^ 2 by
        field_simp; linarith]
      exact Real.sqrt_sq (by positivity)
    have e : ∀ x : ℝ, x / (1 / gy1 q) = x * gy1 q := fun x => by field_simp
    refine Subtype.ext (Subtype.ext (Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_)) rfl))
    · show 1 / √(1 + gu c q ^ 2 + gv c q ^ 2) = gy1 q
      rw [gu_eq _ hk.le, gv_eq _ hk.le, hρ, one_div_one_div]
    · show gu c q / √(1 + gu c q ^ 2 + gv c q ^ 2) = gy2 q
      rw [gu_eq _ hk.le, gv_eq _ hk.le, hρ, e]
      field_simp
    · show gv c q / √(1 + gu c q ^ 2 + gv c q ^ 2) = gy3 q
      rw [gu_eq _ hk.le, gv_eq _ hk.le, hρ, e]
      field_simp
  right_inv p := Subtype.ext (XS_ext (gu_chartInv H p.2) (gv_chartInv H p.2) rfl rfl)
  continuous_toFun := by
    have hq : Continuous fun q : NG c δ δ' => (q : OmG) := continuous_subtype_val
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact ((continuous_gu H.hc).comp hq).prodMk (((continuous_gv H.hc).comp hq).prodMk
      ((continuous_gw1.comp hq).prodMk (continuous_gw2.comp hq)))
  continuous_invFun := by
    have hp : Continuous fun p : NS δ δ' => ((p : XS) : E4) :=
      continuous_subtype_val.comp continuous_subtype_val
    have hu : Continuous fun p : NS δ δ' => uS p := continuous_fst.comp hp
    have hv : Continuous fun p : NS δ δ' => vS p := continuous_fst.comp (continuous_snd.comp hp)
    have hx : Continuous fun p : NS δ δ' => xS p :=
      continuous_fst.comp (continuous_snd.comp (continuous_snd.comp hp))
    have hy : Continuous fun p : NS δ δ' => yS p :=
      continuous_snd.comp (continuous_snd.comp (continuous_snd.comp hp))
    have hρ : Continuous fun p : NS δ δ' => rhoS p := by unfold rhoS; fun_prop
    have hne : ∀ p : NS δ δ', rhoS p ≠ 0 := fun p => (rhoS_pos p).ne'
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact ((continuous_const.div hρ hne).prodMk ((hu.div hρ hne).prodMk (hv.div hρ hne))).prodMk
      (hx.prodMk hy)

/-- `h(TC^+) = S¹` for the flow on `Ω`. -/
theorem hasIndex_TCp (H : TCHyp c δ δ') : HasIndex (ϕG c) TCp (Sphere 1) (Sphere.pt 1) := by
  obtain ⟨e⟩ := indexS1 H.hδ.le (H.hδ.trans H.h1).le
  have hP := (modelG H.hc).isIndexPair_L H
  rw [TCp_eq H.hc] at hP
  exact ⟨NG c δ δ', LG c δ δ', hP,
    ⟨(IndexSpace.homeoEquiv (chartG H) fun _ => Iff.rfl).trans e⟩⟩

end TC

/-! ## `cor:attractors` -/

section Attractors

variable {c a η δ : ℝ}

/-- The Morse sets below `TC^+`, below `M^-` and below `M^±`. -/
def P1 : Set GM := {.A, .Tp}
def P2 : Set GM := {.A, .Tp, .Bm}
def P3 : Set GM := {.A, .Tp, .Bm, .Bp}

/-- The attractor of the Morse sets in `P`. -/
def attrG (c a η δ : ℝ) (P : Set GM) : Set OmG := morseAttr (ϕG c) univ (MG c a η δ) P

theorem down_A : IsDown (fun i j : GM => i.rank < j.rank) {GM.A} := fun i j hij hj => by
  cases i <;> cases j <;> simp_all [GM.rank]

theorem down_P1 : IsDown (fun i j : GM => i.rank < j.rank) P1 := fun i j hij hj => by
  cases i <;> cases j <;> simp_all [P1, GM.rank]

theorem down_P2 : IsDown (fun i j : GM => i.rank < j.rank) P2 := fun i j hij hj => by
  cases i <;> cases j <;> simp_all [P2, GM.rank]

theorem down_P3 : IsDown (fun i j : GM => i.rank < j.rank) P3 := fun i j hij hj => by
  cases i <;> cases j <;> simp_all [P3, GM.rank]

variable (H : KHyp c a η δ)
include H

theorem isolated_attrG {P : Set GM} (hP : IsDown (fun i j : GM => i.rank < j.rank) P) :
    IsIsolatedInvariantSet (ϕG c) (attrG c a η δ P) :=
  (thmM_morse H).isIsolated_attr hP

/-- `(Σ_I(A), TC^+)` is an attractor–repeller pair in `A₁`. -/
theorem pair_A1 : IsAttractorRepellerPair (ϕG c) (attrG c a η δ P1) (SIA c a) TCp := by
  have h := thmM_morse H
  have hpair := h.isAttractorRepellerPair down_P1 down_A (by simp [P1])
  rw [h.attr_singleton down_A, h.attr_inter_rep_eq down_P1 down_A (k := GM.Tp) (by simp [P1])
    (by simp) fun l hl hl0 => by simp [P1] at hl hl0; tauto] at hpair
  exact hpair

/-- `(A₁, M^-)` is an attractor–repeller pair in `A₂`. -/
theorem pair_A12 : IsAttractorRepellerPair (ϕG c) (attrG c a η δ P2) (attrG c a η δ P1)
    (Inv (ϕG c) (Km a η δ)) := by
  have h := thmM_morse H
  have hpair := h.isAttractorRepellerPair down_P2 down_P1 (by simp [P1, P2, insert_subset_iff])
  rw [h.attr_inter_rep_eq down_P2 down_P1 (k := GM.Bm) (by simp [P2]) (by simp [P1])
    fun l hl hl0 => by simp [P1, P2] at hl hl0; tauto] at hpair
  exact hpair

/-- `(A₂, M^+)` is an attractor–repeller pair in `A₃`. -/
theorem pair_A23 : IsAttractorRepellerPair (ϕG c) (attrG c a η δ P3) (attrG c a η δ P2)
    (Inv (ϕG c) (Kp a η δ)) := by
  have h := thmM_morse H
  have hpair := h.isAttractorRepellerPair down_P3 down_P2 (by simp [P2, P3, insert_subset_iff])
  rw [h.attr_inter_rep_eq down_P3 down_P2 (k := GM.Bp) (by simp [P3]) (by simp [P2])
    fun l hl hl0 => by simp [P2, P3] at hl hl0; tauto] at hpair
  exact hpair

/-- Each `A_j` is an attractor of `Ω`. -/
theorem pair_univ {P : Set GM} (hP : IsDown (fun i j : GM => i.rank < j.rank) P) :
    ∃ R, IsAttractorRepellerPair (ϕG c) univ (attrG c a η δ P) R := by
  have h := thmM_morse H
  have hpair := h.isAttractorRepellerPair (P := univ) (fun _ _ _ _ => trivial) hP (subset_univ _)
  rw [h.attr_univ] at hpair
  exact ⟨_, hpair⟩

variable (K : Type) [CommRing K]

theorem hasTrivial_Mm : HasTrivialHomologyIndex K (pair_A12 H).isolated_R := by
  obtain ⟨N, L, hP, hc⟩ := H.indexTrivial_Mm
  exact hasTrivialHomologyIndex_of_indexPair (K := K) _ hP hc

theorem hasTrivial_Mp : HasTrivialHomologyIndex K (pair_A23 H).isolated_R := by
  obtain ⟨N, L, hP, hc⟩ := H.indexTrivial_Mp
  exact hasTrivialHomologyIndex_of_indexPair (K := K) _ hP hc

/-- `CH_*(A₁) = K[0] ⊕ K[1]`. -/
theorem hasPointCircleIndex_A1 : HasPointCircleIndex K (isolated_attrG H down_P1) := by
  have hp := pair_A1 H
  obtain ⟨R, hU⟩ := pair_univ H down_P1
  obtain ⟨B, hB, -⟩ := hU.exists_trapping
  obtain ⟨d, d', hT, -⟩ := exists_TC H.hc H.ha0
  have hne : (attrG c a η δ P1).Nonempty := by
    have hq : ((1 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ HF ∧ ((1 : ℝ), (0 : ℝ)) ∈ S1 :=
      ⟨⟨by norm_num, le_rfl⟩, by norm_num [S1]⟩
    exact ⟨_, hp.subset_R (show (⟨(((1 : ℝ), (0 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))), hq⟩ : OmG) ∈ TCp
      from rfl)⟩
  exact homologyIndex_point_circle K hp hB hne
    ((hasIndex_SIA H.hc H.ha H.ha0).homologyIndex_sphere K hp.isolated_A)
    ((hasIndex_TCp hT).homologyIndex_sphere K hp.isolated_R)

/-- The maps `CH_*(A₁) → CH_*(A₂)` of the attractor–repeller sequence are isomorphisms. -/
theorem iso_A12 : ∃ i : ∀ n, homologyIndex K (ϕG c) (isolated_attrG H down_P1) n →ₗ[K]
    homologyIndex K (ϕG c) (isolated_attrG H down_P2) n, ∀ n, Function.Bijective (i n) :=
  homologyIndex_attractor_iso_of_pair K (pair_A12 H) (hasTrivial_Mm H K)

/-- The maps `CH_*(A₂) → CH_*(A₃)` of the attractor–repeller sequence are isomorphisms. -/
theorem iso_A23 : ∃ i : ∀ n, homologyIndex K (ϕG c) (isolated_attrG H down_P2) n →ₗ[K]
    homologyIndex K (ϕG c) (isolated_attrG H down_P3) n, ∀ n, Function.Bijective (i n) :=
  homologyIndex_attractor_iso_of_pair K (pair_A23 H) (hasTrivial_Mp H K)

theorem hasPointCircleIndex_A2 : HasPointCircleIndex K (isolated_attrG H down_P2) := by
  obtain ⟨i, hi⟩ := iso_A12 H K
  exact (hasPointCircleIndex_A1 H K).of_bijective i hi

theorem hasPointCircleIndex_A3 : HasPointCircleIndex K (isolated_attrG H down_P3) := by
  obtain ⟨i, hi⟩ := iso_A23 H K
  exact (hasPointCircleIndex_A2 H K).of_bijective i hi

/-- `cor:attractors`. Over any commutative ring `K`:
* `CH_*(A_j) = K[0] ⊕ K[1]` for `j = 1, 2, 3`;
* the maps `CH_*(A₁) → CH_*(A₂) → CH_*(A₃)` of the attractor–repeller sequences of
  `(A₁, M^-)` in `A₂` and `(A₂, M^+)` in `A₃` are isomorphisms;
* each `A_j` has a compact positively invariant neighborhood `B` with `Inv(B) = A_j`, and every
  such `B` has `H_*(B) = K[0] ⊕ K[1]`. -/
theorem cor_attractors :
    (HasPointCircleIndex K (isolated_attrG H down_P1) ∧
      HasPointCircleIndex K (isolated_attrG H down_P2) ∧
      HasPointCircleIndex K (isolated_attrG H down_P3)) ∧
    ((∃ i : ∀ n, homologyIndex K (ϕG c) (isolated_attrG H down_P1) n →ₗ[K]
        homologyIndex K (ϕG c) (isolated_attrG H down_P2) n, ∀ n, Function.Bijective (i n)) ∧
      (∃ i : ∀ n, homologyIndex K (ϕG c) (isolated_attrG H down_P2) n →ₗ[K]
        homologyIndex K (ϕG c) (isolated_attrG H down_P3) n, ∀ n, Function.Bijective (i n))) ∧
    ∀ P ∈ ({P1, P2, P3} : Set (Set GM)),
      (∃ B : Set OmG, IsCompact B ∧ (∀ x ∈ B, ∀ t, 0 ≤ t → ϕG c t x ∈ B) ∧
        Inv (ϕG c) B = attrG c a η δ P ∧ attrG c a η δ P ⊆ interior B) ∧
      ∀ B : Set OmG, IsCompact B → (∀ x ∈ B, ∀ t, 0 ≤ t → ϕG c t x ∈ B) →
        Inv (ϕG c) B = attrG c a η δ P → attrG c a η δ P ⊆ interior B →
        Nonempty (singH K OmG (Int.ofNat 0) B ∅ ≃ₗ[K] K) ∧
          Nonempty (singH K OmG (Int.ofNat 1) B ∅ ≃ₗ[K] K) ∧
          ∀ n, 2 ≤ n → Subsingleton (singH K OmG (Int.ofNat n) B ∅) := by
  refine ⟨⟨hasPointCircleIndex_A1 H K, hasPointCircleIndex_A2 H K, hasPointCircleIndex_A3 H K⟩,
    ⟨iso_A12 H K, iso_A23 H K⟩, fun P hP => ?_⟩
  have key : ∀ (hP : IsDown (fun i j : GM => i.rank < j.rank) P),
      HasPointCircleIndex K (isolated_attrG H hP) →
      (∃ B : Set OmG, IsCompact B ∧ (∀ x ∈ B, ∀ t, 0 ≤ t → ϕG c t x ∈ B) ∧
        Inv (ϕG c) B = attrG c a η δ P ∧ attrG c a η δ P ⊆ interior B) ∧
      ∀ B : Set OmG, IsCompact B → (∀ x ∈ B, ∀ t, 0 ≤ t → ϕG c t x ∈ B) →
        Inv (ϕG c) B = attrG c a η δ P → attrG c a η δ P ⊆ interior B →
        Nonempty (singH K OmG (Int.ofNat 0) B ∅ ≃ₗ[K] K) ∧
          Nonempty (singH K OmG (Int.ofNat 1) B ∅ ≃ₗ[K] K) ∧
          ∀ n, 2 ≤ n → Subsingleton (singH K OmG (Int.ofNat n) B ∅) := fun hP hI => by
    obtain ⟨R, hU⟩ := pair_univ H hP
    obtain ⟨B, -, hB⟩ := hU.exists_trapping
    exact ⟨⟨B, hB⟩, fun B hB hf hi hint => hI.singH K hB hf hi hint⟩
  simp only [mem_insert_iff, mem_singleton_iff] at hP
  rcases hP with rfl | rfl | rfl
  · exact key down_P1 (hasPointCircleIndex_A1 H K)
  · exact key down_P2 (hasPointCircleIndex_A2 H K)
  · exact key down_P3 (hasPointCircleIndex_A3 H K)

end Attractors

end ConleyCheck.Gubser
