import ConleyCheck.Gubser.MBlocks
import ConleyCheck.Gubser.TCIndex

/-!
# The Conley indices of `M^±` (`thm:M` (i))

Both blocks are instances of the model block `K = {σ y₃ ≤ e y₂, |δ y₁| ≤ e y₂}` with `e = ±1`, whose
exit set is `L = K ∩ ({σ y₃ = e y₂, y₁ + k τ y₃ ≥ 0} ∪ {δ y₁ = e y₂})`. In the chart
`U = δ y₁ / (e y₂)`, `Z = σ y₃ / (e y₂)`, the slice of `K` over each `w` is the square
`[-1, 1] × [0, 1]`, and that of `L` is the arc formed by `{Z = 1, U ≥ u₀}` and `{U = 1}`, where
`u₀ = -δ k τ / σ ∈ (-1, 1)`. The straight-line homotopy to an explicit retraction onto this arc
deforms `K` into `L` through maps fixing `L`, so `K/L` is contractible (`CP.indexTrivial`).
-/

open Set unitInterval
open ConleyCheck.Conley ConleyCheck.ODE

namespace ConleyCheck.Gubser

/-- The parameters of the model block. -/
structure CP where
  e : ℝ
  sg : ℝ
  dl : ℝ
  k : ℝ
  he : e ^ 2 = 1
  hsg : 0 < sg
  hdl : 0 < dl
  hk0 : 0 ≤ k
  hk : dl * k < sg

namespace CP

variable (P : CP)

/-- The model block. -/
def K : Set OmG :=
  {q | P.sg * gy3 q - P.e * gy2 q ≤ 0 ∧ P.dl * gy1 q - P.e * gy2 q ≤ 0 ∧
    -P.dl * gy1 q - P.e * gy2 q ≤ 0}

/-- Its exit set. -/
def L : Set OmG :=
  {q | q ∈ P.K ∧ ((P.sg * gy3 q - P.e * gy2 q = 0 ∧ 0 ≤ gy1 q + P.k * gw1 q * gy3 q) ∨
    P.dl * gy1 q - P.e * gy2 q = 0)}

/-- A lower bound for `e y₂` on `K`. -/
noncomputable def ε : ℝ := P.dl ^ 2 * P.sg ^ 2 / (P.sg ^ 2 + P.dl ^ 2 * P.sg ^ 2 + P.dl ^ 2)

noncomputable def d (q : OmG) : ℝ := max (P.e * gy2 q) P.ε
noncomputable def U (q : OmG) : ℝ := P.dl * gy1 q / P.d q
noncomputable def Z (q : OmG) : ℝ := P.sg * gy3 q / P.d q
noncomputable def u0 (q : OmG) : ℝ := -(P.dl * P.k / P.sg * gw1 q)

/-- The position along the arc `L`, between `0` (the point `(u₀, 1)`) and `2` (the point
`(1, 0)`). -/
noncomputable def lam (q : OmG) : ℝ :=
  max 0 (min 2 ((P.U q - P.u0 q) / (1 - P.u0 q) + 1 - P.Z q))

noncomputable def rU (q : OmG) : ℝ := P.u0 q + min (P.lam q) 1 * (1 - P.u0 q)
noncomputable def rZ (q : OmG) : ℝ := 2 - max (P.lam q) 1
noncomputable def hU (t : ℝ) (q : OmG) : ℝ := (1 - t) * P.U q + t * P.rU q
noncomputable def hZ (t : ℝ) (q : OmG) : ℝ := (1 - t) * P.Z q + t * P.rZ q
noncomputable def n (t : ℝ) (q : OmG) : ℝ :=
  Real.sqrt ((P.hU t q / P.dl) ^ 2 + 1 + (P.hZ t q / P.sg) ^ 2)

/-- The point with chart coordinates `(hU, hZ)` over the base point of `q`. -/
noncomputable def pt (t : ℝ) (q : OmG) : EG :=
  ((P.hU t q / P.dl / P.n t q, P.e / P.n t q, P.hZ t q / P.sg / P.n t q), (q : EG).2)

/-! ## Elementary bounds -/

theorem ε_pos : 0 < P.ε := by
  unfold ε; have := P.hsg; have := P.hdl; positivity

theorem d_pos (q : OmG) : 0 < P.d q := lt_max_of_lt_right P.ε_pos

theorem ε_le {q : OmG} (hq : q ∈ P.K) : P.ε ≤ P.e * gy2 q := by
  obtain ⟨h1, h2, h3⟩ := hq
  have hs := sphere_G q
  have hσ := P.hsg
  have hδ := P.hdl
  have he2 : (P.e * gy2 q) ^ 2 = gy2 q ^ 2 := by rw [mul_pow, P.he, one_mul]
  have hpos : 0 ≤ P.e * gy2 q := by linarith
  have hy1 : (P.dl * gy1 q) ^ 2 ≤ (P.e * gy2 q) ^ 2 := sq_le_sq' (by linarith) (by linarith)
  have hy3 : (P.sg * gy3 q) ^ 2 ≤ (P.e * gy2 q) ^ 2 :=
    sq_le_sq' (by nlinarith [gy3_nonneg q]) (by linarith)
  rw [he2] at hy1 hy3
  have hle : P.e * gy2 q ≤ 1 := by nlinarith
  have e1 : P.sg ^ 2 * (P.dl * gy1 q) ^ 2 ≤ P.sg ^ 2 * gy2 q ^ 2 :=
    mul_le_mul_of_nonneg_left hy1 (sq_nonneg _)
  have e3 : P.dl ^ 2 * (P.sg * gy3 q) ^ 2 ≤ P.dl ^ 2 * gy2 q ^ 2 :=
    mul_le_mul_of_nonneg_left hy3 (sq_nonneg _)
  have key : P.dl ^ 2 * P.sg ^ 2 = P.dl ^ 2 * P.sg ^ 2 * (gy1 q ^ 2 + gy2 q ^ 2 + gy3 q ^ 2) := by
    rw [hs, mul_one]
  have hε : P.ε ≤ gy2 q ^ 2 := by
    unfold ε
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

theorem d_eq {q : OmG} (hq : q ∈ P.K) : P.d q = P.e * gy2 q := max_eq_left (P.ε_le hq)

theorem ey2_pos {q : OmG} (hq : q ∈ P.K) : 0 < P.e * gy2 q := P.d_eq hq ▸ P.d_pos q

theorem continuous_d : Continuous P.d :=
  (continuous_const.mul continuous_gy2).max continuous_const

theorem continuous_U : Continuous P.U :=
  (continuous_const.mul continuous_gy1).div P.continuous_d fun q => (P.d_pos q).ne'

theorem continuous_Z : Continuous P.Z :=
  (continuous_const.mul continuous_gy3).div P.continuous_d fun q => (P.d_pos q).ne'

theorem continuous_u0 : Continuous P.u0 := (continuous_const.mul continuous_gw1).neg

theorem u0_mem (q : OmG) : -1 < P.u0 q ∧ P.u0 q < 1 := by
  have hκ0 : 0 ≤ P.dl * P.k / P.sg := div_nonneg (mul_nonneg P.hdl.le P.hk0) P.hsg.le
  have hκ1 : P.dl * P.k / P.sg < 1 := (div_lt_one P.hsg).2 P.hk
  have hτ := gw1_mem q
  have a1 := mul_le_mul_of_nonneg_left hτ.2 hκ0
  have a2 := mul_le_mul_of_nonneg_left hτ.1 hκ0
  unfold u0
  constructor <;> nlinarith

theorem one_sub_u0_pos (q : OmG) : 0 < 1 - P.u0 q := by linarith [(P.u0_mem q).2]

theorem continuous_lam : Continuous P.lam :=
  continuous_const.max (continuous_const.min
    ((((P.continuous_U.sub P.continuous_u0).div (continuous_const.sub P.continuous_u0)
      fun q => (P.one_sub_u0_pos q).ne').add continuous_const).sub P.continuous_Z))

theorem continuous_rU : Continuous P.rU :=
  P.continuous_u0.add ((P.continuous_lam.min continuous_const).mul
    (continuous_const.sub P.continuous_u0))

theorem continuous_rZ : Continuous P.rZ :=
  continuous_const.sub (P.continuous_lam.max continuous_const)

theorem lam_mem (q : OmG) : P.lam q ∈ Icc (0 : ℝ) 2 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem rU_mem (q : OmG) : P.rU q ∈ Icc (-1 : ℝ) 1 := by
  have h1 : 0 ≤ min (P.lam q) 1 := le_min (P.lam_mem q).1 zero_le_one
  have h2 : min (P.lam q) 1 ≤ 1 := min_le_right _ _
  have := P.u0_mem q
  have := P.one_sub_u0_pos q
  unfold rU
  constructor <;> nlinarith

theorem rZ_mem (q : OmG) : P.rZ q ∈ Icc (0 : ℝ) 1 := by
  have h1 : 1 ≤ max (P.lam q) 1 := le_max_right _ _
  have h2 : max (P.lam q) 1 ≤ 2 := max_le (P.lam_mem q).2 (by norm_num)
  unfold rZ
  constructor <;> linarith

theorem U_mem {q : OmG} (hq : q ∈ P.K) : P.U q ∈ Icc (-1 : ℝ) 1 := by
  have hp := P.ey2_pos hq
  unfold U
  rw [P.d_eq hq]
  obtain ⟨-, h2, h3⟩ := hq
  exact ⟨by rw [le_div_iff₀ hp]; linarith, by rw [div_le_one hp]; linarith⟩

theorem Z_mem {q : OmG} (hq : q ∈ P.K) : P.Z q ∈ Icc (0 : ℝ) 1 := by
  have hp := P.ey2_pos hq
  unfold Z
  rw [P.d_eq hq]
  obtain ⟨h1, -, -⟩ := hq
  exact ⟨div_nonneg (mul_nonneg P.hsg.le (gy3_nonneg q)) hp.le, by rw [div_le_one hp]; linarith⟩

theorem conv_mem {t lo hi x y : ℝ} (ht : t ∈ I) (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo hi) :
    (1 - t) * x + t * y ∈ Icc lo hi := by
  have := ht.1; have := ht.2; have := hx.1; have := hx.2; have := hy.1; have := hy.2
  constructor <;> nlinarith

theorem hU_mem (t : I) {q : OmG} (hq : q ∈ P.K) : P.hU t q ∈ Icc (-1 : ℝ) 1 :=
  conv_mem t.2 (P.U_mem hq) (P.rU_mem q)

theorem hZ_mem (t : I) {q : OmG} (hq : q ∈ P.K) : P.hZ t q ∈ Icc (0 : ℝ) 1 :=
  conv_mem t.2 (P.Z_mem hq) (P.rZ_mem q)

theorem n_pos (t : ℝ) (q : OmG) : 0 < P.n t q := Real.sqrt_pos.2 (by positivity)

theorem n_sq (t : ℝ) (q : OmG) :
    P.n t q ^ 2 = (P.hU t q / P.dl) ^ 2 + 1 + (P.hZ t q / P.sg) ^ 2 :=
  Real.sq_sqrt (by positivity)

/-! ## The deformation -/

theorem pt_mem (t : ℝ) (q : OmG) (hZ0 : 0 ≤ P.hZ t q) : P.pt t q ∈ OmG := by
  refine ⟨⟨?_, ?_⟩, (q : OmG).2.2⟩
  · show (P.hU t q / P.dl / P.n t q) ^ 2 + (P.e / P.n t q) ^ 2 + (P.hZ t q / P.sg / P.n t q) ^ 2 = 1
    have hn := (P.n_pos t q).ne'
    have e : (P.hU t q / P.dl / P.n t q) ^ 2 + (P.e / P.n t q) ^ 2 +
        (P.hZ t q / P.sg / P.n t q) ^ 2 =
        ((P.hU t q / P.dl) ^ 2 + P.e ^ 2 + (P.hZ t q / P.sg) ^ 2) / P.n t q ^ 2 := by
      field_simp
    rw [e, P.he, ← P.n_sq, div_self (pow_ne_zero 2 hn)]
  · exact div_nonneg (div_nonneg hZ0 P.hsg.le) (P.n_pos t q).le

/-- The deformed point as a point of `Ω`. -/
noncomputable def ptO (t : I) (q : P.K) : OmG :=
  ⟨P.pt t q, P.pt_mem t q (P.hZ_mem t q.2).1⟩

theorem ptO_ey2 (t : I) (q : P.K) : P.e * gy2 (P.ptO t q) = 1 / P.n t q := by
  show P.e * (P.e / P.n t q) = 1 / P.n t q
  rw [← mul_div_assoc, ← sq, P.he]

theorem ptO_y1 (t : I) (q : P.K) : P.dl * gy1 (P.ptO t q) = P.hU t q / P.n t q := by
  show P.dl * (P.hU t q / P.dl / P.n t q) = P.hU t q / P.n t q
  have := P.hdl.ne'
  field_simp

theorem ptO_y3 (t : I) (q : P.K) : P.sg * gy3 (P.ptO t q) = P.hZ t q / P.n t q := by
  show P.sg * (P.hZ t q / P.sg / P.n t q) = P.hZ t q / P.n t q
  have := P.hsg.ne'
  field_simp

theorem ptO_w1 (t : I) (q : P.K) : gw1 (P.ptO t q) = gw1 (q : OmG) := rfl

theorem ptO_mem (t : I) (q : P.K) : P.ptO t q ∈ P.K := by
  have hn := P.n_pos t q
  have hU := P.hU_mem t q.2
  have hZ := P.hZ_mem t q.2
  refine ⟨?_, ?_, ?_⟩
  · rw [P.ptO_y3, P.ptO_ey2, div_sub_div_same]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hZ.2]) hn.le
  · rw [P.ptO_y1, P.ptO_ey2, div_sub_div_same]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hU.2]) hn.le
  · rw [neg_mul, P.ptO_y1, P.ptO_ey2, ← neg_div, div_sub_div_same]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hU.1]) hn.le

theorem continuous_hU : Continuous fun p : ℝ × OmG => P.hU p.1 p.2 :=
  ((continuous_const.sub continuous_fst).mul (P.continuous_U.comp continuous_snd)).add
    (continuous_fst.mul (P.continuous_rU.comp continuous_snd))

theorem continuous_hZ : Continuous fun p : ℝ × OmG => P.hZ p.1 p.2 :=
  ((continuous_const.sub continuous_fst).mul (P.continuous_Z.comp continuous_snd)).add
    (continuous_fst.mul (P.continuous_rZ.comp continuous_snd))

theorem continuous_n : Continuous fun p : ℝ × OmG => P.n p.1 p.2 :=
  Real.continuous_sqrt.comp ((((P.continuous_hU.div_const _).pow 2).add continuous_const).add
    ((P.continuous_hZ.div_const _).pow 2))

theorem continuous_pt : Continuous fun p : ℝ × OmG => P.pt p.1 p.2 := by
  have hn : ∀ p : ℝ × OmG, P.n p.1 p.2 ≠ 0 := fun p => (P.n_pos _ _).ne'
  exact ((((P.continuous_hU.div_const _).div P.continuous_n hn).prodMk
    ((continuous_const.div P.continuous_n hn).prodMk
      ((P.continuous_hZ.div_const _).div P.continuous_n hn))).prodMk
    (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))

/-- The deformation of `K` into `L`. -/
noncomputable def H : C(I × P.K, P.K) where
  toFun p := ⟨P.ptO p.1 p.2, P.ptO_mem p.1 p.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact P.continuous_pt.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

/-- If the chart coordinates are unchanged, so is the point. -/
theorem pt_eq_self {t : ℝ} {q : OmG} (hq : q ∈ P.K) (h1 : P.hU t q = P.U q)
    (h2 : P.hZ t q = P.Z q) : P.pt t q = (q : EG) := by
  have hd := P.d_eq hq
  have hp := P.ey2_pos hq
  have hne := hp.ne'
  have he0 : P.e ≠ 0 := left_ne_zero_of_mul hne
  have hy2 : gy2 q ≠ 0 := right_ne_zero_of_mul hne
  have hδ := P.hdl.ne'
  have hσ := P.hsg.ne'
  have hU' : P.hU t q / P.dl = gy1 q / (P.e * gy2 q) := by
    rw [h1, U, hd]; field_simp
  have hZ' : P.hZ t q / P.sg = gy3 q / (P.e * gy2 q) := by
    rw [h2, Z, hd]; field_simp
  have key : (gy1 q / (P.e * gy2 q)) ^ 2 + 1 + (gy3 q / (P.e * gy2 q)) ^ 2 =
      (1 / (P.e * gy2 q)) ^ 2 := by
    have hs := sphere_G q
    have he := P.he
    field_simp
    linear_combination hs + gy2 q ^ 2 * he
  have hn : P.n t q = 1 / (P.e * gy2 q) := by
    unfold n
    rw [hU', hZ', key]
    exact Real.sqrt_sq (by positivity)
  refine Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_)) rfl
  · show P.hU t q / P.dl / P.n t q = gy1 q
    rw [hU', hn]; field_simp
  · show P.e / P.n t q = gy2 q
    rw [hn, div_div_eq_mul_div, div_one, ← mul_assoc, ← sq, P.he, one_mul]
  · show P.hZ t q / P.sg / P.n t q = gy3 q
    rw [hZ', hn]; field_simp

theorem H_zero (x : P.K) : P.H (0, x) = x :=
  Subtype.ext (Subtype.ext (P.pt_eq_self x.2 (by simp [hU]) (by simp [hZ])))

/-- On `L` the retraction is the identity. -/
theorem r_eq {q : OmG} (hq : q ∈ P.L) : P.rU q = P.U q ∧ P.rZ q = P.Z q := by
  obtain ⟨hK, h⟩ := hq
  have hd := P.d_eq hK
  have hp := P.ey2_pos hK
  have hU := P.U_mem hK
  have hZ := P.Z_mem hK
  have h0 := P.one_sub_u0_pos q
  rcases h with ⟨h1, hQ⟩ | h1
  · have hZ1 : P.Z q = 1 := by
      unfold Z; rw [hd, div_eq_one_iff_eq hp.ne']; linarith
    have hy3 : gy3 q = P.e * gy2 q / P.sg := by
      rw [eq_div_iff P.hsg.ne']; linarith
    have hUu : P.U q - P.u0 q = P.dl * (gy1 q + P.k * gw1 q * gy3 q) / (P.e * gy2 q) := by
      unfold U u0
      rw [hd, hy3]
      have := P.hsg.ne'
      have : P.e ≠ 0 := left_ne_zero_of_mul hp.ne'
      have : gy2 q ≠ 0 := right_ne_zero_of_mul hp.ne'
      field_simp
      ring
    have hge : 0 ≤ P.U q - P.u0 q := by
      rw [hUu]; exact div_nonneg (mul_nonneg P.hdl.le hQ) hp.le
    have hlam : P.lam q = (P.U q - P.u0 q) / (1 - P.u0 q) := by
      unfold lam
      rw [hZ1, add_sub_cancel_right]
      have : (P.U q - P.u0 q) / (1 - P.u0 q) ≤ 1 := by
        rw [div_le_one h0]; linarith [hU.2]
      rw [min_eq_right (by linarith), max_eq_right (div_nonneg hge h0.le)]
    have hl1 : P.lam q ≤ 1 := by rw [hlam, div_le_one h0]; linarith [hU.2]
    refine ⟨?_, ?_⟩
    · unfold rU
      rw [min_eq_left hl1, hlam, div_mul_cancel₀ _ h0.ne']
      ring
    · unfold rZ
      rw [max_eq_right hl1, hZ1]
      norm_num
  · have hU1 : P.U q = 1 := by
      unfold U; rw [hd, div_eq_one_iff_eq hp.ne']; linarith
    have hlam : P.lam q = 2 - P.Z q := by
      unfold lam
      rw [hU1, div_self h0.ne']
      rw [min_eq_right (by linarith [hZ.1]), max_eq_right (by linarith [hZ.2])]
      ring
    have hl1 : 1 ≤ P.lam q := by rw [hlam]; linarith [hZ.2]
    refine ⟨?_, ?_⟩
    · unfold rU
      rw [min_eq_right hl1, hU1]
      ring
    · unfold rZ
      rw [max_eq_left hl1, hlam]
      ring

theorem H_L (t : I) (x : P.K) (hx : (x : OmG) ∈ P.L) : ((P.H (t, x) : P.K) : OmG) ∈ P.L := by
  have h := P.r_eq hx
  have he : P.H (t, x) = x := Subtype.ext (Subtype.ext (P.pt_eq_self x.2
    (by unfold hU; rw [h.1]; ring) (by unfold hZ; rw [h.2]; ring)))
  rw [he]
  exact hx

theorem H_one (x : P.K) : ((P.H (1, x) : P.K) : OmG) ∈ P.L := by
  have hn := P.n_pos 1 x
  have hU1 : P.hU 1 x = P.rU x := by unfold hU; ring
  have hZ1 : P.hZ 1 x = P.rZ x := by unfold hZ; ring
  refine ⟨P.ptO_mem 1 x, ?_⟩
  show (P.sg * gy3 (P.ptO 1 x) - P.e * gy2 (P.ptO 1 x) = 0 ∧
    0 ≤ gy1 (P.ptO 1 x) + P.k * gw1 (P.ptO 1 x) * gy3 (P.ptO 1 x)) ∨
    P.dl * gy1 (P.ptO 1 x) - P.e * gy2 (P.ptO 1 x) = 0
  rcases le_total (P.lam x) 1 with hl | hl
  · have hrZ : P.rZ x = 1 := by unfold rZ; rw [max_eq_right hl]; norm_num
    refine Or.inl ⟨?_, ?_⟩
    · rw [P.ptO_y3, P.ptO_ey2, Set.Icc.coe_one, hZ1, hrZ, sub_self]
    · have e : gy1 (P.ptO 1 x) + P.k * gw1 (P.ptO 1 x) * gy3 (P.ptO 1 x) =
          P.lam x * (1 - P.u0 x) / P.dl / P.n 1 x := by
        show P.hU 1 x / P.dl / P.n 1 x + P.k * gw1 (x : OmG) * (P.hZ 1 x / P.sg / P.n 1 x) =
          P.lam x * (1 - P.u0 x) / P.dl / P.n 1 x
        rw [hU1, hZ1, hrZ]
        unfold rU
        rw [min_eq_left hl]
        unfold u0
        have := P.hsg.ne'
        have := P.hdl.ne'
        have := hn.ne'
        field_simp
        ring
      rw [e]
      exact div_nonneg (div_nonneg (mul_nonneg (P.lam_mem x).1 (P.one_sub_u0_pos x).le)
        P.hdl.le) hn.le
  · have hrU : P.rU x = 1 := by unfold rU; rw [min_eq_right hl]; ring
    refine Or.inr ?_
    rw [P.ptO_y1, P.ptO_ey2, Set.Icc.coe_one, hU1, hrU, sub_self]

/-- The model block has trivial index for every flow for which it is an isolating block with exit
set `L`. -/
theorem indexTrivial {ϕ : Flow ℝ OmG} (hB : IsBlock ϕ P.K P.L) : IndexTrivial ϕ (Inv ϕ P.K) :=
  ⟨P.K, P.L, hB.isIndexPair,
    pointedContractible_of_deform P.H P.H_zero P.H_L P.H_one⟩

end CP

/-! ## `thm:M` (i) -/

namespace KHyp

variable {c a η δ : ℝ} (H : KHyp c a η δ)
include H

/-- `K^-` as a model block. -/
noncomputable def cpm : CP where
  e := -1
  sg := a - η
  dl := δ
  k := kS c a (a - η)
  he := by norm_num
  hsg := H.haη
  hdl := H.hδ
  hk0 := H.kminus_pos.le
  hk := by rw [kS_minus]; exact H.k2m

/-- `K^+` as a model block. -/
noncomputable def cpp : CP where
  e := 1
  sg := a + η
  dl := δ
  k := kS c a (-(a + η))
  he := by norm_num
  hsg := H.haη'
  hdl := H.hδ
  hk0 := H.kplus_pos.le
  hk := by rw [kS_plus]; exact H.k2p

theorem Km_eq : Km a η δ = H.cpm.K := by
  ext q
  simp only [Km, CP.K, cpm, gH, gL, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨by linarith, by linarith, by linarith⟩

theorem Lm_eq : Lm c a η δ = H.cpm.L := by
  ext q
  simp only [Lm, CP.L, H.Km_eq, cpm, gH, gL, gQ, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hK, (⟨h1, h2⟩ | h1)⟩
    · exact ⟨hK, Or.inl ⟨by linarith, h2⟩⟩
    · exact ⟨hK, Or.inr (by linarith)⟩
  · rintro ⟨hK, (⟨h1, h2⟩ | h1)⟩
    · exact ⟨hK, Or.inl ⟨by linarith, h2⟩⟩
    · exact ⟨hK, Or.inr (by linarith)⟩

theorem Kp_eq : Kp a η δ = H.cpp.K := by
  ext q
  simp only [Kp, CP.K, cpp, gG, gL, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨by linarith, by linarith, by linarith⟩

theorem Lp_eq : Lp c a η δ = H.cpp.L := by
  ext q
  simp only [Lp, CP.L, H.Kp_eq, cpp, gG, gL, gQ, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hK, (⟨h1, h2⟩ | h1)⟩
    · exact ⟨hK, Or.inl ⟨by linarith, h2⟩⟩
    · exact ⟨hK, Or.inr (by linarith)⟩
  · rintro ⟨hK, (⟨h1, h2⟩ | h1)⟩
    · exact ⟨hK, Or.inl ⟨by linarith, h2⟩⟩
    · exact ⟨hK, Or.inr (by linarith)⟩

/-- `thm:M` (i) for `M^-`: the Conley index of `Inv(K^-)` is trivial. -/
theorem indexTrivial_Mm : IndexTrivial (ϕG c) (Inv (ϕG c) (Km a η δ)) := by
  have hB := H.isBlock_Km
  rw [H.Km_eq, H.Lm_eq] at hB
  rw [H.Km_eq]
  exact H.cpm.indexTrivial hB

/-- `thm:M` (i) for `M^+`: the Conley index of `Inv(K^+)` is trivial. -/
theorem indexTrivial_Mp : IndexTrivial (ϕG c) (Inv (ϕG c) (Kp a η δ)) := by
  have hB := H.isBlock_Kp
  rw [H.Kp_eq, H.Lp_eq] at hB
  rw [H.Kp_eq]
  exact H.cpp.indexTrivial hB

end KHyp

end ConleyCheck.Gubser
