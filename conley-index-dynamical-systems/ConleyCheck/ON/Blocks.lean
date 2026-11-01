import ConleyCheck.ON.Unstable
import ConleyCheck.Conley.FaceBlock
import ConleyCheck.Conley.PointIndex

/-!
# Small isolating blocks of the `O(N)`-type model

Boxes `b ≤ λ ≤ t`, `|w| ≤ e` in linear coordinates `λ, w` of the plane.

* `LBox.isBlock`: if the flow crosses the face `λ = b` outward and the other three faces inward,
  the box is an isolating block with exit set the face `λ = b`, and the quotient is contractible.
* `boxG`: a square around `Σ_G` with no exit set.
* `boxI`, `boxH`, `boxC`: thin boxes around the segments from `Σ_I`, `Σ_H` (`N > 4`), `Σ_C`
  (`N < 4`) to `Σ_G` along the invariant lines.
-/

open Set Filter Topology

namespace ConleyCheck.ON

open ConleyCheck.Conley ConleyCheck.ODE ConleyCheck.Gubser

variable {N : ℝ}

/-! ## Boxes in linear coordinates -/

/-- The box `b ≤ l₁ y₁ + l₂ y₂ ≤ t`, `|w₁ y₁ + w₂ y₂| ≤ e`. -/
structure LBox where
  l₁ : ℝ
  l₂ : ℝ
  w₁ : ℝ
  w₂ : ℝ
  b : ℝ
  t : ℝ
  e : ℝ

namespace LBox

variable (B : LBox)

def lam (p : ℝ × ℝ) : ℝ := B.l₁ * p.1 + B.l₂ * p.2

def wc (p : ℝ × ℝ) : ℝ := B.w₁ * p.1 + B.w₂ * p.2

/-- The four constraints `g k ≤ 0` of the box. -/
def g : Fin 4 → ℝ × ℝ → ℝ :=
  ![fun p => B.b - B.lam p, fun p => B.lam p - B.t, fun p => B.wc p - B.e, fun p => -B.wc p - B.e]

def set : Set (ℝ × ℝ) := {p | ∀ k, B.g k p ≤ 0}

/-- The face `λ = b`. -/
def exit : Set (ℝ × ℝ) := {p | (∀ k, B.g k p ≤ 0) ∧ ∃ k ∈ ({0} : Set (Fin 4)), B.g k p = 0}

theorem fin4 (k : Fin 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
  fin_cases k <;> simp

theorem g_zero : B.g 0 = fun p => B.b - B.lam p := rfl
theorem g_one : B.g 1 = fun p => B.lam p - B.t := rfl
theorem g_two : B.g 2 = fun p => B.wc p - B.e := rfl
theorem g_three : B.g 3 = fun p => -B.wc p - B.e := rfl

theorem continuous_g (k : Fin 4) : Continuous (B.g k) := by
  rcases fin4 k with rfl | rfl | rfl | rfl <;>
    simp only [g_zero, g_one, g_two, g_three, lam, wc] <;> fun_prop

theorem mem_set {p : ℝ × ℝ} :
    p ∈ B.set ↔ B.b ≤ B.lam p ∧ B.lam p ≤ B.t ∧ B.wc p ≤ B.e ∧ -B.e ≤ B.wc p := by
  constructor
  · intro h
    have h0 : B.b - B.lam p ≤ 0 := h 0
    have h1 : B.lam p - B.t ≤ 0 := h 1
    have h2 : B.wc p - B.e ≤ 0 := h 2
    have h3 : -B.wc p - B.e ≤ 0 := h 3
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2, h3⟩ k
    rcases fin4 k with rfl | rfl | rfl | rfl
    · show B.b - B.lam p ≤ 0; linarith
    · show B.lam p - B.t ≤ 0; linarith
    · show B.wc p - B.e ≤ 0; linarith
    · show -B.wc p - B.e ≤ 0; linarith

theorem mem_exit {p : ℝ × ℝ} : p ∈ B.exit ↔ p ∈ B.set ∧ B.lam p = B.b := by
  constructor
  · rintro ⟨hp, k, hk, h0⟩
    rw [mem_singleton_iff.1 hk] at h0
    have h0' : B.b - B.lam p = 0 := h0
    exact ⟨hp, by linarith⟩
  · rintro ⟨hp, h⟩
    exact ⟨hp, 0, rfl, show B.b - B.lam p = 0 by rw [h]; ring⟩

theorem isClosed_set : IsClosed B.set := by
  rw [set, ofPred_forall]
  exact isClosed_iInter fun k => isClosed_le (B.continuous_g k) continuous_const

/-- The derivative of `λ` along the field. -/
def lamF (N : ℝ) (p : ℝ × ℝ) : ℝ := B.l₁ * f₁ N p.1 p.2 + B.l₂ * f₂ N p.1 p.2

/-- The derivative of `w` along the field. -/
def wF (N : ℝ) (p : ℝ × ℝ) : ℝ := B.w₁ * f₁ N p.1 p.2 + B.w₂ * f₂ N p.1 p.2

def D (N : ℝ) : Fin 4 → ℝ × ℝ → ℝ :=
  ![fun p => -B.lamF N p, fun p => B.lamF N p, fun p => B.wF N p, fun p => -B.wF N p]

theorem hasDerivAt_g {p : ℝ × ℝ} (hp : ‖p‖ ≤ 1) (k : Fin 4) :
    HasDerivAt (fun s => B.g k (flowON N s p)) (B.D N k p) 0 := by
  have h1 := hasDerivAt_flowON_fst (N := N) hp
  have h2 := hasDerivAt_flowON_snd (N := N) hp
  have hl : HasDerivAt (fun s => B.lam (flowON N s p)) (B.lamF N p) 0 :=
    (h1.const_mul B.l₁).add (h2.const_mul B.l₂)
  have hw : HasDerivAt (fun s => B.wc (flowON N s p)) (B.wF N p) 0 :=
    (h1.const_mul B.w₁).add (h2.const_mul B.w₂)
  rcases fin4 k with rfl | rfl | rfl | rfl
  · exact hl.const_sub B.b
  · exact hl.sub_const B.t
  · exact hw.sub_const B.e
  · exact hw.neg.sub_const B.e

theorem isCompact_set (hball : ∀ p ∈ B.set, ‖p‖ ≤ 1) : IsCompact B.set :=
  Metric.isCompact_of_isClosed_isBounded B.isClosed_set
    (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := 1) |>.subset fun p hp =>
      mem_closedBall_zero_iff.2 (hball p hp))

/-- A box crossed outward on `λ = b` and inward on its other faces is an isolating block with exit
set `λ = b`. -/
theorem isBlock (hball : ∀ p ∈ B.set, ‖p‖ ≤ 1)
    (h0 : ∀ p ∈ B.set, B.lam p = B.b → B.lamF N p < 0)
    (h1 : ∀ p ∈ B.set, B.lam p = B.t → B.lamF N p < 0)
    (h2 : ∀ p ∈ B.set, B.wc p = B.e → B.wF N p < 0)
    (h3 : ∀ p ∈ B.set, B.wc p = -B.e → 0 < B.wF N p) :
    IsBlock (flowON N) B.set B.exit := by
  refine isBlock_of_faces B.continuous_g (B.isCompact_set hball)
    (fun k p hp => B.hasDerivAt_g (hball p hp) k) (fun k hk p hp hk0 => ?_)
    (fun k hk p hp hk0 => ?_)
  · rw [mem_singleton_iff.1 hk] at hk0 ⊢
    have : B.b - B.lam p = 0 := hk0
    show 0 < -B.lamF N p
    linarith [h0 p hp (by linarith)]
  · rcases fin4 k with rfl | rfl | rfl | rfl
    · exact absurd rfl hk
    · have : B.lam p - B.t = 0 := hk0
      exact h1 p hp (by linarith)
    · have : B.wc p - B.e = 0 := hk0
      exact h2 p hp (by linarith)
    · have : -B.wc p - B.e = 0 := hk0
      show -B.wF N p < 0
      linarith [h3 p hp (by linarith)]

/-- A box crossed inward on all four faces is an isolating block with empty exit set. -/
theorem isBlock_attr (hball : ∀ p ∈ B.set, ‖p‖ ≤ 1)
    (h0 : ∀ p ∈ B.set, B.lam p = B.b → 0 < B.lamF N p)
    (h1 : ∀ p ∈ B.set, B.lam p = B.t → B.lamF N p < 0)
    (h2 : ∀ p ∈ B.set, B.wc p = B.e → B.wF N p < 0)
    (h3 : ∀ p ∈ B.set, B.wc p = -B.e → 0 < B.wF N p) :
    IsBlock (flowON N) B.set ∅ := by
  refine isBlock_of_faces_attr B.continuous_g (B.isCompact_set hball)
    (fun k p hp => B.hasDerivAt_g (hball p hp) k) (fun k p hp hk0 => ?_)
  rcases fin4 k with rfl | rfl | rfl | rfl
  · have : B.b - B.lam p = 0 := hk0
    show -B.lamF N p < 0
    linarith [h0 p hp (by linarith)]
  · have : B.lam p - B.t = 0 := hk0
    exact h1 p hp (by linarith)
  · have : B.wc p - B.e = 0 := hk0
    exact h2 p hp (by linarith)
  · have : -B.wc p - B.e = 0 := hk0
    show -B.wF N p < 0
    linarith [h3 p hp (by linarith)]

theorem lam_sub {v₁ v₂ : ℝ} (hv : B.l₁ * v₁ + B.l₂ * v₂ = 1) (p : ℝ × ℝ) (c : ℝ) :
    B.lam (p.1 - c * v₁, p.2 - c * v₂) = B.lam p - c := by
  simp only [lam]; linear_combination (-c) * hv

theorem wc_sub {v₁ v₂ : ℝ} (hw : B.w₁ * v₁ + B.w₂ * v₂ = 0) (p : ℝ × ℝ) (c : ℝ) :
    B.wc (p.1 - c * v₁, p.2 - c * v₂) = B.wc p := by
  simp only [wc]; linear_combination (-c) * hw

/-- Sliding along `v` onto the face `λ = b` makes the quotient by that face contractible. -/
theorem pointedContractible {v₁ v₂ : ℝ} (hv : B.l₁ * v₁ + B.l₂ * v₂ = 1)
    (hw : B.w₁ * v₁ + B.w₂ * v₂ = 0) :
    PointedContractible (IndexSpace B.set B.exit) (IndexSpace.pt _ _) := by
  have hmem : ∀ (s : unitInterval) (p : B.set),
      ((p : ℝ × ℝ).1 - (s : ℝ) * (B.lam p - B.b) * v₁,
        (p : ℝ × ℝ).2 - (s : ℝ) * (B.lam p - B.b) * v₂) ∈ B.set := by
    intro s p
    obtain ⟨h0, h1, h2, h3⟩ := (B.mem_set).1 p.2
    rw [B.mem_set, B.lam_sub hv, B.wc_sub hw]
    have hs0 := s.2.1
    have hs1 := s.2.2
    refine ⟨?_, ?_, h2, h3⟩ <;> nlinarith
  let H : C(unitInterval × B.set, B.set) :=
    { toFun := fun q => ⟨_, hmem q.1 q.2⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        simp only [lam]
        fun_prop }
  refine pointedContractible_of_deform H (fun p => Subtype.ext ?_) (fun s p hp => ?_) (fun p => ?_)
  · show ((p : ℝ × ℝ).1 - ((0 : unitInterval) : ℝ) * (B.lam p - B.b) * v₁,
      (p : ℝ × ℝ).2 - ((0 : unitInterval) : ℝ) * (B.lam p - B.b) * v₂) = p
    simp
  · obtain ⟨-, hb⟩ := (B.mem_exit).1 hp
    refine (B.mem_exit).2 ⟨hmem s p, ?_⟩
    show B.lam ((p : ℝ × ℝ).1 - (s : ℝ) * (B.lam p - B.b) * v₁,
      (p : ℝ × ℝ).2 - (s : ℝ) * (B.lam p - B.b) * v₂) = B.b
    rw [show ∀ c : ℝ, (p : ℝ × ℝ).1 - c * v₁ = (p : ℝ × ℝ).1 - c * v₁ from fun _ => rfl,
      B.lam_sub hv, hb]
    ring
  · refine (B.mem_exit).2 ⟨hmem 1 p, ?_⟩
    show B.lam ((p : ℝ × ℝ).1 - ((1 : unitInterval) : ℝ) * (B.lam p - B.b) * v₁,
      (p : ℝ × ℝ).2 - ((1 : unitInterval) : ℝ) * (B.lam p - B.b) * v₂) = B.b
    rw [B.lam_sub hv]
    simp

theorem convex_set : Convex ℝ B.set := by
  intro p hp q hq a c ha hc hac
  rw [B.mem_set] at hp hq ⊢
  have hl : B.lam (a • p + c • q) = a * B.lam p + c * B.lam q := by
    simp only [lam, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hw : B.wc (a • p + c • q) = a * B.wc p + c * B.wc q := by
    simp only [wc, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [hl, hw]
  obtain ⟨h0, h1, h2, h3⟩ := hp
  obtain ⟨k0, k1, k2, k3⟩ := hq
  have hc' : c = 1 - a := by linarith
  subst hc'
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    nlinarith [mul_nonneg ha (sub_nonneg.2 h0), mul_nonneg hc (sub_nonneg.2 k0),
      mul_nonneg ha (sub_nonneg.2 h1), mul_nonneg hc (sub_nonneg.2 k1),
      mul_nonneg ha (sub_nonneg.2 h2), mul_nonneg hc (sub_nonneg.2 k2),
      mul_nonneg ha (sub_nonneg.2 h3), mul_nonneg hc (sub_nonneg.2 k3)]

end LBox

/-! ## Orbits in a small block -/

theorem norm_le_one_of_abs {p : ℝ × ℝ} (h1 : |p.1| ≤ 1) (h2 : |p.2| ≤ 1) : ‖p‖ ≤ 1 :=
  norm_prod_le_iff.2 ⟨by rwa [Real.norm_eq_abs], by rwa [Real.norm_eq_abs]⟩

/-- Full orbits in a bounded set of the unit ball are bounded solutions, so they lie in `B_N`. -/
theorem Inv_subset_Inv_R (hN : 1 < N) {B : Set (ℝ × ℝ)} (hball : ∀ p ∈ B, ‖p‖ ≤ 1) :
    Inv (flowON N) B ⊆ Inv (flowON N) blockR := by
  intro x hx
  rw [Inv_R_eq hN]
  refine ⟨fun t => flowON N t x, fun t => ?_, ?_, 0, Flow.map_zero_apply _ _⟩
  · rw [← cutField_eq (hball _ (hx t))]
    exact hasDerivAt_flowON N x t
  · exact (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := 1)).subset
      (range_subset_iff.2 fun t => mem_closedBall_zero_iff.2 (hball _ (hx t)))

theorem tendsto_mem_alphaLim {x q : ℝ × ℝ} (hq : Tendsto (fun t => flowON N t x) atBot (𝓝 q)) :
    q ∈ alphaLim (flowON N) x :=
  (mem_omegaLimit_singleton_iff_mapClusterPt (f := atBot) (ϕ := (flowON N).toFun) x q).2
    hq.mapClusterPt

theorem pts_zero (N : ℝ) : pts N 0 = ptG := rfl
theorem pts_one (N : ℝ) : pts N 1 = ptI := rfl
theorem pts_two (N : ℝ) : pts N 2 = ptC N := rfl
theorem pts_three (N : ℝ) : pts N 3 = ptH N := rfl

/-- The set of points of `B_N` whose `α`-limit is one of the points of `Z`. -/
def attrPts (N : ℝ) (Z : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {x | x ∈ boundedOrbits N ∧ ∃ q ∈ Z, alphaLim (flowON N) x ⊆ {q}}

theorem zero_mem_R (hN : 1 < N) {p : ℝ × ℝ} (hp : IsZero N p) : p ∈ blockR :=
  interior_subset (inner_subset_R hN (zero_mem_inner hN hp))

theorem flowON_eq_of_zero (hN : 1 < N) {p : ℝ × ℝ} (hp : IsZero N p) (t : ℝ) :
    flowON N t p = p :=
  flowON_fixed (zero_mem_R hN hp) hp t

/-- The value of `V` at the fixed points. -/
theorem Vp_pts (hN : 1 < N) :
    Vp N ptG = 0 ∧ Vp N ptI = 1 / 486 ∧ Vp N (ptC N) = (N - 1) * (N + 2) / (486 * N ^ 2) ∧
      Vp N (ptH N) = (N + 2) / (18 * (N + 8) ^ 2) := by
  have h0 : N ≠ 0 := by linarith
  have h8 : N + 8 ≠ 0 := by linarith
  refine ⟨by simp [Vp, V, ptG], by simp [Vp, V, ptI]; norm_num, ?_, ?_⟩
  · simp only [Vp, V, ptC]; field_simp; ring
  · simp only [Vp, V, ptH]; field_simp; ring

theorem Vp_nonneg_of_zero (hN : 1 < N) {p : ℝ × ℝ} (hp : IsZero N p) : 0 ≤ Vp N p := by
  obtain ⟨hG, hI, hC, hH⟩ := Vp_pts hN
  obtain ⟨i, rfl⟩ := exists_pts_eq hN hp
  have hN0 : 0 < N := by linarith
  rcases LBox.fin4 i with rfl | rfl | rfl | rfl <;>
    simp only [pts_zero, pts_one, pts_two, pts_three]
  · rw [hG]
  · rw [hI]; norm_num
  · rw [hC]; have : 0 < N - 1 := by linarith
    positivity
  · rw [hH]; positivity

/-- A point of `B_N` whose `α`-limit is `Σ_G` is `Σ_G`. -/
theorem eq_G_of_tendsto_atBot (hN : 1 < N) {x : ℝ × ℝ} (hx : x ∈ Inv (flowON N) blockR)
    (hq : Tendsto (fun t => flowON N t x) atBot (𝓝 ptG)) : x = ptG := by
  obtain ⟨p, q, hp, -, hpT, hqT⟩ := tendsto_of_mem_Inv hN hx
  have hq' : q = ptG := tendsto_nhds_unique hqT hq
  subst hq'
  have hz := isZero_of_V_le hN hx hpT hqT (by rw [(Vp_pts hN).1]; exact Vp_nonneg_of_zero hN hp)
  have hc : Tendsto (fun t => flowON N t x) atBot (𝓝 x) := by
    simp only [flowON_eq_of_zero hN hz]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hc hq

/-- A fixed point `q` on the line `y₂ = k y₁`, other than `Σ_G`, and an orbit of `B_N` running
from `q` to `Σ_G` along that line: the orbit stays between `q` and `Σ_G`. -/
theorem segment_of_line (hN : 1 < N) {k : ℝ} {x q : ℝ × ℝ}
    (hline : ∀ t, (flowON N t x).2 = k * (flowON N t x).1) (hqz : IsZero N q)
    (hqline : q.2 = k * q.1) (hq0 : q.1 ≠ 0)
    (hq : Tendsto (fun t => flowON N t x) atBot (𝓝 q))
    (hp : Tendsto (fun t => flowON N t x) atTop (𝓝 ptG)) (t : ℝ) :
    min q.1 0 ≤ (flowON N t x).1 ∧ (flowON N t x).1 ≤ max q.1 0 := by
  have hfixed : ∀ t, ∀ z, IsZero N z → flowON N t x = z → ∀ s, flowON N s x = z := by
    intro t z hz ht s
    rw [show s = (s - t) + t by ring, Flow.map_add, ht, flowON_eq_of_zero hN hz]
  refine mem_Icc_of_tendsto (c := fun s => (flowON N s x).1)
    (continuous_fst.comp (continuous_orbit x)) hq0
    ((continuous_fst.tendsto q).comp hq) ((continuous_fst.tendsto ptG).comp hp)
    (fun t ht s => ?_) t
  rcases ht with ht | ht
  · have : flowON N t x = q := Prod.ext ht (by rw [hline, hqline, ht])
    simp only [hfixed t q hqz this s, this]
  · have : flowON N t x = ptG := Prod.ext ht (by rw [hline, ht]; simp [ptG])
    simp only [hfixed t ptG (isZero_G N) this s, this]

/-! ## The block around `Σ_G` -/

/-- The half-width `1/(100(N+8))` of the blocks around `Σ_G` and along the axis. -/
noncomputable def eG (N : ℝ) : ℝ := 1 / (100 * (N + 8))

theorem eG_pos (hN : 1 < N) : 0 < eG N := by unfold eG; positivity

theorem eG_mul (hN : 1 < N) : eG N * (N + 8) = 1 / 100 := by
  unfold eG; field_simp

theorem eG_le (hN : 1 < N) : eG N ≤ 1 / 900 := by
  unfold eG; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith

/-- The square `|y₁|, |y₂| ≤ eG` around `Σ_G`. -/
noncomputable def boxG (N : ℝ) : LBox := ⟨1, 0, 0, 1, -eG N, eG N, eG N⟩

theorem mem_boxG {p : ℝ × ℝ} :
    p ∈ (boxG N).set ↔ -eG N ≤ p.1 ∧ p.1 ≤ eG N ∧ p.2 ≤ eG N ∧ -eG N ≤ p.2 := by
  rw [LBox.mem_set]; simp [boxG, LBox.lam, LBox.wc]

theorem norm_le_boxG (hN : 1 < N) {p : ℝ × ℝ} (hp : p ∈ (boxG N).set) : ‖p‖ ≤ 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_boxG.1 hp
  have := eG_le hN
  exact norm_le_one_of_abs (abs_le.2 ⟨by linarith, by linarith⟩) (abs_le.2 ⟨by linarith, by linarith⟩)

theorem isBlock_G (hN : 1 < N) : IsBlock (flowON N) (boxG N).set ∅ := by
  have he := eG_pos hN
  have hm := eG_mul hN
  refine (boxG N).isBlock_attr (fun p hp => norm_le_boxG hN hp) ?_ ?_ ?_ ?_ <;>
    intro p hp hface <;> obtain ⟨h1, h2, h3, h4⟩ := mem_boxG.1 hp <;>
    simp only [boxG, LBox.lam, LBox.wc, LBox.lamF, LBox.wF, one_mul, zero_mul, add_zero,
      zero_add] at hface ⊢ <;> simp only [f₁, f₂]
  · rw [hface]
    have : p.2 ^ 2 ≤ eG N ^ 2 := by nlinarith
    nlinarith
  · rw [hface]; nlinarith [sq_nonneg p.2]
  · rw [hface]; nlinarith
  · rw [hface]; nlinarith

theorem Inv_G (hN : 1 < N) : Inv (flowON N) (boxG N).set = {ptG} := by
  have he := eG_pos hN
  ext x
  constructor
  · intro hx
    have hxR := Inv_subset_Inv_R hN (fun p hp => norm_le_boxG hN hp) hx
    obtain ⟨p, q, hp, hq, hpT, hqT⟩ := tendsto_of_mem_Inv hN hxR
    have hqB : q ∈ (boxG N).set :=
      (boxG N).isClosed_set.mem_of_tendsto hqT (Eventually.of_forall fun t => hx t)
    obtain ⟨i, rfl⟩ := exists_pts_eq hN hq
    obtain ⟨h1, h2, h3, h4⟩ := mem_boxG.1 hqB
    have hu : 0 < 1 / (N + 8) := by positivity
    have hlt : eG N < 1 / (N + 8) := by
      unfold eG; rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith
    have hC : eG N < 1 / (3 * N) := by
      unfold eG; rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith
    rcases LBox.fin4 i with rfl | rfl | rfl | rfl
    · exact eq_G_of_tendsto_atBot hN hxR hqT
    · simp only [pts_one, ptI] at h1
      have := eG_le hN
      linarith
    · simp only [pts_two, ptC] at h4
      have : -1 / (3 * N) = -(1 / (3 * N)) := by ring
      linarith
    · simp only [pts_three, ptH] at h4
      have : -1 / (N + 8) = -(1 / (N + 8)) := by ring
      linarith
  · rintro rfl t
    rw [flowON_eq_of_zero hN (isZero_G N)]
    exact mem_boxG.2 ⟨by simp [ptG]; linarith, by simp [ptG]; linarith, by simp [ptG]; linarith,
      by simp [ptG]; linarith⟩

/-- `h(Σ_G) = S⁰`. -/
theorem hasIndex_G (hN : 1 < N) : HasIndex (flowON N) {ptG} (Sphere 0) (Sphere.pt 0) := by
  have he := eG_pos hN
  have hP := (isBlock_G hN).isIndexPair
  rw [Inv_G hN] at hP
  have hG : ptG ∈ (boxG N).set := (mem_boxG (N := N)).2 ⟨by simp [ptG]; linarith,
    by simp [ptG]; linarith, by simp [ptG]; linarith, by simp [ptG]; linarith⟩
  exact hasIndex_sphere_zero_of_convex hG (boxG N).convex_set hP

/-! ## The block along the axis from `Σ_I` to `Σ_G` -/

/-- `-1/8 ≤ y₁ ≤ eG`, `|y₂| ≤ eG`. -/
noncomputable def boxI (N : ℝ) : LBox := ⟨1, 0, 0, 1, -1 / 8, eG N, eG N⟩

theorem mem_boxI {p : ℝ × ℝ} :
    p ∈ (boxI N).set ↔ -1 / 8 ≤ p.1 ∧ p.1 ≤ eG N ∧ p.2 ≤ eG N ∧ -eG N ≤ p.2 := by
  rw [LBox.mem_set]; simp [boxI, LBox.lam, LBox.wc]

theorem norm_le_boxI (hN : 1 < N) {p : ℝ × ℝ} (hp : p ∈ (boxI N).set) : ‖p‖ ≤ 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_boxI.1 hp
  have := eG_le hN
  exact norm_le_one_of_abs (abs_le.2 ⟨by linarith, by linarith⟩) (abs_le.2 ⟨by linarith, by linarith⟩)

theorem isBlock_I (hN : 1 < N) : IsBlock (flowON N) (boxI N).set (boxI N).exit := by
  have he := eG_pos hN
  have hm := eG_mul hN
  have hle := eG_le hN
  refine (boxI N).isBlock (fun p hp => norm_le_boxI hN hp) ?_ ?_ ?_ ?_ <;>
    intro p hp hface <;> obtain ⟨h1, h2, h3, h4⟩ := mem_boxI.1 hp <;>
    simp only [boxI, LBox.lam, LBox.wc, LBox.lamF, LBox.wF, one_mul, zero_mul, add_zero,
      zero_add] at hface ⊢
  · rw [hface]; exact face_left hN
  · rw [hface]; simp only [f₁]; nlinarith [sq_nonneg p.2]
  · rw [hface]; simp only [f₂]; nlinarith
  · rw [hface]; simp only [f₂]; nlinarith

theorem pointedContractible_I :
    PointedContractible (IndexSpace (boxI N).set (boxI N).exit) (IndexSpace.pt _ _) :=
  (boxI N).pointedContractible (v₁ := 1) (v₂ := 0) (by simp [boxI]) (by simp [boxI])

/-- The axis attracts transversally at `Σ_I`. -/
theorem axis_identity (y₁ y₂ : ℝ) :
    f₂ N y₁ y₂ - 0 * f₁ N y₁ y₂ = -(y₂ - 0 * y₁) * (1 + 6 * y₁ + (N + 2) * y₂) := by
  simp only [f₂]; ring

theorem Inv_I (hN : 1 < N) : Inv (flowON N) (boxI N).set = attrPts N {ptG, ptI} := by
  have he := eG_pos hN
  have hle := eG_le hN
  ext x
  constructor
  · intro hx
    have hxR := Inv_subset_Inv_R hN (fun p hp => norm_le_boxI hN hp) hx
    obtain ⟨p, q, hp, hq, hpT, hqT⟩ := tendsto_of_mem_Inv hN hxR
    have hqB : q ∈ (boxI N).set :=
      (boxI N).isClosed_set.mem_of_tendsto hqT (Eventually.of_forall fun t => hx t)
    refine ⟨by rwa [← Inv_R_eq hN], q, ?_, fun z hz => eq_of_tendsto_of_mem_alphaLim hqT hz⟩
    obtain ⟨i, rfl⟩ := exists_pts_eq hN hq
    obtain ⟨h1, h2, h3, h4⟩ := mem_boxI.1 hqB
    have hlt : eG N < 1 / (N + 8) := by
      unfold eG; rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith
    have hC : eG N < 1 / (3 * N) := by
      unfold eG; rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith
    rcases LBox.fin4 i with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · simp only [pts_two, ptC] at h4
      have : -1 / (3 * N) = -(1 / (3 * N)) := by ring
      linarith
    · simp only [pts_three, ptH] at h4
      have : -1 / (N + 8) = -(1 / (N + 8)) := by ring
      linarith
  · rintro ⟨hxB, q, hqZ, hα⟩
    have hxR : x ∈ Inv (flowON N) blockR := by rwa [Inv_R_eq hN]
    obtain ⟨p', q', -, -, -, hqT⟩ := tendsto_of_mem_Inv hN hxR
    have hq' : q' = q := hα (tendsto_mem_alphaLim hqT)
    subst hq'
    rcases hqZ with rfl | rfl
    · rw [eq_G_of_tendsto_atBot hN hxR hqT]
      intro t
      rw [flowON_eq_of_zero hN (isZero_G N)]
      exact mem_boxI.2 ⟨by simp [ptG]; norm_num, by simp [ptG]; linarith,
        by simp [ptG]; linarith, by simp [ptG]; linarith⟩
    · have hline := on_line_of_tendsto_atBot axis_identity hxR hqT (by simp [ptI])
        (by simp [ptI]; norm_num)
      intro t
      have hin := (Inv_R_eq hN ▸ boundedOrbits_subset hN) (flow_mem_Inv hxR t)
      obtain ⟨⟨a1, a2⟩, -, -⟩ := hin
      have h0 := hline t
      rw [zero_mul] at h0
      exact mem_boxI.2 ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem isIndexPair_I (hN : 1 < N) :
    IsIndexPair (flowON N) (attrPts N {ptG, ptI}) (boxI N).set (boxI N).exit := by
  rw [← Inv_I hN]
  exact (isBlock_I hN).isIndexPair

/-! ## The block along the diagonal from `Σ_H` to `Σ_G`, `N > 4` -/

/-- The half-width `(N-4)/(100(N+8)(N+4))` of the diagonal block. -/
noncomputable def eH (N : ℝ) : ℝ := (N - 4) / (100 * (N + 8) * (N + 4))

/-- `-1/(N+8) - eH ≤ y₂ ≤ eH`, `|y₁ - y₂| ≤ eH`. -/
noncomputable def boxH (N : ℝ) : LBox := ⟨0, 1, 1, -1, -1 / (N + 8) - eH N, eH N, eH N⟩

theorem mem_boxH {p : ℝ × ℝ} :
    p ∈ (boxH N).set ↔ -1 / (N + 8) - eH N ≤ p.2 ∧ p.2 ≤ eH N ∧ p.1 - p.2 ≤ eH N ∧
      -eH N ≤ p.1 - p.2 := by
  rw [LBox.mem_set]; simp [boxH, LBox.lam, LBox.wc, sub_eq_add_neg]

/-- The bounds used for the diagonal block, in terms of `u = 1/(N+8)`. -/
theorem eH_facts (hN : 4 < N) :
    0 < eH N ∧ 0 < 1 / (N + 8) ∧ (N + 8) * (1 / (N + 8)) = 1 ∧
      100 * (N + 4) * eH N = (N - 4) * (1 / (N + 8)) ∧ 1 / (N + 8) ≤ 1 / 12 ∧
      eH N ≤ 1 / (100 * (N + 8)) := by
  have h8 : 0 < N + 8 := by linarith
  have h4 : 0 < N + 4 := by linarith
  have hpos : 0 < eH N := by
    unfold eH
    have : 0 < N - 4 := by linarith
    positivity
  refine ⟨hpos, by positivity, by field_simp, by unfold eH; field_simp, ?_, ?_⟩
  · rw [div_le_div_iff₀ h8 (by norm_num)]; linarith
  · unfold eH; rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith

theorem norm_le_boxH (hN : 4 < N) {p : ℝ × ℝ} (hp : p ∈ (boxH N).set) : ‖p‖ ≤ 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_boxH.1 hp
  obtain ⟨he, hu, -, -, hu12, hle⟩ := eH_facts hN
  have : eH N ≤ 1 / 100 := hle.trans (by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
  have : -1 / (N + 8) = -(1 / (N + 8)) := by ring
  exact norm_le_one_of_abs (abs_le.2 ⟨by linarith, by linarith⟩) (abs_le.2 ⟨by linarith, by linarith⟩)

theorem diagonal_identity (y₁ y₂ : ℝ) :
    f₂ N y₁ y₂ - 1 * f₁ N y₁ y₂ = -(y₂ - 1 * y₁) * (1 + 9 * y₁ + 3 * y₂) := by
  simp only [f₁, f₂]; ring

theorem isBlock_H (hN : 4 < N) : IsBlock (flowON N) (boxH N).set (boxH N).exit := by
  obtain ⟨he, hu, hu1, he1, hu12, hle⟩ := eH_facts hN
  set u := 1 / (N + 8)
  set e := eH N
  have hNe : 0 < N * e := by nlinarith
  have hNu : 0 < (N - 4) * u := by nlinarith
  have hkey : 21 * e < (N - 4) * u := by nlinarith
  have hneg : -1 / (N + 8) = -u := by ring
  refine (boxH N).isBlock (fun p hp => norm_le_boxH hN hp) ?_ ?_ ?_ ?_ <;>
    intro p hp hface <;> obtain ⟨h1, h2, h3, h4⟩ := mem_boxH.1 hp <;>
    simp only [boxH, LBox.lam, LBox.wc, LBox.lamF, LBox.wF, one_mul, zero_mul,
      zero_add, neg_mul] at hface ⊢ <;> rw [hneg] at h1
  · rw [hneg] at hface
    have hA : 1 + 6 * p.1 + (N + 2) * p.2 < 0 := by
      rw [hface]; nlinarith
    have hf : f₂ N p.1 p.2 = -p.2 * (1 + 6 * p.1 + (N + 2) * p.2) := by simp only [f₂]; ring
    rw [hf]
    have : 0 < -p.2 := by linarith
    nlinarith
  · rw [hface]; simp only [f₂]; nlinarith
  · have hf : f₁ N p.1 p.2 + -f₂ N p.1 p.2 = -(p.1 - p.2) * (1 + 9 * p.1 + 3 * p.2) := by
      simp only [f₁, f₂]; ring
    rw [hf]
    have hx : p.1 = p.2 + e := by linarith
    have : 0 < 1 + 9 * p.1 + 3 * p.2 := by rw [hx]; nlinarith
    have hp12 : p.1 - p.2 = e := by linarith
    rw [hp12]; nlinarith
  · have hf : f₁ N p.1 p.2 + -f₂ N p.1 p.2 = -(p.1 - p.2) * (1 + 9 * p.1 + 3 * p.2) := by
      simp only [f₁, f₂]; ring
    rw [hf]
    have hx : p.1 = p.2 - e := by linarith
    have : 0 < 1 + 9 * p.1 + 3 * p.2 := by rw [hx]; nlinarith
    have hp12 : p.1 - p.2 = -e := by linarith
    rw [hp12]; nlinarith

theorem pointedContractible_H :
    PointedContractible (IndexSpace (boxH N).set (boxH N).exit) (IndexSpace.pt _ _) :=
  (boxH N).pointedContractible (v₁ := 1) (v₂ := 1) (by simp [boxH]) (by simp [boxH])

theorem ptH_line (N : ℝ) : (ptH N).2 = 1 * (ptH N).1 := by simp [ptH]

theorem Inv_H (hN : 4 < N) : Inv (flowON N) (boxH N).set = attrPts N {ptG, ptH N} := by
  have hN1 : 1 < N := by linarith
  obtain ⟨he, hu, hu1, he1, hu12, hle⟩ := eH_facts hN
  have hneg : -1 / (N + 8) = -(1 / (N + 8)) := by ring
  ext x
  constructor
  · intro hx
    have hxR := Inv_subset_Inv_R hN1 (fun p hp => norm_le_boxH hN hp) hx
    obtain ⟨p, q, hp, hq, hpT, hqT⟩ := tendsto_of_mem_Inv hN1 hxR
    have hqB : q ∈ (boxH N).set :=
      (boxH N).isClosed_set.mem_of_tendsto hqT (Eventually.of_forall fun t => hx t)
    refine ⟨by rwa [← Inv_R_eq hN1], q, ?_, fun z hz => eq_of_tendsto_of_mem_alphaLim hqT hz⟩
    obtain ⟨i, rfl⟩ := exists_pts_eq hN1 hq
    obtain ⟨h1, h2, h3, h4⟩ := mem_boxH.1 hqB
    have hle' : eH N < 1 / 900 := hle.trans_lt (by
      rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith)
    rcases LBox.fin4 i with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · simp only [pts_one, ptI] at h4
      linarith
    · simp only [pts_two, ptC] at h4
      exfalso
      have hN0 : 0 < N := by linarith
      have hw : -(N - 1) / (9 * N) - -1 / (3 * N) = -((N - 4) / (9 * N)) := by
        field_simp; ring
      rw [hw] at h4
      have : eH N < (N - 4) / (9 * N) := by
        unfold eH
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        have h4' : 0 < N - 4 := by linarith
        have : 9 * N < 100 * (N + 8) * (N + 4) := by nlinarith
        exact mul_lt_mul_of_pos_left this h4'
      linarith
    · exact Or.inr rfl
  · rintro ⟨hxB, q, hqZ, hα⟩
    have hxR : x ∈ Inv (flowON N) blockR := by rwa [Inv_R_eq hN1]
    obtain ⟨p', q', hp', -, hpT, hqT⟩ := tendsto_of_mem_Inv hN1 hxR
    have hq' : q' = q := hα (tendsto_mem_alphaLim hqT)
    subst hq'
    rcases hqZ with rfl | rfl
    · rw [eq_G_of_tendsto_atBot hN1 hxR hqT]
      intro t
      rw [flowON_eq_of_zero hN1 (isZero_G N)]
      exact mem_boxH.2 ⟨by simp [ptG]; rw [hneg]; linarith, by simp [ptG]; linarith,
        by simp [ptG]; linarith, by simp [ptG]; linarith⟩
    · have hpos : 0 < 1 + 9 * (ptH N).1 + 3 * (ptH N).2 := by
        simp only [ptH]
        rw [show 1 + 9 * (-1 / (N + 8)) + 3 * (-1 / (N + 8)) = (N - 4) * (1 / (N + 8)) by
          field_simp; ring]
        have : 0 < N - 4 := by linarith
        positivity
      have hline := on_line_of_tendsto_atBot diagonal_identity hxR hqT (ptH_line N) hpos
      -- the `ω`-limit lies on the diagonal
      have hp'line : p'.2 = 1 * p'.1 := by
        have h1 := ((continuous_fst.tendsto p').comp hpT)
        have h2 := ((continuous_snd.tendsto p').comp hpT)
        have h2' : Tendsto (fun t => (flowON N t x).2) atTop (𝓝 p'.2) := h2
        rw [show (fun t => (flowON N t x).2) = fun t => 1 * (flowON N t x).1 from
          funext hline] at h2'
        exact tendsto_nhds_unique h2' (h1.const_mul 1)
      obtain ⟨i, rfl⟩ := exists_pts_eq hN1 hp'
      have hH1 : (ptH N).1 ≠ 0 := by simp only [ptH]; exact div_ne_zero (by norm_num) (by linarith)
      rcases LBox.fin4 i with rfl | rfl | rfl | rfl
      · intro t
        have hseg := segment_of_line hN1 hline (isZero_H (by linarith)) (ptH_line N) hH1 hqT
          hpT t
        have hH1' : (ptH N).1 = -(1 / (N + 8)) := by simp only [ptH]; ring
        rw [hH1', min_eq_left (by linarith), max_eq_right (by linarith)] at hseg
        have hl := hline t
        rw [one_mul] at hl
        exact mem_boxH.2 ⟨by rw [hneg, hl]; linarith, by rw [hl]; linarith,
          by rw [hl]; linarith, by rw [hl]; linarith⟩
      · simp only [pts_one, ptI]
          at hp'line
        norm_num at hp'line
      · simp only [pts_two, ptC, one_mul] at hp'line
        exfalso
        have hN0 : N ≠ 0 := by linarith
        have : N = 4 := by field_simp at hp'line; linarith
        linarith
      · have hz := isZero_of_V_le hN1 hxR hpT hqT le_rfl
        have hc : Tendsto (fun t => flowON N t x) atBot (𝓝 x) := by
          simp only [flowON_eq_of_zero hN1 hz]
          exact tendsto_const_nhds
        rw [tendsto_nhds_unique hc hqT]
        intro t
        rw [flowON_eq_of_zero hN1 (isZero_H (by linarith))]
        have hH : (ptH N).1 = -(1 / (N + 8)) ∧ (ptH N).2 = -(1 / (N + 8)) := by
          simp only [ptH]; constructor <;> ring
        exact mem_boxH.2 ⟨by rw [hH.2, hneg]; linarith, by rw [hH.2]; linarith,
          by rw [hH.1, hH.2]; linarith, by rw [hH.1, hH.2]; linarith⟩

theorem isIndexPair_H (hN : 4 < N) :
    IsIndexPair (flowON N) (attrPts N {ptG, ptH N}) (boxH N).set (boxH N).exit := by
  rw [← Inv_H hN]
  exact (isBlock_H hN).isIndexPair

/-! ## The block along the third line from `Σ_C` to `Σ_G`, `1 < N < 4` -/

/-- The slope `3/(N-1)` of the third invariant line. -/
noncomputable def kC (N : ℝ) : ℝ := 3 / (N - 1)

/-- The half-width `(4-N)(N-1)/(100N(N+11))` of the block along the third line. -/
noncomputable def eC (N : ℝ) : ℝ := (4 - N) * (N - 1) / (100 * N * (N + 11))

/-- `c₁ - eC ≤ y₁ ≤ eC`, `|y₂ - kC y₁| ≤ eC`, with `c₁ = -(N-1)/(9N)` the first coordinate of
`Σ_C`. -/
noncomputable def boxC (N : ℝ) : LBox :=
  ⟨1, 0, -kC N, 1, -(N - 1) / (9 * N) - eC N, eC N, eC N⟩

theorem mem_boxC {p : ℝ × ℝ} :
    p ∈ (boxC N).set ↔ -(N - 1) / (9 * N) - eC N ≤ p.1 ∧ p.1 ≤ eC N ∧
      p.2 - kC N * p.1 ≤ eC N ∧ -eC N ≤ p.2 - kC N * p.1 := by
  rw [LBox.mem_set]
  simp only [boxC, LBox.lam, LBox.wc, one_mul, zero_mul, add_zero, neg_mul]
  constructor <;> rintro ⟨a, b, c, d⟩ <;> exact ⟨a, b, by linarith, by linarith⟩

theorem eC_facts (h1 : 1 < N) (h4 : N < 4) :
    0 < eC N ∧ kC N * (N - 1) = 3 ∧ 0 < kC N ∧ 9 * N * (-(N - 1) / (9 * N)) = -(N - 1) ∧
      100 * N * (N + 11) * eC N = (4 - N) * (N - 1) := by
  have hN1 : N - 1 ≠ 0 := by linarith
  have hN0 : N ≠ 0 := by linarith
  have hk0 : 0 < kC N := by
    unfold kC
    have : 0 < N - 1 := by linarith
    positivity
  refine ⟨?_, by unfold kC; field_simp, hk0, by field_simp, by unfold eC; field_simp⟩
  unfold eC
  have : 0 < 4 - N := by linarith
  have : 0 < N - 1 := by linarith
  have : 0 < N := by linarith
  positivity

theorem third_identity (h1 : 1 < N) (y₁ y₂ : ℝ) :
    f₂ N y₁ y₂ - kC N * f₁ N y₁ y₂ = -(y₂ - kC N * y₁) * (1 + 9 * y₁ + (N - 1) * y₂) := by
  have hk : kC N * (N - 1) = 3 := div_mul_cancel₀ 3 (by linarith)
  simp only [f₁, f₂]
  linear_combination (y₂ ^ 2 - y₁ * y₂) * hk

theorem norm_le_boxC (h1 : 1 < N) (h4 : N < 4) {p : ℝ × ℝ} (hp : p ∈ (boxC N).set) :
    ‖p‖ ≤ 1 := by
  obtain ⟨a, b, c, d⟩ := mem_boxC.1 hp
  obtain ⟨he, hk, hk0, hc, he1⟩ := eC_facts h1 h4
  set k := kC N
  set e := eC N
  set c₁ := -(N - 1) / (9 * N) with hc₁
  have hN0 : 0 < N := by linarith
  have hc1 : -(1 / 9) < c₁ := by
    rw [hc₁, lt_div_iff₀ (by positivity)]; linarith
  have hc0 : c₁ < 0 := by
    rw [hc₁]; exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  have hkc : -(1 / 3) ≤ k * c₁ := by
    have : k * c₁ * (9 * N) = -3 := by
      calc k * c₁ * (9 * N) = k * (9 * N * c₁) := by ring
        _ = -3 := by rw [hc]; linarith [hk]
    have : k * c₁ = -3 / (9 * N) := by field_simp; linarith
    rw [this, le_div_iff₀ (by positivity)]; linarith
  have hke : k * e < 1 / 100 := by
    have h3e : 3 * e * (100 * N * (N + 11)) < (N - 1) / 100 * (100 * N * (N + 11)) := by
      rw [show 3 * e * (100 * N * (N + 11)) = 3 * (100 * N * (N + 11) * e) by ring, he1,
        show (N - 1) / 100 * (100 * N * (N + 11)) = (N - 1) * (N * (N + 11)) by ring,
        show 3 * ((4 - N) * (N - 1)) = (N - 1) * (3 * (4 - N)) by ring]
      exact mul_lt_mul_of_pos_left (by nlinarith) (by linarith)
    have h3e' : 3 * e < (N - 1) / 100 := lt_of_mul_lt_mul_right h3e (by positivity)
    have : k * e * (N - 1) = 3 * e := by rw [mul_right_comm, hk]
    nlinarith
  have hle : e < 1 / 100 := by
    have : e * (100 * N * (N + 11)) < 1 / 100 * (100 * N * (N + 11)) := by
      rw [mul_comm e, he1]; nlinarith
    exact lt_of_mul_lt_mul_right this (by positivity)
  have hy1 : |p.1| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  refine norm_le_one_of_abs hy1 (abs_le.2 ⟨?_, ?_⟩)
  · have : k * (c₁ - e) ≤ k * p.1 := mul_le_mul_of_nonneg_left a hk0.le
    nlinarith
  · have : k * p.1 ≤ k * e := mul_le_mul_of_nonneg_left b hk0.le
    nlinarith

theorem isBlock_C (h1 : 1 < N) (h4 : N < 4) : IsBlock (flowON N) (boxC N).set (boxC N).exit := by
  obtain ⟨he, hk, hk0, hc, he1⟩ := eC_facts h1 h4
  set k := kC N with hkdef
  set e := eC N
  set c₁ := -(N - 1) / (9 * N) with hc₁
  have hN0 : 0 < N := by linarith
  have hc0 : c₁ < 0 := by
    rw [hc₁]; exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  -- `(9 + 3k) c₁ = -1`
  have hα : (9 + 3 * k) * c₁ = -1 := by
    have : (9 + 3 * k) * c₁ * (9 * N) * (N - 1) = -(9 * N) * (N - 1) := by
      calc (9 + 3 * k) * c₁ * (9 * N) * (N - 1) = (9 * (N - 1) + 3 * (k * (N - 1))) *
            (9 * N * c₁) := by ring
        _ = -(9 * N) * (N - 1) := by rw [hk, hc]; ring
    have hne : (9 * N) * (N - 1) ≠ 0 := by
      have : 0 < N - 1 := by linarith
      positivity
    field_simp at this ⊢
    nlinarith [this]
  have hk3 : 0 < 3 * k := by linarith
  -- `3N (1 + 12 c₁) = 4 - N`
  have h12 : 3 * N * (1 + 12 * c₁) = 4 - N := by
    have : 3 * N * (1 + 12 * c₁) = 3 * N + 4 * (9 * N * c₁) := by ring
    rw [this, hc]; ring
  have hNe : 0 < N * e := by positivity
  have hkey1 : 3 * N * (12 * e) < 4 - N := by
    have : 100 * (N + 11) * (36 * N * e) = 36 * (4 - N) * (N - 1) := by
      rw [show 100 * (N + 11) * (36 * N * e) = 36 * (100 * N * (N + 11) * e) by ring, he1]; ring
    nlinarith
  have hkey2 : 3 * N * ((N + 11) * e) < 4 - N := by
    have : 100 * (3 * N * ((N + 11) * e)) = 3 * (4 - N) * (N - 1) := by
      rw [show 100 * (3 * N * ((N + 11) * e)) = 3 * (100 * N * (N + 11) * e) by ring, he1]
      ring
    nlinarith
  refine (boxC N).isBlock (fun p hp => norm_le_boxC h1 h4 hp) ?_ ?_ ?_ ?_ <;>
    intro p hp hface <;> obtain ⟨a, b, c, d⟩ := mem_boxC.1 hp <;>
    simp only [boxC, LBox.lam, LBox.wc, LBox.lamF, LBox.wF, one_mul, zero_mul, add_zero,
      neg_mul] at hface ⊢
  · -- the exit face `y₁ = c₁ - e`
    set w := p.2 - k * p.1 with hw
    have hy2 : p.2 = k * p.1 + w := by rw [hw]; ring
    have hf : f₁ N p.1 p.2 = -(p.1 + (9 + 3 * k) * p.1 ^ 2 + 6 * p.1 * w + (N - 1) * w ^ 2) := by
      simp only [f₁]; rw [hy2]
      linear_combination (-(p.1 ^ 2) * k - 2 * p.1 * w) * hk
    rw [hf]
    set m := e - c₁ with hm
    have hm0 : 0 < m := by rw [hm]; linarith
    have hy1 : p.1 = -m := by rw [hm]; linarith
    have hαm : (9 + 3 * k) * m = (9 + 3 * k) * e + 1 := by rw [hm]; linarith [hα]
    rw [hy1]
    have h1' : 0 ≤ m * (e - w) := mul_nonneg hm0.le (by linarith)
    have h2' : 0 ≤ m * (e + w) := mul_nonneg hm0.le (by linarith)
    have hNw : 0 ≤ (N - 1) * w ^ 2 := mul_nonneg (by linarith) (sq_nonneg w)
    have : 0 < m * ((3 + 3 * k) * e) := by positivity
    nlinarith
  · rw [hface]; simp only [f₁]; nlinarith [sq_nonneg p.2]
  · have hf : -(k * f₁ N p.1 p.2) + f₂ N p.1 p.2 =
        -(p.2 - k * p.1) * (1 + 9 * p.1 + (N - 1) * p.2) := by
      rw [← third_identity h1]; ring
    rw [hf]
    have hw : p.2 - k * p.1 = e := by linarith
    have hy2 : (N - 1) * p.2 = 3 * p.1 + (N - 1) * e := by
      have : p.2 = k * p.1 + e := by linarith
      rw [this]; linear_combination p.1 * hk
    have : 0 < 1 + 9 * p.1 + (N - 1) * p.2 := by
      rw [hy2]
      have : 0 < 3 * N * (1 + 12 * p.1 + (N - 1) * e) := by nlinarith
      have : 0 < 1 + 12 * p.1 + (N - 1) * e := by
        by_contra hc'; push Not at hc'; nlinarith
      linarith
    rw [hw]; nlinarith
  · have hf : -(k * f₁ N p.1 p.2) + f₂ N p.1 p.2 =
        -(p.2 - k * p.1) * (1 + 9 * p.1 + (N - 1) * p.2) := by
      rw [← third_identity h1]; ring
    rw [hf]
    have hw : p.2 - k * p.1 = -e := by linarith
    have hy2 : (N - 1) * p.2 = 3 * p.1 - (N - 1) * e := by
      have : p.2 = k * p.1 - e := by linarith
      rw [this]; linear_combination p.1 * hk
    have : 0 < 1 + 9 * p.1 + (N - 1) * p.2 := by
      rw [hy2]
      have : 0 < 3 * N * (1 + 12 * p.1 - (N - 1) * e) := by nlinarith
      have : 0 < 1 + 12 * p.1 - (N - 1) * e := by
        by_contra hc'; push Not at hc'; nlinarith
      linarith
    rw [hw]; nlinarith

theorem pointedContractible_C :
    PointedContractible (IndexSpace (boxC N).set (boxC N).exit) (IndexSpace.pt _ _) :=
  (boxC N).pointedContractible (v₁ := 1) (v₂ := kC N) (by simp [boxC]) (by simp [boxC])

theorem ptC_line (h1 : 1 < N) : (ptC N).2 = kC N * (ptC N).1 := ptC_on_third_line h1

theorem Inv_C (h1 : 1 < N) (h4 : N < 4) :
    Inv (flowON N) (boxC N).set = attrPts N {ptG, ptC N} := by
  obtain ⟨he, hk, hk0, hc, he1⟩ := eC_facts h1 h4
  have hN0 : 0 < N := by linarith
  have hle : eC N < 1 / 100 := by
    have : eC N * (100 * N * (N + 11)) < 1 / 100 * (100 * N * (N + 11)) := by
      rw [mul_comm (eC N), he1]; nlinarith
    exact lt_of_mul_lt_mul_right this (by positivity)
  ext x
  constructor
  · intro hx
    have hxR := Inv_subset_Inv_R h1 (fun p hp => norm_le_boxC h1 h4 hp) hx
    obtain ⟨p, q, hp, hq, hpT, hqT⟩ := tendsto_of_mem_Inv h1 hxR
    have hqB : q ∈ (boxC N).set :=
      (boxC N).isClosed_set.mem_of_tendsto hqT (Eventually.of_forall fun t => hx t)
    refine ⟨by rwa [← Inv_R_eq h1], q, ?_, fun z hz => eq_of_tendsto_of_mem_alphaLim hqT hz⟩
    obtain ⟨i, rfl⟩ := exists_pts_eq h1 hq
    obtain ⟨a, b, c, d⟩ := mem_boxC.1 hqB
    rcases LBox.fin4 i with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · simp only [pts_one, ptI] at c
      exfalso
      have : kC N * (-1 / 9) * (N - 1) = -1 / 3 := by
        rw [show kC N * (-1 / 9) * (N - 1) = kC N * (N - 1) * (-1 / 9) by ring, hk]; norm_num
      have hk9 : 0 < kC N / 9 := by positivity
      have : 1 / 100 < kC N / 9 := by
        have hk' : kC N = 3 / (N - 1) := rfl
        rw [hk', div_div, lt_div_iff₀ (by nlinarith)]; nlinarith
      linarith
    · exact Or.inr rfl
    · simp only [pts_three, ptH] at c d
      exfalso
      -- `h - kC h = (4 - N)/((N+8)(N-1)) > eC`
      have hval : -1 / (N + 8) - kC N * (-1 / (N + 8)) = (4 - N) / ((N + 8) * (N - 1)) := by
        have : N - 1 ≠ 0 := by linarith
        unfold kC; field_simp; ring
      rw [hval] at c
      have : eC N < (4 - N) / ((N + 8) * (N - 1)) := by
        unfold eC
        have : 0 < 4 - N := by linarith
        have : 0 < N - 1 := by linarith
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        have : (N - 1) * ((N + 8) * (N - 1)) < 100 * N * (N + 11) := by nlinarith
        nlinarith
      linarith
  · rintro ⟨hxB, q, hqZ, hα⟩
    have hxR : x ∈ Inv (flowON N) blockR := by rwa [Inv_R_eq h1]
    obtain ⟨p', q', hp', -, hpT, hqT⟩ := tendsto_of_mem_Inv h1 hxR
    have hq' : q' = q := hα (tendsto_mem_alphaLim hqT)
    subst hq'
    have hc1 : -(N - 1) / (9 * N) < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
    rcases hqZ with rfl | rfl
    · rw [eq_G_of_tendsto_atBot h1 hxR hqT]
      intro t
      rw [flowON_eq_of_zero h1 (isZero_G N)]
      have hG1 : ptG.1 = 0 := rfl
      have hG2 : ptG.2 = 0 := rfl
      exact mem_boxC.2 ⟨by rw [hG1]; linarith, by rw [hG1]; linarith,
        by rw [hG1, hG2]; linarith, by rw [hG1, hG2]; linarith⟩
    · have hpos : 0 < 1 + 9 * (ptC N).1 + (N - 1) * (ptC N).2 := by
        simp only [ptC]
        rw [show 1 + 9 * (-(N - 1) / (9 * N)) + (N - 1) * (-1 / (3 * N)) = (4 - N) / (3 * N) by
          field_simp; ring]
        have : 0 < 4 - N := by linarith
        positivity
      have hline := on_line_of_tendsto_atBot (third_identity h1) hxR hqT (ptC_line h1) hpos
      have hp'line : p'.2 = kC N * p'.1 := by
        have h1' := ((continuous_fst.tendsto p').comp hpT)
        have h2' := ((continuous_snd.tendsto p').comp hpT)
        have h2'' : Tendsto (fun t => (flowON N t x).2) atTop (𝓝 p'.2) := h2'
        rw [show (fun t => (flowON N t x).2) = fun t => kC N * (flowON N t x).1 from
          funext hline] at h2''
        exact tendsto_nhds_unique h2'' (h1'.const_mul (kC N))
      obtain ⟨i, rfl⟩ := exists_pts_eq h1 hp'
      have hC1 : (ptC N).1 ≠ 0 := by simp only [ptC]; exact hc1.ne
      rcases LBox.fin4 i with rfl | rfl | rfl | rfl
      · intro t
        have hseg := segment_of_line h1 hline (isZero_C (by linarith)) (ptC_line h1) hC1 hqT
          hpT t
        have hC1' : (ptC N).1 = -(N - 1) / (9 * N) := rfl
        rw [hC1', min_eq_left hc1.le, max_eq_right hc1.le] at hseg
        have hl := hline t
        exact mem_boxC.2 ⟨by linarith, by linarith, by rw [hl]; linarith, by rw [hl]; linarith⟩
      · simp only [pts_one, ptI]
          at hp'line
        have : kC N * (-1 / 9) < 0 := by nlinarith
        linarith
      · have hz := isZero_of_V_le h1 hxR hpT hqT le_rfl
        have hc : Tendsto (fun t => flowON N t x) atBot (𝓝 x) := by
          simp only [flowON_eq_of_zero h1 hz]
          exact tendsto_const_nhds
        rw [tendsto_nhds_unique hc hqT]
        intro t
        rw [flowON_eq_of_zero h1 (isZero_C (by linarith))]
        exact mem_boxC.2 ⟨by simp only [ptC]; linarith, by simp only [ptC]; linarith,
          by rw [← ptC_line h1, sub_self]; linarith, by rw [← ptC_line h1, sub_self]; linarith⟩
      · simp only [pts_three, ptH] at hp'line
        exfalso
        have hh : -1 / (N + 8) ≠ 0 := div_ne_zero (by norm_num) (by linarith)
        have hk1 : kC N = 1 := by
          have := mul_right_cancel₀ hh (hp'line.symm.trans (one_mul _).symm)
          exact this
        have : (3 : ℝ) = N - 1 := by rw [← hk, hk1, one_mul]
        linarith

theorem isIndexPair_C (h1 : 1 < N) (h4 : N < 4) :
    IsIndexPair (flowON N) (attrPts N {ptG, ptC N}) (boxC N).set (boxC N).exit := by
  rw [← Inv_C h1 h4]
  exact (isBlock_C h1 h4).isIndexPair

end ConleyCheck.ON
