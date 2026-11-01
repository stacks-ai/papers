import ConleyCheck.Gubser.GlobalTC
import ConleyCheck.ODE.Affine
import ConleyCheck.Conley.OrbitTools

/-!
# Barriers and faces for the doubled compactified flow

All statements are along orbits of `ϕG` on `Ω`, in the homogeneous coordinates `y`.

* `hasDerivAt_gB1`, `hasDerivAt_gB2`: the barrier planes `B₁ = y₂ + a y₃` (`π̄ = -a`) and
  `B₂ = a y₃ - y₂` (`π̄ = a`) satisfy `B' = k B + a y₁ y₃ / c`. Hence `{B ≥ 0}` is forward
  invariant where `y₁ ≥ 0`, and `{B ≤ 0}` where `y₁ ≤ 0` (`gB1_nonneg` etc.).
* `hasDerivAt_gH`: the plane function `H_σ = y₂ + σ y₃` (`π̄ = -σ`) satisfies
  `H_σ' = (σ y₃ / c) Q_σ + k H_σ` with `Q_σ = y₁ + k_σ τ y₃`, where `k_σ = 4c(a² - σ²)/(3σ)`.
  For `σ = a - η` and `σ = -(a + η)` this gives `k_σ = k_-` and `k_σ = k_+`.
* `hasDerivAt_gQ`: `Q_σ' = P₁ - s Q_σ + k_σ y₃² (1 - τ²)`, and on `{H_σ = Q_σ = 0}` the derivative
  of `Q_σ` is positive (`gQ_deriv_pos`).
* `face_core`: the sign estimate behind the faces `u = ∓δ` of `K^∓` (condition (k1)).
* The finite part `y₃ > 0`: `T = y₁/y₃`, `π̄ = y₂/y₃` and `F_σ = Q_σ / y₃ = T + k_σ τ` solve
  `y₃ ·` (the Gubser field) (`hasDerivAt_gT`, `hasDerivAt_gπ`, `hasDerivAt_gF`).
-/

open Set Filter Topology
open ConleyCheck.Conley ConleyCheck.ODE

namespace ConleyCheck.Gubser

variable {c a : ℝ}

theorem gP1_eq (q : OmG) : gP1 q = gw1 q * gy1 q * (gy2 q - 2 * gy3 q) / 3 := rfl

theorem gP2_eq (c : ℝ) (q : OmG) :
    gP2 c q = -(4 / 3) * gw1 q * (gy2 q ^ 2 - gy3 q ^ 2 / 5) - gy1 q * gy2 q / c := rfl

theorem gS_eq (c : ℝ) (q : OmG) : gS c q = gy1 q * gP1 q + gy2 q * gP2 c q := rfl

theorem continuous_gP1 : Continuous gP1 := by
  have : gP1 = fun q => gw1 q * gy1 q * (gy2 q - 2 * gy3 q) / 3 := rfl
  rw [this]
  exact ((continuous_gw1.mul continuous_gy1).mul
    (continuous_gy2.sub (continuous_const.mul continuous_gy3))).div_const 3

theorem continuous_gP2 (c : ℝ) : Continuous (gP2 c) := by
  have : gP2 c = fun q => -(4 / 3) * gw1 q * (gy2 q ^ 2 - gy3 q ^ 2 / 5) - gy1 q * gy2 q / c := rfl
  rw [this]
  exact ((continuous_const.mul continuous_gw1).mul ((continuous_gy2.pow 2).sub
    ((continuous_gy3.pow 2).div_const 5))).sub ((continuous_gy1.mul continuous_gy2).div_const c)

/-! ## Sign of `y₁` -/

theorem gy1_nonneg_all (c : ℝ) {p : OmG} (h : 0 ≤ gy1 p) (t : ℝ) : 0 ≤ gy1 (ϕG c t p) := by
  rcases h.lt_or_eq with h | h
  · exact (gy1_pos c p h t).le
  · exact (gy1_zero c p h.symm t).ge

theorem gy1_nonpos_all (c : ℝ) {p : OmG} (h : gy1 p ≤ 0) (t : ℝ) : gy1 (ϕG c t p) ≤ 0 := by
  rcases h.lt_or_eq with h | h
  · exact (gy1_neg c p h t).le
  · exact (gy1_zero c p h t).le

theorem gy1_sign (c : ℝ) (p : OmG) (t : ℝ) :
    (0 < gy1 p ↔ 0 < gy1 (ϕG c t p)) ∧ (gy1 p < 0 ↔ gy1 (ϕG c t p) < 0) := by
  have back : ∀ q : OmG, ϕG c (-t) (ϕG c t q) = q := fun q => by
    rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  refine ⟨⟨fun h => gy1_pos c p h t, fun h => ?_⟩, ⟨fun h => gy1_neg c p h t, fun h => ?_⟩⟩
  · have := gy1_pos c _ h (-t); rwa [back] at this
  · have := gy1_neg c _ h (-t); rwa [back] at this

theorem gy3_pos_iff (c : ℝ) (p : OmG) (t : ℝ) : 0 < gy3 p ↔ 0 < gy3 (ϕG c t p) := by
  refine ⟨fun h => gy3_pos c p h t, fun h => ?_⟩
  have := gy3_pos c _ h (-t)
  rwa [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply] at this

/-! ## The barrier planes `π̄ = ∓a` -/

/-- `B₁ = y₂ + a y₃`. -/
def gB1 (a : ℝ) (q : OmG) : ℝ := gy2 q + a * gy3 q

/-- `B₂ = a y₃ - y₂`. -/
def gB2 (a : ℝ) (q : OmG) : ℝ := a * gy3 q - gy2 q

noncomputable def kB1 (c a : ℝ) (q : OmG) : ℝ :=
  -(4 / 3) * gw1 q * (gy2 q - a * gy3 q) - gy1 q / c - gS c q

noncomputable def kB2 (c a : ℝ) (q : OmG) : ℝ :=
  -(4 / 3) * gw1 q * (gy2 q + a * gy3 q) - gy1 q / c - gS c q

theorem continuous_kB1 (c a : ℝ) : Continuous (kB1 c a) :=
  (((continuous_const.mul continuous_gw1).mul (continuous_gy2.sub
    (continuous_const.mul continuous_gy3))).sub (continuous_gy1.div_const c)).sub (continuous_gS c)

theorem continuous_kB2 (c a : ℝ) : Continuous (kB2 c a) :=
  (((continuous_const.mul continuous_gw1).mul (continuous_gy2.add
    (continuous_const.mul continuous_gy3))).sub (continuous_gy1.div_const c)).sub (continuous_gS c)

section Orbit

variable (c) (p : OmG)

theorem hasDerivAt_gB1 (ha : a ^ 2 = 1 / 5) (t : ℝ) : HasDerivAt (fun s => gB1 a (ϕG c s p))
    (kB1 c a (ϕG c t p) * gB1 a (ϕG c t p) + a * gy1 (ϕG c t p) * gy3 (ϕG c t p) / c) t := by
  have h := hasDerivAt_lin c p 0 1 a t
  simp only [zero_mul, zero_add, one_mul] at h
  refine h.congr_deriv ?_
  simp only [kB1, gB1, gP2_eq]
  have : gy3 (ϕG c t p) ^ 2 / 5 = a ^ 2 * gy3 (ϕG c t p) ^ 2 := by rw [ha]; ring
  rw [this]; ring

theorem hasDerivAt_gB2 (ha : a ^ 2 = 1 / 5) (t : ℝ) : HasDerivAt (fun s => gB2 a (ϕG c s p))
    (kB2 c a (ϕG c t p) * gB2 a (ϕG c t p) + a * gy1 (ϕG c t p) * gy3 (ϕG c t p) / c) t := by
  have h := hasDerivAt_lin c p 0 (-1) a t
  simp only [zero_mul, zero_add, neg_one_mul] at h
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  · simp only [kB2, gB2, gP2_eq]
    have : gy3 (ϕG c t p) ^ 2 / 5 = a ^ 2 * gy3 (ϕG c t p) ^ 2 := by rw [ha]; ring
    rw [this]; ring
  · simp only [gB2]; ring

variable {c}

theorem gB1_nonneg (ha : a ^ 2 = 1 / 5) (ha0 : 0 < a) (hc : 0 < c) (hy : 0 ≤ gy1 p) {t₀ t₁ : ℝ}
    (h01 : t₀ ≤ t₁) (h0 : 0 ≤ gB1 a (ϕG c t₀ p)) : 0 ≤ gB1 a (ϕG c t₁ p) :=
  affine_nonneg (g := fun s => gB1 a (ϕG c s p)) (hasDerivAt_gB1 c p ha)
    (continuous_k c p _ (continuous_kB1 c a)) h01
    (fun s _ => div_nonneg (mul_nonneg (mul_nonneg ha0.le (gy1_nonneg_all c hy s))
      (gy3_nonneg _)) hc.le) h0

theorem gB2_nonneg (ha : a ^ 2 = 1 / 5) (ha0 : 0 < a) (hc : 0 < c) (hy : 0 ≤ gy1 p) {t₀ t₁ : ℝ}
    (h01 : t₀ ≤ t₁) (h0 : 0 ≤ gB2 a (ϕG c t₀ p)) : 0 ≤ gB2 a (ϕG c t₁ p) :=
  affine_nonneg (g := fun s => gB2 a (ϕG c s p)) (hasDerivAt_gB2 c p ha)
    (continuous_k c p _ (continuous_kB2 c a)) h01
    (fun s _ => div_nonneg (mul_nonneg (mul_nonneg ha0.le (gy1_nonneg_all c hy s))
      (gy3_nonneg _)) hc.le) h0

theorem gB2_pos (ha : a ^ 2 = 1 / 5) (ha0 : 0 < a) (hc : 0 < c) (hy : 0 ≤ gy1 p) {t₀ t₁ : ℝ}
    (h01 : t₀ ≤ t₁) (h0 : 0 < gB2 a (ϕG c t₀ p)) : 0 < gB2 a (ϕG c t₁ p) :=
  affine_pos (g := fun s => gB2 a (ϕG c s p)) (hasDerivAt_gB2 c p ha)
    (continuous_k c p _ (continuous_kB2 c a)) h01
    (fun s _ => div_nonneg (mul_nonneg (mul_nonneg ha0.le (gy1_nonneg_all c hy s))
      (gy3_nonneg _)) hc.le) h0

theorem gB1_nonpos (ha : a ^ 2 = 1 / 5) (ha0 : 0 < a) (hc : 0 < c) (hy : gy1 p ≤ 0) {t₀ t₁ : ℝ}
    (h01 : t₀ ≤ t₁) (h0 : gB1 a (ϕG c t₀ p) ≤ 0) : gB1 a (ϕG c t₁ p) ≤ 0 :=
  affine_nonpos (g := fun s => gB1 a (ϕG c s p)) (hasDerivAt_gB1 c p ha)
    (continuous_k c p _ (continuous_kB1 c a)) h01
    (fun s _ => div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos ha0.le (gy1_nonpos_all c hy s)) (gy3_nonneg _)) hc.le) h0

theorem gB2_nonpos (ha : a ^ 2 = 1 / 5) (ha0 : 0 < a) (hc : 0 < c) (hy : gy1 p ≤ 0) {t₀ t₁ : ℝ}
    (h01 : t₀ ≤ t₁) (h0 : gB2 a (ϕG c t₀ p) ≤ 0) : gB2 a (ϕG c t₁ p) ≤ 0 :=
  affine_nonpos (g := fun s => gB2 a (ϕG c s p)) (hasDerivAt_gB2 c p ha)
    (continuous_k c p _ (continuous_kB2 c a)) h01
    (fun s _ => div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos ha0.le (gy1_nonpos_all c hy s)) (gy3_nonneg _)) hc.le) h0

end Orbit

/-! ## The planes `π̄ = -σ` -/

/-- `k_σ = 4c(a² - σ²)/(3σ)`. -/
noncomputable def kS (c a σ : ℝ) : ℝ := 4 * c * (a ^ 2 - σ ^ 2) / (3 * σ)

theorem kS_minus {η : ℝ} : kS c a (a - η) = kminus a c η := by
  unfold kS kminus; congr 1; ring

theorem kS_plus {η : ℝ} : kS c a (-(a + η)) = kplus a c η := by
  unfold kS kplus
  rw [show 3 * -(a + η) = -(3 * (a + η)) by ring, div_neg, ← neg_div]
  congr 1; ring

/-- `H_σ = y₂ + σ y₃`. -/
def gH (σ : ℝ) (q : OmG) : ℝ := gy2 q + σ * gy3 q

/-- `Q_σ = y₁ + k_σ τ y₃`. -/
noncomputable def gQ (c a σ : ℝ) (q : OmG) : ℝ := gy1 q + kS c a σ * gw1 q * gy3 q

noncomputable def kH (c σ : ℝ) (q : OmG) : ℝ :=
  -(4 / 3) * gw1 q * (gH σ q - 2 * σ * gy3 q) - gy1 q / c - gS c q

theorem continuous_gH (σ : ℝ) : Continuous (gH σ) :=
  continuous_gy2.add (continuous_const.mul continuous_gy3)

theorem continuous_gQ (c a σ : ℝ) : Continuous (gQ c a σ) :=
  continuous_gy1.add ((continuous_const.mul continuous_gw1).mul continuous_gy3)

theorem continuous_kH (c σ : ℝ) : Continuous (kH c σ) :=
  (((continuous_const.mul continuous_gw1).mul ((continuous_gH σ).sub
    (continuous_const.mul continuous_gy3))).sub (continuous_gy1.div_const c)).sub (continuous_gS c)

theorem gP2_plane (ha : a ^ 2 = 1 / 5) (hc : c ≠ 0) {σ : ℝ} (hσ : σ ≠ 0) (q : OmG) :
    gP2 c q = σ * gy3 q / c * gQ c a σ q + (kH c σ q + gS c q) * gH σ q := by
  simp only [gP2_eq, gQ, kS, kH, gH]
  have : gy3 q ^ 2 / 5 = a ^ 2 * gy3 q ^ 2 := by rw [ha]; ring
  rw [this]
  field_simp
  ring

section Orbit

variable (c) (p : OmG)

theorem hasDerivAt_gH (ha : a ^ 2 = 1 / 5) (hc : c ≠ 0) {σ : ℝ} (hσ : σ ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => gH σ (ϕG c s p))
      (kH c σ (ϕG c t p) * gH σ (ϕG c t p) +
        σ * gy3 (ϕG c t p) / c * gQ c a σ (ϕG c t p)) t := by
  have h := hasDerivAt_lin c p 0 1 σ t
  simp only [zero_mul, zero_add, one_mul] at h
  refine h.congr_deriv ?_
  rw [gP2_plane ha hc hσ]
  simp only [gH]; ring

theorem hasDerivAt_gQ (σ : ℝ) (t : ℝ) :
    HasDerivAt (fun s => gQ c a σ (ϕG c s p))
      (gP1 (ϕG c t p) - gS c (ϕG c t p) * gQ c a σ (ϕG c t p) +
        kS c a σ * gy3 (ϕG c t p) ^ 2 * (1 - gw1 (ϕG c t p) ^ 2)) t := by
  have h := (hasDerivAt_gy1 c p t).add (((hasDerivAt_gw1 c p t).mul
    (hasDerivAt_gy3 c p t)).const_mul (kS c a σ))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  · simp only [gQ]; ring
  · simp only [gQ, Pi.add_apply, Pi.mul_apply]; ring

end Orbit

/-- On `{H_σ = Q_σ = 0}` the function `Q_σ` increases. -/
theorem gQ_deriv_pos {σ : ℝ} (hk : 0 < kS c a σ) (hσ : -2 < σ) {q : OmG} (hH : gH σ q = 0)
    (hQ : gQ c a σ q = 0) (h3 : 0 < gy3 q) :
    0 < gP1 q - gS c q * gQ c a σ q + kS c a σ * gy3 q ^ 2 * (1 - gw1 q ^ 2) := by
  have hy2 : gy2 q = -σ * gy3 q := by simp only [gH] at hH; linarith
  have hy1 : gy1 q = -(kS c a σ * gw1 q * gy3 q) := by simp only [gQ] at hQ; linarith
  rw [hQ, mul_zero, sub_zero, gP1_eq, hy1, hy2]
  have hw := gw1_mem q
  have h1 : 0 ≤ 1 - gw1 q ^ 2 := by nlinarith [hw.1, hw.2]
  have key : 0 < (1 - gw1 q ^ 2) + gw1 q ^ 2 * (2 + σ) / 3 := by
    rcases eq_or_lt_of_le h1 with h | h
    · have : gw1 q ^ 2 = 1 := by linarith
      rw [this]; linarith
    · have : 0 ≤ gw1 q ^ 2 * (2 + σ) / 3 := by
        apply div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by norm_num)
      linarith
  have := mul_pos (mul_pos hk (pow_pos h3 2)) key
  nlinarith [this]

/-! ## The faces `u = ∓δ` -/

/-- The sign estimate behind the side faces of `K^±`, under condition (k1). -/
theorem face_core {σ δ z y τ₁ τ₂ τ₃ : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hδ : 0 < δ)
    (hk : δ * (5 / 3 + 4 / (15 * σ ^ 2) + 2 / (3 * σ)) < 1 / c) (hz : 0 < z) (hy : 0 ≤ y)
    (hy' : σ * y ≤ δ * z) (h1 : |τ₁| ≤ 1) (h2 : |τ₂| ≤ 1) (h3 : |τ₃| ≤ 1) :
    0 < δ * z ^ 2 / c - 5 / 3 * δ ^ 2 * τ₁ * z ^ 2 + 4 / 15 * τ₂ * y ^ 2 -
      2 / 3 * δ * τ₃ * z * y := by
  obtain ⟨h1a, h1b⟩ := abs_le.1 h1
  obtain ⟨h2a, h2b⟩ := abs_le.1 h2
  obtain ⟨h3a, h3b⟩ := abs_le.1 h3
  have hyb : y ≤ δ * z / σ := by rw [le_div_iff₀ hσ]; linarith
  have hy2 : y ^ 2 ≤ δ ^ 2 * z ^ 2 / σ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : y * σ ≤ δ * z := by linarith
    nlinarith [mul_nonneg hy hσ.le]
  have hzy : z * y ≤ δ * z ^ 2 / σ := by
    rw [le_div_iff₀ hσ]; nlinarith
  have t1 : 5 / 3 * δ ^ 2 * τ₁ * z ^ 2 ≤ 5 / 3 * δ ^ 2 * z ^ 2 := by
    have : 0 ≤ δ ^ 2 * z ^ 2 := by positivity
    nlinarith
  have t2 : -(4 / 15 * τ₂ * y ^ 2) ≤ 4 / 15 * y ^ 2 := by nlinarith [sq_nonneg y]
  have t3 : 2 / 3 * δ * τ₃ * z * y ≤ 2 / 3 * δ * z * y := by
    have : 0 ≤ δ * z * y := by positivity
    nlinarith
  have hmain : 0 < δ * z ^ 2 * (1 / c - δ * (5 / 3 + 4 / (15 * σ ^ 2) + 2 / (3 * σ))) :=
    mul_pos (by positivity) (by linarith)
  have e : δ * z ^ 2 * (1 / c - δ * (5 / 3 + 4 / (15 * σ ^ 2) + 2 / (3 * σ))) =
      δ * z ^ 2 / c - 5 / 3 * δ ^ 2 * z ^ 2 - 4 / 15 * (δ ^ 2 * z ^ 2 / σ ^ 2) -
        2 / 3 * δ * (δ * z ^ 2 / σ) := by
    field_simp
    ring
  have h4 : 4 / 15 * y ^ 2 ≤ 4 / 15 * (δ ^ 2 * z ^ 2 / σ ^ 2) := by linarith
  have h5 : 2 / 3 * δ * z * y ≤ 2 / 3 * δ * (δ * z ^ 2 / σ) := by
    have := mul_le_mul_of_nonneg_left hzy (by positivity : (0 : ℝ) ≤ 2 / 3 * δ)
    linarith
  linarith

/-! ## The finite part -/

/-- `T = y₁ / y₃`. -/
noncomputable def gT (q : OmG) : ℝ := gy1 q / gy3 q

/-- `π̄ = y₂ / y₃`. -/
noncomputable def gπ (q : OmG) : ℝ := gy2 q / gy3 q

/-- `F_σ = Q_σ / y₃ = T + k_σ τ`. -/
noncomputable def gF (c a σ : ℝ) (q : OmG) : ℝ := gT q + kS c a σ * gw1 q

section Orbit

variable (c) (p : OmG)

theorem hasDerivAt_ratio (l₁ l₂ l₃ : ℝ) {t : ℝ} (h3 : 0 < gy3 (ϕG c t p)) :
    HasDerivAt (fun s => (l₁ * gy1 (ϕG c s p) + l₂ * gy2 (ϕG c s p) + l₃ * gy3 (ϕG c s p)) /
      gy3 (ϕG c s p)) ((l₁ * gP1 (ϕG c t p) + l₂ * gP2 c (ϕG c t p)) / gy3 (ϕG c t p)) t := by
  have h := (hasDerivAt_lin c p l₁ l₂ l₃ t).div (hasDerivAt_gy3 c p t) h3.ne'
  refine h.congr_deriv ?_
  field_simp
  ring

theorem hasDerivAt_gT {t : ℝ} (h3 : 0 < gy3 (ϕG c t p)) :
    HasDerivAt (fun s => gT (ϕG c s p))
      (gy3 (ϕG c t p) * βT (gT (ϕG c t p)) (gπ (ϕG c t p)) (gw1 (ϕG c t p))) t := by
  have h := hasDerivAt_ratio c p 1 0 0 h3
  simp only [one_mul, zero_mul, add_zero] at h
  refine h.congr_deriv ?_
  simp only [gT, gπ, βT, gP1_eq]
  field_simp

theorem hasDerivAt_gπ {t : ℝ} (h3 : 0 < gy3 (ϕG c t p)) :
    HasDerivAt (fun s => gπ (ϕG c s p))
      (gy3 (ϕG c t p) * βπ c (gT (ϕG c t p)) (gπ (ϕG c t p)) (gw1 (ϕG c t p))) t := by
  have h := hasDerivAt_ratio c p 0 1 0 h3
  simp only [one_mul, zero_mul, add_zero, zero_add] at h
  refine h.congr_deriv ?_
  simp only [gT, gπ, βπ, gP2_eq]
  field_simp

theorem hasDerivAt_gF (σ : ℝ) {t : ℝ} (h3 : 0 < gy3 (ϕG c t p)) :
    HasDerivAt (fun s => gF c a σ (ϕG c s p))
      (gy3 (ϕG c t p) * (βT (gT (ϕG c t p)) (gπ (ϕG c t p)) (gw1 (ϕG c t p)) +
        kS c a σ * (1 - gw1 (ϕG c t p) ^ 2))) t := by
  have h := (hasDerivAt_gT c p h3).add ((hasDerivAt_gw1 c p t).const_mul (kS c a σ))
  refine h.congr_deriv ?_
  ring

end Orbit

theorem gQ_eq_gF {σ : ℝ} {q : OmG} (h3 : 0 < gy3 q) : gQ c a σ q = gy3 q * gF c a σ q := by
  simp only [gQ, gF, gT]
  field_simp

end ConleyCheck.Gubser
