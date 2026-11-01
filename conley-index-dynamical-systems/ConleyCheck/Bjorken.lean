import ConleyCheck.Calculus

/-!
# Section `sec:bjorken`: the Bjorken flow

The compactified system is
`dc/dt = -(k u c + (1-u) P(c))/(1 - c/20)`, `du/dt = u(1-u)^2`, with `k = 3/(2θ₀)` and
`P(c) = 5/7 c - 1/5 c^2 + 4`.

Checked here: the roots `c^± = (25 ± 3√505)/14` of `P` and its factorization, the fiber eigenvalues
`(101 ± 17√505)/168`, the sign of `P`, the sign of the numerator on the faces of `N = [c_L, c_R]`
for all `u ∈ [0,1]`, the zeros of the frozen fields `f_±` in `N`, the linearization `-3/(2θ₀)`, the
change of clock `u = w/(1+w)`, the convex-combination form, `g(τ) = ¼(1+τ)(1-τ)^2` and the function
`G` of Lemma `lem:G` for this `g`.

Existence, uniqueness and index of the attractor (Proposition `prop:bjorken`) are in
`ConleyCheck.BjorkenFlow`, and the invertibility of its linearized operator is in
`ConleyCheck.Palmer.BjorkenApp`.
-/

namespace ConleyCheck.Bjorken

/-- The UV polynomial. -/
noncomputable def P (c : ℝ) : ℝ := 5 / 7 * c - 1 / 5 * c ^ 2 + 4

noncomputable def s : ℝ := Real.sqrt 505

noncomputable def cplus : ℝ := (25 + 3 * s) / 14
noncomputable def cminus : ℝ := (25 - 3 * s) / 14

theorem s_sq : s ^ 2 = 505 := Real.sq_sqrt (by norm_num)

theorem s_bounds : 22 < s ∧ s < 23 := by
  constructor
  · rw [s, Real.lt_sqrt (by norm_num)]; norm_num
  · rw [s, Real.sqrt_lt' (by norm_num)]; norm_num

theorem P_factor (c : ℝ) : P c = -1 / 5 * (c - cplus) * (c - cminus) := by
  have hs := s_sq
  simp only [P, cplus, cminus]
  linear_combination (-9 / 980) * hs

theorem P_cplus : P cplus = 0 := by rw [P_factor]; ring
theorem P_cminus : P cminus = 0 := by rw [P_factor]; ring

/-- `c^- ≈ -3.03 < 0 < c^+ ≈ 6.60 < 20`. -/
theorem cminus_neg : cminus < 0 := by
  have := s_bounds; simp only [cminus]; linarith

theorem cplus_pos : 0 < cplus := by
  have := s_bounds; simp only [cplus]; linarith

theorem cplus_lt_20 : cplus < 20 := by
  have := s_bounds; simp only [cplus]; linarith

theorem approx : 6.6 < cplus ∧ cplus < 6.61 ∧ -3.03 < cminus ∧ cminus < -3.02 := by
  have hs := s_sq
  have h0 : 0 ≤ s := Real.sqrt_nonneg _
  simp only [cplus, cminus]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- `P < 0` outside `[c^-, c^+]` and `P > 0` inside. -/
theorem P_neg_outside {c : ℝ} (h : c < cminus ∨ cplus < c) : P c < 0 := by
  rw [P_factor]
  have hlt : cminus < cplus := by linarith [cminus_neg, cplus_pos]
  rcases h with h | h
  · have := mul_pos (by linarith : 0 < cplus - c) (by linarith : 0 < cminus - c)
    nlinarith
  · have := mul_pos (by linarith : 0 < c - cplus) (by linarith : 0 < c - cminus)
    nlinarith

theorem P_pos_inside {c : ℝ} (h1 : cminus < c) (h2 : c < cplus) : 0 < P c := by
  rw [P_factor]
  have := mul_pos (by linarith : 0 < cplus - c) (by linarith : 0 < c - cminus)
  nlinarith

/-! ## Fiber eigenvalues -/

/-- The UV fiber field `f_-(c) = -P(c)/(1 - c/20)`. -/
noncomputable def fminus (c : ℝ) : ℝ := -P c / (1 - c / 20)

/-- At a zero of `P` the derivative of `f_-` is `-P'(c)/(1 - c/20)`. -/
theorem hasDerivAt_fminus {c : ℝ} (hP : P c = 0) (hc : c < 20) :
    HasDerivAt fminus (-(5 / 7 - 2 / 5 * c) / (1 - c / 20)) c := by
  have hq : 1 - c / 20 ≠ 0 := by intro h; linarith
  have hP' : HasDerivAt P (5 / 7 - 2 / 5 * c) c :=
    hasDerivAt_of_cubic 0 (-1 / 5) (5 / 7) 4 c _ (fun y => by simp only [P]; ring) (by ring)
  have hq' : HasDerivAt (fun y : ℝ => 1 - y / 20) (-(1 / 20)) c :=
    hasDerivAt_of_cubic 0 0 (-1 / 20) 1 c _ (fun y => by ring) (by ring)
  have h := hP'.neg.div hq' hq
  convert h using 1
  · funext y; simp only [fminus, Pi.div_apply, Pi.neg_apply]
  · have h20 : (20 : ℝ) - c ≠ 0 := by intro h; linarith
    simp only [Pi.neg_apply]; rw [hP]; field_simp; ring

theorem eig_cplus : -(5 / 7 - 2 / 5 * cplus) / (1 - cplus / 20) = (101 + 17 * s) / 168 := by
  have hs := s_sq
  have hq : 1 - cplus / 20 ≠ 0 := by intro h; linarith [cplus_lt_20]
  rw [div_eq_div_iff hq (by norm_num)]
  simp only [cplus]
  linear_combination (51 / 280) * hs

theorem eig_cminus : -(5 / 7 - 2 / 5 * cminus) / (1 - cminus / 20) = (101 - 17 * s) / 168 := by
  have hs := s_sq
  have hq : 1 - cminus / 20 ≠ 0 := by intro h; linarith [cminus_neg]
  rw [div_eq_div_iff hq (by norm_num)]
  simp only [cminus]
  linear_combination (51 / 280) * hs

/-- The fiber eigenvalues `≈ 2.87` at `c^+` and `≈ -1.67` at `c^-`. With the normal eigenvalue
`+1` this gives Morse indices `2` and `1` in the double, i.e. fiber indices `μ = 1, 0`. -/
theorem eig_signs : 0 < (101 + 17 * s) / 168 ∧ (101 - 17 * s) / 168 < 0 ∧
    2.87 < (101 + 17 * s) / 168 ∧ (101 - 17 * s) / 168 < -1.67 := by
  have := s_bounds
  have hs := s_sq
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- The normal eigenvalues: `d/du [u(1-u)^2] = 1` at `u = 0` and `= 0` at `u = 1`. -/
theorem normal_eig :
    HasDerivAt (fun u : ℝ => u * (1 - u) ^ 2) 1 0 ∧ HasDerivAt (fun u : ℝ => u * (1 - u) ^ 2) 0 1 :=
  ⟨hasDerivAt_of_cubic 1 (-2) 1 0 0 _ (fun y => by ring) (by ring),
    hasDerivAt_of_cubic 1 (-2) 1 0 1 _ (fun y => by ring) (by ring)⟩

/-! ## Proposition `prop:bjorken`: the block `N = [c_L, c_R]` -/

/-- The numerator `k u c + (1-u) P(c)` with `k = 3/(2θ₀)`. -/
noncomputable def num (k u c : ℝ) : ℝ := k * u * c + (1 - u) * P c

/-- At `c_L < c^-` the numerator is negative for every `u ∈ [0,1]`. -/
theorem num_left {k u cL : ℝ} (hk : 0 < k) (hL : cL < cminus) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    num k u cL < 0 := by
  have hP := P_neg_outside (Or.inl hL)
  have hc : cL < 0 := lt_trans hL cminus_neg
  simp only [num]
  rcases eq_or_lt_of_le hu0 with rfl | hu
  · simp; exact hP
  · have h1 : k * u * cL < 0 := mul_neg_of_pos_of_neg (mul_pos hk hu) hc
    have h2 : (1 - u) * P cL ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hP.le
    linarith

/-- At `0 < c_R < c^+` the numerator is positive for every `u ∈ [0,1]`. -/
theorem num_right {k u cR : ℝ} (hk : 0 < k) (hR0 : 0 < cR) (hR : cR < cplus) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) : 0 < num k u cR := by
  have hP := P_pos_inside (lt_trans cminus_neg hR0) hR
  simp only [num]
  rcases eq_or_lt_of_le hu0 with rfl | hu
  · simp; exact hP
  · have h1 : 0 < k * u * cR := mul_pos (mul_pos hk hu) hR0
    have h2 : 0 ≤ (1 - u) * P cR := mul_nonneg (by linarith) hP.le
    linarith

/-- Hence `dc/dt > 0` at `c_L` and `dc/dt < 0` at `c_R`, i.e. `N` is strictly attracting for every
frozen field. -/
theorem faces {k u cL cR : ℝ} (hk : 0 < k) (hL : cL < cminus) (hR0 : 0 < cR) (hR : cR < cplus)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 < -num k u cL / (1 - cL / 20) ∧ -num k u cR / (1 - cR / 20) < 0 := by
  have hqL : 0 < 1 - cL / 20 := by linarith [cminus_neg]
  have hqR : 0 < 1 - cR / 20 := by linarith [cplus_lt_20]
  exact ⟨div_pos (by linarith [num_left hk hL hu0 hu1]) hqL,
    div_neg_of_neg_of_pos (by linarith [num_right hk hR0 hR hu0 hu1]) hqR⟩

/-- The zeros of `f_-` in `N` are `c^-` alone. -/
theorem fminus_zeros {cL cR c : ℝ} (hR : cR < cplus) (_hc1 : cL ≤ c) (hc2 : c ≤ cR)
    (h : fminus c = 0) : c = cminus := by
  have hq : 1 - c / 20 ≠ 0 := by intro h; linarith [cplus_lt_20]
  simp only [fminus, div_eq_zero_iff, neg_eq_zero, hq, or_false] at h
  rw [P_factor] at h
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · norm_num at h
    · exfalso; linarith
  · linarith

/-- The IR fiber field `f_+(c) = -k c/(1 - c/20)`. -/
noncomputable def fplus (k c : ℝ) : ℝ := -(k * c) / (1 - c / 20)

theorem fplus_zero_iff {k c : ℝ} (hk : 0 < k) (hc : c < 20) : fplus k c = 0 ↔ c = 0 := by
  have hq : 1 - c / 20 ≠ 0 := by intro h; linarith
  simp only [fplus, div_eq_zero_iff, neg_eq_zero, hq, or_false, mul_eq_zero, hk.ne', false_or]

/-- Linearization at local equilibrium: `f_+'(0) = -k = -3/(2θ₀)`. -/
theorem hasDerivAt_fplus (k : ℝ) : HasDerivAt (fplus k) (-k) 0 := by
  have hq' : HasDerivAt (fun y : ℝ => 1 - y / 20) (-(1 / 20)) 0 :=
    hasDerivAt_of_cubic 0 0 (-1 / 20) 1 0 _ (fun y => by ring) (by ring)
  have h := ((hasDerivAt_id (0 : ℝ)).const_mul k).neg.div hq' (by norm_num)
  convert h using 1
  · funext y; simp [fplus]
  · simp

/-! ## The clock `t` and the compactification -/

/-- `u = w/(1+w)` and `dt/dw = 1 + 1/w` give `du/dt = u(1-u)^2`. -/
theorem du_dt {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun x => x / (1 + x)) (1 / (1 + w) ^ 2) w ∧
      1 / (1 + w) ^ 2 / (1 + 1 / w) = w / (1 + w) * (1 - w / (1 + w)) ^ 2 := by
  have h1 : (1 + w) ≠ 0 := by linarith
  constructor
  · have h := (hasDerivAt_id w).div ((hasDerivAt_const w (1 : ℝ)).add (hasDerivAt_id w)) h1
    convert h using 1
    · funext x; simp only [Pi.div_apply, Pi.add_apply, id]
    · simp only [Pi.add_apply, id]; field_simp; ring
  · field_simp; ring

/-- The `c`-equation in the clock `t`. -/
theorem dc_dt {k w c : ℝ} (hw : 0 < w) (hc : c < 20) :
    -(1 / (1 - c / 20)) * (k * c + 1 / w * P c) / (1 + 1 / w) =
      -num k (w / (1 + w)) c / (1 - c / 20) := by
  have h1 : (1 + w) ≠ 0 := by linarith
  have hq : 1 - c / 20 ≠ 0 := by intro h; linarith
  simp only [num]
  field_simp; ring

/-- `F` is the convex combination of the UV and IR limit fields. -/
theorem convex_combination (k u c : ℝ) :
    -num k u c / (1 - c / 20) = u * fplus k c + (1 - u) * fminus c := by
  simp only [num, fplus, fminus]; ring

/-- After `τ = 2u - 1`, `dτ/dt = 2u(1-u)^2 = ¼(1+τ)(1-τ)^2`. -/
theorem g_bjorken (u : ℝ) :
    2 * (u * (1 - u) ^ 2) = 1 / 4 * (1 + (2 * u - 1)) * (1 - (2 * u - 1)) ^ 2 := by ring

/-- `g'(1) = 0` (degenerate IR end) and `g'(-1) = 1`. -/
theorem g_deriv :
    HasDerivAt (fun τ : ℝ => 1 / 4 * (1 + τ) * (1 - τ) ^ 2) 0 1 ∧
      HasDerivAt (fun τ : ℝ => 1 / 4 * (1 + τ) * (1 - τ) ^ 2) 1 (-1) :=
  ⟨hasDerivAt_of_cubic (1 / 4) (-1 / 4) (-1 / 4) (1 / 4) 1 _ (fun y => by ring) (by ring),
    hasDerivAt_of_cubic (1 / 4) (-1 / 4) (-1 / 4) (1 / 4) (-1) _ (fun y => by ring) (by ring)⟩

/-- Lemma `lem:G` for the Bjorken `g`: `G(θ) = -g(cos θ)/sin θ = -sin θ (1 - cos θ)/4`. -/
theorem G_bjorken {θ : ℝ} (h : Real.sin θ ≠ 0) :
    -(1 / 4 * (1 + Real.cos θ) * (1 - Real.cos θ) ^ 2) / Real.sin θ =
      -(Real.sin θ * (1 - Real.cos θ)) / 4 := by
  rw [div_eq_div_iff h (by norm_num)]
  linear_combination (1 - Real.cos θ) * Real.sin_sq_add_cos_sq θ

/-- `G'(0) = 0 = g'(1)/2` and `G'(π) = 1/2 = g'(-1)/2`. -/
theorem G_bjorken_deriv :
    HasDerivAt (fun θ => -(Real.sin θ * (1 - Real.cos θ)) / 4) 0 0 ∧
      HasDerivAt (fun θ => -(Real.sin θ * (1 - Real.cos θ)) / 4) (1 / 2) Real.pi := by
  have H : ∀ x : ℝ, HasDerivAt (fun θ => -(Real.sin θ * (1 - Real.cos θ)) / 4)
      (-(Real.cos x * (1 - Real.cos x) + Real.sin x * Real.sin x) / 4) x := by
    intro x
    have h := (((Real.hasDerivAt_sin x).mul
      ((hasDerivAt_const x (1 : ℝ)).sub (Real.hasDerivAt_cos x))).neg).div_const 4
    convert h using 1
    simp only [Pi.sub_apply]; ring
  constructor
  · convert H 0 using 1; simp
  · convert H Real.pi using 1; simp; norm_num

end ConleyCheck.Bjorken
