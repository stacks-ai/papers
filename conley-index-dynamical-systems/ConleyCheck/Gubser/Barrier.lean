import ConleyCheck.Gubser.Infinity
import ConleyCheck.ODE.Fence

/-!
# Lemma `lem:barrier`(ii), (iii): the flow on the circle at infinity and the barrier planes

* `lem_barrier_ii_pos`: for `τ > 0` the six arcs of `C_θ` are the orbits of `eq:arcs`, namely
  `D⁺ → P⁻`, `D⁺ → TC⁺`, `P⁺ → TC⁺`, `P⁺ → D⁻`, `TC⁻ → D⁻` and `TC⁻ → P⁻`, where
  `TC⁺ = 0`, `TC⁻ = ±π`, `P^± = ±π/2`, `D⁺ = φ₊ = arctan u_*` and `D⁻ = φ₊ + π`.
* `lem_barrier_ii_zero`: for `τ = 0` the orbits are `TC⁻ → P^± → TC⁺`.
* `lem_barrier_ii_neg`: for `τ < 0` the arcs are the images of those for `-τ` under
  `φ ↦ π - φ` with time reversed, which is the reversor `S̃` on `C_θ`.
* `lem_barrier_iii`: for `T > 0` the half-spaces `{π̄ ≥ -a}` and `{π̄ ≤ a}` are positively
  invariant, and for `T < 0` so are `{π̄ ≤ -a}` and `{π̄ ≥ a}`. The sign of `T` is preserved.
-/

open Set Filter Topology Real
open scoped NNReal

namespace ConleyCheck.Gubser

open ConleyCheck.ODE

/-! ## The polar field -/

/-- The right-hand side of `eq:polar`. -/
noncomputable def polarF (c τ φ : ℝ) : ℝ :=
  -(sin φ * cos φ) * (1 / c * cos φ + 5 / 3 * τ * sin φ)

/-- Orbits of `F` starting strictly between `p` and `q` stay there and run from `p` to `q`. -/
def Connects (F : ℝ → ℝ) (p q : ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, (∀ t, HasDerivAt φ (F (φ t)) t) → φ 0 ∈ Ioo (min p q) (max p q) →
    (∀ t, φ t ∈ Ioo (min p q) (max p q)) ∧ Tendsto φ atBot (𝓝 p) ∧ Tendsto φ atTop (𝓝 q)

theorem connects_of_pos {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) {p q : ℝ} (hpq : p < q)
    (hp : F p = 0) (hq : F q = 0) (hpos : ∀ x ∈ Ioo p q, 0 < F x) : Connects F p q := by
  intro φ hφ h0
  rw [min_eq_left hpq.le, max_eq_right hpq.le] at h0 ⊢
  obtain ⟨h1, -, h2, h3⟩ := arc_orbit hF hp hq hpos hφ h0
  exact ⟨h1, h2, h3⟩

theorem connects_of_neg {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) {p q : ℝ} (hqp : q < p)
    (hp : F p = 0) (hq : F q = 0) (hneg : ∀ x ∈ Ioo q p, F x < 0) : Connects F p q := by
  intro φ hφ h0
  rw [min_eq_right hqp.le, max_eq_left hqp.le] at h0 ⊢
  obtain ⟨h1, -, h2, h3⟩ := arc_orbit_neg hF hq hp hneg hφ h0
  exact ⟨h1, h2, h3⟩

theorem polarF_eq (c τ φ : ℝ) : polarF c τ φ =
    -(1 / c) * (sin φ * cos φ ^ 2) + -(5 / 3 * τ) * (sin φ ^ 2 * cos φ) := by
  unfold polarF; ring

theorem hasDerivAt_polarF (c τ φ : ℝ) : HasDerivAt (polarF c τ)
    (-(1 / c) * (cos φ ^ 3 - 2 * sin φ ^ 2 * cos φ) +
      -(5 / 3 * τ) * (2 * sin φ * cos φ ^ 2 - sin φ ^ 3)) φ := by
  have h1 := (hasDerivAt_sin φ).mul ((hasDerivAt_cos φ).pow 2)
  have h2 := ((hasDerivAt_sin φ).pow 2).mul (hasDerivAt_cos φ)
  have h := (h1.const_mul (-(1 / c))).add (h2.const_mul (-(5 / 3 * τ)))
  convert h using 1
  · funext x; rw [polarF_eq]; rfl
  · norm_num; ring

theorem abs_trig_le_three (x : ℝ) :
    |cos x ^ 3 - 2 * sin x ^ 2 * cos x| ≤ 3 ∧ |2 * sin x * cos x ^ 2 - sin x ^ 3| ≤ 3 := by
  have hs := abs_sin_le_one x
  have hc := abs_cos_le_one x
  have hs0 := abs_nonneg (sin x)
  have hc0 := abs_nonneg (cos x)
  have hc3 : |cos x| ^ 3 ≤ 1 := pow_le_one₀ hc0 hc
  have hs3 : |sin x| ^ 3 ≤ 1 := pow_le_one₀ hs0 hs
  have hs2 : |sin x| ^ 2 ≤ 1 := pow_le_one₀ hs0 hs
  have hc2 : |cos x| ^ 2 ≤ 1 := pow_le_one₀ hc0 hc
  have h1 : |sin x| ^ 2 * |cos x| ≤ 1 := by simpa using mul_le_mul hs2 hc hc0 zero_le_one
  have h2 : |sin x| * |cos x| ^ 2 ≤ 1 := by
    simpa using mul_le_mul hs hc2 (by positivity) zero_le_one
  constructor
  · refine (abs_sub _ _).trans ?_
    rw [abs_pow, abs_mul, abs_mul, abs_pow, abs_two]
    nlinarith
  · refine (abs_sub _ _).trans ?_
    rw [abs_pow, abs_mul, abs_mul, abs_pow, abs_two]
    nlinarith

theorem lipschitz_polarF (c τ : ℝ) : ∃ K, LipschitzWith K (polarF c τ) := by
  refine ⟨Real.toNNReal (3 * |1 / c| + 3 * |5 / 3 * τ|),
    lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_polarF c τ x).differentiableAt)
      fun x => ?_⟩
  rw [(hasDerivAt_polarF c τ x).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
    Real.coe_toNNReal _ (by positivity)]
  obtain ⟨h1, h2⟩ := abs_trig_le_three x
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_neg, abs_neg]
  nlinarith [abs_nonneg (1 / c), abs_nonneg (5 / 3 * τ),
    mul_le_mul_of_nonneg_left h1 (abs_nonneg (1 / c)),
    mul_le_mul_of_nonneg_left h2 (abs_nonneg (5 / 3 * τ))]

/-! ## Signs of `sin` and `cos` -/

theorem sin_pos' {x : ℝ} (h1 : 0 < x) (h2 : x < π) : 0 < sin x := sin_pos_of_pos_of_lt_pi h1 h2

theorem sin_neg' {x : ℝ} (h1 : -π < x) (h2 : x < 0) : sin x < 0 :=
  sin_neg_of_neg_of_neg_pi_lt h2 h1

theorem sin_neg'' {x : ℝ} (h1 : π < x) (h2 : x < 2 * π) : sin x < 0 := by
  have := sin_pos_of_pos_of_lt_pi (x := x - π) (by linarith) (by linarith)
  rw [sin_sub_pi] at this
  linarith

theorem cos_pos' {x : ℝ} (h1 : -(π / 2) < x) (h2 : x < π / 2) : 0 < cos x :=
  cos_pos_of_mem_Ioo ⟨h1, h2⟩

theorem cos_neg' {x : ℝ} (h1 : π / 2 < x) (h2 : x < π) : cos x < 0 :=
  cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith [pi_pos])

theorem cos_neg'' {x : ℝ} (h1 : -π < x) (h2 : x < -(π / 2)) : cos x < 0 := by
  rw [← cos_neg]; exact cos_neg' (by linarith) (by linarith)

/-! ## The diagonal angle `φ₊` -/

/-- The angle `φ₊ ∈ (-π/2, π/2)` with `tan φ₊ = u_*`. -/
noncomputable def phiPlus (c τ : ℝ) : ℝ := arctan (ustar c τ)

theorem phiPlus_mem {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ) : phiPlus c τ ∈ Ioo (-(π / 2)) 0 := by
  refine ⟨neg_pi_div_two_lt_arctan _, ?_⟩
  have hu : ustar c τ < 0 := by
    simp only [ustar]; exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  rw [phiPlus, ← arctan_zero]
  exact arctan_strictMono hu

/-- `cos φ/c + 5/3 τ sin φ = (5/3 τ / cos φ₊) sin(φ - φ₊)`. -/
theorem g_eq {c τ : ℝ} (hc : c ≠ 0) (hτ : τ ≠ 0) (φ : ℝ) :
    1 / c * cos φ + 5 / 3 * τ * sin φ =
      5 / 3 * τ / cos (phiPlus c τ) * sin (φ - phiPlus c τ) := by
  have hq : sqrt (1 + ustar c τ ^ 2) ≠ 0 := by positivity
  rw [sin_sub, phiPlus, sin_arctan, cos_arctan]
  simp only [ustar]
  field_simp
  ring

theorem polarF_eq_sin {c τ : ℝ} (hc : c ≠ 0) (hτ : τ ≠ 0) (φ : ℝ) :
    polarF c τ φ = -(sin φ * cos φ) * (5 / 3 * τ / cos (phiPlus c τ) * sin (φ - phiPlus c τ)) := by
  rw [polarF, g_eq hc hτ]

/-! ## Lemma `lem:barrier`(ii) -/

/-- Lemma `lem:barrier`(ii) for `τ > 0`: the six arcs of `eq:arcs`. -/
theorem lem_barrier_ii_pos {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ) :
    phiPlus c τ ∈ Ioo (-(π / 2)) 0 ∧
    Connects (polarF c τ) (phiPlus c τ) (-(π / 2)) ∧
    Connects (polarF c τ) (phiPlus c τ) 0 ∧
    Connects (polarF c τ) (π / 2) 0 ∧
    Connects (polarF c τ) (π / 2) (phiPlus c τ + π) ∧
    Connects (polarF c τ) π (phiPlus c τ + π) ∧
    Connects (polarF c τ) (-π) (-(π / 2)) := by
  obtain ⟨K, hK⟩ := lipschitz_polarF c τ
  obtain ⟨hp1, hp2⟩ := phiPlus_mem hc hτ
  have hF := polarF_eq_sin hc.ne' hτ.ne'
  set φp := phiPlus c τ
  have hpi := pi_pos
  have hcos : 0 < cos φp := cos_pos' hp1 (by linarith)
  have hk : 0 < 5 / 3 * τ / cos φp := by positivity
  -- the zeros
  have z0 : polarF c τ 0 = 0 := by simp [polarF]
  have zpi : polarF c τ π = 0 := by simp [polarF]
  have zmpi : polarF c τ (-π) = 0 := by simp [polarF]
  have zhalf : polarF c τ (π / 2) = 0 := by simp [polarF]
  have zmhalf : polarF c τ (-(π / 2)) = 0 := by simp [polarF]
  have zp : polarF c τ φp = 0 := by rw [hF, sub_self, sin_zero, mul_zero, mul_zero]
  have zp' : polarF c τ (φp + π) = 0 := by
    rw [hF, add_sub_cancel_left, sin_pi, mul_zero, mul_zero]
  -- sign combinations
  have pos_of : ∀ x, (sin x * cos x < 0) → 0 < sin (x - φp) → 0 < polarF c τ x :=
    fun x h1 h2 => by rw [hF]; exact mul_pos (by linarith) (mul_pos hk h2)
  have pos_of' : ∀ x, (0 < sin x * cos x) → sin (x - φp) < 0 → 0 < polarF c τ x :=
    fun x h1 h2 => by rw [hF]; nlinarith [mul_neg_of_pos_of_neg hk h2]
  have neg_of : ∀ x, (0 < sin x * cos x) → 0 < sin (x - φp) → polarF c τ x < 0 :=
    fun x h1 h2 => by rw [hF]; nlinarith [mul_pos hk h2]
  have neg_of' : ∀ x, (sin x * cos x < 0) → sin (x - φp) < 0 → polarF c τ x < 0 :=
    fun x h1 h2 => by rw [hF]; nlinarith [mul_neg_of_pos_of_neg hk h2]
  refine ⟨⟨hp1, hp2⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `D⁺ → P⁻` on `(-π/2, φ₊)`
    refine connects_of_neg hK hp1 zp zmhalf fun x hx => neg_of' x ?_ ?_
    · exact mul_neg_of_neg_of_pos (sin_neg' (by linarith [hx.1]) (by linarith [hx.2]))
        (cos_pos' hx.1 (by linarith [hx.2]))
    · exact sin_neg' (by linarith [hx.1]) (by linarith [hx.2])
  · -- `D⁺ → TC⁺` on `(φ₊, 0)`
    refine connects_of_pos hK hp2 zp z0 fun x hx => pos_of x ?_ ?_
    · exact mul_neg_of_neg_of_pos (sin_neg' (by linarith [hx.1]) hx.2)
        (cos_pos' (by linarith [hx.1]) (by linarith [hx.2]))
    · exact sin_pos' (by linarith [hx.1]) (by linarith [hx.2])
  · -- `P⁺ → TC⁺` on `(0, π/2)`
    refine connects_of_neg hK (by linarith) zhalf z0 fun x hx => neg_of x ?_ ?_
    · exact mul_pos (sin_pos' hx.1 (by linarith [hx.2])) (cos_pos' (by linarith [hx.1]) hx.2)
    · exact sin_pos' (by linarith [hx.1]) (by linarith [hx.2])
  · -- `P⁺ → D⁻` on `(π/2, φ₊ + π)`
    refine connects_of_pos hK (by linarith) zhalf zp' fun x hx => pos_of x ?_ ?_
    · exact mul_neg_of_pos_of_neg (sin_pos' (by linarith [hx.1]) (by linarith [hx.2]))
        (cos_neg' hx.1 (by linarith [hx.2]))
    · exact sin_pos' (by linarith [hx.1]) (by linarith [hx.2])
  · -- `TC⁻ → D⁻` on `(φ₊ + π, π)`
    refine connects_of_neg hK (by linarith) zpi zp' fun x hx => neg_of' x ?_ ?_
    · exact mul_neg_of_pos_of_neg (sin_pos' (by linarith [hx.1]) hx.2)
        (cos_neg' (by linarith [hx.1]) hx.2)
    · exact sin_neg'' (by linarith [hx.1]) (by linarith [hx.2])
  · -- `TC⁻ → P⁻` on `(-π, -π/2)`
    refine connects_of_pos hK (by linarith) zmpi zmhalf fun x hx => pos_of' x ?_ ?_
    · exact mul_pos_of_neg_of_neg (sin_neg' hx.1 (by linarith [hx.2])) (cos_neg'' hx.1 hx.2)
    · exact sin_neg' (by linarith [hx.1]) (by linarith [hx.2])

/-- Lemma `lem:barrier`(ii) for `τ = 0`: the orbits `TC⁻ → P^± → TC⁺`. -/
theorem lem_barrier_ii_zero {c : ℝ} (hc : 0 < c) :
    Connects (polarF c 0) (π / 2) 0 ∧ Connects (polarF c 0) π (π / 2) ∧
    Connects (polarF c 0) (-(π / 2)) 0 ∧ Connects (polarF c 0) (-π) (-(π / 2)) := by
  obtain ⟨K, hK⟩ := lipschitz_polarF c 0
  have hpi := pi_pos
  have hF : ∀ x, polarF c 0 x = -(sin x * cos x ^ 2) / c := fun x => by
    simp only [polarF]; field_simp; ring
  have hcp : 0 < c := hc
  have z0 : polarF c 0 0 = 0 := by simp [polarF]
  have zpi : polarF c 0 π = 0 := by simp [polarF]
  have zmpi : polarF c 0 (-π) = 0 := by simp [polarF]
  have zhalf : polarF c 0 (π / 2) = 0 := by simp [polarF]
  have zmhalf : polarF c 0 (-(π / 2)) = 0 := by simp [polarF]
  have neg_of : ∀ x, 0 < sin x → cos x ≠ 0 → polarF c 0 x < 0 := fun x h1 h2 => by
    rw [hF]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos h1 (pow_pos_of_ne_zero h2))) hc
  have pos_of : ∀ x, sin x < 0 → cos x ≠ 0 → 0 < polarF c 0 x := fun x h1 h2 => by
    rw [hF]
    exact div_pos (neg_pos.2 (mul_neg_of_neg_of_pos h1 (pow_pos_of_ne_zero h2))) hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact connects_of_neg hK (by linarith) zhalf z0 fun x hx =>
      neg_of x (sin_pos' hx.1 (by linarith [hx.2]))
        (cos_pos' (by linarith [hx.1]) hx.2).ne'
  · exact connects_of_neg hK (by linarith) zpi zhalf fun x hx =>
      neg_of x (sin_pos' (by linarith [hx.1]) hx.2) (cos_neg' hx.1 hx.2).ne
  · exact connects_of_pos hK (by linarith) zmhalf z0 fun x hx =>
      pos_of x (sin_neg' (by linarith [hx.1]) hx.2) (cos_pos' hx.1 (by linarith [hx.2])).ne'
  · exact connects_of_pos hK (by linarith) zmpi zmhalf fun x hx =>
      pos_of x (sin_neg' hx.1 (by linarith [hx.2])) (cos_neg'' hx.1 hx.2).ne
where
  pow_pos_of_ne_zero {y : ℝ} (h : y ≠ 0) : 0 < y ^ 2 := by positivity

/-- The reversor `S̃` on `C_θ`: `φ ↦ π - φ` maps the polar field for `τ` to minus the polar field
for `-τ`. -/
theorem polarF_reflect (c τ φ : ℝ) : polarF c τ (π - φ) = polarF c (-τ) φ := by
  simp only [polarF, sin_pi_sub, cos_pi_sub]; ring

/-- Lemma `lem:barrier`(ii) for `τ < 0`: the arcs are the images of the arcs for `-τ` under
`φ ↦ π - φ`, with time reversed. -/
theorem lem_barrier_ii_neg {c τ p q : ℝ} (h : Connects (polarF c (-τ)) p q) :
    Connects (polarF c τ) (π - q) (π - p) := by
  intro ψ hψ h0
  have hφ : ∀ t, HasDerivAt (fun t => π - ψ (-t)) (polarF c (-τ) (π - ψ (-t))) t := fun t => by
    have := ((hψ (-t)).comp t (hasDerivAt_neg t)).const_sub π
    convert this using 1
    · rfl
    · rw [polarF_reflect, neg_neg]; ring
  have hmin : min (π - q) (π - p) = π - max p q := by
    rw [min_comm]; exact min_sub_sub_left π p q
  have hmax : max (π - q) (π - p) = π - min p q := by
    rw [max_comm]; exact max_sub_sub_left π p q
  rw [hmin, hmax] at h0 ⊢
  obtain ⟨hin, hbot, htop⟩ := h _ hφ ⟨by simp only [neg_zero]; linarith [h0.2],
    by simp only [neg_zero]; linarith [h0.1]⟩
  refine ⟨fun t => ?_, ?_, ?_⟩
  · have := hin (-t)
    rw [neg_neg] at this
    exact ⟨by linarith [this.2], by linarith [this.1]⟩
  · have := (htop.comp tendsto_neg_atBot_atTop).const_sub π
    refine this.congr fun t => ?_
    simp
  · have := (hbot.comp tendsto_neg_atTop_atBot).const_sub π
    refine this.congr fun t => ?_
    simp

/-! ## Lemma `lem:barrier`(iii) -/

section Barrier

variable {c a : ℝ} {T P τ : ℝ → ℝ} {t : ℝ}

/-- The sign of `T` is preserved, `T' = ((π̄ - 2) τ / 3) T`. -/
theorem T_pos (ht : 0 ≤ t) (hT : ∀ s ∈ Icc 0 t, HasDerivAt T (βT (T s) (P s) (τ s)) s)
    (hPc : ContinuousOn P (Icc 0 t)) (hτc : ContinuousOn τ (Icc 0 t)) (h0 : 0 < T 0) :
    0 < T t :=
  pos_of_linear (k := fun s => (P s - 2) * τ s / 3) ht
    (fun s hs => (hT s hs).congr_deriv (by simp only [βT]; ring)) (by fun_prop) h0

theorem T_neg (ht : 0 ≤ t) (hT : ∀ s ∈ Icc 0 t, HasDerivAt T (βT (T s) (P s) (τ s)) s)
    (hPc : ContinuousOn P (Icc 0 t)) (hτc : ContinuousOn τ (Icc 0 t)) (h0 : T 0 < 0) :
    T t < 0 := by
  have := pos_of_linear (T := fun s => -T s) (k := fun s => (P s - 2) * τ s / 3) ht
    (fun s hs => (hT s hs).neg.congr_deriv (by simp only [βT]; ring)) (by fun_prop)
    (by simpa using h0)
  simpa using this

/-- Lemma `lem:barrier`(iii): positive invariance of the half-spaces bounded by the barrier planes
`π̄ = ±a`, for solutions of `eq:gT`, `eq:gpi` on `[0, t]`. -/
theorem lem_barrier_iii (ha : a ^ 2 = 1 / 5) (ha0 : 0 < a) (hc : 0 < c) (ht : 0 ≤ t)
    (hT : ∀ s ∈ Icc 0 t, HasDerivAt T (βT (T s) (P s) (τ s)) s)
    (hP : ∀ s ∈ Icc 0 t, HasDerivAt P (βπ c (T s) (P s) (τ s)) s)
    (hτc : ContinuousOn τ (Icc 0 t)) :
    (0 < T 0 → -a ≤ P 0 → -a ≤ P t) ∧ (0 < T 0 → P 0 ≤ a → P t ≤ a) ∧
    (T 0 < 0 → P 0 ≤ -a → P t ≤ -a) ∧ (T 0 < 0 → a ≤ P 0 → a ≤ P t) := by
  have hTc : ContinuousOn T (Icc 0 t) := fun s hs => (hT s hs).continuousAt.continuousWithinAt
  have hPc : ContinuousOn P (Icc 0 t) := fun s hs => (hP s hs).continuousAt.continuousWithinAt
  have hsub : ∀ s ∈ Icc 0 t, Icc 0 s ⊆ Icc 0 t := fun s hs r hr => ⟨hr.1, hr.2.trans hs.2⟩
  have hTpos : 0 < T 0 → ∀ s ∈ Icc 0 t, 0 < T s := fun h0 s hs =>
    T_pos hs.1 (fun r hr => hT r (hsub s hs hr)) (hPc.mono (hsub s hs)) (hτc.mono (hsub s hs)) h0
  have hTneg : T 0 < 0 → ∀ s ∈ Icc 0 t, T s < 0 := fun h0 s hs =>
    T_neg hs.1 (fun r hr => hT r (hsub s hs hr)) (hPc.mono (hsub s hs)) (hτc.mono (hsub s hs)) h0
  have hβ : ∀ x y z, βπ c x y z = -(4 / 3) * (y ^ 2 - a ^ 2) * z - x * y / c := fun x y z => by
    simp only [βπ, ha]
  refine ⟨fun h0 hP0 => ?_, fun h0 hP0 => ?_, fun h0 hP0 => ?_, fun h0 hP0 => ?_⟩
  · have := fence_affine (g := fun s => -a - P s) (g' := fun s => -βπ c (T s) (P s) (τ s))
      (m := fun s => a * T s / c) (k := fun s => -(4 / 3 * (P s - a) * τ s + T s / c)) ht
      (fun s hs => (hP s hs).const_sub (-a)) (by linarith)
      (fun s _ => by rw [hβ]; field_simp; ring)
      (fun s hs => div_nonneg (mul_nonneg ha0.le (hTpos h0 s hs).le) hc.le) (by fun_prop)
    linarith
  · have := fence_affine (g := fun s => P s - a) (g' := fun s => βπ c (T s) (P s) (τ s))
      (m := fun s => a * T s / c) (k := fun s => -(4 / 3) * (P s + a) * τ s - T s / c) ht
      (fun s hs => (hP s hs).sub_const a) (by linarith)
      (fun s _ => by rw [hβ]; field_simp; ring)
      (fun s hs => div_nonneg (mul_nonneg ha0.le (hTpos h0 s hs).le) hc.le) (by fun_prop)
    linarith
  · have := fence_affine (g := fun s => P s + a) (g' := fun s => βπ c (T s) (P s) (τ s))
      (m := fun s => -(a * T s / c)) (k := fun s => -(4 / 3) * (P s - a) * τ s - T s / c) ht
      (fun s hs => (hP s hs).add_const a) (by linarith)
      (fun s _ => by rw [hβ]; field_simp; ring)
      (fun s hs => neg_nonneg.2 (div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos ha0.le (hTneg h0 s hs).le) hc.le)) (by fun_prop)
    linarith
  · have := fence_affine (g := fun s => a - P s) (g' := fun s => -βπ c (T s) (P s) (τ s))
      (m := fun s => -(a * T s / c)) (k := fun s => -(4 / 3) * (P s + a) * τ s - T s / c) ht
      (fun s hs => (hP s hs).const_sub a) (by linarith)
      (fun s _ => by rw [hβ]; field_simp; ring)
      (fun s hs => neg_nonneg.2 (div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos ha0.le (hTneg h0 s hs).le) hc.le)) (by fun_prop)
    linarith

end Barrier

end ConleyCheck.Gubser
