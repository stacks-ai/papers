import ConleyCheck.Gubser.TCFlow
import ConleyCheck.Conley.Sphere
import ConleyCheck.Conley.Conjugacy

/-!
# The Conley indices of the corner `TC` (`lem:TC`)

* (i) In the circle model, `(N^+, L^+)` deforms onto the circle `{u = 0, v = δ'}` with the arc
  `{x ≥ 0}` collapsed, which is `S¹` via `(x, y) ↦ (1 - 2m², 2my)`, `m = max(-x, 0)`. Hence
  `h(TC) = S¹` (`lem_TC_i`).
* (ii) For the reversed flow, `(N^+, E)` deforms onto the annulus `{|u| ≤ δ, v = δ'}` with
  `{|u| = δ} ∪ {x ≤ 0}` collapsed, which is `S²` (`lem_TC_ii`).
* (iii) In the interval model both pairs deform onto their exit sets, so both indices are
  trivial (`lem_TC_iii`).
-/

open Set Metric unitInterval WithLp
open ConleyCheck.Conley ConleyCheck.ODE

namespace ConleyCheck.Gubser

/-! ## Generic tools -/

section Generic

variable {α : Type*} [TopologicalSpace α]

/-- The map `N/L → N'/L` induced by the end of a deformation of `N` into `N'`. -/
noncomputable def retractMap {N L N' : Set α} (H : C(I × N, N))
    (hL : ∀ (t : I) (x : N), (x : α) ∈ L → (H (t, x) : α) ∈ L) (h1 : ∀ x, (H (1, x) : α) ∈ N') :
    C(IndexSpace N L, IndexSpace N' L) :=
  descend (IndexSpace.pt _ _)
    ((IndexSpace.proj N' L).comp ⟨fun x => ⟨H (1, x), h1 x⟩,
      ((continuous_subtype_val.comp H.continuous).comp
        (continuous_const.prodMk continuous_id)).subtype_mk _⟩)
    (fun x hx => IndexSpace.proj_eq_pt (hL 1 x hx))

/-- The map `N'/L → N/L` induced by the inclusion. -/
noncomputable def inclMap {N L N' : Set α} (hN' : N' ⊆ N) : C(IndexSpace N' L, IndexSpace N L) :=
  descend (IndexSpace.pt _ _)
    ((IndexSpace.proj N L).comp ⟨fun x => ⟨x, hN' x.2⟩, continuous_subtype_val.subtype_mk _⟩)
    (fun _ hx => IndexSpace.proj_eq_pt hx)

/-- A deformation of `N`, through maps preserving `L`, onto a retraction to `N' ⊆ N` gives
`N/L ≃ N'/L`. -/
noncomputable def retractEquiv {N L N' : Set α} (hN' : N' ⊆ N) (H : C(I × N, N))
    (h0 : ∀ x, H (0, x) = x) (hL : ∀ (t : I) (x : N), (x : α) ∈ L → (H (t, x) : α) ∈ L)
    (h1 : ∀ x, (H (1, x) : α) ∈ N') (hfix : ∀ x : N, (x : α) ∈ N' → H (1, x) = x) :
    PointedHomotopyEquiv (IndexSpace N L) (IndexSpace N' L) (IndexSpace.pt _ _)
      (IndexSpace.pt _ _) where
  toFun := retractMap H hL h1
  invFun := inclMap hN'
  map_pt := rfl
  inv_pt := rfl
  left := by
    refine ⟨ContinuousMap.HomotopyRel.symm
      { toFun := descendProd (IndexSpace.pt _ _) ((IndexSpace.proj N L).comp H)
          (fun s y hy => IndexSpace.proj_eq_pt (hL s y hy))
        continuous_toFun := (descendProd _ _ _).continuous
        map_zero_left := fun q => ?_
        map_one_left := fun q => ?_
        prop' := fun t q hq => ?_ }⟩
    · induction q using Quotient.inductionOn
      rename_i q
      rcases q with z | ⟨⟩
      · show IndexSpace.proj N L (H (0, z)) = IndexSpace.proj N L z
        rw [h0]
      · rfl
    · induction q using Quotient.inductionOn
      rename_i q
      rcases q with z | ⟨⟩
      · rfl
      · rfl
    · rw [mem_singleton_iff.1 hq]; rfl
  right := by
    have : (retractMap H hL h1).comp (inclMap hN') = ContinuousMap.id _ :=
      IndexSpace.hom_ext (fun y => by
        show IndexSpace.proj N' L ⟨H (1, ⟨y, hN' y.2⟩), _⟩ = IndexSpace.proj N' L y
        have e := congrArg Subtype.val (hfix ⟨y, hN' y.2⟩ y.2)
        exact congrArg (IndexSpace.proj _ _) (Subtype.ext e)) rfl
    rw [this]
    exact ContinuousMap.HomotopicRel.refl _

/-- A deformation of `N` into `L` through maps preserving `L` makes `N/L` contractible. -/
theorem pointedContractible_of_deform {N L : Set α} (H : C(I × N, N)) (h0 : ∀ x, H (0, x) = x)
    (hL : ∀ (t : I) (x : N), (x : α) ∈ L → (H (t, x) : α) ∈ L) (h1 : ∀ x, (H (1, x) : α) ∈ L) :
    PointedContractible (IndexSpace N L) (IndexSpace.pt N L) := by
  refine ⟨{
    toFun := descendProd (IndexSpace.pt _ _) ((IndexSpace.proj N L).comp H)
      (fun s y hy => IndexSpace.proj_eq_pt (hL s y hy))
    continuous_toFun := (descendProd _ _ _).continuous
    map_zero_left := fun q => ?_
    map_one_left := fun q => ?_
    prop' := fun t q hq => ?_ }⟩
  · induction q using Quotient.inductionOn
    rename_i q
    rcases q with z | ⟨⟩
    · show IndexSpace.proj N L (H (0, z)) = IndexSpace.proj N L z
      rw [h0]
    · rfl
  · induction q using Quotient.inductionOn
    rename_i q
    rcases q with z | ⟨⟩
    · exact IndexSpace.proj_eq_pt (h1 z)
    · rfl
  · rw [mem_singleton_iff.1 hq]; rfl

/-- A map `N → S^k` sending exactly `L` to the base point and bijective off `L` induces
`N/L ≅ S^k`, for compact `N`. -/
noncomputable def sphereEquivOf {N L : Set α} (hN : IsCompact N) {k : ℕ} (F : C(N, Sphere k))
    (hF : ∀ x : N, F x = Sphere.pt k ↔ (x : α) ∈ L)
    (hinj : ∀ x y : N, (x : α) ∉ L → F x = F y → x = y)
    (hsurj : ∀ p : Sphere k, p ≠ Sphere.pt k → ∃ x : N, F x = p) :
    PointedHomotopyEquiv (IndexSpace N L) (Sphere k) (IndexSpace.pt _ _) (Sphere.pt k) := by
  let G : C(IndexSpace N L, Sphere k) := descend (Sphere.pt k) F (fun x hx => (hF x).2 hx)
  have hG : Function.Bijective G := by
    constructor
    · intro a b hab
      induction a using Quotient.inductionOn
      induction b using Quotient.inductionOn
      rename_i a b
      rcases a with x | ⟨⟩ <;> rcases b with y | ⟨⟩
      · have h : F x = F y := hab
        by_cases hx : (x : α) ∈ L
        · have hy : (y : α) ∈ L := (hF y).1 (h ▸ (hF x).2 hx)
          exact Quotient.sound (Or.inr ⟨hx, hy⟩)
        · rw [hinj x y hx h]
      · have h : F x = Sphere.pt k := hab
        exact Quotient.sound (Or.inr ⟨(hF x).1 h, trivial⟩)
      · have h : F y = Sphere.pt k := hab.symm
        exact Quotient.sound (Or.inr ⟨trivial, (hF y).1 h⟩)
      · rfl
    · intro p
      by_cases hp : p = Sphere.pt k
      · exact ⟨IndexSpace.pt _ _, hp.symm⟩
      · obtain ⟨x, hx⟩ := hsurj p hp
        exact ⟨IndexSpace.proj _ _ x, hx⟩
  haveI := IndexSpace.compactSpace (N := N) L hN
  let h : IndexSpace N L ≃ₜ Sphere k :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective G hG) G.continuous
  exact PointedHomotopyEquiv.ofInverse ⟨h, h.continuous⟩ ⟨h.symm, h.symm.continuous⟩ rfl
    (by show h.symm (Sphere.pt k) = _; rw [Homeomorph.symm_apply_eq]; rfl)
    (ContinuousMap.ext fun x => h.symm_apply_apply x)
    (ContinuousMap.ext fun x => h.apply_symm_apply x)

end Generic

/-! ## Vectors in `ℝ²` and `ℝ³` -/

section Vec

/-- `(a, b) ∈ ℝ²`. -/
noncomputable def vec2 (a b : ℝ) : EuclideanSpace ℝ (Fin 2) := toLp 2 ![a, b]

/-- `(a, b, d) ∈ ℝ³`. -/
noncomputable def vec3 (a b d : ℝ) : EuclideanSpace ℝ (Fin 3) := toLp 2 ![a, b, d]

theorem norm_vec2_sq (a b : ℝ) : ‖vec2 a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]; simp [vec2]

theorem norm_vec3_sq (a b d : ℝ) : ‖vec3 a b d‖ ^ 2 = a ^ 2 + b ^ 2 + d ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]; simp [vec3]

theorem vec2_eq_iff {a b a' b' : ℝ} : vec2 a b = vec2 a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    exact ⟨by simpa [vec2] using congrArg (fun v => v 0) h,
      by simpa [vec2] using congrArg (fun v => v 1) h⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem vec3_eq_iff {a b d a' b' d' : ℝ} :
    vec3 a b d = vec3 a' b' d' ↔ a = a' ∧ b = b' ∧ d = d' := by
  constructor
  · intro h
    exact ⟨by simpa [vec3] using congrArg (fun v => v 0) h,
      by simpa [vec3] using congrArg (fun v => v 1) h,
      by simpa [vec3] using congrArg (fun v => v 2) h⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

theorem eq_vec2 (p : EuclideanSpace ℝ (Fin 2)) : p = vec2 (p 0) (p 1) := by
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i <;> simp [vec2]

theorem eq_vec3 (p : EuclideanSpace ℝ (Fin 3)) : p = vec3 (p 0) (p 1) (p 2) := by
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i <;> simp [vec3]

theorem single_eq_vec2 : EuclideanSpace.single (0 : Fin 2) (1 : ℝ) = vec2 1 0 := by
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i <;> simp [vec2]

theorem single_eq_vec3 : EuclideanSpace.single (0 : Fin 3) (1 : ℝ) = vec3 1 0 0 := by
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i <;> simp [vec3]

theorem continuous_vec2 {X : Type*} [TopologicalSpace X] {f g : X → ℝ} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => vec2 (f x) (g x) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i
  · simpa using hf
  · simpa using hg

theorem continuous_vec3 {X : Type*} [TopologicalSpace X] {f g h : X → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hh : Continuous h) : Continuous fun x => vec3 (f x) (g x) (h x) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i
  · simpa using hf
  · simpa using hg
  · simpa using hh

theorem norm_eq_one_of_sq {E : Type*} [NormedAddCommGroup E] {v : E} (h : ‖v‖ ^ 2 = 1) :
    ‖v‖ = 1 :=
  (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [h, one_pow])

end Vec

/-! ## Real algebra for the two sphere maps -/

section Algebra

theorem circ_norm {X Y : ℝ} (h : X ^ 2 + Y ^ 2 = 1) :
    (1 - 2 * max (-X) 0 ^ 2) ^ 2 + (2 * max (-X) 0 * Y) ^ 2 = 1 := by
  rcases le_total X 0 with hX | hX
  · rw [max_eq_left (by linarith)]; linear_combination (4 * X ^ 2) * h
  · rw [max_eq_right (by linarith)]; ring

theorem circ_pt {X Y : ℝ} :
    (1 - 2 * max (-X) 0 ^ 2 = 1 ∧ 2 * max (-X) 0 * Y = 0) ↔ 0 ≤ X := by
  constructor
  · rintro ⟨h1, -⟩
    have hm : max (-X) 0 ^ 2 = 0 := by linarith
    have := (pow_eq_zero_iff two_ne_zero).1 hm
    linarith [le_max_left (-X) 0]
  · intro hX; rw [max_eq_right (by linarith)]; simp

theorem circ_inj {X₁ Y₁ X₂ Y₂ : ℝ} (hX : X₁ < 0)
    (e1 : 1 - 2 * max (-X₁) 0 ^ 2 = 1 - 2 * max (-X₂) 0 ^ 2)
    (e2 : 2 * max (-X₁) 0 * Y₁ = 2 * max (-X₂) 0 * Y₂) : X₁ = X₂ ∧ Y₁ = Y₂ := by
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ -X₁)] at e1 e2
  have hm : max (-X₂) 0 = -X₁ := by
    have hsq : max (-X₂) 0 ^ 2 = (-X₁) ^ 2 := by linarith
    exact (sq_eq_sq₀ (le_max_right _ _) (by linarith)).1 hsq
  rw [hm] at e2
  have hX2 : -X₂ = -X₁ := by
    rcases le_total (-X₂) 0 with h | h
    · rw [max_eq_right h] at hm; linarith
    · rw [max_eq_left h] at hm; exact hm
  refine ⟨by linarith, ?_⟩
  exact mul_left_cancel₀ (mul_ne_zero two_ne_zero (by linarith : -X₁ ≠ 0)) e2

theorem circ_surj {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) (ha : a < 1) :
    ∃ X Y : ℝ, X ^ 2 + Y ^ 2 = 1 ∧ 1 - 2 * max (-X) 0 ^ 2 = a ∧ 2 * max (-X) 0 * Y = b := by
  obtain ⟨m, hm2, hm⟩ : ∃ m : ℝ, m ^ 2 = (1 - a) / 2 ∧ 0 < m :=
    ⟨√((1 - a) / 2), Real.sq_sqrt (by linarith), Real.sqrt_pos.2 (by linarith)⟩
  have hmax : max (-(-m)) 0 = m := by rw [neg_neg, max_eq_left hm.le]
  refine ⟨-m, b / (2 * m), ?_, ?_, ?_⟩
  · have e : (b / (2 * m)) ^ 2 * (4 * m ^ 2) = b ^ 2 := by field_simp; ring
    have h4 : 0 < 4 * m ^ 2 := by positivity
    have : ((-m) ^ 2 + (b / (2 * m)) ^ 2) * (4 * m ^ 2) = 1 * (4 * m ^ 2) := by
      have e2 : ((-m) ^ 2 + (b / (2 * m)) ^ 2) * (4 * m ^ 2) =
          4 * (m ^ 2) ^ 2 + (b / (2 * m)) ^ 2 * (4 * m ^ 2) := by ring
      rw [e2, e, hm2]; linear_combination h
    exact mul_right_cancel₀ h4.ne' this
  · rw [hmax, hm2]; ring
  · rw [hmax]; field_simp

/-- First coordinate of the map `[-δ, δ] × S¹ → S²`. -/
noncomputable def sphA (δ U X : ℝ) : ℝ := 1 - 2 * (1 - (U / δ) ^ 2) * max X 0 ^ 2

/-- Second coordinate. -/
noncomputable def sphB (δ U X : ℝ) : ℝ := 2 * (U / δ) * max X 0 ^ 2 * √(1 - (U / δ) ^ 2)

/-- Third coordinate. -/
noncomputable def sphC (δ U X Y : ℝ) : ℝ := -(2 * max X 0 * Y * √(1 - (U / δ) ^ 2))

theorem sq_div_le_one {δ U : ℝ} (hδ : 0 < δ) (hU : |U| ≤ δ) : (U / δ) ^ 2 ≤ 1 := by
  rw [div_pow, div_le_one (by positivity), ← sq_abs U]
  exact pow_le_pow_left₀ (abs_nonneg U) hU 2

theorem sq_div_lt_one {δ U : ℝ} (hδ : 0 < δ) (hU : |U| < δ) : (U / δ) ^ 2 < 1 := by
  rw [div_pow, div_lt_one (by positivity), ← sq_abs U]
  exact pow_lt_pow_left₀ hU (abs_nonneg U) two_ne_zero

theorem sph_norm {δ U X Y : ℝ} (hδ : 0 < δ) (hU : |U| ≤ δ) (h : X ^ 2 + Y ^ 2 = 1) :
    sphA δ U X ^ 2 + sphB δ U X ^ 2 + sphC δ U X Y ^ 2 = 1 := by
  have hs := sq_div_le_one hδ hU
  unfold sphA sphB sphC
  set s := U / δ
  have hr : √(1 - s ^ 2) ^ 2 = 1 - s ^ 2 := Real.sq_sqrt (by linarith)
  set r := √(1 - s ^ 2)
  rcases le_total X 0 with hX | hX
  · rw [max_eq_right hX]; ring
  · rw [max_eq_left hX]
    linear_combination (4 * (1 - s ^ 2) * X ^ 2) * h + (4 * X ^ 2 * (s ^ 2 * X ^ 2 + Y ^ 2)) * hr

theorem sph_pt {δ U X Y : ℝ} (hδ : 0 < δ) :
    (sphA δ U X = 1 ∧ sphB δ U X = 0 ∧ sphC δ U X Y = 0) ↔ (|U| = δ ∨ X ≤ 0) := by
  constructor
  · rintro ⟨h1, -, -⟩
    unfold sphA at h1
    have : (1 - (U / δ) ^ 2) * max X 0 ^ 2 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · left
      have hU : U ^ 2 = δ ^ 2 := by
        rw [div_pow] at h; field_simp at h; linarith
      rw [← sq_abs U] at hU
      exact (sq_eq_sq₀ (abs_nonneg U) hδ.le).1 hU
    · right
      have := (pow_eq_zero_iff two_ne_zero).1 h
      linarith [le_max_left X 0]
  · rintro (h | h)
    · have hs : 1 - (U / δ) ^ 2 = 0 := by
        rw [div_pow, ← sq_abs U, h, div_self (by positivity)]; ring
      simp [sphA, sphB, sphC, hs]
    · simp [sphA, sphB, sphC, max_eq_right h]

theorem sph_inj {δ U₁ X₁ Y₁ U₂ X₂ Y₂ : ℝ} (hδ : 0 < δ) (hU₁ : |U₁| < δ) (hX₁ : 0 < X₁)
    (hU₂ : |U₂| ≤ δ) (h₁ : X₁ ^ 2 + Y₁ ^ 2 = 1) (h₂ : X₂ ^ 2 + Y₂ ^ 2 = 1)
    (eA : sphA δ U₁ X₁ = sphA δ U₂ X₂) (eB : sphB δ U₁ X₁ = sphB δ U₂ X₂)
    (eC : sphC δ U₁ X₁ Y₁ = sphC δ U₂ X₂ Y₂) : U₁ = U₂ ∧ X₁ = X₂ ∧ Y₁ = Y₂ := by
  have hs₁ := sq_div_lt_one hδ hU₁
  have hs₂ := sq_div_le_one hδ hU₂
  simp only [sphA, sphB, sphC] at eA eB eC
  rw [max_eq_left hX₁.le] at eA eB eC
  have hr₁ : √(1 - (U₁ / δ) ^ 2) ^ 2 = 1 - (U₁ / δ) ^ 2 := Real.sq_sqrt (by linarith)
  have hr₂ : √(1 - (U₂ / δ) ^ 2) ^ 2 = 1 - (U₂ / δ) ^ 2 := Real.sq_sqrt (by linarith)
  have hr₁p : 0 < √(1 - (U₁ / δ) ^ 2) := Real.sqrt_pos.2 (by linarith)
  have hr₂0 : 0 ≤ √(1 - (U₂ / δ) ^ 2) := Real.sqrt_nonneg _
  set r₁ := √(1 - (U₁ / δ) ^ 2)
  set r₂ := √(1 - (U₂ / δ) ^ 2)
  set s₁ := U₁ / δ with hs₁def
  set s₂ := U₂ / δ with hs₂def
  have hw₂ : 0 ≤ max X₂ 0 := le_max_right _ _
  set w₂ := max X₂ 0 with hw₂def
  have ha : r₁ * X₁ = r₂ * w₂ := by
    have : (r₁ * X₁) ^ 2 = (r₂ * w₂) ^ 2 := by
      linear_combination X₁ ^ 2 * hr₁ - w₂ ^ 2 * hr₂ - (1 / 2) * eA
    exact (sq_eq_sq₀ (by positivity) (by positivity)).1 this
  have hapos : 0 < r₁ * X₁ := by positivity
  have hY : Y₁ = Y₂ := by
    have : (r₁ * X₁) * Y₁ = (r₁ * X₁) * Y₂ := by
      linear_combination (-1 / 2) * eC - Y₂ * ha
    exact mul_left_cancel₀ hapos.ne' this
  have hw₂p : 0 < w₂ := pos_of_mul_pos_right (ha ▸ hapos) hr₂0
  have hX₂ : 0 < X₂ := by
    by_contra hn
    rw [hw₂def, max_eq_right (not_lt.1 hn)] at hw₂p
    exact lt_irrefl _ hw₂p
  rw [hw₂def, max_eq_left hX₂.le] at ha eB
  have hX : X₁ = X₂ := by
    have : X₁ ^ 2 = X₂ ^ 2 := by rw [hY] at h₁; linarith
    exact (sq_eq_sq₀ hX₁.le hX₂.le).1 this
  subst hX hY
  have hr : r₁ = r₂ := mul_right_cancel₀ hX₁.ne' ha
  rw [← hr] at eB
  have hs : s₁ = s₂ := by
    have : (2 * X₁ ^ 2 * r₁) * s₁ = (2 * X₁ ^ 2 * r₁) * s₂ := by linear_combination eB
    exact mul_left_cancel₀ (by positivity) this
  refine ⟨?_, rfl, rfl⟩
  rw [hs₁def, hs₂def] at hs
  exact (div_left_inj' hδ.ne').1 hs

theorem sph_surj {δ p0 p1 p2 : ℝ} (hδ : 0 < δ) (h : p0 ^ 2 + p1 ^ 2 + p2 ^ 2 = 1) (hp : p0 < 1) :
    ∃ U X Y : ℝ, |U| ≤ δ ∧ X ^ 2 + Y ^ 2 = 1 ∧ sphA δ U X = p0 ∧ sphB δ U X = p1 ∧
      sphC δ U X Y = p2 := by
  obtain ⟨a, ha2, ha⟩ : ∃ a : ℝ, a ^ 2 = (1 - p0) / 2 ∧ 0 < a :=
    ⟨√((1 - p0) / 2), Real.sq_sqrt (by linarith), Real.sqrt_pos.2 (by linarith)⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y * (2 * a) = -p2 := ⟨-p2 / (2 * a), by field_simp⟩
  have hY2 : (2 * a) ^ 2 * Y ^ 2 = p2 ^ 2 := by
    have : (Y * (2 * a)) ^ 2 = p2 ^ 2 := by rw [hY]; ring
    linear_combination this
  have hY1 : Y ^ 2 < 1 := by
    have hlt : p2 ^ 2 < (2 * a) ^ 2 := by
      have : (2 * a) ^ 2 = 2 * (1 - p0) := by rw [mul_pow, ha2]; ring
      rw [this]; nlinarith [sq_nonneg p1]
    by_contra hn
    have : (2 * a) ^ 2 * 1 ≤ (2 * a) ^ 2 * Y ^ 2 :=
      mul_le_mul_of_nonneg_left (not_lt.1 hn) (by positivity)
    linarith
  obtain ⟨X, hX2, hX⟩ : ∃ X : ℝ, X ^ 2 = 1 - Y ^ 2 ∧ 0 < X :=
    ⟨√(1 - Y ^ 2), Real.sq_sqrt (by linarith), Real.sqrt_pos.2 (by linarith)⟩
  obtain ⟨r, hr, hr0⟩ : ∃ r : ℝ, r * X = a ∧ 0 < r :=
    ⟨a / X, div_mul_cancel₀ a hX.ne', by positivity⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s * (2 * X * a) = p1 :=
    ⟨p1 / (2 * X * a), div_mul_cancel₀ _ (by positivity)⟩
  have key : s ^ 2 + r ^ 2 = 1 := by
    have h4 : 0 < 4 * X ^ 2 * a ^ 2 := by positivity
    have : (s ^ 2 + r ^ 2) * (4 * X ^ 2 * a ^ 2) = 1 * (4 * X ^ 2 * a ^ 2) := by
      have e : (s ^ 2 + r ^ 2) * (4 * X ^ 2 * a ^ 2) =
          (s * (2 * X * a)) ^ 2 + 4 * a ^ 2 * (r * X) ^ 2 := by ring
      rw [e, hs, hr, hX2]
      linear_combination hY2 + h + (4 * a ^ 2 - 2 - 2 * p0) * ha2
    exact mul_right_cancel₀ h4.ne' this
  have hs1 : |s| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg r]
  refine ⟨δ * s, X, Y, ?_, by linarith, ?_, ?_, ?_⟩
  · rw [abs_mul, abs_of_pos hδ]; nlinarith [abs_nonneg s]
  all_goals
    simp only [sphA, sphB, sphC]
    rw [mul_div_cancel_left₀ s hδ.ne', max_eq_left hX.le, show 1 - s ^ 2 = r ^ 2 by linarith]
    try rw [Real.sqrt_sq hr0.le]
  · linear_combination -(2 * (r * X + a)) * hr - 2 * ha2
  · linear_combination (2 * s * X) * hr + hs
  · linear_combination (-2 * Y) * hr - hY

end Algebra

/-! ## Coordinates on the circle model -/

/-- `u` on `XS`. -/
abbrev uS (q : XS) : ℝ := (q : E4).1
/-- `v` on `XS`. -/
abbrev vS (q : XS) : ℝ := (q : E4).2.1
/-- `x` on `XS`. -/
abbrev xS (q : XS) : ℝ := (q : E4).2.2.1
/-- `y` on `XS`. -/
abbrev yS (q : XS) : ℝ := (q : E4).2.2.2

theorem XS_ext {p q : XS} (h1 : uS p = uS q) (h2 : vS p = vS q) (h3 : xS p = xS q)
    (h4 : yS p = yS q) : p = q :=
  Subtype.ext (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4)))

theorem interp_le {t v δ' : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hv : v ≤ δ') : (1 - t) * v + t * δ' ≤ δ' := by
  nlinarith [ht.1, ht.2]

theorem interp_nonneg {t v δ' : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hv : 0 ≤ v) (hδ' : 0 ≤ δ') :
    0 ≤ (1 - t) * v + t * δ' := by
  nlinarith [ht.1, ht.2]

theorem abs_shrink_le {t u δ : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : |u| ≤ δ) : |(1 - t) * u| ≤ δ := by
  rw [abs_mul, abs_of_nonneg (by linarith [ht.2])]; nlinarith [ht.1, abs_nonneg u]

/-! ## The blocks in the circle model -/

/-- `N^+ = {|u| ≤ δ, v ≤ δ'}` in `XS`. -/
def NS (δ δ' : ℝ) : Set XS := {q | |uS q| ≤ δ ∧ vS q ≤ δ'}

/-- `L^+ = {|u| ≤ δ, v = δ', x ≥ 0}`, the exit set of the forward flow. -/
def LS (δ δ' : ℝ) : Set XS := {q | |uS q| ≤ δ ∧ vS q = δ' ∧ 0 ≤ xS q}

/-- `{|u| = δ} ∪ {v = δ', x ≤ 0}`, the exit set of the reversed flow. -/
def ES (δ δ' : ℝ) : Set XS :=
  {q | |uS q| ≤ δ ∧ vS q ≤ δ' ∧ (|uS q| = δ ∨ (vS q = δ' ∧ xS q ≤ 0))}

theorem isCompact_NS {δ δ' : ℝ} : IsCompact (NS δ δ') := (modelS 0).isCompact_N

/-! ## Part (i): `N^+/L^+ ≃ S¹` -/

section PartI

variable {c δ δ' : ℝ}

/-- The circle `{u = 0, v = δ'}` onto which `N^+` deforms. -/
def NS1 (δ' : ℝ) : Set XS := {q | uS q = 0 ∧ vS q = δ'}

theorem NS1_subset (hδ : 0 ≤ δ) : NS1 δ' ⊆ NS δ δ' := fun q hq => by
  show |uS q| ≤ δ ∧ vS q ≤ δ'
  rw [hq.1, abs_zero]; exact ⟨hδ, hq.2.le⟩

theorem isCompact_NS1 (hδ : 0 ≤ δ) : IsCompact (NS1 δ') :=
  isCompact_NS.of_isClosed_subset
    ((isClosed_eq (by fun_prop) continuous_const).inter (isClosed_eq (by fun_prop) continuous_const))
    (NS1_subset hδ)

/-- `(t, (u, v, x, y)) ↦ ((1 - t) u, (1 - t) v + t δ', x, y)`. -/
noncomputable def homS1 (hδ' : 0 ≤ δ') : C(I × NS δ δ', NS δ δ') where
  toFun p := ⟨⟨((1 - (p.1 : ℝ)) * uS p.2, (1 - (p.1 : ℝ)) * vS p.2 + (p.1 : ℝ) * δ', xS p.2, yS p.2),
      interp_nonneg p.1.2 (p.2 : XS).2.1 hδ', (p.2 : XS).2.2⟩,
    abs_shrink_le p.1.2 p.2.2.1, interp_le p.1.2 p.2.2.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    fun_prop

/-- The map `{u = 0, v = δ'} → S¹`. -/
noncomputable def circMap (δ' : ℝ) : C(NS1 δ', Sphere 1) where
  toFun y := ⟨vec2 (1 - 2 * max (-xS y) 0 ^ 2) (2 * max (-xS y) 0 * yS y), by
    rw [mem_sphere_zero_iff_norm]
    exact norm_eq_one_of_sq (by rw [norm_vec2_sq]; exact circ_norm (y : XS).2.2)⟩
  continuous_toFun := Continuous.subtype_mk (continuous_vec2 (by fun_prop) (by fun_prop)) _

theorem circMap_pt_iff (hδ : 0 ≤ δ) (y : NS1 δ') :
    circMap δ' y = Sphere.pt 1 ↔ (y : XS) ∈ LS δ δ' := by
  rw [Subtype.ext_iff]
  change vec2 _ _ = EuclideanSpace.single 0 1 ↔ _
  rw [single_eq_vec2, vec2_eq_iff, circ_pt]
  constructor
  · intro h
    show |uS y| ≤ δ ∧ vS y = δ' ∧ 0 ≤ xS y
    rw [y.2.1, abs_zero]; exact ⟨hδ, y.2.2, h⟩
  · intro h; exact h.2.2

/-- `N^+/L^+` is the pointed circle. -/
theorem indexS1 (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') :
    Nonempty (PointedHomotopyEquiv (IndexSpace (NS δ δ') (LS δ δ')) (Sphere 1)
      (IndexSpace.pt _ _) (Sphere.pt 1)) := by
  refine ⟨(retractEquiv (NS1_subset hδ) (homS1 hδ')
    (fun x => ?_) (fun t x hx => ?_) (fun x => ?_) (fun x hx => ?_)).trans
    (sphereEquivOf (isCompact_NS1 hδ) (circMap δ') (circMap_pt_iff hδ)
      (fun x y hx hxy => ?_) (fun p hp => ?_))⟩
  · refine Subtype.ext (XS_ext ?_ ?_ rfl rfl)
    · show (1 - ((0 : I) : ℝ)) * uS x = uS x; simp
    · show (1 - ((0 : I) : ℝ)) * vS x + ((0 : I) : ℝ) * δ' = vS x; simp
  · obtain ⟨-, hv, hτ⟩ := hx
    refine ⟨(homS1 hδ' (t, x)).2.1, ?_, hτ⟩
    change (1 - (t : ℝ)) * vS x + t * δ' = δ'
    rw [show vS x = δ' from hv]; ring
  · show (1 - ((1 : I) : ℝ)) * uS x = 0 ∧ (1 - ((1 : I) : ℝ)) * vS x + ((1 : I) : ℝ) * δ' = δ'
    simp
  · refine Subtype.ext (XS_ext ?_ ?_ rfl rfl)
    · show (1 - ((1 : I) : ℝ)) * uS x = uS x
      rw [show uS x = 0 from hx.1]; simp
    · show (1 - ((1 : I) : ℝ)) * vS x + ((1 : I) : ℝ) * δ' = vS x
      rw [show vS x = δ' from hx.2]; simp
  · have hX : xS x < 0 := by
      by_contra hn
      exact hx (by
        show |uS x| ≤ δ ∧ vS x = δ' ∧ 0 ≤ xS x
        rw [x.2.1, abs_zero]; exact ⟨hδ, x.2.2, not_lt.1 hn⟩)
    have e := congrArg Subtype.val hxy
    change vec2 _ _ = vec2 _ _ at e
    obtain ⟨e1, e2⟩ := vec2_eq_iff.1 e
    obtain ⟨h3, h4⟩ := circ_inj hX e1 e2
    exact Subtype.ext (XS_ext (by rw [x.2.1, y.2.1]) (by rw [x.2.2, y.2.2]) h3 h4)
  · obtain ⟨p, hpS⟩ := p
    have hpv := eq_vec2 p
    have hn : (p 0) ^ 2 + (p 1) ^ 2 = 1 := by
      rw [← norm_vec2_sq, ← hpv, mem_sphere_zero_iff_norm.1 hpS, one_pow]
    have ha : p 0 < 1 := by
      refine lt_of_le_of_ne (by nlinarith [sq_nonneg (p 1)]) fun h1 => hp (Subtype.ext ?_)
      have hb : p 1 = 0 := by
        rw [h1] at hn; exact pow_eq_zero_iff two_ne_zero |>.1 (by linarith)
      change p = EuclideanSpace.single 0 1
      rw [single_eq_vec2, hpv, h1, hb]
    obtain ⟨X, Y, hXY, e1, e2⟩ := circ_surj hn ha
    refine ⟨⟨⟨(0, δ', X, Y), hδ', hXY⟩, rfl, rfl⟩, Subtype.ext ?_⟩
    change vec2 (1 - 2 * max (-X) 0 ^ 2) (2 * max (-X) 0 * Y) = p
    rw [e1, e2, ← hpv]

/-- Part (i) of `lem:TC`, for every flow on the doubled chart `XS` whose coordinates satisfy
`eq:flowTp` (with `τ = x`) near `N^+`: `h(TC^+) = S¹`. -/
theorem lem_TC_i_of (M : TCModel c XS) (hu : ∀ q, M.u q = uS q) (hv : ∀ q, M.v q = vS q)
    (hτ : ∀ q, M.τ q = xS q) (H : TCHyp c δ δ') : HasIndex M.ϕ M.TC (Sphere 1) (Sphere.pt 1) := by
  obtain ⟨e⟩ := indexS1 H.hδ.le (H.hδ.trans H.h1).le
  refine ⟨NS δ δ', LS δ δ', ?_, ⟨e⟩⟩
  have hN : M.N δ δ' = NS δ δ' := by ext q; simp only [TCModel.N, NS, mem_setOf_eq, hu, hv]
  have hL : M.L δ δ' = LS δ δ' := by
    ext q; simp only [TCModel.L, LS, mem_setOf_eq, hu, hv, hτ]
  rw [← hN, ← hL]; exact M.isIndexPair_L H

/-- Part (i) of `lem:TC` for the cut-off circle flow. -/
theorem lem_TC_i (H : TCHyp c δ δ') : HasIndex (ϕS c) (modelS c).TC (Sphere 1) (Sphere.pt 1) :=
  lem_TC_i_of (modelS c) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) H

end PartI

/-! ## Part (ii): `N^+/E ≃ S²` -/

section PartII

variable {c δ δ' : ℝ}

/-- The annulus `{|u| ≤ δ, v = δ'}` onto which `N^+` deforms. -/
def NS2 (δ δ' : ℝ) : Set XS := {q | |uS q| ≤ δ ∧ vS q = δ'}

theorem NS2_subset : NS2 δ δ' ⊆ NS δ δ' := fun _ hq => ⟨hq.1, hq.2.le⟩

theorem isCompact_NS2 : IsCompact (NS2 δ δ') :=
  isCompact_NS.of_isClosed_subset
    ((isClosed_le (by fun_prop : Continuous fun q : XS => |uS q|) continuous_const).inter
      (isClosed_eq (by fun_prop : Continuous fun q : XS => vS q) continuous_const))
    NS2_subset

/-- `(t, (u, v, x, y)) ↦ (u, (1 - t) v + t δ', x, y)`. -/
noncomputable def homS2 (hδ' : 0 ≤ δ') : C(I × NS δ δ', NS δ δ') where
  toFun p := ⟨⟨(uS p.2, (1 - (p.1 : ℝ)) * vS p.2 + (p.1 : ℝ) * δ', xS p.2, yS p.2),
      interp_nonneg p.1.2 (p.2 : XS).2.1 hδ', (p.2 : XS).2.2⟩,
    p.2.2.1, interp_le p.1.2 p.2.2.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    fun_prop

/-- The map `{|u| ≤ δ, v = δ'} → S²`. -/
noncomputable def annMap (hδ : 0 < δ) (δ' : ℝ) : C(NS2 δ δ', Sphere 2) where
  toFun y := ⟨vec3 (sphA δ (uS y) (xS y)) (sphB δ (uS y) (xS y)) (sphC δ (uS y) (xS y) (yS y)), by
    rw [mem_sphere_zero_iff_norm]
    exact norm_eq_one_of_sq (by rw [norm_vec3_sq]; exact sph_norm hδ y.2.1 (y : XS).2.2)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_vec3 ?_ ?_ ?_) _ <;>
      · simp only [sphA, sphB, sphC]; fun_prop

theorem annMap_pt_iff (hδ : 0 < δ) (y : NS2 δ δ') :
    annMap hδ δ' y = Sphere.pt 2 ↔ (y : XS) ∈ ES δ δ' := by
  rw [Subtype.ext_iff]
  change vec3 _ _ _ = EuclideanSpace.single 0 1 ↔ _
  rw [single_eq_vec3, vec3_eq_iff, sph_pt hδ]
  constructor
  · intro h
    show |uS y| ≤ δ ∧ vS y ≤ δ' ∧ (|uS y| = δ ∨ (vS y = δ' ∧ xS y ≤ 0))
    refine ⟨y.2.1, y.2.2.le, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨y.2.2, h⟩
  · rintro ⟨-, -, h | h⟩
    · exact Or.inl h
    · exact Or.inr h.2

/-- `N^+/E` is the pointed 2-sphere. -/
theorem indexS2 (hδ : 0 < δ) (hδ' : 0 ≤ δ') :
    Nonempty (PointedHomotopyEquiv (IndexSpace (NS δ δ') (ES δ δ')) (Sphere 2)
      (IndexSpace.pt _ _) (Sphere.pt 2)) := by
  refine ⟨(retractEquiv NS2_subset (homS2 hδ')
    (fun x => ?_) (fun t x hx => ?_) (fun x => ?_) (fun x hx => ?_)).trans
    (sphereEquivOf isCompact_NS2 (annMap hδ δ') (annMap_pt_iff hδ)
      (fun x y hx hxy => ?_) (fun p hp => ?_))⟩
  · refine Subtype.ext (XS_ext rfl ?_ rfl rfl)
    show (1 - ((0 : I) : ℝ)) * vS x + ((0 : I) : ℝ) * δ' = vS x; simp
  · obtain ⟨hu, hv, h⟩ := hx
    refine ⟨hu, (homS2 hδ' (t, x)).2.2, ?_⟩
    rcases h with h | ⟨hv', hτ⟩
    · exact Or.inl h
    · refine Or.inr ⟨?_, hτ⟩
      change (1 - (t : ℝ)) * vS x + t * δ' = δ'
      rw [show vS x = δ' from hv']; ring
  · show |uS x| ≤ δ ∧ (1 - ((1 : I) : ℝ)) * vS x + ((1 : I) : ℝ) * δ' = δ'
    exact ⟨x.2.1, by simp⟩
  · refine Subtype.ext (XS_ext rfl ?_ rfl rfl)
    show (1 - ((1 : I) : ℝ)) * vS x + ((1 : I) : ℝ) * δ' = vS x
    rw [show vS x = δ' from hx.2]; simp
  · have hxE : ¬(|uS x| = δ ∨ xS x ≤ 0) := fun h => hx (by
      show |uS x| ≤ δ ∧ vS x ≤ δ' ∧ (|uS x| = δ ∨ (vS x = δ' ∧ xS x ≤ 0))
      refine ⟨x.2.1, x.2.2.le, ?_⟩
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨x.2.2, h⟩)
    push Not at hxE
    have hU : |uS x| < δ := lt_of_le_of_ne x.2.1 hxE.1
    have e := congrArg Subtype.val hxy
    change vec3 _ _ _ = vec3 _ _ _ at e
    obtain ⟨eA, eB, eC⟩ := vec3_eq_iff.1 e
    obtain ⟨h1, h3, h4⟩ := sph_inj hδ hU hxE.2 y.2.1 (x : XS).2.2 (y : XS).2.2 eA eB eC
    exact Subtype.ext (XS_ext h1 (by rw [x.2.2, y.2.2]) h3 h4)
  · obtain ⟨p, hpS⟩ := p
    have hpv := eq_vec3 p
    have hn : (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 = 1 := by
      rw [← norm_vec3_sq, ← hpv, mem_sphere_zero_iff_norm.1 hpS, one_pow]
    have ha : p 0 < 1 := by
      refine lt_of_le_of_ne (by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2)]) fun h1 =>
        hp (Subtype.ext ?_)
      rw [h1] at hn
      have hb : p 1 = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by nlinarith [sq_nonneg (p 2)])
      have hd : p 2 = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by nlinarith [sq_nonneg (p 1)])
      change p = EuclideanSpace.single 0 1
      rw [single_eq_vec3, hpv, h1, hb, hd]
    obtain ⟨U, X, Y, hU, hXY, e1, e2, e3⟩ := sph_surj hδ hn ha
    refine ⟨⟨⟨(U, δ', X, Y), hδ', hXY⟩, hU, rfl⟩, Subtype.ext ?_⟩
    change vec3 (sphA δ U X) (sphB δ U X) (sphC δ U X Y) = p
    rw [e1, e2, e3, ← hpv]

/-- Part (ii) of `lem:TC` in the chart `T = +∞`, for every flow on `XS` whose coordinates satisfy
`eq:flowTp` near `N^+`: the reversed flow has `h(TC^+) = S²`. -/
theorem lem_TC_ii_of (M : TCModel c XS) (hu : ∀ q, M.u q = uS q) (hv : ∀ q, M.v q = vS q)
    (hτ : ∀ q, M.τ q = xS q) (H : TCHyp c δ δ') :
    HasIndex M.ϕ.reverse M.TC (Sphere 2) (Sphere.pt 2) := by
  obtain ⟨e⟩ := indexS2 H.hδ (H.hδ.trans H.h1).le
  refine ⟨NS δ δ', ES δ δ', ?_, ⟨e⟩⟩
  have hN : M.N δ δ' = NS δ δ' := by ext q; simp only [TCModel.N, NS, mem_setOf_eq, hu, hv]
  have hE : M.E δ δ' = ES δ δ' := by
    ext q; simp only [TCModel.E, ES, mem_setOf_eq, hu, hv, hτ]
  rw [← hN, ← hE]; exact M.isIndexPair_E H

/-- Part (ii) of `lem:TC` in the chart `T = +∞` for the cut-off circle flow. -/
theorem lem_TC_ii (H : TCHyp c δ δ') :
    HasIndex (ϕS c).reverse (modelS c).TC (Sphere 2) (Sphere.pt 2) :=
  lem_TC_ii_of (modelS c) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) H

end PartII

/-! ## Part (iii): the interval model -/

section PartIII

variable {c δ δ' : ℝ}

/-- `u` on `XI`. -/
abbrev uI (q : XI) : ℝ := (q : E3).1
/-- `v` on `XI`. -/
abbrev vI (q : XI) : ℝ := (q : E3).2.1
/-- `τ` on `XI`. -/
abbrev τI (q : XI) : ℝ := (q : E3).2.2

theorem XI_ext {p q : XI} (h1 : uI p = uI q) (h2 : vI p = vI q) (h3 : τI p = τI q) : p = q :=
  Subtype.ext (Prod.ext h1 (Prod.ext h2 h3))

/-- `N^+` in `XI`. -/
def NI (δ δ' : ℝ) : Set XI := {q | |uI q| ≤ δ ∧ vI q ≤ δ'}

/-- `L^+ = {|u| ≤ δ, v = δ', τ ≥ 0}` in `XI`. -/
def LI (δ δ' : ℝ) : Set XI := {q | |uI q| ≤ δ ∧ vI q = δ' ∧ 0 ≤ τI q}

/-- `{|u| = δ} ∪ {v = δ', τ ≤ 0}` in `XI`. -/
def EI (δ δ' : ℝ) : Set XI :=
  {q | |uI q| ≤ δ ∧ vI q ≤ δ' ∧ (|uI q| = δ ∨ (vI q = δ' ∧ τI q ≤ 0))}

/-- `(t, (u, v, τ)) ↦ ((1 - t) u, (1 - t) v + t δ', (1 - t) τ + t)`, ending at `(0, δ', 1) ∈ L`. -/
noncomputable def homI1 (hδ' : 0 ≤ δ') : C(I × NI δ δ', NI δ δ') where
  toFun p := ⟨⟨((1 - (p.1 : ℝ)) * uI p.2, (1 - (p.1 : ℝ)) * vI p.2 + (p.1 : ℝ) * δ',
        (1 - (p.1 : ℝ)) * τI p.2 + p.1),
      interp_nonneg p.1.2 (p.2 : XI).2.1 hδ',
      by nlinarith [p.1.2.1, p.1.2.2, (p.2 : XI).2.2.1],
      by nlinarith [p.1.2.1, p.1.2.2, (p.2 : XI).2.2.2]⟩,
    abs_shrink_le p.1.2 p.2.2.1, interp_le p.1.2 p.2.2.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    fun_prop

/-- `(t, (u, v, τ)) ↦ (u, (1 - t) v + t δ', (1 - t) τ - t)`, ending at `(u, δ', -1) ∈ E`. -/
noncomputable def homI2 (hδ' : 0 ≤ δ') : C(I × NI δ δ', NI δ δ') where
  toFun p := ⟨⟨(uI p.2, (1 - (p.1 : ℝ)) * vI p.2 + (p.1 : ℝ) * δ',
        (1 - (p.1 : ℝ)) * τI p.2 - p.1),
      interp_nonneg p.1.2 (p.2 : XI).2.1 hδ',
      by nlinarith [p.1.2.1, p.1.2.2, (p.2 : XI).2.2.1],
      by nlinarith [p.1.2.1, p.1.2.2, (p.2 : XI).2.2.2]⟩,
    p.2.2.1, interp_le p.1.2 p.2.2.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    fun_prop

theorem contractible_LI (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') :
    PointedContractible (IndexSpace (NI δ δ') (LI δ δ')) (IndexSpace.pt _ _) := by
  refine pointedContractible_of_deform (homI1 hδ') (fun x => ?_) (fun t x hx => ?_) (fun x => ?_)
  · refine Subtype.ext (XI_ext ?_ ?_ ?_)
    · show (1 - ((0 : I) : ℝ)) * uI x = uI x; simp
    · show (1 - ((0 : I) : ℝ)) * vI x + ((0 : I) : ℝ) * δ' = vI x; simp
    · show (1 - ((0 : I) : ℝ)) * τI x + ((0 : I) : ℝ) = τI x; simp
  · obtain ⟨-, hv, hτ⟩ := hx
    refine ⟨(homI1 hδ' (t, x)).2.1, ?_, ?_⟩
    · change (1 - (t : ℝ)) * vI x + t * δ' = δ'
      rw [show vI x = δ' from hv]; ring
    · change 0 ≤ (1 - (t : ℝ)) * τI x + t
      have hτ' : 0 ≤ τI x := hτ
      nlinarith [t.2.1, t.2.2]
  · show |(1 - ((1 : I) : ℝ)) * uI x| ≤ δ ∧ (1 - ((1 : I) : ℝ)) * vI x + ((1 : I) : ℝ) * δ' = δ' ∧
      0 ≤ (1 - ((1 : I) : ℝ)) * τI x + ((1 : I) : ℝ)
    simp [hδ]

theorem contractible_EI (hδ' : 0 ≤ δ') :
    PointedContractible (IndexSpace (NI δ δ') (EI δ δ')) (IndexSpace.pt _ _) := by
  refine pointedContractible_of_deform (homI2 hδ') (fun x => ?_) (fun t x hx => ?_) (fun x => ?_)
  · refine Subtype.ext (XI_ext rfl ?_ ?_)
    · show (1 - ((0 : I) : ℝ)) * vI x + ((0 : I) : ℝ) * δ' = vI x; simp
    · show (1 - ((0 : I) : ℝ)) * τI x - ((0 : I) : ℝ) = τI x; simp
  · obtain ⟨hu, hv, h⟩ := hx
    refine ⟨hu, (homI2 hδ' (t, x)).2.2, ?_⟩
    rcases h with h | ⟨hv', hτ⟩
    · exact Or.inl h
    · refine Or.inr ⟨?_, ?_⟩
      · change (1 - (t : ℝ)) * vI x + t * δ' = δ'
        rw [show vI x = δ' from hv']; ring
      · change (1 - (t : ℝ)) * τI x - t ≤ 0
        have hτ' : τI x ≤ 0 := hτ
        nlinarith [t.2.1, t.2.2]
  · show |uI x| ≤ δ ∧ (1 - ((1 : I) : ℝ)) * vI x + ((1 : I) : ℝ) * δ' ≤ δ' ∧
      (|uI x| = δ ∨ ((1 - ((1 : I) : ℝ)) * vI x + ((1 : I) : ℝ) * δ' = δ' ∧
        (1 - ((1 : I) : ℝ)) * τI x - ((1 : I) : ℝ) ≤ 0))
    refine ⟨x.2.1, by simp, Or.inr ⟨by simp, by simp⟩⟩

/-- Part (iii) of `lem:TC` in the chart `T = +∞`, for every flow on `XI` whose coordinates satisfy
`eq:flowTp` near `N^+`: `TC` has trivial index for the flow and for the reversed flow. -/
theorem lem_TC_iii_of (M : TCModel c XI) (hu : ∀ q, M.u q = uI q) (hv : ∀ q, M.v q = vI q)
    (hτ : ∀ q, M.τ q = τI q) (H : TCHyp c δ δ') :
    IndexTrivial M.ϕ M.TC ∧ IndexTrivial M.ϕ.reverse M.TC := by
  have hδ' : 0 ≤ δ' := (H.hδ.trans H.h1).le
  have hN : M.N δ δ' = NI δ δ' := by ext q; simp only [TCModel.N, NI, mem_setOf_eq, hu, hv]
  have hL : M.L δ δ' = LI δ δ' := by ext q; simp only [TCModel.L, LI, mem_setOf_eq, hu, hv, hτ]
  have hE : M.E δ δ' = EI δ δ' := by ext q; simp only [TCModel.E, EI, mem_setOf_eq, hu, hv, hτ]
  refine ⟨⟨NI δ δ', LI δ δ', ?_, contractible_LI H.hδ.le hδ'⟩,
    ⟨NI δ δ', EI δ δ', ?_, contractible_EI hδ'⟩⟩
  · rw [← hN, ← hL]; exact M.isIndexPair_L H
  · rw [← hN, ← hE]; exact M.isIndexPair_E H

/-- Part (iii) of `lem:TC` in the chart `T = +∞` for the cut-off interval flow. -/
theorem lem_TC_iii (H : TCHyp c δ δ') :
    IndexTrivial (ϕI c) (modelI c).TC ∧ IndexTrivial (ϕI c).reverse (modelI c).TC :=
  lem_TC_iii_of (modelI c) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) H

end PartIII

end ConleyCheck.Gubser
