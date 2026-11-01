import ConleyCheck.Gubser.Attractors
import ConleyCheck.Conley.FaceBlock
import ConleyCheck.Conley.Radial
import ConleyCheck.Conley.Duality
import ConleyCheck.Conley.Connecting

/-!
# The connecting orbit `Σ_U(A) → TC⁻`

* `subsingleton_CH3_univ`: `CH_3(Ω) = H_3(Ω) = 0`, since `Ω = HF × S¹` deforms onto the circle
  `{e₃} × S¹`.
* `hasIndex_SIA_reverse`: for the reversed flow, `N_A` is an isolating block all of whose faces are
  exit faces, and a chart identifies `(N_A, ∂N_A)` with `(D³, S²)`, so `h(Σ_I(A), -ϕ) = S³`. By the
  reversor, `CH_*(Σ_U(A)) = K[3]`.
* `exists_conn_SUA_TCm`: the attractor–repeller sequence of `(A₃, R₁)` in `Ω`, where `R₁` is the
  Morse set of `{TC⁻, Σ_U(A)}`, gives `CH_3(R₁) = 0` from `CH_3(Ω) = 0` and `CH_2(A₃) = 0`. The
  sequence of `(TC⁻, Σ_U(A))` in `R₁` then makes `CH_3(Σ_U(A)) → CH_2(TC⁻)` injective, hence
  nonzero, so there is an orbit from `Σ_U(A)` to `TC⁻`.
-/

open Set Metric CategoryTheory Limits unitInterval

namespace ConleyCheck.Conley

/-- In positive degrees reduced and unreduced singular homology agree. -/
theorem absH_subsingleton_of_redH (K : Type) [Ring K] {X : Type} [TopologicalSpace X] {x₀ : X}
    {n : ℕ} (hn : n ≠ 0) (h : Subsingleton (redH K X x₀ n)) : Subsingleton (absH K X n) := by
  have : Subsingleton (absH K PUnit.{1} n) := (ModuleCat.isZero_iff_subsingleton).1
    (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{0} K) n (ModuleCat.of K K) (TopCat.of PUnit.{1}) hn)
  let e := (ModuleCat.cokernelIsoRangeQuotient (hMap K (ptMap x₀) n)).toLinearEquiv
  refine ⟨fun x y => ?_⟩
  have hq : (Submodule.Quotient.mk x : _ ⧸ LinearMap.range (hMap K (ptMap x₀) n).hom) =
      Submodule.Quotient.mk y := e.symm.injective (Subsingleton.elim _ _)
  obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).1 hq
  rw [Subsingleton.elim z 0, map_zero] at hz
  exact (sub_eq_zero.1 hz.symm)

end ConleyCheck.Conley

namespace ConleyCheck.Gubser

open ConleyCheck.Conley

/-! ## `H_3(Ω) = 0` -/

section Circle

theorem nrm3_sq' {v : E3} (h : 0 < v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2) :
    (nrm3 v).1 ^ 2 + (nrm3 v).2.1 ^ 2 + (nrm3 v).2.2 ^ 2 = 1 := by
  simp only [nrm3, div_pow, Real.sq_sqrt h.le]
  rw [← add_div, ← add_div, div_self h.ne']

theorem continuous_nrm3' {Z : Type*} [TopologicalSpace Z] {f : Z → E3} (hf : Continuous f)
    (h : ∀ z, 0 < (f z).1 ^ 2 + (f z).2.1 ^ 2 + (f z).2.2 ^ 2) :
    Continuous fun z => nrm3 (f z) := by
  have hr : Continuous fun z => √((f z).1 ^ 2 + (f z).2.1 ^ 2 + (f z).2.2 ^ 2) := by fun_prop
  have hne : ∀ z, √((f z).1 ^ 2 + (f z).2.1 ^ 2 + (f z).2.2 ^ 2) ≠ 0 := fun z =>
    (Real.sqrt_pos.2 (h z)).ne'
  exact (hf.fst.div hr hne).prodMk ((hf.snd.fst.div hr hne).prodMk (hf.snd.snd.div hr hne))

/-- The segment from `e₃` to `y`. -/
def segE (t : ℝ) (q : OmG) : E3 := (t * gy1 q, t * gy2 q, t * gy3 q + (1 - t))

theorem segE_pos {t : ℝ} (ht : t ∈ I) (q : OmG) :
    0 < (segE t q).1 ^ 2 + (segE t q).2.1 ^ 2 + (segE t q).2.2 ^ 2 := by
  obtain ⟨h0, h1⟩ := ht
  have hs := sphere_G q
  have h3 := gy3_nonneg q
  have e : (segE t q).1 ^ 2 + (segE t q).2.1 ^ 2 + (segE t q).2.2 ^ 2 =
      t ^ 2 * (gy1 q ^ 2 + gy2 q ^ 2 + gy3 q ^ 2) + 2 * t * (1 - t) * gy3 q + (1 - t) ^ 2 := by
    simp only [segE]; ring
  rw [e, hs]
  nlinarith [mul_nonneg (mul_nonneg h0 (sub_nonneg.2 h1)) h3, sq_nonneg (2 * t - 1)]

theorem segE_mem {t : ℝ} (ht : t ∈ I) (q : OmG) : (nrm3 (segE t q), (q : EG).2) ∈ OmG := by
  refine ⟨⟨nrm3_sq' (segE_pos ht q), div_nonneg ?_ (Real.sqrt_nonneg _)⟩, q.2.2⟩
  change 0 ≤ t * gy3 q + (1 - t)
  have := gy3_nonneg q
  nlinarith [ht.1, ht.2]

/-- `Ω → S¹`, `(y, w) ↦ w`. -/
theorem toCirc_mem (q : OmG) : vec2 (gw1 q) (gw2 q) ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  rw [mem_sphere_zero_iff_norm]
  exact norm_eq_one_of_sq (by rw [norm_vec2_sq]; exact circle_G q)

/-- `Ω → S¹`, `(y, w) ↦ w`. -/
noncomputable def toCirc : C(OmG, Sphere 1) where
  toFun q := ⟨vec2 (gw1 q) (gw2 q), toCirc_mem q⟩
  continuous_toFun := (continuous_vec2 continuous_gw1 continuous_gw2).subtype_mk toCirc_mem

theorem sq_add_sq_of_sphere1 (v : Sphere 1) :
    (v : EuclideanSpace ℝ (Fin 2)) 0 ^ 2 + (v : EuclideanSpace ℝ (Fin 2)) 1 ^ 2 = 1 := by
  have h := norm_vec2_sq ((v : EuclideanSpace ℝ (Fin 2)) 0) ((v : EuclideanSpace ℝ (Fin 2)) 1)
  rw [← eq_vec2, mem_sphere_zero_iff_norm.1 v.2, one_pow] at h
  exact h.symm

/-- `S¹ → Ω`, `w ↦ (e₃, w)`. -/
noncomputable def ofCirc : C(Sphere 1, OmG) where
  toFun v := ⟨(((0 : ℝ), (0 : ℝ), (1 : ℝ)),
    ((v : EuclideanSpace ℝ (Fin 2)) 0, (v : EuclideanSpace ℝ (Fin 2)) 1)),
    ⟨⟨by norm_num, zero_le_one⟩, sq_add_sq_of_sphere1 v⟩⟩
  continuous_toFun := by
    have h0 : Continuous fun v : Sphere 1 => (v : EuclideanSpace ℝ (Fin 2)) 0 :=
      (PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val
    have h1 : Continuous fun v : Sphere 1 => (v : EuclideanSpace ℝ (Fin 2)) 1 :=
      (PiLp.continuous_apply 2 _ 1).comp continuous_subtype_val
    exact (continuous_const.prodMk (h0.prodMk h1)).subtype_mk _

/-- `Ω` deforms onto the circle `{e₃} × S¹`. -/
noncomputable def circHom : ContinuousMap.Homotopy (ofCirc.comp toCirc) (ContinuousMap.id OmG) where
  toFun p := ⟨(nrm3 (segE p.1 p.2), ((p.2 : OmG) : EG).2), segE_mem p.1.2 p.2⟩
  continuous_toFun := by
    have hq : Continuous fun p : I × OmG => p.2 := continuous_snd
    have ht : Continuous fun p : I × OmG => (p.1 : ℝ) := continuous_subtype_val.comp continuous_fst
    have hY : Continuous fun p : I × OmG => segE p.1 p.2 := by
      unfold segE
      exact (ht.mul (continuous_gy1.comp hq)).prodMk ((ht.mul (continuous_gy2.comp hq)).prodMk
        ((ht.mul (continuous_gy3.comp hq)).add (continuous_const.sub ht)))
    refine Continuous.subtype_mk ((continuous_nrm3' hY fun p => segE_pos p.1.2 p.2).prodMk ?_) _
    exact continuous_snd.comp (continuous_subtype_val.comp hq)
  map_zero_left q := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · change nrm3 (segE 0 q) = ((0 : ℝ), (0 : ℝ), (1 : ℝ))
      have e : segE 0 q = ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by simp [segE]
      rw [e, nrm3_of_sq (by norm_num)]
    · simp [ofCirc, toCirc, vec2, gw1, gw2]
  map_one_left q := by
    refine Subtype.ext (Prod.ext ?_ rfl)
    change nrm3 (segE 1 q) = (q : EG).1
    have e : segE 1 q = (gy1 q, gy2 q, gy3 q) := by simp [segE]
    rw [e, nrm3_of_sq (v := (gy1 q, gy2 q, gy3 q)) (sphere_G q)]
    rfl

theorem subsingleton_absH_OmG (K : Type) [Ring K] : Subsingleton (absH K OmG 3) := by
  have hS : Subsingleton (absH K (Sphere 1) 3) :=
    absH_subsingleton_of_redH K (x₀ := Sphere.pt 1) (by norm_num)
      ((sphere_homology K 1).2 3 (by norm_num))
  have hc : hMap K toCirc 3 ≫ hMap K ofCirc 3 = 𝟙 _ := by
    rw [← hMap_comp, hMap_congr K ⟨circHom⟩ 3, hMap_id]
  refine ⟨fun x y => ?_⟩
  have ex := congrArg (fun φ => φ.hom x) hc
  have ey := congrArg (fun φ => φ.hom y) hc
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply]
    at ex ey
  rw [← ex, ← ey, Subsingleton.elim ((hMap K toCirc 3).hom x) ((hMap K toCirc 3).hom y)]

/-- `CH_3(Ω) = H_3(Ω) = 0`. -/
theorem subsingleton_CH3_univ (K : Type) [Ring K] (c : ℝ) :
    Subsingleton (homologyIndex K (ϕG c) (isIsolated_univ (ϕ := ϕG c)) 3) := by
  obtain ⟨e⟩ := homologyIndex_univ K (ϕG c) 3
  have := subsingleton_absH_OmG K
  have hb := absToRel_bijective K (X := OmG) 3
  have : Subsingleton (singH K OmG (Int.ofNat 3) univ ∅) := ⟨fun x y => by
    obtain ⟨x', rfl⟩ := hb.2 x
    obtain ⟨y', rfl⟩ := hb.2 y
    rw [Subsingleton.elim x' y']⟩
  exact e.toEquiv.subsingleton

end Circle

/-! ## `h(Σ_I(A), -ϕ) = S³` -/

section Block

variable {c a : ℝ}

/-- The five faces of `N_A`, as functions `≤ 0` on `N_A`. -/
noncomputable def gA (c a : ℝ) : Fin 5 → OmG → ℝ :=
  ![fun q => 1 / 2 - gw1 q,
    fun q => 1 * gy1 q + 0 * gy2 q + -(a * c / 2) * gy3 q,
    fun q => -1 * gy1 q + 0 * gy2 q + -(a * c / 2) * gy3 q,
    fun q => 0 * gy1 q + 1 * gy2 q + -(3 * a / 2) * gy3 q,
    fun q => 0 * gy1 q + -1 * gy2 q + a / 2 * gy3 q]

/-- Their derivatives along `ϕG`. -/
noncomputable def dA (c a : ℝ) : Fin 5 → OmG → ℝ :=
  ![fun q => -(gy3 q * (1 - gw1 q ^ 2)),
    fun q => 1 * gP1 q + 0 * gP2 c q - gS c q * gA c a 1 q,
    fun q => -1 * gP1 q + 0 * gP2 c q - gS c q * gA c a 2 q,
    fun q => 0 * gP1 q + 1 * gP2 c q - gS c q * gA c a 3 q,
    fun q => 0 * gP1 q + -1 * gP2 c q - gS c q * gA c a 4 q]

theorem NA_eq : NA c a = {q | ∀ k, gA c a k q ≤ 0} := by
  ext q
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩ k
    fin_cases k
    · change 1 / 2 - gw1 q ≤ 0; linarith
    · change 1 * gy1 q + 0 * gy2 q + -(a * c / 2) * gy3 q ≤ 0; linarith
    · change -1 * gy1 q + 0 * gy2 q + -(a * c / 2) * gy3 q ≤ 0; linarith
    · change 0 * gy1 q + 1 * gy2 q + -(3 * a / 2) * gy3 q ≤ 0; linarith
    · change 0 * gy1 q + -1 * gy2 q + a / 2 * gy3 q ≤ 0; linarith
  · intro h
    have h0 : 1 / 2 - gw1 q ≤ 0 := h 0
    have h1 : 1 * gy1 q + 0 * gy2 q + -(a * c / 2) * gy3 q ≤ 0 := h 1
    have h2 : -1 * gy1 q + 0 * gy2 q + -(a * c / 2) * gy3 q ≤ 0 := h 2
    have h3 : 0 * gy1 q + 1 * gy2 q + -(3 * a / 2) * gy3 q ≤ 0 := h 3
    have h4 : 0 * gy1 q + -1 * gy2 q + a / 2 * gy3 q ≤ 0 := h 4
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem continuous_gA (k : Fin 5) : Continuous (gA c a k) := by
  have := continuous_gy1; have := continuous_gy2; have := continuous_gy3; have := continuous_gw1
  fin_cases k
  · exact continuous_const.sub continuous_gw1
  all_goals
    simp only [gA, Fin.reduceFinMk, Matrix.cons_val]
    fun_prop

theorem hasDerivAt_gA (k : Fin 5) (p : OmG) :
    HasDerivAt (fun s => gA c a k (ϕG c s p)) (dA c a k p) 0 := by
  fin_cases k
  · have h := hasDerivAt_gw1 c p 0
    simp only [Flow.map_zero_apply] at h
    exact h.const_sub (1 / 2)
  · have h := hasDerivAt_lin c p 1 0 (-(a * c / 2)) 0
    simp only [Flow.map_zero_apply] at h
    exact h
  · have h := hasDerivAt_lin c p (-1) 0 (-(a * c / 2)) 0
    simp only [Flow.map_zero_apply] at h
    exact h
  · have h := hasDerivAt_lin c p 0 1 (-(3 * a / 2)) 0
    simp only [Flow.map_zero_apply] at h
    exact h
  · have h := hasDerivAt_lin c p 0 (-1) (a / 2) 0
    simp only [Flow.map_zero_apply] at h
    exact h

theorem hasDerivAt_rev {f : OmG → ℝ} {p : OmG} {d : ℝ}
    (h : HasDerivAt (fun s => f (ϕG c s p)) d 0) :
    HasDerivAt (fun t => f ((ϕG c).reverse t p)) (-d) 0 := by
  have h' : HasDerivAt (fun s => f (ϕG c s p)) d (-0) := by rwa [neg_zero]
  exact (h'.comp 0 (hasDerivAt_neg 0)).congr_deriv (by ring)

/-- Every face of `N_A` is crossed strictly inward by `ϕG`. -/
theorem dA_neg (hc : 0 < c) (ha : a ^ 2 = 1 / 5) (ha0 : 0 < a) (k : Fin 5) {p : OmG}
    (hp : p ∈ NA c a) (hk : gA c a k p = 0) : dA c a k p < 0 := by
  have h3 := gy3_pos_of_NA hp
  obtain ⟨hτ, h1, h2, h3', h4⟩ := hp
  have hτ0 : 0 < gw1 p := by linarith
  have hac : 0 < a * c / 2 := by positivity
  have hu1 : gy1 p / c ≤ a / 2 * gy3 p := by rw [div_le_iff₀ hc]; nlinarith
  have hu2 : -(a / 2 * gy3 p) ≤ gy1 p / c := by rw [le_div_iff₀ hc]; nlinarith
  have hpos : 0 < a ^ 2 * gy3 p ^ 2 := by positivity
  have h5 : gy3 p ^ 2 / 5 = a ^ 2 * gy3 p ^ 2 := by rw [ha]; ring
  have hrw : ∀ y : ℝ, gy1 p * y / c = gy1 p / c * y := fun y => by ring
  fin_cases k
  · have hk' : 1 / 2 - gw1 p = 0 := hk
    have hw : gw1 p = 1 / 2 := by linarith
    change -(gy3 p * (1 - gw1 p ^ 2)) < 0
    rw [hw]
    nlinarith
  · have hk' : 1 * gy1 p + 0 * gy2 p + -(a * c / 2) * gy3 p = 0 := hk
    have hy : gy1 p = a * c / 2 * gy3 p := by linarith
    change 1 * gP1 p + 0 * gP2 c p - gS c p * gA c a 1 p < 0
    have h0 : gA c a 1 p = 0 := hk
    rw [h0, mul_zero, sub_zero]
    have : gw1 p * gy1 p * (gy2 p - 2 * gy3 p) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hτ0 (by rw [hy]; positivity)) (by nlinarith [a_lt_one ha ha0])
    rw [gP1_eq]; linarith
  · have hk' : -1 * gy1 p + 0 * gy2 p + -(a * c / 2) * gy3 p = 0 := hk
    have hy : gy1 p = -(a * c / 2 * gy3 p) := by linarith
    change -1 * gP1 p + 0 * gP2 c p - gS c p * gA c a 2 p < 0
    have h0 : gA c a 2 p = 0 := hk
    rw [h0, mul_zero, sub_zero]
    have : gw1 p * gy1 p * (gy2 p - 2 * gy3 p) > 0 :=
      mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hτ0 (by rw [hy]; nlinarith))
        (by nlinarith [a_lt_one ha ha0])
    rw [gP1_eq]; linarith
  · have hk' : 0 * gy1 p + 1 * gy2 p + -(3 * a / 2) * gy3 p = 0 := hk
    have hy : gy2 p = 3 * a / 2 * gy3 p := by linarith
    change 0 * gP1 p + 1 * gP2 c p - gS c p * gA c a 3 p < 0
    have h0 : gA c a 3 p = 0 := hk
    rw [h0, mul_zero, sub_zero]
    rw [gP2_eq, hrw, hy, h5]
    nlinarith [mul_nonneg (sub_nonneg.2 hτ) hpos.le,
      mul_nonneg (by linarith : 0 ≤ gy1 p / c + a / 2 * gy3 p) (mul_pos ha0 h3).le]
  · have hk' : 0 * gy1 p + -1 * gy2 p + a / 2 * gy3 p = 0 := hk
    have hy : gy2 p = a / 2 * gy3 p := by linarith
    change 0 * gP1 p + -1 * gP2 c p - gS c p * gA c a 4 p < 0
    have h0 : gA c a 4 p = 0 := hk
    rw [h0, mul_zero, sub_zero]
    rw [gP2_eq, hrw, hy, h5]
    nlinarith [mul_nonneg (sub_nonneg.2 hτ) hpos.le,
      mul_nonneg (by linarith : 0 ≤ a / 2 * gy3 p - gy1 p / c) (mul_pos ha0 h3).le]

/-- The exit set of `N_A` for the reversed flow: its boundary. -/
def LA (c a : ℝ) : Set OmG :=
  {p | (∀ k, gA c a k p ≤ 0) ∧ ∃ k ∈ (univ : Set (Fin 5)), gA c a k p = 0}

/-- For the reversed flow, `N_A` is an isolating block with exit set `∂N_A`. -/
theorem isIndexPair_NA_reverse (hc : 0 < c) (ha : a ^ 2 = 1 / 5) (ha0 : 0 < a) :
    IsIndexPair (ϕG c).reverse (SIA c a) (NA c a) (LA c a) := by
  have hB : IsBlock (ϕG c).reverse {p | ∀ k, gA c a k p ≤ 0} (LA c a) :=
    isBlock_of_faces (X := univ) (D := fun k p => -dA c a k p) continuous_gA
      (by rw [← NA_eq]; exact (isClosed_NA c a).isCompact)
      (fun k p _ => hasDerivAt_rev (hasDerivAt_gA k p))
      (fun k _ p hp hk => neg_pos.2 (dA_neg hc ha ha0 k (NA_eq ▸ hp) hk))
      (fun k hk => absurd (mem_univ k) hk)
  have hP := hB.isIndexPair
  rw [← NA_eq, Inv_reverse] at hP
  exact hP

/-! ### `(N_A, ∂N_A) ≅ (D³, S²)` -/

/-- The sup gauge on `ℝ³`. -/
noncomputable def ρA (v : EuclideanSpace ℝ (Fin 3)) : ℝ := max |v 0| (max |v 1| |v 2|)

theorem ρA_vec3 (u v w : ℝ) : ρA (vec3 u v w) = max |u| (max |v| |w|) := by simp [ρA, vec3]

theorem continuous_ρA : Continuous ρA := by
  have h : ∀ i : Fin 3, Continuous fun v : EuclideanSpace ℝ (Fin 3) => |v i| := fun i =>
    continuous_abs.comp (PiLp.continuous_apply 2 _ i)
  exact (h 0).max ((h 1).max (h 2))

theorem ρA_smul (t : ℝ) (ht : 0 ≤ t) (v : EuclideanSpace ℝ (Fin 3)) :
    ρA (t • v) = t * ρA v := by
  simp only [ρA, PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht]
  rw [mul_max_of_nonneg _ _ ht, mul_max_of_nonneg _ _ ht]

theorem abs_le_ρA (v : EuclideanSpace ℝ (Fin 3)) : |v 0| ≤ ρA v ∧ |v 1| ≤ ρA v ∧ |v 2| ≤ ρA v :=
  ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

theorem norm_le_ρA (v : EuclideanSpace ℝ (Fin 3)) : 1 / 3 * ‖v‖ ≤ ρA v := by
  have hn : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  obtain ⟨h0, h1, h2⟩ := abs_le_ρA v
  have hs : ‖v‖ ^ 2 ≤ (|v 0| + |v 1| + |v 2|) ^ 2 := by
    rw [hn]
    nlinarith [sq_abs (v 0), sq_abs (v 1), sq_abs (v 2),
      mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1)),
      mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 2)),
      mul_nonneg (abs_nonneg (v 1)) (abs_nonneg (v 2))]
  have := (pow_le_pow_iff_left₀ (norm_nonneg v) (by positivity) two_ne_zero).1 hs
  linarith

theorem max3_eq_one {x y z : ℝ} (hx : x ≤ 1) (hy : y ≤ 1) (hz : z ≤ 1) :
    max x (max y z) = 1 ↔ x = 1 ∨ y = 1 ∨ z = 1 := by
  constructor
  · intro h
    rcases hx.lt_or_eq with hx' | hx'
    · rcases hy.lt_or_eq with hy' | hy'
      · rcases hz.lt_or_eq with hz' | hz'
        · exact absurd h (ne_of_lt (max_lt hx' (max_lt hy' hz')))
        · exact Or.inr (Or.inr hz')
      · exact Or.inr (Or.inl hy')
    · exact Or.inl hx'
  · rintro (h | h | h)
    · exact le_antisymm (max_le hx (max_le hy hz)) (le_max_of_le_left h.ge)
    · exact le_antisymm (max_le hx (max_le hy hz)) (le_max_of_le_right (le_max_of_le_left h.ge))
    · exact le_antisymm (max_le hx (max_le hy hz)) (le_max_of_le_right (le_max_of_le_right h.ge))

/-- The cube `[-1, 1]³`. -/
def CubeA : Set (EuclideanSpace ℝ (Fin 3)) := {v | ρA v ≤ 1}

/-- The radial homeomorphism of the cube onto the ball. -/
noncomputable def cubeBall : CubeA ≃ₜ diskD 3 :=
  (radialHomeo continuous_ρA ρA_smul (by norm_num : (0 : ℝ) < 1 / 3) norm_le_ρA).subtype
    fun v => by
      rw [radialHomeo_apply]
      change ρA v ≤ 1 ↔ radialFun ρA v ∈ closedBall 0 1
      rw [mem_closedBall_zero_iff, norm_radialFun' ρA_smul (by norm_num : (0 : ℝ) < 1 / 3)
        norm_le_ρA]

theorem cubeBall_mem_diskS (v : CubeA) :
    (cubeBall v : EuclideanSpace ℝ (Fin 3)) ∈ diskS 3 ↔ ρA v = 1 := by
  change radialFun ρA v ∈ sphere 0 1 ↔ _
  rw [mem_sphere_zero_iff_norm, norm_radialFun' ρA_smul (by norm_num : (0 : ℝ) < 1 / 3)
    norm_le_ρA]

theorem hγ : (0 : ℝ) < √3 / 2 := by positivity

theorem hγ2 : (√3 / 2 : ℝ) ^ 2 = 3 / 4 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- The chart coordinates of `N_A`. -/
noncomputable def cU (c a : ℝ) (q : OmG) : ℝ := gy1 q / (a * c / 2 * gy3 q)
noncomputable def cV (a : ℝ) (q : OmG) : ℝ := (gy2 q - a * gy3 q) / (a / 2 * gy3 q)
noncomputable def cW (q : OmG) : ℝ := gw2 q / (√3 / 2)

theorem abs_cW_le_iff (q : OmG) : |cW q| ≤ 1 ↔ gw2 q ^ 2 ≤ 3 / 4 := by
  rw [cW, abs_div, abs_of_pos hγ, div_le_one hγ, ← sq_le_sq₀ (abs_nonneg _) hγ.le, sq_abs, hγ2]

theorem abs_cW_eq_iff (q : OmG) : |cW q| = 1 ↔ gw2 q ^ 2 = 3 / 4 := by
  rw [cW, abs_div, abs_of_pos hγ, div_eq_one_iff_eq hγ.ne', ← sq_eq_sq₀ (abs_nonneg _) hγ.le,
    sq_abs, hγ2]

theorem cube_bounds (hc : 0 < c) (ha0 : 0 < a) {q : OmG} (hq : q ∈ NA c a) :
    |cU c a q| ≤ 1 ∧ |cV a q| ≤ 1 ∧ |cW q| ≤ 1 := by
  have h3 := gy3_pos_of_NA hq
  obtain ⟨hτ, h1, h2, h3', h4⟩ := hq
  have hD : 0 < a * c / 2 * gy3 q := by positivity
  have hE : 0 < a / 2 * gy3 q := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [cU, abs_div, abs_of_pos hD, div_le_one hD]
    exact abs_le.2 ⟨by linarith, by linarith⟩
  · rw [cV, abs_div, abs_of_pos hE, div_le_one hE]
    exact abs_le.2 ⟨by linarith, by linarith⟩
  · rw [abs_cW_le_iff]
    nlinarith [circle_G q]

/-- On `N_A`, the boundary of the cube is the union of the faces. -/
theorem face_iff (hc : 0 < c) (ha0 : 0 < a) {q : OmG} (hq : q ∈ NA c a) :
    (|cU c a q| = 1 ∨ |cV a q| = 1 ∨ |cW q| = 1) ↔ q ∈ LA c a := by
  have h3 := gy3_pos_of_NA hq
  have hτ := hq.1
  have hD : 0 < a * c / 2 * gy3 q := by positivity
  have hE : 0 < a / 2 * gy3 q := by positivity
  have hg : ∀ k, gA c a k q ≤ 0 := by rw [NA_eq] at hq; exact hq
  have hw := circle_G q
  have e0 : gA c a 0 q = 1 / 2 - gw1 q := rfl
  have e1 : gA c a 1 q = 1 * gy1 q + 0 * gy2 q + -(a * c / 2) * gy3 q := rfl
  have e2 : gA c a 2 q = -1 * gy1 q + 0 * gy2 q + -(a * c / 2) * gy3 q := rfl
  have e3 : gA c a 3 q = 0 * gy1 q + 1 * gy2 q + -(3 * a / 2) * gy3 q := rfl
  have e4 : gA c a 4 q = 0 * gy1 q + -1 * gy2 q + a / 2 * gy3 q := rfl
  constructor
  · intro h
    refine ⟨hg, ?_⟩
    rcases h with h | h | h
    · rcases (abs_eq zero_le_one).1 h with h | h
      · rw [cU, div_eq_one_iff_eq hD.ne'] at h
        exact ⟨1, mem_univ _, by rw [e1]; linarith⟩
      · rw [cU, div_eq_iff hD.ne'] at h
        exact ⟨2, mem_univ _, by rw [e2]; linarith⟩
    · rcases (abs_eq zero_le_one).1 h with h | h
      · rw [cV, div_eq_one_iff_eq hE.ne'] at h
        exact ⟨3, mem_univ _, by rw [e3]; linarith⟩
      · rw [cV, div_eq_iff hE.ne'] at h
        exact ⟨4, mem_univ _, by rw [e4]; linarith⟩
    · rw [abs_cW_eq_iff] at h
      refine ⟨0, mem_univ _, ?_⟩
      rw [e0]
      nlinarith
  · rintro ⟨-, k, -, hk⟩
    fin_cases k
    · right; right
      have hk' : 1 / 2 - gw1 q = 0 := hk
      rw [abs_cW_eq_iff]
      have : gw1 q = 1 / 2 := by linarith
      rw [this] at hw
      linarith
    · left
      have hk' : 1 * gy1 q + 0 * gy2 q + -(a * c / 2) * gy3 q = 0 := hk
      rw [abs_eq zero_le_one, cU, div_eq_one_iff_eq hD.ne']
      left; linarith
    · left
      have hk' : -1 * gy1 q + 0 * gy2 q + -(a * c / 2) * gy3 q = 0 := hk
      rw [abs_eq zero_le_one, cU]
      right; rw [div_eq_iff hD.ne']; linarith
    · right; left
      have hk' : 0 * gy1 q + 1 * gy2 q + -(3 * a / 2) * gy3 q = 0 := hk
      rw [abs_eq zero_le_one, cV, div_eq_one_iff_eq hE.ne']
      left; linarith
    · right; left
      have hk' : 0 * gy1 q + -1 * gy2 q + a / 2 * gy3 q = 0 := hk
      rw [abs_eq zero_le_one, cV]
      right; rw [div_eq_iff hE.ne']; linarith

/-- The inverse chart. -/
noncomputable def chY (c a : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : E3 :=
  (a * c / 2 * v 0, a + a / 2 * v 1, 1)

noncomputable def chW (v : EuclideanSpace ℝ (Fin 3)) : ℝ × ℝ :=
  (√(1 - (√3 / 2 * v 2) ^ 2), √3 / 2 * v 2)

theorem invW_sq_le {v : EuclideanSpace ℝ (Fin 3)} (hv : v ∈ CubeA) :
    (√3 / 2 * v 2) ^ 2 ≤ 3 / 4 := by
  have h2 := (abs_le_ρA v).2.2.trans hv
  have : v 2 ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (v 2)]
  rw [mul_pow, hγ2]
  nlinarith

theorem invMem {v : EuclideanSpace ℝ (Fin 3)} (hv : v ∈ CubeA) :
    (nrm3 (chY c a v), chW v) ∈ OmG := by
  refine ⟨⟨nrm3_sq (v := chY c a v) one_pos, div_nonneg zero_le_one (Real.sqrt_nonneg _)⟩, ?_⟩
  change (√(1 - (√3 / 2 * v 2) ^ 2)) ^ 2 + (√3 / 2 * v 2) ^ 2 = 1
  rw [Real.sq_sqrt (by linarith [invW_sq_le hv])]
  ring

theorem lin_le_iff {Y : E3} {W : ℝ × ℝ} (h : (nrm3 Y, W) ∈ OmG) (hY : 0 < Y.2.2)
    (l₁ l₂ l₃ : ℝ) :
    l₁ * gy1 ⟨(nrm3 Y, W), h⟩ + l₂ * gy2 ⟨(nrm3 Y, W), h⟩ + l₃ * gy3 ⟨(nrm3 Y, W), h⟩ ≤ 0 ↔
      l₁ * Y.1 + l₂ * Y.2.1 + l₃ * Y.2.2 ≤ 0 := by
  have hr := nrm3_pos hY
  change l₁ * (Y.1 / √(Y.1 ^ 2 + Y.2.1 ^ 2 + Y.2.2 ^ 2)) +
    l₂ * (Y.2.1 / √(Y.1 ^ 2 + Y.2.1 ^ 2 + Y.2.2 ^ 2)) +
    l₃ * (Y.2.2 / √(Y.1 ^ 2 + Y.2.1 ^ 2 + Y.2.2 ^ 2)) ≤ 0 ↔ _
  rw [show ∀ r : ℝ, l₁ * (Y.1 / r) + l₂ * (Y.2.1 / r) + l₃ * (Y.2.2 / r) =
    (l₁ * Y.1 + l₂ * Y.2.1 + l₃ * Y.2.2) / r from fun r => by ring, div_le_iff₀ hr, zero_mul]

theorem invNA (hc : 0 < c) (ha0 : 0 < a) {v : EuclideanSpace ℝ (Fin 3)} (hv : v ∈ CubeA) :
    (⟨(nrm3 (chY c a v), chW v), invMem hv⟩ : OmG) ∈ NA c a := by
  obtain ⟨h0, h1, -⟩ := abs_le_ρA v
  have h0' := abs_le.1 (h0.trans hv)
  have h1' := abs_le.1 (h1.trans hv)
  have hac : 0 < a * c / 2 := by positivity
  have hY : 0 < (chY c a v).2.2 := one_pos
  have L := lin_le_iff (invMem (c := c) (a := a) hv) hY
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change 1 / 2 ≤ √(1 - (√3 / 2 * v 2) ^ 2)
    rw [show (1 / 2 : ℝ) = √((1 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith [invW_sq_le hv])
  · have := (L 1 0 (-(a * c / 2))).2 (by
      change 1 * (a * c / 2 * v 0) + 0 * (a + a / 2 * v 1) + -(a * c / 2) * 1 ≤ 0
      nlinarith)
    linarith
  · have := (L (-1) 0 (-(a * c / 2))).2 (by
      change -1 * (a * c / 2 * v 0) + 0 * (a + a / 2 * v 1) + -(a * c / 2) * 1 ≤ 0
      nlinarith)
    linarith
  · have := (L 0 1 (-(3 * a / 2))).2 (by
      change 0 * (a * c / 2 * v 0) + 1 * (a + a / 2 * v 1) + -(3 * a / 2) * 1 ≤ 0
      nlinarith)
    linarith
  · have := (L 0 (-1) (a / 2)).2 (by
      change 0 * (a * c / 2 * v 0) + -1 * (a + a / 2 * v 1) + a / 2 * 1 ≤ 0
      nlinarith)
    linarith

theorem nrm3_div {q : OmG} (h3 : 0 < gy3 q) :
    nrm3 (gy1 q / gy3 q, gy2 q / gy3 q, 1) = (q : EG).1 := by
  have hs := sphere_G q
  have hρ : √((gy1 q / gy3 q) ^ 2 + (gy2 q / gy3 q) ^ 2 + 1 ^ 2) = 1 / gy3 q := by
    rw [show (gy1 q / gy3 q) ^ 2 + (gy2 q / gy3 q) ^ 2 + 1 ^ 2 = (1 / gy3 q) ^ 2 by
      field_simp; linarith]
    exact Real.sqrt_sq (by positivity)
  simp only [nrm3, hρ]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change gy1 q / gy3 q / (1 / gy3 q) = gy1 q
    field_simp
  · change gy2 q / gy3 q / (1 / gy3 q) = gy2 q
    field_simp
  · change 1 / (1 / gy3 q) = gy3 q
    field_simp

/-- The chart `N_A ≃ [-1, 1]³`. -/
noncomputable def chartA (hc : 0 < c) (ha0 : 0 < a) : NA c a ≃ₜ CubeA where
  toFun q := ⟨vec3 (cU c a q) (cV a q) (cW q), by
    obtain ⟨b1, b2, b3⟩ := cube_bounds hc ha0 q.2
    change ρA _ ≤ 1
    rw [ρA_vec3]
    exact max_le b1 (max_le b2 b3)⟩
  invFun v := ⟨⟨(nrm3 (chY c a v), chW v), invMem v.2⟩, invNA hc ha0 v.2⟩
  left_inv q := by
    have h3 := gy3_pos_of_NA q.2
    have hτ := q.2.1
    have hY : chY c a (vec3 (cU c a q) (cV a q) (cW q)) = (gy1 q / gy3 q, gy2 q / gy3 q, 1) := by
      simp only [chY, vec3, cU, cV]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      refine Prod.ext ?_ (Prod.ext ?_ rfl)
      · change a * c / 2 * (gy1 q / (a * c / 2 * gy3 q)) = gy1 q / gy3 q
        field_simp
      · change a + a / 2 * ((gy2 q - a * gy3 q) / (a / 2 * gy3 q)) = gy2 q / gy3 q
        field_simp
        ring
    have hW : chW (vec3 (cU c a q) (cV a q) (cW q)) = (gw1 q, gw2 q) := by
      simp only [chW, vec3, cW]
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      have e : √3 / 2 * (gw2 q / (√3 / 2)) = gw2 q := mul_div_cancel₀ _ hγ.ne'
      rw [e, show 1 - gw2 q ^ 2 = gw1 q ^ 2 by linarith [circle_G q],
        Real.sqrt_sq (by linarith)]
    refine Subtype.ext (Subtype.ext ?_)
    change (nrm3 (chY c a (vec3 (cU c a q) (cV a q) (cW q))),
      chW (vec3 (cU c a q) (cV a q) (cW q))) = (q : EG)
    rw [hY, hW, nrm3_div h3]
    rfl
  right_inv v := by
    have hr := nrm3_pos (v := chY c a v) one_pos
    have hac : 0 < a * c / 2 := by positivity
    refine Subtype.ext ?_
    change vec3 (cU c a _) (cV a _) (cW _) = (v : EuclideanSpace ℝ (Fin 3))
    conv_rhs => rw [eq_vec3 (v : EuclideanSpace ℝ (Fin 3))]
    rw [vec3_eq_iff]
    set r := √((chY c a v).1 ^ 2 + (chY c a v).2.1 ^ 2 + (chY c a v).2.2 ^ 2)
    refine ⟨?_, ?_, ?_⟩
    · change a * c / 2 * (v : EuclideanSpace ℝ (Fin 3)) 0 / r / (a * c / 2 * (1 / r)) = _
      field_simp
    · change ((a + a / 2 * (v : EuclideanSpace ℝ (Fin 3)) 1) / r - a * (1 / r)) /
        (a / 2 * (1 / r)) = _
      field_simp
      ring
    · change √3 / 2 * (v : EuclideanSpace ℝ (Fin 3)) 2 / (√3 / 2) = _
      field_simp
  continuous_toFun := by
    have hq : Continuous fun q : NA c a => (q : OmG) := continuous_subtype_val
    have h3 : ∀ q : NA c a, gy3 q ≠ 0 := fun q => (gy3_pos_of_NA q.2).ne'
    have hac : 0 < a * c / 2 := by positivity
    refine Continuous.subtype_mk (continuous_vec3 ?_ ?_ ?_) _
    · exact (continuous_gy1.comp hq).div (continuous_const.mul (continuous_gy3.comp hq))
        fun q => mul_ne_zero hac.ne' (h3 q)
    · exact ((continuous_gy2.comp hq).sub (continuous_const.mul (continuous_gy3.comp hq))).div
        (continuous_const.mul (continuous_gy3.comp hq)) fun q => mul_ne_zero (by positivity) (h3 q)
    · exact (continuous_gw2.comp hq).div_const _
  continuous_invFun := by
    have hv : ∀ i : Fin 3, Continuous fun v : CubeA => (v : EuclideanSpace ℝ (Fin 3)) i :=
      fun i => (PiLp.continuous_apply 2 _ i).comp continuous_subtype_val
    have hY : Continuous fun v : CubeA => chY c a v :=
      (continuous_const.mul (hv 0)).prodMk
        ((continuous_const.add (continuous_const.mul (hv 1))).prodMk continuous_const)
    have hW : Continuous fun v : CubeA => chW v := by
      unfold chW
      exact (Real.continuous_sqrt.comp (continuous_const.sub
        ((continuous_const.mul (hv 2)).pow 2))).prodMk (continuous_const.mul (hv 2))
    exact Continuous.subtype_mk (Continuous.subtype_mk
      ((continuous_nrm3 hY fun _ => one_pos).prodMk hW) _) _

/-- `h(Σ_I(A)) = S³` for the reversed flow. -/
theorem hasIndex_SIA_reverse (hc : 0 < c) (ha : a ^ 2 = 1 / 5) (ha0 : 0 < a) :
    HasIndex (ϕG c).reverse (SIA c a) (Sphere 3) (Sphere.pt 3) := by
  refine ⟨NA c a, LA c a, isIndexPair_NA_reverse hc ha ha0,
    ⟨(IndexSpace.homeoEquiv ((chartA hc ha0).trans cubeBall) fun q => ?_).trans (diskEquiv 3)⟩⟩
  obtain ⟨b1, b2, b3⟩ := cube_bounds hc ha0 q.2
  rw [Homeomorph.trans_apply, cubeBall_mem_diskS, ← face_iff hc ha0 q.2]
  change ρA (vec3 (cU c a q) (cV a q) (cW q)) = 1 ↔ _
  rw [ρA_vec3, max3_eq_one b1 b2 b3]

end Block

/-! ## The connecting orbit -/

section Conn

variable {c a η δ : ℝ}

/-- `CH_*(Σ_U(A)) = K[3]` over any ring: the reversor carries `Σ_I(A)` with the reversed flow to
`Σ_U(A)`. -/
theorem homologyIndex_SUA (H : KHyp c a η δ) (K : Type) [Ring K]
    (hU : IsIsolatedInvariantSet (ϕG c) (revΩ ⁻¹' SIA c a)) :
    Nonempty (homologyIndex K (ϕG c) hU 3 ≃ₗ[K] K) ∧
      ∀ n, n ≠ 3 → Subsingleton (homologyIndex K (ϕG c) hU n) := by
  have hR := isReversor_revΩ c
  have hS : IsIsolatedInvariantSet (ϕG c) (SIA c a) := (thmM_morse H).isolated_M .A
  obtain ⟨⟨e0⟩, hz⟩ := (hasIndex_SIA_reverse H.hc H.ha H.ha0).homologyIndex_sphere K hS.reverse
  have iso : ∀ n, homologyIndex K (ϕG c) hU n ≃ₗ[K] homologyIndex K (ϕG c).reverse hS.reverse n :=
    fun n => (IsReversor.homologyIndex_set_congr (ψ := ϕG c) K
      (hR.image_eq_preimage (SIA c a)).symm hU (hR.isIsolated_image hS) n).some.trans
        (hR.homologyIndex_image K hS n).some
  refine ⟨⟨(iso 3).trans e0⟩, fun n hn => ?_⟩
  have := hz n hn
  exact (iso n).toEquiv.subsingleton

/-- The Morse sets below `Σ_U(A)`. -/
def P4 : Set GM := {.A, .Tp, .Bm, .Bp, .Tm}

theorem down_P4 : IsDown (fun i j : GM => i.rank < j.rank) P4 := fun i j hij hj => by
  cases i <;> cases j <;> simp_all [P4, GM.rank]

theorem down_univ : IsDown (fun i j : GM => i.rank < j.rank) univ := fun _ _ _ _ => trivial

/-- There is an orbit from `Σ_U(A)` to `TC⁻`. In the attractor–repeller sequence of `(A₃, R₁)` in
`Ω`, where `R₁` is the Morse set of `{TC⁻, Σ_U(A)}`, `CH_3(Ω) = 0` and `CH_2(A₃) = 0` give
`CH_3(R₁) = 0`. In the sequence of `(TC⁻, Σ_U(A))` in `R₁`, the connecting map
`CH_3(Σ_U(A)) = K → CH_2(TC⁻)` is therefore injective, hence nonzero. -/
theorem exists_conn_SUA_TCm (H : KHyp c a η δ) :
    ∃ x, x ∉ revΩ ⁻¹' SIA c a ∧ x ∉ revΩ ⁻¹' TCp ∧
      alphaLim (ϕG c) x ⊆ revΩ ⁻¹' SIA c a ∧ omegaLim (ϕG c) x ⊆ revΩ ⁻¹' TCp := by
  have h := thmM_morse H
  have p1 := h.isAttractorRepellerPair down_univ down_P3 (subset_univ P3)
  obtain ⟨-, q1, d1, -, ex1, -, -, -⟩ := homologyIndex_attractor_repeller_connecting ℚ p1
  have hU : Subsingleton (homologyIndex ℚ (ϕG c) p1.isolated 3) := by
    have := subsingleton_CH3_univ ℚ c
    obtain ⟨e⟩ := IsReversor.homologyIndex_set_congr (ψ := ϕG c) ℚ h.attr_univ p1.isolated
      (isIsolated_univ (ϕ := ϕG c)) 3
    exact e.toEquiv.subsingleton
  have hA : Subsingleton (homologyIndex ℚ (ϕG c) p1.isolated_A 2) :=
    (hasPointCircleIndex_A3 H ℚ).2.2 2 le_rfl
  have hR1 : ∀ z : homologyIndex ℚ (ϕG c) p1.isolated_R 3, z = 0 := fun z => by
    obtain ⟨y, hy⟩ := ((ex1 2) z).1 (Subsingleton.elim _ _)
    rw [← hy, Subsingleton.elim y 0, map_zero]
  have p2 := h.isAttractorRepellerPair_interval down_univ down_P4 down_P3
    (by simp [P3, P4, insert_subset_iff]) (subset_univ P4)
  obtain ⟨-, q2, d2, -, ex2, -, -, hconn⟩ := homologyIndex_attractor_repeller_connecting ℚ p2
  have eA := h.attr_inter_rep_eq down_P4 down_P3 (k := GM.Tm) (by simp [P4]) (by simp [P3])
    fun l hl hl0 => by simp [P3, P4] at hl hl0; tauto
  have eR := h.attr_inter_rep_eq down_univ down_P4 (k := GM.R) (mem_univ _) (by simp [P4])
    fun l _ hl0 => by cases l <;> simp [P4] at hl0 ⊢
  have hUR : IsIsolatedInvariantSet (ϕG c) (revΩ ⁻¹' SIA c a) := h.isolated_M .R
  have eR' : morseAttr (ϕG c) univ (MG c a η δ) univ ∩ morseRep (ϕG c) univ (MG c a η δ) P4ᶜ =
      revΩ ⁻¹' SIA c a := eR
  have hd : d2 2 ≠ 0 := by
    intro h0
    obtain ⟨e⟩ := IsReversor.homologyIndex_set_congr (ψ := ϕG c) ℚ eR' p2.isolated_R hUR 3
    obtain ⟨⟨e'⟩, -⟩ := homologyIndex_SUA H ℚ hUR
    have hz : e.symm (e'.symm 1) = 0 := by
      obtain ⟨y, hy⟩ := (ex2 2 (e.symm (e'.symm 1))).1 (by rw [h0, LinearMap.zero_apply])
      rw [← hy, hR1 y, map_zero]
    have h1 : e' (e (e.symm (e'.symm 1))) = 1 := by simp
    rw [hz, map_zero, map_zero] at h1
    exact zero_ne_one h1
  obtain ⟨x, -, hxA, hxR, hω, hα⟩ := hconn 2 hd
  rw [eA] at hxA hω
  rw [eR] at hxR hα
  exact ⟨x, hxR, hxA, hα, hω⟩

end Conn

end ConleyCheck.Gubser
