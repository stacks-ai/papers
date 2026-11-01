import ConleyCheck.Gubser.TCBlock
import ConleyCheck.ODE.Cutoff

/-!
# Global flows near the corner `TC` (`lem:TC`)

Two concrete models of the abstract `TCModel`.

* The circle model lives on `XS = {v ≥ 0, x² + y² = 1} ⊆ ℝ⁴`, coordinates `(u, v, x, y)`, with
  `τ = x`. The field is `(Fu, Fv, v y², -v x y)`, i.e. the angle `θ` with `τ = sin θ` is rotated
  at rate `v`, as in the extended phase space of `S̃`.
* The interval model lives on `XI = {v ≥ 0, -1 ≤ τ ≤ 1} ⊆ ℝ³`, with field `(Fu, Fv, v (1 - τ²))`.

In both cases the field is cut off outside a large ball, so the flows are global, and the cut-off
equals `1` wherever `|u|, v < 1/c`, so it is positive there, as required by `TCModel.b_pos`.
-/

open Set Filter Topology Metric
open ConleyCheck.ODE

namespace ConleyCheck.Gubser

section Components
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {γ : ℝ → F × G} {w : F × G} {t : ℝ}

theorem hasDerivAt_fst' (h : HasDerivAt γ w t) : HasDerivAt (fun s => (γ s).1) w.1 t := by
  have := (hasFDerivAt_fst (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t h
  exact this

theorem hasDerivAt_snd' (h : HasDerivAt γ w t) : HasDerivAt (fun s => (γ s).2) w.2 t := by
  have := (hasFDerivAt_snd (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t h
  exact this

end Components

theorem nonneg_of_linear_all {T k : ℝ → ℝ} (hT : ∀ s, HasDerivAt T (k s * T s) s)
    (hk : Continuous k) {s₀ : ℝ} (h0 : 0 ≤ T s₀) (s : ℝ) : 0 ≤ T s := by
  rcases h0.lt_or_eq with h | h
  · exact (pos_of_linear_all hT hk h s).le
  · exact (eq_zero_of_linear_all hT hk h.symm s).ge

/-- The cut-off radius. -/
noncomputable def radTC (c : ℝ) : ℝ := 2 + |1 / c|

theorem radTC_pos (c : ℝ) : 0 < radTC c := by unfold radTC; positivity

theorem lt_radTC_of_lt {c a : ℝ} (ha : a < 1 / c) : a < radTC c := by
  unfold radTC; linarith [le_abs_self (1 / c)]

theorem le_radTC_of_abs_le_one {c a : ℝ} (ha : |a| ≤ 1) : |a| ≤ radTC c := by
  unfold radTC; linarith [abs_nonneg (1 / c)]

/-! ## The circle model -/

/-- Coordinates `(u, v, x, y)`. -/
abbrev E4 := ℝ × ℝ × ℝ × ℝ

/-- The field `(Fu, Fv, v y², -v x y)` on `ℝ⁴`. -/
noncomputable def fieldS (c : ℝ) (p : E4) : E4 :=
  (Fu c p.1 p.2.1 p.2.2.1, Fv p.1 p.2.1 p.2.2.1, p.2.1 * p.2.2.2 ^ 2, -(p.2.1 * p.2.2.1 * p.2.2.2))

theorem contDiff_fieldS (c : ℝ) : ContDiff ℝ 1 (fieldS c) := by
  unfold fieldS Fu Fv; fun_prop

/-- The global flow of the cut-off circle field on `ℝ⁴`. -/
noncomputable def flowS (c : ℝ) : Flow ℝ E4 := bumpFlow (contDiff_fieldS c) (radTC c) (radTC_pos c)

/-- The cut-off of the circle model. -/
noncomputable def bS (c : ℝ) : E4 → ℝ := (bumpOf (E := E4) (radTC c) (radTC_pos c) : E4 → ℝ)

theorem continuous_bS (c : ℝ) : Continuous (bS c) := continuous_bumpOf

theorem hasDerivAt_flowS (c : ℝ) (p : E4) (t : ℝ) :
    HasDerivAt (fun s => flowS c s p) (bS c (flowS c t p) • fieldS c (flowS c t p)) t :=
  hasDerivAt_bumpFlow _ p t

/-- The extended phase space of the circle model. -/
def XS : Set E4 := {p | 0 ≤ p.2.1 ∧ p.2.2.1 ^ 2 + p.2.2.2 ^ 2 = 1}

theorem isClosed_XS : IsClosed XS :=
  (isClosed_le continuous_const (by fun_prop : Continuous fun p : E4 => p.2.1)).inter
    (isClosed_eq (by fun_prop : Continuous fun p : E4 => p.2.2.1 ^ 2 + p.2.2.2 ^ 2) continuous_const)

theorem isInvariant_XS (c : ℝ) : IsInvariant (flowS c) XS := by
  intro t p hp
  have hγ := hasDerivAt_flowS c p
  have hcγ : Continuous fun s => flowS c s p := (flowS c).continuous continuous_id continuous_const
  refine ⟨?_, ?_⟩
  · have hV : ∀ s, HasDerivAt (fun r => (flowS c r p).2.1)
        ((bS c (flowS c s p) * ((flowS c s p).2.2.1 / 3 * (2 * (flowS c s p).2.1 - (flowS c s p).1)))
          * (flowS c s p).2.1) s := by
      intro s
      convert hasDerivAt_fst' (hasDerivAt_snd' (hγ s)) using 1
      simp only [Prod.smul_fst, Prod.smul_snd, fieldS, Fv, smul_eq_mul]; ring
    have h0 : 0 ≤ (flowS c 0 p).2.1 := by rw [Flow.map_zero_apply]; exact hp.1
    exact nonneg_of_linear_all hV (((continuous_bS c).comp hcγ).mul (by fun_prop)) h0 t
  · have hW : ∀ s, HasDerivAt (fun r => (flowS c r p).2.2.1 ^ 2 + (flowS c r p).2.2.2 ^ 2) 0 s := by
      intro s
      have h1 := (hasDerivAt_fst' (hasDerivAt_snd' (hasDerivAt_snd' (hγ s)))).pow 2
      have h2 := (hasDerivAt_snd' (hasDerivAt_snd' (hasDerivAt_snd' (hγ s)))).pow 2
      convert h1.add h2 using 1
      simp only [Prod.smul_fst, Prod.smul_snd, fieldS, smul_eq_mul, Nat.cast_ofNat]; ring
    have := is_const_of_deriv_eq_zero (fun s => (hW s).differentiableAt) (fun s => (hW s).deriv) t 0
    simp only [Flow.map_zero_apply] at this
    rw [this]; exact hp.2

/-- The circle model flow on `XS`. -/
noncomputable def ϕS (c : ℝ) : Flow ℝ XS := (flowS c).restrict (isInvariant_XS c)

theorem norm_le_of_coords {p : E4} {R : ℝ} (h1 : |p.1| ≤ R) (h2 : |p.2.1| ≤ R) (h3 : |p.2.2.1| ≤ R)
    (h4 : |p.2.2.2| ≤ R) : ‖p‖ ≤ R :=
  norm_prod_le_iff.2 ⟨h1, norm_prod_le_iff.2 ⟨h2, norm_prod_le_iff.2 ⟨h3, h4⟩⟩⟩

theorem abs_le_one_of_sq_add {x y : ℝ} (h : x ^ 2 + y ^ 2 = 1) : |x| ≤ 1 :=
  abs_le.2 ⟨by nlinarith, by nlinarith⟩

theorem bS_eq_one {c : ℝ} (q : XS) (hu : |(q : E4).1| < 1 / c) (hv : (q : E4).2.1 < 1 / c) :
    bS c q = 1 := by
  have hv0 := q.2.1
  refine bumpOf_eq_one (norm_le_of_coords (lt_radTC_of_lt hu).le ?_
    (le_radTC_of_abs_le_one (abs_le_one_of_sq_add q.2.2)) (le_radTC_of_abs_le_one ?_))
  · rw [abs_of_nonneg hv0]; exact (lt_radTC_of_lt hv).le
  · exact abs_le_one_of_sq_add (by rw [add_comm]; exact q.2.2)

/-- The circle model as a `TCModel`. -/
noncomputable def modelS (c : ℝ) : TCModel c XS where
  ϕ := ϕS c
  u q := (q : E4).1
  v q := (q : E4).2.1
  τ q := (q : E4).2.2.1
  b q := bS c q
  cu := by fun_prop
  cv := by fun_prop
  cτ := by fun_prop
  cb := (continuous_bS c).comp continuous_subtype_val
  v_nonneg q := q.2.1
  τ_ge q := (abs_le.1 (abs_le_one_of_sq_add q.2.2)).1
  τ_le q := (abs_le.1 (abs_le_one_of_sq_add q.2.2)).2
  b_pos q hu hv := by rw [bS_eq_one q hu hv]; exact one_pos
  du q t _ _ := hasDerivAt_fst' (hasDerivAt_flowS c q t)
  dv q t _ _ := hasDerivAt_fst' (hasDerivAt_snd' (hasDerivAt_flowS c q t))
  tc_inv := tc_inv_of_global (ϕ := ϕS c) (u := fun q => (q : E4).1) (v := fun q => (q : E4).2.1)
    (τ := fun q => (q : E4).2.2.1) (b := fun q => bS c q) (by fun_prop) (by fun_prop) (by fun_prop)
    ((continuous_bS c).comp continuous_subtype_val)
    (fun q t => hasDerivAt_fst' (hasDerivAt_flowS c q t))
    (fun q t => hasDerivAt_fst' (hasDerivAt_snd' (hasDerivAt_flowS c q t)))
  dτ q t _ _ := by
    have hq := (ϕS c t q).2.2
    refine (hasDerivAt_fst' (hasDerivAt_snd' (hasDerivAt_snd' (hasDerivAt_flowS c q t)))).congr_deriv ?_
    change bS c (flowS c t q) * ((flowS c t q).2.1 * (flowS c t q).2.2.2 ^ 2) =
      bS c (flowS c t q) * ((flowS c t q).2.1 * (1 - (flowS c t q).2.2.1 ^ 2))
    change (flowS c t q).2.2.1 ^ 2 + (flowS c t q).2.2.2 ^ 2 = 1 at hq
    rw [show 1 - (flowS c t q).2.2.1 ^ 2 = (flowS c t q).2.2.2 ^ 2 by linarith]
  compact a a' := by
    let K : Set E4 := {p | |p.1| ≤ a} ∩ {p | p.2.1 ≤ a'}
    change IsCompact (Subtype.val ⁻¹' K)
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe]
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_XS.inter
      ((isClosed_le (by fun_prop : Continuous fun p : E4 => |p.1|) continuous_const).inter
        (isClosed_le (by fun_prop : Continuous fun p : E4 => p.2.1) continuous_const))) ?_
    refine (Metric.isBounded_closedBall (x := (0 : E4)) (r := |a| + |a'| + 1)).subset ?_
    rintro p ⟨⟨hv, hxy⟩, (hu : |p.1| ≤ a), (hv' : p.2.1 ≤ a')⟩
    rw [mem_closedBall_zero_iff]
    refine norm_le_of_coords ?_ ?_ ?_ ?_
    · linarith [le_abs_self a, abs_nonneg a']
    · rw [abs_of_nonneg hv]; linarith [le_abs_self a', abs_nonneg a]
    · linarith [abs_le_one_of_sq_add hxy, abs_nonneg a, abs_nonneg a']
    · linarith [abs_le_one_of_sq_add (by rw [add_comm]; exact hxy), abs_nonneg a, abs_nonneg a']

/-! ## The interval model -/

/-- Coordinates `(u, v, τ)`. -/
abbrev E3 := ℝ × ℝ × ℝ

/-- The field `(Fu, Fv, v (1 - τ²))` on `ℝ³`. -/
noncomputable def fieldI (c : ℝ) (p : E3) : E3 :=
  (Fu c p.1 p.2.1 p.2.2, Fv p.1 p.2.1 p.2.2, p.2.1 * (1 - p.2.2 ^ 2))

theorem contDiff_fieldI (c : ℝ) : ContDiff ℝ 1 (fieldI c) := by
  unfold fieldI Fu Fv; fun_prop

/-- The global flow of the cut-off interval field on `ℝ³`. -/
noncomputable def flowI (c : ℝ) : Flow ℝ E3 := bumpFlow (contDiff_fieldI c) (radTC c) (radTC_pos c)

/-- The cut-off of the interval model. -/
noncomputable def bI (c : ℝ) : E3 → ℝ := (bumpOf (E := E3) (radTC c) (radTC_pos c) : E3 → ℝ)

theorem continuous_bI (c : ℝ) : Continuous (bI c) := continuous_bumpOf

theorem hasDerivAt_flowI (c : ℝ) (p : E3) (t : ℝ) :
    HasDerivAt (fun s => flowI c s p) (bI c (flowI c t p) • fieldI c (flowI c t p)) t :=
  hasDerivAt_bumpFlow _ p t

/-- The extended phase space of the interval model. -/
def XI : Set E3 := {p | 0 ≤ p.2.1 ∧ -1 ≤ p.2.2 ∧ p.2.2 ≤ 1}

theorem isClosed_XI : IsClosed XI :=
  (isClosed_le continuous_const (by fun_prop : Continuous fun p : E3 => p.2.1)).inter
    ((isClosed_le continuous_const (by fun_prop : Continuous fun p : E3 => p.2.2)).inter
      (isClosed_le (by fun_prop : Continuous fun p : E3 => p.2.2) continuous_const))

theorem isInvariant_XI (c : ℝ) : IsInvariant (flowI c) XI := by
  intro t p hp
  have hγ := hasDerivAt_flowI c p
  have hcγ : Continuous fun s => flowI c s p := (flowI c).continuous continuous_id continuous_const
  have hb := (continuous_bI c).comp hcγ
  refine ⟨?_, ?_, ?_⟩
  · have hV : ∀ s, HasDerivAt (fun r => (flowI c r p).2.1)
        ((bI c (flowI c s p) * ((flowI c s p).2.2 / 3 * (2 * (flowI c s p).2.1 - (flowI c s p).1)))
          * (flowI c s p).2.1) s := by
      intro s
      convert hasDerivAt_fst' (hasDerivAt_snd' (hγ s)) using 1
      simp only [Prod.smul_fst, Prod.smul_snd, fieldI, Fv, smul_eq_mul]; ring
    have h0 : 0 ≤ (flowI c 0 p).2.1 := by rw [Flow.map_zero_apply]; exact hp.1
    exact nonneg_of_linear_all hV (hb.mul (by fun_prop)) h0 t
  · have hV : ∀ s, HasDerivAt (fun r => 1 + (flowI c r p).2.2)
        ((bI c (flowI c s p) * ((flowI c s p).2.1 * (1 - (flowI c s p).2.2)))
          * (1 + (flowI c s p).2.2)) s := by
      intro s
      refine ((hasDerivAt_snd' (hasDerivAt_snd' (hγ s))).const_add 1).congr_deriv ?_
      simp only [Prod.smul_snd, fieldI, smul_eq_mul]; ring
    have h0 : 0 ≤ 1 + (flowI c 0 p).2.2 := by rw [Flow.map_zero_apply]; linarith [hp.2.1]
    have := nonneg_of_linear_all hV (hb.mul (by fun_prop)) h0 t
    linarith
  · have hV : ∀ s, HasDerivAt (fun r => 1 - (flowI c r p).2.2)
        ((-(bI c (flowI c s p) * ((flowI c s p).2.1 * (1 + (flowI c s p).2.2))))
          * (1 - (flowI c s p).2.2)) s := by
      intro s
      refine ((hasDerivAt_snd' (hasDerivAt_snd' (hγ s))).const_sub 1).congr_deriv ?_
      simp only [Prod.smul_snd, fieldI, smul_eq_mul]; ring
    have h0 : 0 ≤ 1 - (flowI c 0 p).2.2 := by rw [Flow.map_zero_apply]; linarith [hp.2.2]
    have := nonneg_of_linear_all hV (hb.mul (by fun_prop)).neg h0 t
    linarith

/-- The interval model flow on `XI`. -/
noncomputable def ϕI (c : ℝ) : Flow ℝ XI := (flowI c).restrict (isInvariant_XI c)

theorem norm_le_of_coords3 {p : E3} {R : ℝ} (h1 : |p.1| ≤ R) (h2 : |p.2.1| ≤ R)
    (h3 : |p.2.2| ≤ R) : ‖p‖ ≤ R :=
  norm_prod_le_iff.2 ⟨h1, norm_prod_le_iff.2 ⟨h2, h3⟩⟩

theorem bI_eq_one {c : ℝ} (q : XI) (hu : |(q : E3).1| < 1 / c) (hv : (q : E3).2.1 < 1 / c) :
    bI c q = 1 := by
  have hv0 := q.2.1
  refine bumpOf_eq_one (norm_le_of_coords3 (lt_radTC_of_lt hu).le ?_
    (le_radTC_of_abs_le_one (abs_le.2 q.2.2)))
  rw [abs_of_nonneg hv0]; exact (lt_radTC_of_lt hv).le

/-- The interval model as a `TCModel`. -/
noncomputable def modelI (c : ℝ) : TCModel c XI where
  ϕ := ϕI c
  u q := (q : E3).1
  v q := (q : E3).2.1
  τ q := (q : E3).2.2
  b q := bI c q
  cu := by fun_prop
  cv := by fun_prop
  cτ := by fun_prop
  cb := (continuous_bI c).comp continuous_subtype_val
  v_nonneg q := q.2.1
  τ_ge q := q.2.2.1
  τ_le q := q.2.2.2
  b_pos q hu hv := by rw [bI_eq_one q hu hv]; exact one_pos
  du q t _ _ := hasDerivAt_fst' (hasDerivAt_flowI c q t)
  dv q t _ _ := hasDerivAt_fst' (hasDerivAt_snd' (hasDerivAt_flowI c q t))
  dτ q t _ _ := hasDerivAt_snd' (hasDerivAt_snd' (hasDerivAt_flowI c q t))
  tc_inv := tc_inv_of_global (ϕ := ϕI c) (u := fun q => (q : E3).1) (v := fun q => (q : E3).2.1)
    (τ := fun q => (q : E3).2.2) (b := fun q => bI c q) (by fun_prop) (by fun_prop) (by fun_prop)
    ((continuous_bI c).comp continuous_subtype_val)
    (fun q t => hasDerivAt_fst' (hasDerivAt_flowI c q t))
    (fun q t => hasDerivAt_fst' (hasDerivAt_snd' (hasDerivAt_flowI c q t)))
  compact a a' := by
    let K : Set E3 := {p | |p.1| ≤ a} ∩ {p | p.2.1 ≤ a'}
    change IsCompact (Subtype.val ⁻¹' K)
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe]
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_XI.inter
      ((isClosed_le (by fun_prop : Continuous fun p : E3 => |p.1|) continuous_const).inter
        (isClosed_le (by fun_prop : Continuous fun p : E3 => p.2.1) continuous_const))) ?_
    refine (Metric.isBounded_closedBall (x := (0 : E3)) (r := |a| + |a'| + 1)).subset ?_
    rintro p ⟨⟨hv, hτ1, hτ2⟩, (hu : |p.1| ≤ a), (hv' : p.2.1 ≤ a')⟩
    rw [mem_closedBall_zero_iff]
    refine norm_le_of_coords3 ?_ ?_ ?_
    · linarith [le_abs_self a, abs_nonneg a']
    · rw [abs_of_nonneg hv]; linarith [le_abs_self a', abs_nonneg a]
    · linarith [abs_le.2 ⟨hτ1, hτ2⟩, abs_nonneg a, abs_nonneg a']

end ConleyCheck.Gubser
