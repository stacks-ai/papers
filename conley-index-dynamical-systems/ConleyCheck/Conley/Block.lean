import ConleyCheck.Conley.Existence

/-!
# Isolating blocks for nonlinear saddles

Let `ψ` be a flow on `V₁ × V₂` with generator `F`, with `F z = (B₁ z₁, B₂ z₂) + o(‖z‖)` at the
fixed point `0`. Given quadratic forms `q₁ = ⟪·, P₁ ·⟫`, `q₂ = ⟪·, P₂ ·⟫` that increase along `B₁`
and decrease along `B₂` (`ConleyCheck.Conley.exists_lyapunov`), the product of small ellipsoids
`{q₁ ≤ δ², q₂ ≤ δ²}` with exit set `{q₁ = δ²}` is an index pair for `{0}` (`exists_block`).
-/

namespace ConleyCheck.Conley

open Set Filter Topology
open scoped RealInnerProductSpace

/-! ### One-variable calculus -/

theorem eventually_lt_of_hasDerivAt_neg {q : ℝ → ℝ} {q' t₀ : ℝ} (h : HasDerivAt q q' t₀)
    (hq : q' < 0) : ∀ᶠ s in 𝓝[>] t₀, q s < q t₀ := by
  have h1 := (hasDerivAt_iff_tendsto_slope.1 h).mono_left
    (nhdsWithin_mono _ fun s (hs : t₀ < s) => hs.ne')
  filter_upwards [h1.eventually (Iio_mem_nhds hq), self_mem_nhdsWithin] with s hs hs'
  rw [slope_def_field] at hs
  have hpos : 0 < s - t₀ := sub_pos.2 hs'
  have := mul_neg_of_neg_of_pos hs hpos
  rw [div_mul_cancel₀ _ hpos.ne'] at this
  linarith

theorem exists_gt_of_hasDerivAt_pos {q : ℝ → ℝ} {q' t₀ : ℝ} (h : HasDerivAt q q' t₀)
    (hq : 0 < q') {t : ℝ} (ht : t₀ < t) : ∃ s ∈ Ioc t₀ t, q t₀ < q s := by
  have h' := eventually_lt_of_hasDerivAt_neg h.neg (neg_lt_zero.2 hq)
  obtain ⟨s, hs, hs'⟩ := (h'.and (Ioo_mem_nhdsGT ht)).exists
  exact ⟨s, Ioo_subset_Ioc_self hs', by simpa using hs⟩

theorem growth_of_deriv_ge {v v' : ℝ → ℝ} (hv : ∀ s, HasDerivAt v (v' s) s) {a b c : ℝ}
    (hab : a ≤ b) (h : ∀ s ∈ Ioo a b, c ≤ v' s) : c * (b - a) ≤ v b - v a := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  · obtain ⟨d, hd, hd'⟩ := exists_hasDerivAt_eq_slope (f := v) (f' := v') hab
      (fun s _ => (hv s).continuousAt.continuousWithinAt) (fun s _ => hv s)
    have := h d hd
    rw [hd', le_div_iff₀ (sub_pos.2 hab)] at this
    exact this

/-! ### Quadratic forms -/

section Quadratic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The quadratic form `a ↦ ⟪a, P a⟫`. -/
def qf (P : V →L[ℝ] V) (a : V) : ℝ := ⟪a, P a⟫

/-- Its derivative at `a` in direction `w`. -/
def dq (P : V →L[ℝ] V) (a w : V) : ℝ := ⟪a, P w⟫ + ⟪w, P a⟫

theorem continuous_qf (P : V →L[ℝ] V) : Continuous (qf P) :=
  continuous_id.inner P.continuous

theorem qf_zero (P : V →L[ℝ] V) : qf P 0 = 0 := by simp [qf]

theorem qf_le (P : V →L[ℝ] V) (a : V) : qf P a ≤ ‖P‖ * ‖a‖ ^ 2 := by
  have h1 := real_inner_le_norm a (P a)
  have h2 := mul_le_mul_of_nonneg_left (P.le_opNorm a) (norm_nonneg a)
  unfold qf
  nlinarith

theorem hasDerivAt_qf (P : V →L[ℝ] V) {a : ℝ → V} {a' : V} {s : ℝ} (ha : HasDerivAt a a' s) :
    HasDerivAt (fun s => qf P (a s)) (dq P (a s) a') s :=
  ha.inner ℝ (P.hasFDerivAt.comp_hasDerivAt s ha)

theorem dq_add (P : V →L[ℝ] V) (a w₁ w₂ : V) : dq P a (w₁ + w₂) = dq P a w₁ + dq P a w₂ := by
  simp only [dq, map_add, inner_add_left, inner_add_right]; ring

theorem abs_dq_le (P : V →L[ℝ] V) (a w : V) : |dq P a w| ≤ 2 * ‖P‖ * ‖a‖ * ‖w‖ := by
  have h1 := abs_real_inner_le_norm a (P w)
  have h2 := abs_real_inner_le_norm w (P a)
  have h3 := mul_le_mul_of_nonneg_left (P.le_opNorm w) (norm_nonneg a)
  have h4 := mul_le_mul_of_nonneg_left (P.le_opNorm a) (norm_nonneg w)
  calc |dq P a w| ≤ |⟪a, P w⟫| + |⟪w, P a⟫| := abs_add_le _ _
    _ ≤ ‖a‖ * (‖P‖ * ‖w‖) + ‖w‖ * (‖P‖ * ‖a‖) := add_le_add (h1.trans h3) (h2.trans h4)
    _ = 2 * ‖P‖ * ‖a‖ * ‖w‖ := by ring

theorem dq_ge (P : V →L[ℝ] V) (a v w : V) : dq P a v - 2 * ‖P‖ * ‖a‖ * ‖w - v‖ ≤ dq P a w := by
  have e : w = v + (w - v) := by abel
  have h := abs_dq_le P a (w - v)
  rw [e, dq_add]
  simp only [add_sub_cancel_left]
  linarith [neg_abs_le (dq P a (w - v))]

theorem dq_le (P : V →L[ℝ] V) (a v w : V) : dq P a w ≤ dq P a v + 2 * ‖P‖ * ‖a‖ * ‖w - v‖ := by
  have e : w = v + (w - v) := by abel
  have h := abs_dq_le P a (w - v)
  rw [e, dq_add]
  simp only [add_sub_cancel_left]
  linarith [le_abs_self (dq P a (w - v))]

end Quadratic

/-! ### Elementary inequalities -/

theorem face_aux {K ε τ x y w : ℝ} (hK : 0 < K) (hτ : 0 < τ)
    (hε : ε = 1 / (16 * K * (K / τ + 1))) (hw0 : 0 ≤ w) (hy : 0 ≤ y)
    (h1 : w ^ 2 ≤ x ^ 2 + y ^ 2) (h2 : τ * x ^ 2 ≤ K * y ^ 2) :
    2 * K * ε * y * w ≤ 1 / 4 * y ^ 2 := by
  have hKτ : 0 < K / τ := div_pos hK hτ
  have hx : x ^ 2 ≤ K / τ * y ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hτ]; linarith
  have hw : w ^ 2 ≤ (K / τ + 1) * y ^ 2 := by nlinarith
  have h8 : 8 * K * ε = 1 / (2 * (K / τ + 1)) := by
    rw [hε]; field_simp; ring
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hkey : 8 * K * ε * w ≤ y := by
    have hpos : 0 ≤ 8 * K * ε * w := by positivity
    refine (pow_le_pow_iff_left₀ hpos hy two_ne_zero).1 ?_
    rw [h8, div_mul_eq_mul_div, one_mul, div_pow, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg y]
  nlinarith [mul_le_mul_of_nonneg_left hkey hy]

theorem iso_aux {K ε x y w : ℝ} (hK : 0 < K) (hε0 : 0 ≤ ε) (hε : 4 * K * ε ≤ 1 / 4)
    (hx0 : 0 ≤ x) (_hy0 : 0 ≤ y) (hx : x ≤ w) (hy : y ≤ w) (h1 : w ^ 2 ≤ x ^ 2 + y ^ 2) :
    1 / 4 * w ^ 2 ≤ (1 / 2 * x ^ 2 - 2 * K * ε * x * w) - (-(1 / 2) * y ^ 2 + 2 * K * ε * y * w) := by
  have hw0 : 0 ≤ w := hx0.trans hx
  have h2 : 2 * K * ε * (x + y) * w ≤ 4 * K * ε * w ^ 2 := by
    have : 0 ≤ 2 * K * ε := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hx hy) (mul_nonneg this hw0)]
  nlinarith [mul_le_mul_of_nonneg_right hε (sq_nonneg w)]

/-! ### The block -/

section Block

variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]

/-- The product of ellipsoids `{q₁ ≤ δ²} × {q₂ ≤ δ²}`. -/
def blockN (P₁ : V₁ →L[ℝ] V₁) (P₂ : V₂ →L[ℝ] V₂) (δ : ℝ) : Set (V₁ × V₂) :=
  {z | qf P₁ z.1 ≤ δ ^ 2 ∧ qf P₂ z.2 ≤ δ ^ 2}

/-- Its unstable boundary `{q₁ = δ²} × {q₂ ≤ δ²}`. -/
def blockL (P₁ : V₁ →L[ℝ] V₁) (P₂ : V₂ →L[ℝ] V₂) (δ : ℝ) : Set (V₁ × V₂) :=
  {z | qf P₁ z.1 = δ ^ 2 ∧ qf P₂ z.2 ≤ δ ^ 2}

omit [InnerProductSpace ℝ V₁] [InnerProductSpace ℝ V₂] in
theorem norm_prod_sq_le (z : V₁ × V₂) : ‖z‖ ^ 2 ≤ ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  rw [Prod.norm_def]
  rcases le_total ‖z.1‖ ‖z.2‖ with h | h
  · rw [max_eq_right h]; nlinarith [sq_nonneg ‖z.1‖]
  · rw [max_eq_left h]; nlinarith [sq_nonneg ‖z.2‖]

variable [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]

theorem exists_block {ψ : Flow ℝ (V₁ × V₂)} {F : V₁ × V₂ → V₁ × V₂}
    (hgen : ∀ z t, HasDerivAt (fun s => ψ s z) (F (ψ t z)) t) (hfix : ∀ t, ψ t 0 = 0)
    {B₁ : V₁ →L[ℝ] V₁} {B₂ : V₂ →L[ℝ] V₂}
    (hsmall : ∀ ε > 0, ∀ᶠ z in 𝓝 (0 : V₁ × V₂),
      ‖(F z).1 - B₁ z.1‖ ≤ ε * ‖z‖ ∧ ‖(F z).2 - B₂ z.2‖ ≤ ε * ‖z‖)
    {P₁ : V₁ →L[ℝ] V₁} {P₂ : V₂ →L[ℝ] V₂} {τ₁ τ₂ : ℝ} (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂)
    (hP₁ : ∀ a, τ₁ * ‖a‖ ^ 2 ≤ qf P₁ a ∧ 1 / 2 * ‖a‖ ^ 2 ≤ dq P₁ a (B₁ a))
    (hP₂ : ∀ b, τ₂ * ‖b‖ ^ 2 ≤ qf P₂ b ∧ dq P₂ b (B₂ b) ≤ -(1 / 2) * ‖b‖ ^ 2) :
    ∃ δ > 0, IsIndexPair ψ {0} (blockN P₁ P₂ δ) (blockL P₁ P₂ δ) := by
  set K := ‖P₁‖ + ‖P₂‖ + 1 with hKdef
  have hK : 0 < K := by positivity
  have hK₁ : ‖P₁‖ ≤ K := by linarith [norm_nonneg P₂]
  have hK₂ : ‖P₂‖ ≤ K := by linarith [norm_nonneg P₁]
  set τ := min τ₁ τ₂ with hτdef
  have hτ : 0 < τ := lt_min hτ₁ hτ₂
  set ε := 1 / (16 * K * (K / τ + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hε4 : 4 * K * ε ≤ 1 / 4 := by
    rw [hεdef, mul_one_div, div_le_iff₀ (by positivity)]
    have : 0 < K / τ := div_pos hK hτ
    nlinarith
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (hsmall ε hε)
  set δ := Real.sqrt τ * r / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hδsq : δ ^ 2 = τ * r ^ 2 / 4 := by
    rw [hδdef, div_pow, mul_pow, Real.sq_sqrt hτ.le]; ring
  refine ⟨δ, hδ, ?_⟩
  set N := blockN P₁ P₂ δ with hNdef
  set L := blockL P₁ P₂ δ with hLdef
  -- basic bounds on `N`
  have hq₁0 : ∀ a, 0 ≤ qf P₁ a := fun a => le_trans (by positivity) (hP₁ a).1
  have hq₂0 : ∀ b, 0 ≤ qf P₂ b := fun b => le_trans (by positivity) (hP₂ b).1
  have hsmallN : ∀ z ∈ N, ‖z.1‖ ≤ r / 2 ∧ ‖z.2‖ ≤ r / 2 := by
    intro z hz
    have h1 : τ * ‖z.1‖ ^ 2 ≤ τ * r ^ 2 / 4 :=
      ((mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans (hP₁ z.1).1).trans
        (hδsq ▸ hz.1)
    have h2 : τ * ‖z.2‖ ^ 2 ≤ τ * r ^ 2 / 4 :=
      ((mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans (hP₂ z.2).1).trans
        (hδsq ▸ hz.2)
    have h1' : ‖z.1‖ ^ 2 ≤ (r / 2) ^ 2 := by nlinarith
    have h2' : ‖z.2‖ ^ 2 ≤ (r / 2) ^ 2 := by nlinarith
    exact ⟨(pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1',
      (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2'⟩
  have hnormN : ∀ z ∈ N, ‖z‖ < r := by
    intro z hz
    obtain ⟨h1, h2⟩ := hsmallN z hz
    rw [Prod.norm_def]
    exact max_lt (by linarith) (by linarith)
  have hF : ∀ z ∈ N, ‖(F z).1 - B₁ z.1‖ ≤ ε * ‖z‖ ∧ ‖(F z).2 - B₂ z.2‖ ≤ ε * ‖z‖ :=
    fun z hz => hball (by simpa [dist_zero_right] using hnormN z hz)
  -- pointwise derivative bounds on `N`
  have hD₁ : ∀ z ∈ N, 1 / 2 * ‖z.1‖ ^ 2 - 2 * K * ε * ‖z.1‖ * ‖z‖ ≤ dq P₁ z.1 (F z).1 := by
    intro z hz
    have h := dq_ge P₁ z.1 (B₁ z.1) (F z).1
    have h2 : 2 * ‖P₁‖ * ‖z.1‖ * ‖(F z).1 - B₁ z.1‖ ≤ 2 * K * ‖z.1‖ * (ε * ‖z‖) := by
      have := (hF z hz).1
      gcongr
    have h3 : 2 * K * ‖z.1‖ * (ε * ‖z‖) = 2 * K * ε * ‖z.1‖ * ‖z‖ := by ring
    linarith [(hP₁ z.1).2]
  have hD₂ : ∀ z ∈ N, dq P₂ z.2 (F z).2 ≤ -(1 / 2) * ‖z.2‖ ^ 2 + 2 * K * ε * ‖z.2‖ * ‖z‖ := by
    intro z hz
    have h := dq_le P₂ z.2 (B₂ z.2) (F z).2
    have h2 : 2 * ‖P₂‖ * ‖z.2‖ * ‖(F z).2 - B₂ z.2‖ ≤ 2 * K * ‖z.2‖ * (ε * ‖z‖) := by
      have := (hF z hz).2
      gcongr
    have h3 : 2 * K * ‖z.2‖ * (ε * ‖z‖) = 2 * K * ε * ‖z.2‖ * ‖z‖ := by ring
    linarith [(hP₂ z.2).2]
  -- faces
  have hface₁ : ∀ z ∈ N, qf P₁ z.1 = δ ^ 2 → 0 < dq P₁ z.1 (F z).1 := by
    intro z hz hq
    have hne : z.1 ≠ 0 := fun h0 => by
      rw [h0, qf_zero] at hq; exact (pow_pos hδ 2).ne' hq.symm
    have hy : 0 < ‖z.1‖ := norm_pos_iff.2 hne
    have h2 : τ * ‖z.2‖ ^ 2 ≤ K * ‖z.1‖ ^ 2 := by
      have := ((mul_le_mul_of_nonneg_right (min_le_right τ₁ τ₂) (sq_nonneg ‖z.2‖)).trans
        (hP₂ z.2).1).trans hz.2
      rw [← hq] at this
      exact this.trans ((qf_le P₁ z.1).trans (mul_le_mul_of_nonneg_right hK₁ (sq_nonneg _)))
    have h1 : ‖z‖ ^ 2 ≤ ‖z.2‖ ^ 2 + ‖z.1‖ ^ 2 := by linarith [norm_prod_sq_le z]
    have := face_aux hK hτ hεdef (norm_nonneg z) (norm_nonneg _) h1 h2
    nlinarith [hD₁ z hz]
  have hface₂ : ∀ z ∈ N, qf P₂ z.2 = δ ^ 2 → dq P₂ z.2 (F z).2 < 0 := by
    intro z hz hq
    have hne : z.2 ≠ 0 := fun h0 => by
      rw [h0, qf_zero] at hq; exact (pow_pos hδ 2).ne' hq.symm
    have hy : 0 < ‖z.2‖ := norm_pos_iff.2 hne
    have h2 : τ * ‖z.1‖ ^ 2 ≤ K * ‖z.2‖ ^ 2 := by
      have := ((mul_le_mul_of_nonneg_right (min_le_left τ₁ τ₂) (sq_nonneg ‖z.1‖)).trans
        (hP₁ z.1).1).trans hz.1
      rw [← hq] at this
      exact this.trans ((qf_le P₂ z.2).trans (mul_le_mul_of_nonneg_right hK₂ (sq_nonneg _)))
    have h1 := norm_prod_sq_le z
    have := face_aux hK hτ hεdef (norm_nonneg z) (norm_nonneg _) h1 h2
    nlinarith [hD₂ z hz]
  have hiso : ∀ z ∈ N, 1 / 4 * ‖z‖ ^ 2 ≤ dq P₁ z.1 (F z).1 - dq P₂ z.2 (F z).2 := by
    intro z hz
    have := iso_aux hK hε.le hε4 (norm_nonneg z.1) (norm_nonneg z.2) (norm_fst_le z)
      (norm_snd_le z) (norm_prod_sq_le z)
    linarith [hD₁ z hz, hD₂ z hz]
  -- derivatives along orbits
  have hq₁ : ∀ x s, HasDerivAt (fun s => qf P₁ (ψ s x).1) (dq P₁ (ψ s x).1 (F (ψ s x)).1) s :=
    fun x s => by
      have ha := (hasFDerivAt_fst (p := ψ s x)).comp_hasDerivAt s (hgen x s)
      exact hasDerivAt_qf P₁ ha
  have hq₂ : ∀ x s, HasDerivAt (fun s => qf P₂ (ψ s x).2) (dq P₂ (ψ s x).2 (F (ψ s x)).2) s :=
    fun x s => by
      have ha := (hasFDerivAt_snd (p := ψ s x)).comp_hasDerivAt s (hgen x s)
      exact hasDerivAt_qf P₂ ha
  -- topology of `N` and `L`
  have hc₁ : Continuous fun z : V₁ × V₂ => qf P₁ z.1 := (continuous_qf P₁).comp continuous_fst
  have hc₂ : Continuous fun z : V₁ × V₂ => qf P₂ z.2 := (continuous_qf P₂).comp continuous_snd
  have hNc : IsClosed N :=
    (isClosed_le hc₁ continuous_const).inter (isClosed_le hc₂ continuous_const)
  have hLc : IsClosed L :=
    (isClosed_eq hc₁ continuous_const).inter (isClosed_le hc₂ continuous_const)
  have hNb : N ⊆ Metric.closedBall 0 r := fun z hz =>
    mem_closedBall_zero_iff.2 (hnormN z hz).le
  have hNcpt : IsCompact N := (isCompact_closedBall _ _).of_isClosed_subset hNc hNb
  have hLN : L ⊆ N := fun z hz => ⟨hz.1.le, hz.2⟩
  have hU : (0 : V₁ × V₂) ∈ interior (N \ L) := by
    refine interior_maximal (s := N \ L) (t := {z | qf P₁ z.1 < δ ^ 2 ∧ qf P₂ z.2 < δ ^ 2})
      (fun z hz => ⟨⟨hz.1.le, hz.2.le⟩, fun hL => hz.1.ne hL.1⟩)
      ((isOpen_lt hc₁ continuous_const).inter (isOpen_lt hc₂ continuous_const)) ?_
    simp only [mem_ofPred_eq, Prod.fst_zero, Prod.snd_zero, qf_zero]
    exact ⟨pow_pos hδ 2, pow_pos hδ 2⟩
  -- isolation
  have hInv : Inv ψ N ⊆ {0} := by
    intro x hx
    by_contra hx0
    have hnz : ∀ s, ψ s x ≠ 0 := fun s h0 => hx0 (by
      have := congrArg (ψ (-s)) h0
      rwa [← ψ.map_add, neg_add_cancel, ψ.map_zero_apply, hfix] at this)
    set v := fun s => qf P₁ (ψ s x).1 - qf P₂ (ψ s x).2 with hvdef
    set v' := fun s => dq P₁ (ψ s x).1 (F (ψ s x)).1 - dq P₂ (ψ s x).2 (F (ψ s x)).2
    have hv : ∀ s, HasDerivAt v (v' s) s := fun s => (hq₁ x s).sub (hq₂ x s)
    have hvpos : ∀ s, 0 < v' s := fun s => by
      have := hiso _ (hx s)
      have : 0 < ‖ψ s x‖ := norm_pos_iff.2 (hnz s)
      nlinarith [hiso _ (hx s)]
    have hvabs : ∀ s, |v s| ≤ K * ‖ψ s x‖ ^ 2 := fun s => by
      have h1 := (qf_le P₁ (ψ s x).1).trans
        (mul_le_mul_of_nonneg_right hK₁ (sq_nonneg _))
      have h2 := (qf_le P₂ (ψ s x).2).trans
        (mul_le_mul_of_nonneg_right hK₂ (sq_nonneg _))
      have h3 := pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le (ψ s x)) 2
      have h4 := pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le (ψ s x)) 2
      rw [abs_le]
      constructor <;> nlinarith [hq₁0 (ψ s x).1, hq₂0 (ψ s x).2]
    have hv'abs : ∀ s, |v s| / (4 * K) ≤ v' s := fun s => by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hiso _ (hx s), hvabs s]
    have hvub : ∀ s, v s ≤ δ ^ 2 := fun s => by
      have := (hx s).1; linarith [hq₂0 (ψ s x).2]
    have hvlb : ∀ s, -δ ^ 2 ≤ v s := fun s => by
      have := (hx s).2; linarith [hq₁0 (ψ s x).1]
    have hmono : ∀ a b, a ≤ b → v a ≤ v b := fun a b hab => by
      have := growth_of_deriv_ge hv hab (c := 0) fun s _ => (hvpos s).le
      linarith
    rcases le_or_gt 0 (v 0) with h0 | h0
    · have h1 : 0 < v 1 := by
        obtain ⟨d, hd, hd'⟩ := exists_hasDerivAt_eq_slope (f := v) (f' := v') one_pos
          (fun s _ => (hv s).continuousAt.continuousWithinAt) (fun s _ => hv s)
        have := hvpos d
        rw [hd', sub_zero, div_one] at this
        linarith
      set b := 1 + 4 * K * (δ ^ 2 + 1) / v 1
      have hb : 1 ≤ b := by
        have : 0 ≤ 4 * K * (δ ^ 2 + 1) / v 1 := by positivity
        linarith
      have hg := growth_of_deriv_ge hv hb (c := v 1 / (4 * K)) fun s hs => by
        refine le_trans ?_ (hv'abs s)
        have : v 1 ≤ |v s| := (hmono 1 s hs.1.le).trans (le_abs_self _)
        exact div_le_div_of_nonneg_right this (by positivity)
      have e : v 1 / (4 * K) * (b - 1) = δ ^ 2 + 1 := by
        have h1' := h1.ne'
        have hK' := hK.ne'
        simp only [b, add_sub_cancel_left]
        field_simp
      linarith [hvub b]
    · set a := -(4 * K * (δ ^ 2 + 1) / -v 0)
      have ha : a ≤ 0 := by
        have : 0 ≤ 4 * K * (δ ^ 2 + 1) / -v 0 := div_nonneg (by positivity) (by linarith)
        simp only [a]; linarith
      have hg := growth_of_deriv_ge hv ha (c := -v 0 / (4 * K)) fun s hs => by
        refine le_trans ?_ (hv'abs s)
        have : -v 0 ≤ |v s| := by
          have := hmono s 0 hs.2.le
          rw [abs_of_neg (lt_of_le_of_lt this h0)]
          linarith
        exact div_le_div_of_nonneg_right this (by positivity)
      have e : -v 0 / (4 * K) * (0 - a) = δ ^ 2 + 1 := by
        have h0' : v 0 ≠ 0 := h0.ne
        have hK' := hK.ne'
        simp only [a, zero_sub, neg_neg]
        field_simp
      linarith [hvlb a]
  have hcl : closure (N \ L) ⊆ N := closure_minimal sdiff_subset hNc
  have hinv : Inv ψ (closure (N \ L)) = {0} := by
    refine subset_antisymm ((Inv_mono hcl).trans hInv) ?_
    rintro _ rfl t
    rw [hfix]
    exact subset_closure (interior_subset hU)
  exact
    { isCompact_N := hNcpt
      isCompact_L := hNcpt.of_isClosed_subset hLc hLN
      subset := hLN
      isolating := ⟨hNcpt.of_isClosed_subset isClosed_closure hcl, by
        rw [hinv]
        rintro _ rfl
        exact interior_mono subset_closure hU⟩
      inv_eq := hinv
      nhds := by
        rintro _ rfl
        exact hU
      posInv := by
        intro x hx t ht hseg
        rcases ht.eq_or_lt with rfl | ht
        · rw [ψ.map_zero_apply]; exact hx
        · exfalso
          have hd := hq₁ x 0
          rw [ψ.map_zero_apply] at hd
          obtain ⟨s, hs, hlt⟩ := exists_gt_of_hasDerivAt_pos hd (hface₁ x (hLN hx) hx.1) ht
          have h1 := (hseg s ⟨hs.1.le, hs.2⟩).1
          simp only [ψ.map_zero_apply] at hlt
          rw [hx.1] at hlt
          linarith
      exit := by
        intro x hx t ht hout
        set S' := {s | s ∈ Icc 0 t ∧ ∀ r ∈ Icc 0 s, ψ r x ∈ N} with hS'
        have h0S : (0 : ℝ) ∈ S' := ⟨⟨le_rfl, ht⟩, fun r hr => by
          rw [le_antisymm hr.2 hr.1, ψ.map_zero_apply]; exact hx⟩
        have hbdd : BddAbove S' := ⟨t, fun s hs => hs.1.2⟩
        set s₀ := sSup S'
        have hs₀0 : 0 ≤ s₀ := le_csSup hbdd h0S
        have hs₀t : s₀ ≤ t := csSup_le ⟨0, h0S⟩ fun s hs => hs.1.2
        have hlt : ∀ r, 0 ≤ r → r < s₀ → ψ r x ∈ N := fun r hr0 hr => by
          obtain ⟨s, hs, hrs⟩ := exists_lt_of_lt_csSup ⟨0, h0S⟩ hr
          exact hs.2 r ⟨hr0, hrs.le⟩
        have hseg : ∀ r ∈ Icc 0 s₀, ψ r x ∈ N := by
          rcases hs₀0.eq_or_lt with h | h
          · intro r hr
            rw [le_antisymm (h ▸ hr.2) hr.1, ψ.map_zero_apply]; exact hx
          · have hsub : Ico 0 s₀ ⊆ (fun r => ψ r x) ⁻¹' N := fun r hr => hlt r hr.1 hr.2
            have := closure_minimal hsub (hNc.preimage (continuous_orbit ψ x))
            rw [closure_Ico h.ne] at this
            exact this
        have hs₀lt : s₀ < t := by
          rcases hs₀t.eq_or_lt with h | h
          · exact absurd (h ▸ hseg s₀ ⟨hs₀0, le_rfl⟩) hout
          · exact h
        refine ⟨s₀, ⟨hs₀0, hs₀t⟩, hseg, ?_⟩
        by_contra hnL
        have hpN := hseg s₀ ⟨hs₀0, le_rfl⟩
        have hq₁lt : qf P₁ (ψ s₀ x).1 < δ ^ 2 :=
          lt_of_le_of_ne hpN.1 fun h => hnL ⟨h, hpN.2⟩
        have hev₁ : ∀ᶠ s in 𝓝[>] s₀, qf P₁ (ψ s x).1 < δ ^ 2 :=
          eventually_nhdsWithin_of_eventually_nhds
            ((hq₁ x s₀).continuousAt.eventually (gt_mem_nhds hq₁lt))
        have hev₂ : ∀ᶠ s in 𝓝[>] s₀, qf P₂ (ψ s x).2 ≤ δ ^ 2 := by
          rcases hpN.2.lt_or_eq with h | h
          · exact (eventually_nhdsWithin_of_eventually_nhds
              ((hq₂ x s₀).continuousAt.eventually (gt_mem_nhds h))).mono fun s hs => hs.le
          · have := eventually_lt_of_hasDerivAt_neg (hq₂ x s₀) (hface₂ _ hpN h)
            exact this.mono fun s hs => (h ▸ hs).le
        obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 (hev₁.and hev₂)
        set s₁ := min u t
        have hs₁ : s₀ < s₁ := lt_min hu hs₀lt
        have hs₁S : s₁ ∈ S' := by
          refine ⟨⟨hs₀0.trans hs₁.le, min_le_right _ _⟩, fun r hr => ?_⟩
          rcases le_or_gt r s₀ with h | h
          · exact hseg r ⟨hr.1, h⟩
          · have := hsub ⟨h, hr.2.trans (min_le_left _ _)⟩
            exact ⟨this.1.le, this.2⟩
        exact absurd (le_csSup hbdd hs₁S) (not_le.2 hs₁) }

end Block

end ConleyCheck.Conley
