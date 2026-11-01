import ConleyCheck.Conley.Deform
import ConleyCheck.Conley.Skew

/-!
# The suspension isomorphism at a two-sided repeller of the base

Let `Φ` be a skew product over a base flow `θ`, and let `b₀` be a fixed point of `θ` with an index
pair `(J, ∂J)` that is an arc with its two end points (`IntervalChart`), as for a repelling fixed
point of a flow on a curve. Then `CH_{n+1}(K × {b₀}) ≅ CH_n(K; f₀)` for every isolated invariant
set `K` of the fiber flow `f₀` (`skew_suspension`). This is the UV row of `prop:boundary` for the
double, `h(K × {π}) ≅ Σ h_{f_-}(K)`, in homology.

The proof combines the continuation to the product flow (`skew_boundary_setup`), a deformation
collar on the product index pair `(N_K × J, L_K × J ∪ N_K × ∂J)`, and the pair-level suspension
`singH_suspension`.
-/

namespace ConleyCheck.Conley

open CategoryTheory Set Topology unitInterval

universe u

/-! ### Interval charts -/

section Chart

variable {Y : Type*} [TopologicalSpace Y]

/-- `(J, D)` is an arc with its two end points, parametrized by `e` on `[0, 1]`. -/
structure IntervalChart (J D : Set Y) where
  e : C(ℝ, Y)
  injOn : InjOn e (Icc 0 1)
  image_eq : e '' Icc 0 1 = J
  mem_iff : ∀ t ∈ Icc (0 : ℝ) 1, e t ∈ D ↔ (t = 0 ∨ t = 1)
  subset : D ⊆ J

variable {J D : Set Y} (ch : IntervalChart J D)

/-- The chart restricted to `[0, 1]`. -/
def IntervalChart.emb : Icc (0 : ℝ) 1 → Y := fun t => ch.e t

theorem IntervalChart.range_emb : range ch.emb = J :=
  (image_eq_range _ _).symm.trans ch.image_eq

theorem IntervalChart.mem_J {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ch.e t ∈ J := by
  have := mem_image_of_mem ch.e ht
  rwa [ch.image_eq] at this

variable [T2Space Y]

theorem IntervalChart.isEmbedding_emb : IsEmbedding ch.emb :=
  ((ch.e.continuous.comp continuous_subtype_val).isClosedEmbedding
    fun s t h => Subtype.ext (ch.injOn s.2 t.2 h)).isEmbedding

/-- The chart as a homeomorphism `[0, 1] ≃ₜ J`. -/
noncomputable def IntervalChart.homeo : Icc (0 : ℝ) 1 ≃ₜ J :=
  ch.isEmbedding_emb.toHomeomorph.trans (Homeomorph.setCongr ch.range_emb)

theorem IntervalChart.homeo_apply (t : Icc (0 : ℝ) 1) : (ch.homeo t : Y) = ch.e t := rfl

theorem IntervalChart.e_homeo_symm (y : J) : ch.e (ch.homeo.symm y) = y := by
  rw [← ch.homeo_apply, ch.homeo.apply_symm_apply]

/-- The deformation of `[0, 1]` pushing `[0, 1/4]` to `0` and `[3/4, 1]` to `1`. -/
noncomputable def pushEnds (s t : ℝ) : ℝ := (1 - s) * t + s * max 0 (min 1 (2 * t - 1 / 2))

theorem continuous_pushEnds : Continuous fun p : ℝ × ℝ => pushEnds p.1 p.2 :=
  ((continuous_const.sub continuous_fst).mul continuous_snd).add
    (continuous_fst.mul (continuous_const.max (continuous_const.min
      ((continuous_const.mul continuous_snd).sub continuous_const))))

theorem pushEnds_mem {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    pushEnds s t ∈ Icc (0 : ℝ) 1 := by
  have hm0 : 0 ≤ max 0 (min 1 (2 * t - 1 / 2)) := le_max_left _ _
  have hm1 : max 0 (min 1 (2 * t - 1 / 2)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
  have h1 : 0 ≤ 1 - s := by linarith [hs.2]
  unfold pushEnds
  constructor
  · exact add_nonneg (mul_nonneg h1 ht.1) (mul_nonneg hs.1 hm0)
  · nlinarith [mul_le_mul_of_nonneg_left ht.2 h1, mul_le_mul_of_nonneg_left hm1 hs.1]

theorem pushEnds_zero_left (t : ℝ) : pushEnds 0 t = t := by simp [pushEnds]

theorem pushEnds_of_le {s t : ℝ} (ht : t ≤ 1 / 4) : pushEnds s t = (1 - s) * t := by
  have : max 0 (min 1 (2 * t - 1 / 2)) = 0 :=
    max_eq_left ((min_le_right _ _).trans (by linarith))
  rw [pushEnds, this, mul_zero, add_zero]

theorem pushEnds_of_ge {s t : ℝ} (ht : 3 / 4 ≤ t) : pushEnds s t = (1 - s) * t + s := by
  have : max 0 (min 1 (2 * t - 1 / 2)) = 1 := by
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  rw [pushEnds, this, mul_one]

include ch in
/-- An interval chart gives a deformation collar of `(J, D)`. -/
theorem IntervalChart.isDeformCollared : IsDeformCollared J D := by
  let h := ch.homeo
  let r : C(I × J, Icc (0 : ℝ) 1) := ⟨fun p => ⟨pushEnds p.1 (h.symm p.2), pushEnds_mem p.1.2
      (h.symm p.2).2⟩, by
    refine Continuous.subtype_mk ?_ _
    exact continuous_pushEnds.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp (h.symm.continuous.comp continuous_snd)))⟩
  let G : C(I × J, J) := ⟨fun p => h (r p), h.continuous.comp r.continuous⟩
  have hG : ∀ p, h.symm (G p) = r p := fun p => h.symm_apply_apply _
  have hval : ∀ y : J, (h.symm y : ℝ) ∈ Icc (0 : ℝ) 1 := fun y => (h.symm y).2
  have hD : ∀ y : J, (y : Y) ∈ D → (h.symm y : ℝ) = 0 ∨ (h.symm y : ℝ) = 1 := fun y hy =>
    (ch.mem_iff _ (hval y)).1 (by rw [ch.e_homeo_symm]; exact hy)
  have hcs : Continuous fun y : J => (h.symm y : ℝ) := continuous_subtype_val.comp h.symm.continuous
  obtain ⟨O, hO, hOe⟩ := isOpen_induced_iff.1
    ((isOpen_lt hcs continuous_const).union (isOpen_lt continuous_const hcs) :
      IsOpen {y : J | (h.symm y : ℝ) < 1 / 4 ∨ 3 / 4 < (h.symm y : ℝ)})
  have hmemO : ∀ y (hy : y ∈ J), y ∈ O ↔
      ((h.symm ⟨y, hy⟩ : ℝ) < 1 / 4 ∨ 3 / 4 < (h.symm ⟨y, hy⟩ : ℝ)) :=
    fun y hy => Set.ext_iff.1 hOe ⟨y, hy⟩
  have hfix : ∀ (s : I) (y : J), (h.symm y : ℝ) = 0 ∨ (h.symm y : ℝ) = 1 → G (s, y) = y := by
    intro s y hy
    have e : r (s, y) = h.symm y := by
      apply Subtype.ext
      show pushEnds s (h.symm y) = (h.symm y : ℝ)
      rcases hy with hy | hy
      · rw [hy, pushEnds_of_le (by norm_num)]; ring
      · rw [hy, pushEnds_of_ge (by norm_num)]; ring
    show h (r (s, y)) = y
    rw [e, h.apply_symm_apply]
  refine ⟨{y | ∃ hy : y ∈ J, ((h.symm ⟨y, hy⟩ : ℝ) ≤ 1 / 4 ∨ 3 / 4 ≤ (h.symm ⟨y, hy⟩ : ℝ))},
    O, G, hO, fun y hy => ?_, ?_, fun y hy => hy.1, fun y => ?_, ?_, ?_, ?_⟩
  · refine (hmemO y (ch.subset hy)).2 ?_
    rcases hD ⟨y, ch.subset hy⟩ hy with h0 | h1
    · left; rw [h0]; norm_num
    · right; rw [h1]; norm_num
  · rintro y ⟨hyO, hyJ⟩
    refine ⟨hyJ, ?_⟩
    rcases (hmemO y hyJ).1 hyO with h1 | h1
    · exact Or.inl h1.le
    · exact Or.inr h1.le
  · show h (r (0, y)) = y
    have e : r (0, y) = h.symm y := Subtype.ext (pushEnds_zero_left _)
    rw [e, h.apply_symm_apply]
  · intro s y hy
    rw [hfix s y (hD y hy)]
    exact hy
  · rintro s y ⟨hyJ, hy⟩
    refine ⟨(G (s, y)).2, ?_⟩
    show (h.symm (G (s, y)) : ℝ) ≤ 1 / 4 ∨ 3 / 4 ≤ (h.symm (G (s, y)) : ℝ)
    rw [hG]
    show pushEnds s (h.symm y) ≤ 1 / 4 ∨ 3 / 4 ≤ pushEnds s (h.symm y)
    have hs := s.2
    have ht := hval y
    rcases hy with hy | hy
    · left
      rw [pushEnds_of_le hy]
      nlinarith [hs.1, ht.1]
    · right
      rw [pushEnds_of_ge hy]
      nlinarith [hs.2, hs.1]
  · rintro y ⟨hyJ, hy⟩
    show ((h (r (1, y)) : J) : Y) ∈ D
    rw [ch.homeo_apply]
    refine (ch.mem_iff _ (r (1, y)).2).2 ?_
    show pushEnds 1 (h.symm y) = 0 ∨ pushEnds 1 (h.symm y) = 1
    rcases hy with hy | hy
    · left; rw [pushEnds_of_le hy]; ring
    · right; rw [pushEnds_of_ge hy]; ring

variable (K : Type u) [Ring K] {X : Type u} [TopologicalSpace X] {Z : Type} [TopologicalSpace Z]
  [T2Space Z] {J' D' : Set Z}

/-- The chart map `N × [0, 1] → N × J` is an isomorphism on relative homology. -/
theorem IntervalChart.singMap_bijective (ch : IntervalChart J' D') (N L : Set X) (k : ℤ)
    (hB : MapsTo ((ContinuousMap.id X).prodMap ch.e) (cylN N) (N ×ˢ J'))
    (hA : ∀ p ∈ cylN N, p ∈ cylL N L →
      (ContinuousMap.id X).prodMap ch.e p ∈ L ×ˢ J' ∪ N ×ˢ D') :
    Function.Bijective (singMap K ((ContinuousMap.id X).prodMap ch.e) hB hA k).hom := by
  let F : C(X × ℝ, X × Z) := (ContinuousMap.id X).prodMap ch.e
  let g : cylN N → X × Icc (0 : ℝ) 1 := fun p => ((p : X × ℝ).1, ⟨(p : X × ℝ).2, p.2.2⟩)
  have hg : IsEmbedding g :=
    ((IsEmbedding.id.prodMap IsEmbedding.subtypeVal).of_comp_iff).1 IsEmbedding.subtypeVal
  have hemb : IsEmbedding fun p : cylN N => F p :=
    (IsEmbedding.id.prodMap ch.isEmbedding_emb).comp hg
  exact Conley.singMap_bijective K F (B := cylN N) (A := cylL N L) (B' := N ×ˢ J')
    (A' := L ×ˢ J' ∪ N ×ˢ D') hB
    (by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      rw [← ch.image_eq] at hy
      obtain ⟨t, ht, rfl⟩ := hy
      exact ⟨(x, t), ⟨hx, ht⟩, rfl⟩)
    hemb
    (by
      rintro ⟨x, t⟩ ⟨hx, ht⟩
      show (x, t) ∈ cylL N L ↔ (x, ch.e t) ∈ L ×ˢ J' ∪ N ×ˢ D'
      constructor
      · rintro (⟨hxL, -⟩ | ⟨-, ht'⟩)
        · exact Or.inl ⟨hxL, ch.mem_J ht⟩
        · exact Or.inr ⟨hx, (ch.mem_iff t ht).2 ht'⟩
      · rintro (⟨hxL, -⟩ | ⟨-, ht'⟩)
        · exact Or.inl ⟨hxL, ht⟩
        · exact Or.inr ⟨hx, (ch.mem_iff t ht).1 ht'⟩) k

/-- The chart identifies `(N × [0, 1], L × [0, 1] ∪ N × {0, 1})` with `(N × J, L × J ∪ N × D)`. -/
theorem IntervalChart.singH_equiv (ch : IntervalChart J' D') (N L : Set X) (k : ℤ) :
    Nonempty (singH K (X × ℝ) k (cylN N) (cylL N L) ≃ₗ[K]
      singH K (X × Z) k (N ×ˢ J') (L ×ˢ J' ∪ N ×ˢ D')) :=
  ⟨LinearEquiv.ofBijective _ (ch.singMap_bijective K N L k
    (fun p hp => ⟨hp.1, ch.mem_J hp.2⟩) (fun p hp hpA => by
      rcases hpA with ⟨hxL, -⟩ | ⟨-, ht'⟩
      · exact Or.inl ⟨hxL, ch.mem_J hp.2⟩
      · exact Or.inr ⟨hp.1, (ch.mem_iff _ hp.2).2 ht'⟩))⟩

end Chart

/-! ### The suspension isomorphism -/

section Repeller

variable (K : Type u) [Ring K] {X : Type u} {B : Type} [TopologicalSpace X] [TopologicalSpace B]
  [T2Space X] [T2Space B] [TopologicalSpace.MetrizableSpace X] [TopologicalSpace.MetrizableSpace B]
  {Φ : Flow ℝ (X × B)} {θ : Flow ℝ B} (hΦ : IsSkew Φ θ) {U : Set B} (hU : IsInvariant θ U)
  (hUo : IsOpen U) {b₀ : B} (hb₀U : b₀ ∈ U)
  (c : SkewContraction (θ.restrict hU) ⟨b₀, hb₀U⟩)

include hUo in
/-- `CH_n(K × {b₀}) ≅ H_n(N_K × [0, 1], L_K × [0, 1] ∪ N_K × {0, 1})` for an index pair
`(N_K, L_K)` of `K` with a deformation collar. -/
theorem skew_suspension_aux {M : Set X} (hM : IsIsolatingNbhd (c.f₀ hΦ hU hb₀U) M)
    {Nb Lb : Set B} (hb : IsIndexPair θ {b₀} Nb Lb) (hNbU : Nb ⊆ U)
    (ch : IntervalChart (Subtype.val ⁻¹' Nb : Set U) (Subtype.val ⁻¹' Lb : Set U))
    (hS : IsIsolatedInvariantSet Φ (Inv (c.f₀ hΦ hU hb₀U) M ×ˢ {b₀}))
    (hK : IsIsolatedInvariantSet (c.f₀ hΦ hU hb₀U) (Inv (c.f₀ hΦ hU hb₀U) M)) :
    ∃ NK LK, IsIndexPair (c.f₀ hΦ hU hb₀U) (Inv (c.f₀ hΦ hU hb₀U) M) NK LK ∧
      IsDeformCollared NK LK ∧ ∀ n : ℕ, Nonempty (homologyIndex K Φ hS n ≃ₗ[K]
        singH K (X × ℝ) (Int.ofNat n) (cylN NK) (cylL NK LK)) := by
  obtain ⟨N, L, hP, hE⟩ := skew_boundary_setup hΦ hU hUo hb₀U c hM hb hNbU
  obtain ⟨NK, LK, hPK, hcK⟩ := exists_deformCollared_indexPair hK
  obtain ⟨e⟩ := hE NK LK hPK
  have hcP := hcK.prod (IntervalChart.isDeformCollared ch)
  have hJc : IsClosed (Subtype.val ⁻¹' Nb : Set U) :=
    hb.isCompact_N.isClosed.preimage continuous_subtype_val
  have hDc : IsClosed (Subtype.val ⁻¹' Lb : Set U) :=
    hb.isCompact_L.isClosed.preimage continuous_subtype_val
  have hQc : IsClosed (LK ×ˢ (Subtype.val ⁻¹' Nb : Set U) ∪ NK ×ˢ (Subtype.val ⁻¹' Lb : Set U)) :=
    (hPK.isCompact_L.isClosed.prod hJc).union (hPK.isCompact_N.isClosed.prod hDc)
  have hQP : LK ×ˢ (Subtype.val ⁻¹' Nb : Set U) ∪ NK ×ˢ (Subtype.val ⁻¹' Lb : Set U) ⊆
      NK ×ˢ (Subtype.val ⁻¹' Nb : Set U) := by
    rintro p (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨hPK.subset h1, h2⟩
    · exact ⟨h1, hb.subset h2⟩
  refine ⟨NK, LK, hPK, hcK, fun n => ?_⟩
  obtain ⟨e₁⟩ := homologyIndexIso K hS hP n
  obtain ⟨e₂⟩ := deformCollarEquiv_nonempty K hQc hQP hcP n
  obtain ⟨e₃⟩ := ch.singH_equiv K NK LK (Int.ofNat n)
  exact ⟨e₁.toLinearEquiv.trans ((redIso K e.symm n).toLinearEquiv.trans
    (e₂.symm.trans e₃.symm))⟩

include hUo in
/-- The suspension isomorphism `CH_{n+1}(K × {b₀}) ≅ CH_n(K; f₀)` at a fixed point `b₀` of the
base whose index pair `(Nb, Lb)` is an arc with its two end points. -/
theorem skew_suspension {M : Set X} (hM : IsIsolatingNbhd (c.f₀ hΦ hU hb₀U) M)
    {Nb Lb : Set B} (hb : IsIndexPair θ {b₀} Nb Lb) (hNbU : Nb ⊆ U)
    (ch : IntervalChart (Subtype.val ⁻¹' Nb : Set U) (Subtype.val ⁻¹' Lb : Set U))
    (hS : IsIsolatedInvariantSet Φ (Inv (c.f₀ hΦ hU hb₀U) M ×ˢ {b₀}))
    (hK : IsIsolatedInvariantSet (c.f₀ hΦ hU hb₀U) (Inv (c.f₀ hΦ hU hb₀U) M)) (n : ℕ) :
    Nonempty (homologyIndex K Φ hS (n + 1) ≃ₗ[K] homologyIndex K (c.f₀ hΦ hU hb₀U) hK n) := by
  obtain ⟨NK, LK, hPK, hcK, hE⟩ := skew_suspension_aux K hΦ hU hUo hb₀U c hM hb hNbU ch hS hK
  obtain ⟨e₁⟩ := hE (n + 1)
  obtain ⟨e₂⟩ := singH_suspension K hPK.subset (Int.ofNat n)
  obtain ⟨e₃⟩ := homologyIndex_equiv_of_deformCollared K hK hPK hcK n
  exact ⟨e₁.trans (e₂.trans e₃.symm)⟩

include hUo in
/-- `CH_0(K × {b₀}) = 0` at such a fixed point. -/
theorem skew_suspension_zero {M : Set X} (hM : IsIsolatingNbhd (c.f₀ hΦ hU hb₀U) M)
    {Nb Lb : Set B} (hb : IsIndexPair θ {b₀} Nb Lb) (hNbU : Nb ⊆ U)
    (ch : IntervalChart (Subtype.val ⁻¹' Nb : Set U) (Subtype.val ⁻¹' Lb : Set U))
    (hS : IsIsolatedInvariantSet Φ (Inv (c.f₀ hΦ hU hb₀U) M ×ˢ {b₀}))
    (hK : IsIsolatedInvariantSet (c.f₀ hΦ hU hb₀U) (Inv (c.f₀ hΦ hU hb₀U) M)) :
    Subsingleton (homologyIndex K Φ hS 0) := by
  obtain ⟨NK, LK, hPK, -, hE⟩ := skew_suspension_aux K hΦ hU hUo hb₀U c hM hb hNbU ch hS hK
  obtain ⟨e₁⟩ := hE 0
  obtain ⟨e₂⟩ := singH_suspension K hPK.subset (Int.negSucc 0)
  exact (e₁.trans e₂).toEquiv.subsingleton

end Repeller

end ConleyCheck.Conley
