import ConleyCheck.Conley.Uniqueness

/-!
# The pointed sphere as a quotient of a disk and of a box

* `diskEquiv k`: `D^k/S^{k-1}` is homeomorphic to `S^k`, via the map
  `x ↦ (2‖x‖² - 1, 2√(1 - ‖x‖²) x)`, which sends `S^{k-1}` to the base point `(1, 0)`. The map
  is a continuous bijection from a compact space to a Hausdorff space.
* `boxEquiv k m`: for the box `B = D^k × D^m` and `L = S^{k-1} × D^m`, the space `B/L` is
  pointed homotopy equivalent to `S^k`. The homotopy `(u, s) ↦ (u, (1 - t) s)` deforms `B/L` onto
  `D^k/S^{k-1}`.
-/

namespace ConleyCheck.Conley

open Set Metric unitInterval WithLp

/-- The pointed sphere `S^k ⊆ ℝ^{k+1}`. -/
abbrev Sphere (k : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1

noncomputable def Sphere.pt (k : ℕ) : Sphere k :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

theorem IndexSpace.compactSpace {α : Type*} [TopologicalSpace α] {N : Set α} (L : Set α)
    (hN : IsCompact N) : CompactSpace (IndexSpace N L) := by
  haveI := isCompact_iff_compactSpace.mp hN
  refine ⟨?_⟩
  have e : (univ : Set (IndexSpace N L)) = range (Quotient.mk (indexSetoid N L)) :=
    (range_eq_univ.2 Quotient.mk_surjective).symm
  rw [e]
  exact isCompact_range continuous_quotient_mk'

section Cons

variable {k : ℕ}

/-- `(a, x) ↦ (a, x₁, …, x_k)`. -/
def vcons (a : ℝ) (x : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin (k + 1)) :=
  toLp 2 (Fin.cons a fun i => x i)

theorem norm_vcons_sq (a : ℝ) (x : EuclideanSpace ℝ (Fin k)) :
    ‖vcons a x‖ ^ 2 = a ^ 2 + ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp [vcons]

theorem vcons_inj {a b : ℝ} {x y : EuclideanSpace ℝ (Fin k)} (h : vcons a x = vcons b y) :
    a = b ∧ x = y := by
  refine ⟨by simpa [vcons] using congrArg (fun v => v 0) h, ?_⟩
  apply WithLp.ofLp_injective 2
  funext j
  simpa [vcons] using congrArg (fun v => v j.succ) h

theorem vcons_one_zero : vcons 1 (0 : EuclideanSpace ℝ (Fin k)) = EuclideanSpace.single 0 1 := by
  apply WithLp.ofLp_injective 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [vcons]

theorem continuous_vcons {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    {g : X → EuclideanSpace ℝ (Fin k)} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => vcons (f x) (g x) := by
  show Continuous fun x => toLp 2 (Fin.cons (f x) (fun i => g x i) : Fin (k + 1) → ℝ)
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hf
  · simp only [Fin.cons_succ]
    exact (PiLp.continuous_apply 2 _ j).comp hg

end Cons

/-! ### `D^k/S^{k-1} ≅ S^k` -/

section Disk

variable (k : ℕ)

def diskD : Set (EuclideanSpace ℝ (Fin k)) := closedBall 0 1

def diskS : Set (EuclideanSpace ℝ (Fin k)) := sphere 0 1

variable {k}

noncomputable def diskVec (x : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin (k + 1)) :=
  vcons (2 * ‖x‖ ^ 2 - 1) ((2 * √(1 - ‖x‖ ^ 2)) • x)

theorem norm_diskVec {x : EuclideanSpace ℝ (Fin k)} (hx : ‖x‖ ≤ 1) : ‖diskVec x‖ = 1 := by
  have h1 : 0 ≤ 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  have h : ‖diskVec x‖ ^ 2 = 1 := by
    rw [diskVec, norm_vcons_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_pow,
      Real.sq_sqrt h1]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [h, one_pow])

theorem diskVec_of_norm_eq_one {x : EuclideanSpace ℝ (Fin k)} (hx : ‖x‖ = 1) :
    diskVec x = EuclideanSpace.single 0 1 := by
  rw [diskVec, hx]
  simp only [one_pow, mul_one, sub_self, Real.sqrt_zero, mul_zero, zero_smul]
  rw [show (2 : ℝ) - 1 = 1 by norm_num]
  exact vcons_one_zero

theorem norm_eq_one_of_diskVec {x : EuclideanSpace ℝ (Fin k)}
    (h : diskVec x = EuclideanSpace.single 0 1) : ‖x‖ = 1 := by
  rw [← vcons_one_zero, diskVec] at h
  have h1 := (vcons_inj h).1
  have h2 : ‖x‖ ^ 2 = 1 ^ 2 := by linarith
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 h2

theorem diskVec_inj {x y : EuclideanSpace ℝ (Fin k)} (hx : ‖x‖ ≤ 1)
    (h : diskVec x = diskVec y) : x = y ∨ (‖x‖ = 1 ∧ ‖y‖ = 1) := by
  obtain ⟨h1, h2⟩ := vcons_inj h
  have hn : ‖x‖ = ‖y‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)
  rcases eq_or_lt_of_le hx with hx1 | hx1
  · exact Or.inr ⟨hx1, hn ▸ hx1⟩
  · left
    rw [← hn] at h2
    have hc : 0 < 2 * √(1 - ‖x‖ ^ 2) := by
      have : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      positivity
    exact smul_right_injective _ hc.ne' h2

/-- The map `D^k → S^k`. -/
noncomputable def diskMap : C(diskD k, Sphere k) where
  toFun x := ⟨diskVec (x : EuclideanSpace ℝ (Fin k)), by
    rw [mem_sphere_zero_iff_norm]
    exact norm_diskVec (mem_closedBall_zero_iff.1 x.2)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_vcons (by fun_prop) (by fun_prop)

variable (k) in
/-- The induced map `D^k/S^{k-1} → S^k`. -/
noncomputable def diskQ : C(IndexSpace (diskD k) (diskS k), Sphere k) :=
  descend (Sphere.pt k) diskMap fun x hx =>
    Subtype.ext (diskVec_of_norm_eq_one (mem_sphere_zero_iff_norm.1 hx))

theorem diskQ_injective : Function.Injective (diskQ k) := by
  intro a b hab
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  rename_i a b
  rcases a with x | ⟨⟩ <;> rcases b with y | ⟨⟩
  · have h : diskVec (x : EuclideanSpace ℝ (Fin k)) = diskVec (y : EuclideanSpace ℝ (Fin k)) :=
      congrArg Subtype.val hab
    rcases diskVec_inj (mem_closedBall_zero_iff.1 x.2) h with hxy | ⟨hx, hy⟩
    · rw [Subtype.ext hxy]
    · exact Quotient.sound (Or.inr ⟨mem_sphere_zero_iff_norm.2 hx, mem_sphere_zero_iff_norm.2 hy⟩)
  · have h : diskVec (x : EuclideanSpace ℝ (Fin k)) = EuclideanSpace.single 0 1 :=
      congrArg Subtype.val hab
    exact Quotient.sound (Or.inr ⟨mem_sphere_zero_iff_norm.2 (norm_eq_one_of_diskVec h), trivial⟩)
  · have h : diskVec (y : EuclideanSpace ℝ (Fin k)) = EuclideanSpace.single 0 1 :=
      (congrArg Subtype.val hab).symm
    exact Quotient.sound (Or.inr ⟨trivial, mem_sphere_zero_iff_norm.2 (norm_eq_one_of_diskVec h)⟩)
  · rfl

theorem diskQ_surjective : Function.Surjective (diskQ k) := by
  rintro ⟨y, hy⟩
  rw [mem_sphere_zero_iff_norm] at hy
  set a := y 0
  set z : EuclideanSpace ℝ (Fin k) := toLp 2 fun j => y j.succ
  have hyz : y = vcons a z := by
    apply WithLp.ofLp_injective 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [vcons, a, z]
  have hn : a ^ 2 + ‖z‖ ^ 2 = 1 := by rw [← norm_vcons_sq, ← hyz, hy, one_pow]
  have hz0 := norm_nonneg z
  by_cases ha : a = 1
  · refine ⟨IndexSpace.pt _ _, Subtype.ext ?_⟩
    show EuclideanSpace.single 0 1 = y
    have hz : z = 0 := by
      rw [ha] at hn
      have : ‖z‖ ^ 2 = 0 := by linarith
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
    rw [hyz, ha, hz]
    exact vcons_one_zero.symm
  · have ha1 : a < 1 := lt_of_le_of_ne (by nlinarith) ha
    have ha' : -1 ≤ a := by nlinarith
    set r := √((1 + a) / 2)
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hr2 : r ^ 2 = (1 + a) / 2 := Real.sq_sqrt (by linarith)
    have hc : 0 < 1 - r ^ 2 := by rw [hr2]; linarith
    set c := 2 * √(1 - r ^ 2)
    have hcpos : 0 < c := by positivity
    have hc2 : c ^ 2 = 4 * (1 - r ^ 2) := by
      rw [mul_pow, Real.sq_sqrt hc.le]; ring
    set x : EuclideanSpace ℝ (Fin k) := c⁻¹ • z
    have hxn : ‖x‖ = r := by
      have hsq : ‖x‖ ^ 2 = r ^ 2 := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, hc2, hr2]
        have hz2 : ‖z‖ ^ 2 = 1 - a ^ 2 := by linarith
        rw [hz2, show 4 * (1 - (1 + a) / 2) = 2 * (1 - a) by ring,
          show (1 : ℝ) - a ^ 2 = (1 - a) * (1 + a) by ring]
        have : (1 : ℝ) - a ≠ 0 := by linarith
        field_simp
      exact (sq_eq_sq₀ (norm_nonneg _) hr0).1 hsq
    have hx1 : ‖x‖ ≤ 1 := by rw [hxn]; nlinarith
    refine ⟨IndexSpace.proj _ _ ⟨x, mem_closedBall_zero_iff.2 hx1⟩, Subtype.ext ?_⟩
    show diskVec x = y
    rw [hyz, diskVec, hxn]
    congr 1
    · rw [hr2]; ring
    · show c • (c⁻¹ • z) = z
      rw [smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]

variable (k) in
/-- `D^k/S^{k-1} ≅ S^k`. -/
noncomputable def diskHomeo : IndexSpace (diskD k) (diskS k) ≃ₜ Sphere k :=
  haveI := IndexSpace.compactSpace (N := diskD k) (diskS k)
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (diskQ k) ⟨diskQ_injective, diskQ_surjective⟩) (diskQ k).continuous

variable (k) in
noncomputable def diskEquiv :
    PointedHomotopyEquiv (IndexSpace (diskD k) (diskS k)) (Sphere k) (IndexSpace.pt _ _)
      (Sphere.pt k) where
  toFun := ⟨diskHomeo k, (diskHomeo k).continuous⟩
  invFun := ⟨(diskHomeo k).symm, (diskHomeo k).symm.continuous⟩
  map_pt := rfl
  inv_pt := by
    show (diskHomeo k).symm (Sphere.pt k) = _
    rw [Homeomorph.symm_apply_eq]
    rfl
  left := by
    have : (⟨(diskHomeo k).symm, (diskHomeo k).symm.continuous⟩ :
        C(Sphere k, IndexSpace (diskD k) (diskS k))).comp ⟨diskHomeo k, (diskHomeo k).continuous⟩ =
        ContinuousMap.id _ := ContinuousMap.ext fun x => (diskHomeo k).symm_apply_apply x
    rw [this]
    exact ContinuousMap.HomotopicRel.refl _
  right := by
    have : (⟨diskHomeo k, (diskHomeo k).continuous⟩ :
        C(IndexSpace (diskD k) (diskS k), Sphere k)).comp
          ⟨(diskHomeo k).symm, (diskHomeo k).symm.continuous⟩ = ContinuousMap.id _ := ContinuousMap.ext fun x => (diskHomeo k).apply_symm_apply x
    rw [this]
    exact ContinuousMap.HomotopicRel.refl _

end Disk

/-! ### The box `D^k × D^m` -/

section Box

variable (k m : ℕ)

def boxN : Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)) :=
  closedBall 0 1 ×ˢ closedBall 0 1

def boxL : Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)) :=
  sphere 0 1 ×ˢ closedBall 0 1

variable {k m}

theorem smul_mem_closedBall_one {s : EuclideanSpace ℝ (Fin m)} (hs : s ∈ closedBall 0 1) (t : I) :
    (1 - (t : ℝ)) • s ∈ closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 := by
  rw [mem_closedBall_zero_iff] at hs ⊢
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [t.2.2])]
  nlinarith [t.2.1, norm_nonneg s]

variable (k m)

noncomputable def boxToDisk :
    C(IndexSpace (boxN k m) (boxL k m), IndexSpace (diskD k) (diskS k)) :=
  descend (IndexSpace.pt _ _)
    ((IndexSpace.proj _ _).comp
      ⟨fun z => ⟨(z : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)).1, z.2.1⟩,
        (continuous_fst.comp continuous_subtype_val).subtype_mk _⟩)
    fun _ hz => IndexSpace.proj_eq_pt hz.1

noncomputable def diskToBox :
    C(IndexSpace (diskD k) (diskS k), IndexSpace (boxN k m) (boxL k m)) :=
  descend (IndexSpace.pt _ _)
    ((IndexSpace.proj _ _).comp
      ⟨fun x => ⟨((x : EuclideanSpace ℝ (Fin k)), 0), x.2, mem_closedBall_self zero_le_one⟩,
        (continuous_subtype_val.prodMk continuous_const).subtype_mk _⟩)
    fun _ hx => IndexSpace.proj_eq_pt ⟨hx, mem_closedBall_self zero_le_one⟩

theorem boxToDisk_diskToBox : (boxToDisk k m).comp (diskToBox k m) = ContinuousMap.id _ := by
  ext q
  induction q using Quotient.inductionOn
  rename_i q
  rcases q with x | ⟨⟩ <;> rfl

/-- The deformation `(t, [u, s]) ↦ [u, (1 - t) s]`. -/
noncomputable def boxHom : C(I × IndexSpace (boxN k m) (boxL k m), IndexSpace (boxN k m) (boxL k m)) :=
  descendProd (IndexSpace.pt _ _)
    ((IndexSpace.proj _ _).comp
      ⟨fun p => ⟨((p.2 : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)).1,
          (1 - (p.1 : ℝ)) • (p.2 : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)).2),
          p.2.2.1, smul_mem_closedBall_one p.2.2.2 p.1⟩,
        Continuous.subtype_mk (by fun_prop) _⟩)
    fun s y hy => IndexSpace.proj_eq_pt ⟨hy.1, smul_mem_closedBall_one y.2.2 s⟩

theorem boxHomotopicRel : ((diskToBox k m).comp (boxToDisk k m)).HomotopicRel
    (ContinuousMap.id _) {IndexSpace.pt (boxN k m) (boxL k m)} := by
  refine ⟨ContinuousMap.HomotopyRel.symm
    { toFun := boxHom k m
      continuous_toFun := (boxHom k m).continuous
      map_zero_left := fun q => ?_
      map_one_left := fun q => ?_
      prop' := fun t q hq => ?_ }⟩
  · induction q using Quotient.inductionOn
    rename_i q
    rcases q with z | ⟨⟩
    · show IndexSpace.proj _ _ ⟨_, _⟩ = IndexSpace.proj _ _ z
      congr 1
      exact Subtype.ext (Prod.ext rfl (by simp))
    · rfl
  · induction q using Quotient.inductionOn
    rename_i q
    rcases q with z | ⟨⟩
    · show IndexSpace.proj _ _ ⟨_, _⟩ = IndexSpace.proj _ _ ⟨_, _⟩
      congr 1
      exact Subtype.ext (Prod.ext rfl (by simp))
    · rfl
  · rw [mem_singleton_iff.1 hq]
    rfl

noncomputable def boxDiskEquiv :
    PointedHomotopyEquiv (IndexSpace (boxN k m) (boxL k m)) (IndexSpace (diskD k) (diskS k))
      (IndexSpace.pt _ _) (IndexSpace.pt _ _) where
  toFun := boxToDisk k m
  invFun := diskToBox k m
  map_pt := rfl
  inv_pt := rfl
  left := boxHomotopicRel k m
  right := by rw [boxToDisk_diskToBox]; exact ContinuousMap.HomotopicRel.refl _

/-- `(D^k × D^m)/(S^{k-1} × D^m) ≃ S^k`. -/
noncomputable def boxEquiv :
    PointedHomotopyEquiv (IndexSpace (boxN k m) (boxL k m)) (Sphere k) (IndexSpace.pt _ _)
      (Sphere.pt k) :=
  (boxDiskEquiv k m).trans (diskEquiv k)

end Box

end ConleyCheck.Conley
