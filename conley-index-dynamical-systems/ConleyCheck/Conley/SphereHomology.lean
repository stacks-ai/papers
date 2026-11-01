import ConleyCheck.Conley.Deform
import ConleyCheck.Conley.Sphere

/-!
# The homology of spheres

`H̃_n(S^k; K) ≅ K` for `n = k` and `H̃_n(S^k; K) = 0` otherwise (`sphere_homology`), for every ring
`K`. Hence an isolated invariant set with Conley index `S^k` has `CH_*(S; K) = K[k]`
(`HasIndex.homologyIndex_sphere`).

The proof is by induction on the disk pairs `(D^m, S^{m-1}) ⊆ ℝ^m`, starting from
`(D^0, S^{-1}) = (pt, ∅)`, whose homology is the homology of a point (Mathlib, for totally
disconnected spaces).

* `disk_step`: `D^{m+1}` deforms to a point of `S^m`, so the connecting map of the triple
  `{q} ⊆ S^m ⊆ D^{m+1}` gives `H_{n+1}(D^{m+1}, S^m) ≅ H_n(S^m, {q})`.
* `hemisphere`: `H_n(S^m, {q}) ≅ H_n(D^m, S^{m-1})`. The cap `{x₀ > -1/2}` deforms to the north
  pole `q`, excision removes it except for the band `{-1/2 < x₀ ≤ 0}` of the lower hemisphere, the
  band deforms onto the equator, and the projection `(x₀, x') ↦ x'` maps the lower hemisphere and
  the equator homeomorphically onto `(D^m, S^{m-1})`.
-/

namespace ConleyCheck.Conley

open CategoryTheory Limits Set Metric Topology unitInterval WithLp

/-- `ℝ^m` with the Euclidean norm. -/
abbrev E (m : ℕ) : Type := EuclideanSpace ℝ (Fin m)

/-! ### Coordinates `x = (x₀, x')` -/

section Coords

variable {m : ℕ}

/-- `x ↦ x' = (x₁, …, x_m)`. -/
def tailE (x : E (m + 1)) : E m := toLp 2 fun j => x j.succ

theorem continuous_tailE : Continuous (tailE (m := m)) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => PiLp.continuous_apply 2 _ j.succ)

theorem eq_vcons (x : E (m + 1)) : x = vcons (x 0) (tailE x) := by
  apply WithLp.ofLp_injective 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [vcons, tailE]

theorem tailE_vcons (a : ℝ) (y : E m) : tailE (vcons a y) = y := by
  apply WithLp.ofLp_injective 2
  funext j
  simp [vcons, tailE]

theorem vcons_zero (a : ℝ) (y : E m) : vcons a y 0 = a := by simp [vcons]

theorem norm_sq_eq (x : E (m + 1)) : ‖x‖ ^ 2 = x 0 ^ 2 + ‖tailE x‖ ^ 2 := by
  conv_lhs => rw [eq_vcons x]
  exact norm_vcons_sq _ _

theorem continuous_coord0 : Continuous fun x : E (m + 1) => x 0 := PiLp.continuous_apply 2 _ 0

/-- The north pole `q = (1, 0, …, 0)`. -/
noncomputable abbrev npole (m : ℕ) : E (m + 1) := EuclideanSpace.single 0 1

theorem npole_eq : npole m = vcons 1 0 := vcons_one_zero.symm

theorem npole_mem : npole m ∈ sphere (0 : E (m + 1)) 1 := by simp

end Coords

/-! ### The point `D^0` -/

section Point

variable (K : Type) [Ring K]

instance : Unique (E 0) where
  default := 0
  uniq x := by
    apply WithLp.ofLp_injective 2
    funext i
    exact i.elim0

theorem closedBall_E0 : closedBall (0 : E 0) 1 = univ :=
  eq_univ_of_forall fun x => by rw [Subsingleton.elim x 0]; simp

theorem sphere_E0 : sphere (0 : E 0) 1 = ∅ :=
  eq_empty_of_forall_notMem fun x hx => by
    rw [Subsingleton.elim x 0, mem_sphere, dist_self] at hx
    exact zero_ne_one hx

theorem absH_E0_subsingleton {n : ℕ} (hn : n ≠ 0) : Subsingleton (absH K (E 0) n) :=
  (ModuleCat.isZero_iff_subsingleton).1
    (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{0} K) n (ModuleCat.of K K) (TopCat.of (E 0)) hn)

noncomputable def absH_E0_zero : absH K (E 0) 0 ≃ₗ[K] K :=
  ((AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace (ModuleCat.{0} K)
    (ModuleCat.of K K) (TopCat.of (E 0))) ≪≫
      coproductUniqueIso (fun _ : TopCat.of (E 0) => ModuleCat.of K K)).toLinearEquiv

/-- `H_*(D^m, S^{m-1}) ≅ K[m]`. -/
def DiskHom (m : ℕ) : Prop :=
  Nonempty (singH K (E m) (m : ℤ) (closedBall 0 1) (sphere 0 1) ≃ₗ[K] K) ∧
    ∀ n : ℤ, n ≠ m → Subsingleton (singH K (E m) n (closedBall 0 1) (sphere 0 1))

theorem diskHom_zero : DiskHom K 0 := by
  unfold DiskHom
  rw [closedBall_E0, sphere_E0]
  refine ⟨⟨(LinearEquiv.ofBijective _ (absToRel_bijective K (X := E 0) 0)).symm.trans
    (absH_E0_zero K)⟩, fun n hn => ?_⟩
  cases n with
  | ofNat n =>
    have hn' : n ≠ 0 := fun h => hn (by rw [h]; rfl)
    have := absH_E0_subsingleton K hn'
    exact (LinearEquiv.ofBijective _ (absToRel_bijective K (X := E 0) n)).symm.toEquiv.subsingleton
  | negSucc n => exact ⟨fun _ _ => Subsingleton.elim (α := PUnit) _ _⟩

end Point

/-! ### The disk step -/

section Disk

variable (K : Type) [Ring K]

theorem disk_step (m : ℕ) (k : ℤ) :
    Nonempty (singH K (E (m + 1)) (k + 1) (closedBall 0 1) (sphere 0 1) ≃ₗ[K]
      singH K (E (m + 1)) k (sphere 0 1) {npole m}) := by
  have hq : {npole m} ⊆ sphere (0 : E (m + 1)) 1 := singleton_subset_iff.2 npole_mem
  have hSD : sphere (0 : E (m + 1)) 1 ⊆ closedBall 0 1 := sphere_subset_closedBall
  have hqD := hq.trans hSD
  have hmem : ∀ (s : I) {x : E (m + 1)}, x ∈ closedBall 0 1 →
      (1 - (s : ℝ)) • x + (s : ℝ) • npole m ∈ closedBall (0 : E (m + 1)) 1 := fun s x hx =>
    convex_closedBall 0 1 hx (hqD rfl) (by linarith [s.2.2]) s.2.1 (by ring)
  let H : C(I × closedBall (0 : E (m + 1)) 1, closedBall (0 : E (m + 1)) 1) :=
    ⟨fun p => ⟨(1 - (p.1 : ℝ)) • (p.2 : E (m + 1)) + (p.1 : ℝ) • npole m, hmem p.1 p.2.2⟩, by
      refine Continuous.subtype_mk ?_ _
      fun_prop⟩
  have hs := singH_subsingleton_of_deform K hqD H
    (fun x => Subtype.ext (by simp [H]))
    (fun x => by simp [H])
    (fun s x hx => by
      rw [mem_singleton_iff] at hx ⊢
      show (1 - (s : ℝ)) • (x : E (m + 1)) + (s : ℝ) • npole m = npole m
      rw [hx, ← add_smul]
      simp)
  exact ⟨LinearEquiv.ofBijective _ (singδ_bijective_of_subsingleton K hq hSD hs k)⟩

end Disk

/-! ### The hemisphere step -/

section Hemisphere

variable {m : ℕ}

theorem sphere_coords {x : E (m + 1)} (hx : x ∈ sphere (0 : E (m + 1)) 1) :
    x 0 ^ 2 + ‖tailE x‖ ^ 2 = 1 := by
  rw [← norm_sq_eq, mem_sphere_zero_iff_norm.1 hx, one_pow]

theorem vcons_smul_mem {a c : ℝ} {y : E m} (hc : 0 ≤ c) (h : a ^ 2 + c * ‖y‖ ^ 2 = 1) :
    vcons a (√c • y) ∈ sphere (0 : E (m + 1)) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have h2 : ‖vcons a (√c • y)‖ ^ 2 = 1 := by
    rw [norm_vcons_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hc]
    exact h
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [h2, one_pow])

variable (m) in
/-- The cap `{x₀ > -1/2}` of `S^m`. -/
def capA : Set (E (m + 1)) := sphere 0 1 ∩ {x | -1 / 2 < x 0}

variable (m) in
/-- The band `{-1/2 < x₀ ≤ 0}` of `S^m`. -/
def bandB : Set (E (m + 1)) := sphere 0 1 ∩ {x | x 0 ≤ 0} ∩ {x | -1 / 2 < x 0}

/-- The new first coordinate and the scaling factor of the cap deformation. -/
noncomputable def capY (s : ℝ) (x : E (m + 1)) : ℝ := x 0 + s * (1 - x 0)

noncomputable def capC (s : ℝ) (x : E (m + 1)) : ℝ := (1 - s) * (1 + capY s x) / (1 + x 0)

theorem cap_mem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {x : E (m + 1)} (hx : x ∈ capA m) :
    vcons (capY s x) (√(capC s x) • tailE x) ∈ capA m := by
  obtain ⟨hS, hx0⟩ := hx
  have hc := sphere_coords hS
  have h1 : x 0 ≤ 1 := by nlinarith [sq_nonneg (‖tailE x‖)]
  have hd : 0 < 1 + x 0 := by linarith [hx0.out]
  have hy : x 0 ≤ capY s x := by
    simp only [capY]; nlinarith [hs.1]
  have hcn : 0 ≤ capC s x := div_nonneg (mul_nonneg (by linarith [hs.2]) (by linarith)) hd.le
  refine ⟨vcons_smul_mem hcn ?_, ?_⟩
  · have ht : ‖tailE x‖ ^ 2 = (1 - x 0) * (1 + x 0) := by linarith
    rw [ht, capC]
    field_simp
    simp only [capY]
    ring
  · show -1 / 2 < vcons (capY s x) (√(capC s x) • tailE x) 0
    rw [vcons_zero]
    exact lt_of_lt_of_le hx0 hy

theorem continuous_capMap :
    Continuous fun p : I × capA m =>
      vcons (capY (p.1 : ℝ) (p.2 : E (m + 1))) (√(capC (p.1 : ℝ) (p.2 : E (m + 1))) •
        tailE (p.2 : E (m + 1))) := by
  have h0 : Continuous fun p : I × capA m => (p.2 : E (m + 1)) 0 :=
    continuous_coord0.comp (continuous_subtype_val.comp continuous_snd)
  have hsv : Continuous fun p : I × capA m => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hy : Continuous fun p : I × capA m => capY (p.1 : ℝ) (p.2 : E (m + 1)) := by
    simp only [capY]; fun_prop
  have hc : Continuous fun p : I × capA m => √(capC (p.1 : ℝ) (p.2 : E (m + 1))) := by
    refine Real.continuous_sqrt.comp ?_
    simp only [capC]
    refine Continuous.div (by fun_prop) (by fun_prop) fun p => ?_
    have := p.2.2.2
    exact (show (0 : ℝ) < 1 + (p.2 : E (m + 1)) 0 by linarith [this.out]).ne'
  have ht : Continuous fun p : I × capA m => tailE (p.2 : E (m + 1)) :=
    continuous_tailE.comp (continuous_subtype_val.comp continuous_snd)
  exact continuous_vcons hy (hc.smul ht)

/-- The cap `{x₀ > -1/2}` deforms to the north pole along the meridians. -/
noncomputable def capMap : C(I × capA m, capA m) :=
  ⟨fun p => ⟨_, cap_mem p.1.2 p.2.2⟩, continuous_capMap.subtype_mk _⟩

theorem capMap_zero (x : capA m) : capMap (0, x) = x := by
  apply Subtype.ext
  show vcons (capY 0 (x : E (m + 1))) (√(capC 0 (x : E (m + 1))) • tailE (x : E (m + 1))) = x
  have hd : 0 < 1 + (x : E (m + 1)) 0 := by linarith [x.2.2.out]
  have : capC 0 (x : E (m + 1)) = 1 := by
    simp only [capC, capY]; field_simp; ring
  rw [this, Real.sqrt_one, one_smul]
  simp only [capY, zero_mul, add_zero]
  exact (eq_vcons _).symm

theorem capMap_one (x : capA m) : (capMap (1, x) : E (m + 1)) = npole m := by
  show vcons (capY 1 (x : E (m + 1))) (√(capC 1 (x : E (m + 1))) • tailE (x : E (m + 1))) = _
  have h1 : capY 1 (x : E (m + 1)) = 1 := by simp only [capY]; ring
  have h2 : capC 1 (x : E (m + 1)) = 0 := by simp only [capC]; ring
  rw [h1, h2, Real.sqrt_zero, zero_smul, npole_eq]

theorem tailE_npole : tailE (npole m) = 0 := by rw [npole_eq, tailE_vcons]

theorem capMap_npole (s : I) (x : capA m) (hx : (x : E (m + 1)) = npole m) :
    (capMap (s, x) : E (m + 1)) = npole m := by
  show vcons (capY (s : ℝ) (x : E (m + 1))) (√(capC (s : ℝ) (x : E (m + 1))) •
    tailE (x : E (m + 1))) = _
  have h0 : (x : E (m + 1)) 0 = 1 := by rw [hx]; simp
  have h1 : capY (s : ℝ) (x : E (m + 1)) = 1 := by simp only [capY, h0]; ring
  rw [h1, hx, tailE_npole, smul_zero, npole_eq]

/-- The band deformation: `x₀ ↦ (1 - s) x₀`, rescaling `x'` to stay on the sphere. -/
noncomputable def bandC (s : ℝ) (x : E (m + 1)) : ℝ :=
  (1 - ((1 - s) * x 0) ^ 2) / (1 - x 0 ^ 2)

theorem band_mem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {x : E (m + 1)} (hx : x ∈ bandB m) :
    vcons ((1 - s) * x 0) (√(bandC s x) • tailE x) ∈ bandB m := by
  obtain ⟨⟨hS, hx1⟩, hx2⟩ := hx
  have hx1' : x 0 ≤ 0 := hx1
  have hx2' : -1 / 2 < x 0 := hx2
  have hc := sphere_coords hS
  have hd : 0 < 1 - x 0 ^ 2 := by nlinarith
  have hs0 : 0 ≤ 1 - s := by linarith [hs.2]
  have hs1 : 1 - s ≤ 1 := by linarith [hs.1]
  have hy1 : x 0 ≤ (1 - s) * x 0 := by nlinarith
  have hy2 : (1 - s) * x 0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs0 hx1'
  have hcn : 0 ≤ bandC s x := div_nonneg (by nlinarith) hd.le
  refine ⟨⟨vcons_smul_mem hcn ?_, ?_⟩, ?_⟩
  · have ht : ‖tailE x‖ ^ 2 = 1 - x 0 ^ 2 := by linarith
    rw [ht, bandC, div_mul_cancel₀ _ hd.ne']
    ring
  · show vcons ((1 - s) * x 0) (√(bandC s x) • tailE x) 0 ≤ 0
    rw [vcons_zero]; exact hy2
  · show -1 / 2 < vcons ((1 - s) * x 0) (√(bandC s x) • tailE x) 0
    rw [vcons_zero]; linarith

theorem continuous_bandMap :
    Continuous fun p : I × bandB m =>
      vcons ((1 - (p.1 : ℝ)) * (p.2 : E (m + 1)) 0) (√(bandC (p.1 : ℝ) (p.2 : E (m + 1))) •
        tailE (p.2 : E (m + 1))) := by
  have h0 : Continuous fun p : I × bandB m => (p.2 : E (m + 1)) 0 :=
    continuous_coord0.comp (continuous_subtype_val.comp continuous_snd)
  have hsv : Continuous fun p : I × bandB m => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hc : Continuous fun p : I × bandB m => √(bandC (p.1 : ℝ) (p.2 : E (m + 1))) := by
    refine Real.continuous_sqrt.comp ?_
    simp only [bandC]
    refine Continuous.div (by fun_prop) (by fun_prop) fun p => ?_
    obtain ⟨⟨hS, hx1⟩, hx2⟩ := p.2.2
    have hx1' : (p.2 : E (m + 1)) 0 ≤ 0 := hx1
    have hx2' : -1 / 2 < (p.2 : E (m + 1)) 0 := hx2
    nlinarith
  have ht : Continuous fun p : I × bandB m => tailE (p.2 : E (m + 1)) :=
    continuous_tailE.comp (continuous_subtype_val.comp continuous_snd)
  exact continuous_vcons (by fun_prop) (hc.smul ht)

noncomputable def bandMap : C(I × bandB m, bandB m) :=
  ⟨fun p => ⟨_, band_mem p.1.2 p.2.2⟩, continuous_bandMap.subtype_mk _⟩

theorem bandMap_zero (x : bandB m) : bandMap (0, x) = x := by
  apply Subtype.ext
  show vcons ((1 - 0) * (x : E (m + 1)) 0) (√(bandC 0 (x : E (m + 1))) • tailE (x : E (m + 1))) = x
  obtain ⟨⟨hS, hx1⟩, hx2⟩ := x.2
  have hx2' : -1 / 2 < (x : E (m + 1)) 0 := hx2
  have hx1' : (x : E (m + 1)) 0 ≤ 0 := hx1
  have hd : 0 < 1 - (x : E (m + 1)) 0 ^ 2 := by nlinarith
  have : bandC 0 (x : E (m + 1)) = 1 := by
    simp only [bandC, sub_zero, one_mul]; exact div_self hd.ne'
  rw [this, Real.sqrt_one, one_smul, sub_zero, one_mul]
  exact (eq_vcons _).symm

theorem bandMap_one (x : bandB m) : (bandMap (1, x) : E (m + 1)) 0 = 0 := by
  show vcons ((1 - 1) * (x : E (m + 1)) 0) _ 0 = 0
  rw [vcons_zero]; ring

theorem bandMap_eq (s : I) (x : bandB m) (hx : (x : E (m + 1)) 0 = 0) :
    (bandMap (s, x) : E (m + 1)) 0 = 0 := by
  show vcons ((1 - (s : ℝ)) * (x : E (m + 1)) 0) _ 0 = 0
  rw [vcons_zero, hx, mul_zero]

/-- The lower hemisphere over `D^m`. -/
noncomputable def lowerLift (y : E m) : E (m + 1) := vcons (-√(1 - ‖y‖ ^ 2)) y

theorem continuous_lowerLift : Continuous (lowerLift (m := m)) :=
  continuous_vcons (by fun_prop) continuous_id

variable (K : Type) [Ring K]

variable (m) in
theorem hemisphere (k : ℤ) :
    Nonempty (singH K (E (m + 1)) k (sphere 0 1) {npole m} ≃ₗ[K]
      singH K (E m) k (closedBall 0 1) (sphere 0 1)) := by
  set S : Set (E (m + 1)) := sphere 0 1
  set Lo : Set (E (m + 1)) := S ∩ {x | x 0 ≤ 0}
  set Eq : Set (E (m + 1)) := S ∩ {x | x 0 = 0}
  have hAS : capA m ⊆ S := fun x hx => hx.1
  have hpA : {npole m} ⊆ capA m := singleton_subset_iff.2 ⟨npole_mem, by simp; norm_num⟩
  have hLoS : Lo ⊆ S := fun x hx => hx.1
  have hBLo : bandB m ⊆ Lo := fun x hx => hx.1
  have hEB : Eq ⊆ bandB m := fun x hx =>
    ⟨⟨hx.1, le_of_eq hx.2⟩, show -1 / 2 < x 0 by rw [hx.2]; norm_num⟩
  -- the cap deforms to the north pole
  have hs1 := singH_subsingleton_of_deform K hpA capMap capMap_zero
    (fun x => capMap_one x)
    (fun s x hx => capMap_npole s x (mem_singleton_iff.1 hx))
  have b1 := singIncl_bijective_of_subsingleton K hpA hAS hs1 k
  -- excision of the upper part
  have b2 := excision K hAS hLoS (isOpen_lt continuous_const continuous_coord0 :
      IsOpen {x : E (m + 1) | -1 / 2 < x 0})
    (isOpen_lt continuous_coord0 continuous_const : IsOpen {x : E (m + 1) | x 0 < 0})
    (fun x _ => by
      by_cases h : x 0 < 0
      · exact Or.inr h
      · exact Or.inl (show -1 / 2 < x 0 by linarith [not_lt.1 h]))
    (fun x hx => ⟨hx.2, hx.1⟩) (fun x hx => ⟨hx.2, show x 0 ≤ 0 from le_of_lt hx.1⟩) k
  -- `H_*(Lo, A) = H_*(Lo, band)`
  have b3 := singMap_bijective K (ContinuousMap.id (E (m + 1))) (B := Lo) (A := capA m)
    (B' := Lo) (A' := bandB m) (fun x hx => hx) (fun y hy => ⟨y, hy, rfl⟩)
    IsEmbedding.subtypeVal
    (fun x hx => ⟨fun h => ⟨hx, h.2⟩, fun h => ⟨hx.1, h.2⟩⟩) k
  -- the band deforms onto the equator
  have hs2 := singH_subsingleton_of_deform K hEB bandMap bandMap_zero
    (fun x => ⟨(bandMap (1, x)).2.1.1, bandMap_one x⟩)
    (fun s x hx => ⟨(bandMap (s, x)).2.1.1, bandMap_eq s x hx.2⟩)
  have b4 := singIncl_bijective_of_subsingleton K hEB hBLo hs2 k
  -- the projection onto `(D^m, S^{m-1})`
  have hLo : ∀ x ∈ Lo, lowerLift (tailE x) = x := by
    intro x hx
    have hc := sphere_coords hx.1
    have hx0 : x 0 ≤ 0 := hx.2
    have h1 : 1 - ‖tailE x‖ ^ 2 = x 0 ^ 2 := by linarith
    rw [lowerLift, h1, Real.sqrt_sq_eq_abs, abs_of_nonpos hx0, neg_neg]
    exact (eq_vcons x).symm
  have hemb : IsEmbedding (Lo.domRestrict tailE) := by
    refine IsEmbedding.of_comp (continuous_tailE.comp continuous_subtype_val) continuous_lowerLift
      ?_
    have e : lowerLift ∘ Lo.domRestrict tailE = Subtype.val := funext fun x => hLo x x.2
    rw [e]
    exact IsEmbedding.subtypeVal
  have b5 := singMap_bijective K ⟨tailE, continuous_tailE⟩ (B := Lo) (A := Eq)
    (B' := closedBall 0 1) (A' := sphere 0 1)
    (fun x hx => by
      have hc := sphere_coords hx.1
      rw [mem_closedBall_zero_iff]
      show ‖tailE x‖ ≤ 1
      have : ‖tailE x‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x 0)]
      nlinarith [norm_nonneg (tailE x)])
    (fun y hy => by
      have hy1 : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.1 hy
      have hn : 0 ≤ 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
      refine ⟨lowerLift y, ⟨?_, ?_⟩, tailE_vcons _ _⟩
      · rw [lowerLift, mem_sphere_zero_iff_norm]
        have h2 : ‖vcons (-√(1 - ‖y‖ ^ 2)) y‖ ^ 2 = 1 := by
          rw [norm_vcons_sq, neg_sq, Real.sq_sqrt hn]; ring
        exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [h2, one_pow])
      · show lowerLift y 0 ≤ 0
        rw [lowerLift, vcons_zero]
        exact neg_nonpos.2 (Real.sqrt_nonneg _))
    hemb
    (fun x hx => by
      have hc := sphere_coords hx.1
      show x ∈ Eq ↔ tailE x ∈ sphere 0 1
      rw [mem_sphere_zero_iff_norm]
      constructor
      · intro h
        have h0 : x 0 = 0 := h.2
        rw [h0] at hc
        have : ‖tailE x‖ ^ 2 = 1 ^ 2 := by linarith
        exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 this
      · intro h
        rw [h] at hc
        exact ⟨hx.1, show x 0 = 0 by nlinarith⟩) k
  exact ⟨(LinearEquiv.ofBijective _ b1).trans ((LinearEquiv.ofBijective _ b2).symm.trans
    ((LinearEquiv.ofBijective _ b3).trans ((LinearEquiv.ofBijective _ b4).symm.trans
    (LinearEquiv.ofBijective _ b5))))⟩

end Hemisphere

/-! ### Disks and spheres -/

section Main

variable (K : Type) [Ring K]

theorem diskHom (m : ℕ) : DiskHom K m := by
  induction m with
  | zero => exact diskHom_zero K
  | succ m ih =>
    obtain ⟨⟨e⟩, hz⟩ := ih
    refine ⟨?_, fun n hn => ?_⟩
    · obtain ⟨e1⟩ := disk_step K m (m : ℤ)
      obtain ⟨e2⟩ := hemisphere m K (m : ℤ)
      rw [Nat.cast_succ]
      exact ⟨e1.trans (e2.trans e)⟩
    · obtain ⟨k, rfl⟩ := exists_succ n
      have hk : k ≠ m := fun h => hn (by rw [h, Nat.cast_succ])
      obtain ⟨e1⟩ := disk_step K m k
      obtain ⟨e2⟩ := hemisphere m K k
      have := hz k hk
      exact (e1.trans e2).toEquiv.subsingleton

/-- `H_n(S^m, {q}) ≅ H̃_n(S^m)` in the type `Sphere m`, transported to `ℝ^{m+1}`. -/
theorem sphere_rel (m n : ℕ) :
    Nonempty (redH K (Sphere m) (Sphere.pt m) n ≃ₗ[K]
      singH K (E (m + 1)) (Int.ofNat n) (sphere 0 1) {npole m}) := by
  have b := singMap_bijective K (⟨Subtype.val, continuous_subtype_val⟩ : C(Sphere m, E (m + 1)))
    (B := univ) (A := {Sphere.pt m}) (B' := sphere 0 1) (A' := {npole m})
    (fun x _ => x.2) (fun y hy => ⟨⟨y, hy⟩, trivial, rfl⟩)
    (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
    (fun x _ => by
      rw [mem_singleton_iff, mem_singleton_iff, Subtype.ext_iff]
      rfl) (Int.ofNat n)
  exact ⟨(redHEquiv K (Sphere.pt m) n).trans (LinearEquiv.ofBijective _ b)⟩

/-- The homology of spheres, `H̃_*(S^m; K) ≅ K[m]`. -/
theorem sphere_homology (m : ℕ) :
    Nonempty (redH K (Sphere m) (Sphere.pt m) m ≃ₗ[K] K) ∧
      ∀ n : ℕ, n ≠ m → Subsingleton (redH K (Sphere m) (Sphere.pt m) n) := by
  obtain ⟨⟨e⟩, hz⟩ := diskHom K m
  refine ⟨?_, fun n hn => ?_⟩
  · obtain ⟨e1⟩ := sphere_rel K m m
    obtain ⟨e2⟩ := hemisphere m K (Int.ofNat m)
    exact ⟨e1.trans (e2.trans e)⟩
  · obtain ⟨e1⟩ := sphere_rel K m n
    obtain ⟨e2⟩ := hemisphere m K (Int.ofNat n)
    have := hz (Int.ofNat n) (fun h => hn (Int.ofNat.inj h))
    exact (e1.trans e2).toEquiv.subsingleton

/-- An isolated invariant set with Conley index `S^k` has `CH_*(S; K) = K[k]`. -/
theorem HasIndex.homologyIndex_sphere {α : Type} [TopologicalSpace α] [T2Space α]
    {ϕ : Flow ℝ α} {S : Set α} (hS : IsIsolatedInvariantSet ϕ S) {k : ℕ}
    (h : HasIndex ϕ S (Sphere k) (Sphere.pt k)) :
    Nonempty (homologyIndex K ϕ hS k ≃ₗ[K] K) ∧
      ∀ n : ℕ, n ≠ k → Subsingleton (homologyIndex K ϕ hS n) := by
  obtain ⟨N, L, hP, ⟨e⟩⟩ := h
  have iso : ∀ n, homologyIndex K ϕ hS n ≃ₗ[K] redH K (Sphere k) (Sphere.pt k) n := fun n =>
    ((homologyIndexIso K hS hP n).some ≪≫ redIso K e n).toLinearEquiv
  obtain ⟨⟨e0⟩, hz⟩ := sphere_homology K k
  refine ⟨⟨(iso k).trans e0⟩, fun n hn => ?_⟩
  have := hz n hn
  exact (iso n).toEquiv.subsingleton

end Main

end ConleyCheck.Conley

namespace ConleyCheck.Conley

theorem HasIndex.isIsolated {α X : Type*} [TopologicalSpace α] [TopologicalSpace X]
    {ϕ : Flow ℝ α} {S : Set α} {x₀ : X} (h : HasIndex ϕ S X x₀) : IsIsolatedInvariantSet ϕ S :=
  let ⟨_, _, hP, _⟩ := h
  hP.isIsolatedInvariantSet

/-- `h(S) = S^k` gives `CH_*(S; K) = K[k]`, with the isolation of `S` read off from the index
pair. -/
theorem HasIndex.homologyIndex_sphere' (K : Type) [Ring K] {α : Type} [TopologicalSpace α]
    [T2Space α] {ϕ : Flow ℝ α} {S : Set α} {k : ℕ} (h : HasIndex ϕ S (Sphere k) (Sphere.pt k)) :
    Nonempty (homologyIndex K ϕ h.isIsolated k ≃ₗ[K] K) ∧
      ∀ n : ℕ, n ≠ k → Subsingleton (homologyIndex K ϕ h.isIsolated n) :=
  HasIndex.homologyIndex_sphere K h.isIsolated h

end ConleyCheck.Conley
