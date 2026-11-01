import ConleyCheck.Conley.Chains

/-!
# Barycentric subdivision

Linear chains `LC K k m` are finitely supported functions on `(k+1)`-tuples of points of `Δ^m`,
namely formal combinations of affine simplices `linC w : Δ^k → Δ^m`. On them we define the cone
`cone b`, the subdivision `SL` and the chain homotopy `TL` (Hatcher, §2.1), with
`∂ SL = SL ∂` and `∂ TL + TL ∂ = 1 - SL`. A singular simplex `σ : Δ^m → X` acts on linear chains
by precomposition (`act σ`), which turns these operators into the subdivision operator `SdF` and
the homotopy `TF` on singular chains. Iterated subdivision makes simplices small
(`sdF_iterate_small`).
-/

namespace ConleyCheck.Conley

open Convexity Set

universe u

/-! ### Affine simplices -/

/-- Barycentric coordinates. -/
def ew {m : ℕ} (x : Dl m) : Fin (m + 1) → ℝ := fun j => x.weights j

theorem isEmbedding_ew (m : ℕ) : Topology.IsEmbedding (ew : Dl m → Fin (m + 1) → ℝ) :=
  StdSimplex.isEmbedding_toFun_comp_weights ℝ _

theorem continuous_weights {m : ℕ} (j : Fin (m + 1)) : Continuous fun x : Dl m => x.weights j :=
  (continuous_apply j).comp (isEmbedding_ew m).continuous

theorem ew_affineMapMk {k m : ℕ} (w : Fin (k + 1) → Dl m) (t : Dl k) :
    ew (StdSimplex.affineMapMk (R := ℝ) w t) = ∑ i, t.weights i • ew (w i) := by
  have h := (StdSimplex.isAffineMap_weights (R := ℝ) (I := Fin (m + 1))).map_iConvexComb t w
  rw [StdSimplex.affineMapMk_apply]
  ext j
  simp only [ew, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (StdSimplex.iConvexComb t w).weights = _ from h, iConvexComb_eq_sum,
    Finsupp.sum_fintype _ _ (by simp)]
  simp [Finsupp.finset_sum_apply]

/-- The affine simplex with vertices `w`. -/
noncomputable def linC {k m : ℕ} (w : Fin (k + 1) → Dl m) : C(Dl k, Dl m) where
  toFun := StdSimplex.affineMapMk w
  continuous_toFun := by
    rw [(isEmbedding_ew m).continuous_iff]
    have : (ew ∘ fun t => StdSimplex.affineMapMk (R := ℝ) w t) =
        fun t : Dl k => ∑ i, t.weights i • ew (w i) := funext (ew_affineMapMk w)
    rw [this]
    exact continuous_finset_sum _ fun i _ => (continuous_weights i).smul continuous_const

theorem linC_apply {k m : ℕ} (w : Fin (k + 1) → Dl m) (t : Dl k) :
    linC w t = StdSimplex.affineMapMk w t := rfl

theorem linC_single {k m : ℕ} (w : Fin (k + 1) → Dl m) (i : Fin (k + 1)) :
    linC w (StdSimplex.single i) = w i :=
  StdSimplex.affineMapMk_single (R := ℝ) w i

theorem linC_comp {k m p : ℕ} (u : Fin (m + 1) → Dl p) (w : Fin (k + 1) → Dl m) :
    (linC u).comp (linC w) = linC (linC u ∘ w) := by
  ext1 t
  exact congrArg (fun f => f t) (StdSimplex.comp_affineMapMk (StdSimplex.affineMapMk u) w)

/-- The vertices of `Δ^k`. -/
noncomputable def vert (k : ℕ) : Fin (k + 1) → Dl k := fun i => StdSimplex.single i

theorem linC_vert (k : ℕ) : linC (vert k) = ContinuousMap.id _ := by
  ext1 t
  exact StdSimplex.iConvexComb_single t

theorem linC_comp_vert {k m : ℕ} (w : Fin (k + 1) → Dl m) : linC w ∘ vert k = w :=
  funext (linC_single w)

theorem linC_face {k m : ℕ} (w : Fin (k + 2) → Dl m) (i : Fin (k + 2)) :
    (linC w).comp (faceC i) = linC (w ∘ i.succAbove) := by
  have : (StdSimplex.affineMapMk (R := ℝ) w).comp (StdSimplex.affineMap i.succAbove) =
      StdSimplex.affineMapMk (w ∘ i.succAbove) := by
    refine StdSimplex.affineMap_ext fun j => ?_
    simp [StdSimplex.map_single]
  ext1 t
  exact congrArg (fun f => f t) this

theorem linC_injective {k m : ℕ} : Function.Injective (linC : (Fin (k + 1) → Dl m) → _) :=
  fun w w' h => by
    rw [← linC_comp_vert w, ← linC_comp_vert w', h]

/-- The barycenter of an affine simplex. -/
noncomputable def bary {k m : ℕ} (v : Fin (k + 1) → Dl m) : Dl m :=
  linC v StdSimplex.barycenter

theorem bary_mem {k m : ℕ} (v : Fin (k + 1) → Dl m) : bary v ∈ range (linC v) := ⟨_, rfl⟩

theorem linC_bary {k m p : ℕ} (u : Fin (m + 1) → Dl p) (v : Fin (k + 1) → Dl m) :
    linC u (bary v) = bary (linC u ∘ v) := by
  rw [bary, ← ContinuousMap.comp_apply, linC_comp, bary]

/-! ### Linear chains -/

variable (K : Type u) [Ring K]

/-- Linear `k`-chains in `Δ^m`. -/
abbrev LC (k m : ℕ) : Type u := (Fin (k + 1) → Dl m) →₀ K

/-- The boundary of linear chains. -/
noncomputable def dL (k m : ℕ) : LC K (k + 1) m →ₗ[K] LC K k m :=
  Finsupp.linearCombination K fun v =>
    ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (v ∘ i.succAbove) (1 : K)

/-- The cone from a point `b`. -/
noncomputable def cone {m : ℕ} (b : Dl m) (k : ℕ) : LC K k m →ₗ[K] LC K (k + 1) m :=
  Finsupp.lmapDomain K K fun v : Fin (k + 1) → Dl m => (Fin.cons b v : Fin (k + 2) → Dl m)

/-- The image of linear chains under an affine map `Δ^m → Δ^p`. -/
noncomputable def push {m p : ℕ} (g : Dl m → Dl p) (k : ℕ) : LC K k m →ₗ[K] LC K k p :=
  Finsupp.lmapDomain K K (g ∘ ·)

/-- The sum of the coefficients of a `0`-chain. -/
noncomputable def aug (m : ℕ) : LC K 0 m →ₗ[K] K := Finsupp.linearCombination K fun _ => 1

/-- A singular simplex `σ : Δ^m → X` acting on linear chains in `Δ^m`. -/
noncomputable def act {X : TopCat.{u}} {m : ℕ} (σ : Simp X m) (k : ℕ) :
    LC K k m →ₗ[K] (Simp X k →₀ K) :=
  Finsupp.lmapDomain K K fun w => σ.comp (linC w)

variable {K}

theorem dL_single {k m : ℕ} (v : Fin (k + 2) → Dl m) (c : K) :
    dL K k m (Finsupp.single v c) =
      ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (v ∘ i.succAbove) c := by
  simp only [dL, Finsupp.linearCombination_single, Finset.smul_sum, smul_comm c,
    Finsupp.smul_single, smul_eq_mul, mul_one]

theorem act_single {X : TopCat.{u}} {m k : ℕ} (σ : Simp X m) (w : Fin (k + 1) → Dl m) (c : K) :
    act K σ k (Finsupp.single w c) = Finsupp.single (σ.comp (linC w)) c := by
  simp [act]

theorem act_vert {X : TopCat.{u}} {k : ℕ} (σ : Simp X k) (c : K) :
    act K σ k (Finsupp.single (vert k) c) = Finsupp.single σ c := by
  rw [act_single, linC_vert, ContinuousMap.comp_id]

theorem dF_act {X : TopCat.{u}} {m k : ℕ} (σ : Simp X m) (c : LC K (k + 1) m) :
    dF K X k (act K σ (k + 1) c) = act K σ k (dL K k m c) := by
  have : dF K X k ∘ₗ act K σ (k + 1) = act K σ k ∘ₗ dL K k m := by
    refine Finsupp.lhom_ext fun w c => ?_
    simp only [LinearMap.comp_apply, act_single, dL_single, map_sum, map_zsmul, dF,
      Finsupp.linearCombination_single, Finset.smul_sum, ContinuousMap.comp_assoc, linC_face]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm, Finsupp.smul_single, smul_eq_mul, mul_one]
  exact congrArg (fun φ => φ c) this

theorem act_push {X : TopCat.{u}} {m p k : ℕ} (σ : Simp X p) (u : Fin (m + 1) → Dl p)
    (c : LC K k m) : act K σ k (push K (linC u) k c) = act K (σ.comp (linC u)) k c := by
  simp only [act, push, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  congr 1
  funext w
  simp [ContinuousMap.comp_assoc, linC_comp]

theorem dL_push {m p k : ℕ} (g : Dl m → Dl p) (c : LC K (k + 1) m) :
    dL K k p (push K g (k + 1) c) = push K g k (dL K k m c) := by
  have : dL K k p ∘ₗ push K g (k + 1) = push K g k ∘ₗ dL K k m := by
    refine Finsupp.lhom_ext fun w c => ?_
    simp only [LinearMap.comp_apply, push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      dL_single, map_sum, map_zsmul]
    rfl
  exact congrArg (fun φ => φ c) this

theorem cone_push {m p k : ℕ} (g : Dl m → Dl p) (b : Dl m) (c : LC K k m) :
    cone K (g b) k (push K g k c) = push K g (k + 1) (cone K b k c) := by
  simp only [cone, push, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  congr 1
  funext w
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem act_injective {k m : ℕ} :
    Function.Injective (act K (X := TopCat.of (ULift.{u} (Dl m)))
      ⟨ULift.up, continuous_uliftUp⟩ k) := by
  refine Finsupp.mapDomain_injective fun w w' h => linC_injective ?_
  ext1 t
  exact congrArg ULift.down (DFunLike.congr_fun h t)

theorem dF_dF {X : TopCat.{u}} {n : ℕ} (g : Simp X (n + 2) →₀ K) :
    dF K X n (dF K X (n + 1) g) = 0 := by
  apply (bas_bijective (K := K) X n).1
  rw [← bas_d, ← bas_d, map_zero]
  have := congrArg (fun φ => φ.hom (bas K X (n + 2) g))
    (HomologicalComplex.d_comp_d ((singFunctor K).obj X) (n + 2) (n + 1) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at this
  exact this

theorem dL_dL {k m : ℕ} (c : LC K (k + 2) m) : dL K k m (dL K (k + 1) m c) = 0 := by
  apply act_injective (K := K)
  rw [← dF_act, ← dF_act, dF_dF, map_zero]

theorem cone_single {m k : ℕ} (b : Dl m) (v : Fin (k + 1) → Dl m) (c : K) :
    cone K b k (Finsupp.single v c) = Finsupp.single (Fin.cons b v : Fin (k + 2) → Dl m) c := by
  simp [cone]

theorem push_single {m p k : ℕ} (g : Dl m → Dl p) (v : Fin (k + 1) → Dl m) (c : K) :
    push K g k (Finsupp.single v c) = Finsupp.single (g ∘ v) c := by
  simp [push]

theorem dL_cone_succ {m k : ℕ} (b : Dl m) (c : LC K (k + 1) m) :
    dL K (k + 1) m (cone K b (k + 1) c) = c - cone K b k (dL K k m c) := by
  have : dL K (k + 1) m ∘ₗ cone K b (k + 1) = LinearMap.id - cone K b k ∘ₗ dL K k m := by
    refine Finsupp.lhom_ext fun v c => ?_
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, cone_single,
      dL_single, map_sum, map_zsmul, Fin.sum_univ_succ (n := k + 2)]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.cons_comp_succ,
      Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib,
      Fin.cons_comp_succ_succAbove, cone_single]
    abel
  exact congrArg (fun φ => φ c) this

theorem sum_fin_two' {M : Type*} [AddCommMonoid M] (f : Fin (0 + 2) → M) :
    ∑ i, f i = f 0 + f 1 :=
  Fin.sum_univ_two f

theorem dL_cone_zero {m : ℕ} (b : Dl m) (c : LC K 0 m) :
    dL K 0 m (cone K b 0 c) = c - aug K m c • Finsupp.single (fun _ => b) 1 := by
  have : dL K 0 m ∘ₗ cone K b 0 =
      LinearMap.id - (LinearMap.toSpanSingleton K _ (Finsupp.single (fun _ => b) 1)) ∘ₗ aug K m := by
    refine Finsupp.lhom_ext fun v c => ?_
    have h0 : (Fin.cons b v : Fin (0 + 2) → Dl m) ∘ (0 : Fin (0 + 2)).succAbove = v := by
      funext i; fin_cases i; rfl
    have h1 : (Fin.cons b v : Fin (0 + 2) → Dl m) ∘ (1 : Fin (0 + 2)).succAbove = fun _ => b := by
      funext i; fin_cases i; rfl
    rw [LinearMap.comp_apply, cone_single, dL_single, sum_fin_two', h0, h1]
    simp [aug, sub_eq_add_neg]
  exact congrArg (fun φ => φ c) this

theorem aug_dL {m : ℕ} (c : LC K 1 m) : aug K m (dL K 0 m c) = 0 := by
  have : aug K m ∘ₗ dL K 0 m = 0 := by
    refine Finsupp.lhom_ext fun v c => ?_
    rw [LinearMap.comp_apply, dL_single, sum_fin_two', map_add, map_zsmul, map_zsmul]
    simp [aug]
  exact congrArg (fun φ => φ c) this

/-! ### Subdivision and the chain homotopy -/

variable (K)

/-- Barycentric subdivision of linear chains. -/
noncomputable def SL (m : ℕ) : ∀ k, LC K k m →ₗ[K] LC K k m
  | 0 => LinearMap.id
  | k + 1 => Finsupp.linearCombination K fun v =>
      cone K (bary v) k (SL m k (dL K k m (Finsupp.single v 1)))

/-- The chain homotopy between the identity and `SL`. -/
noncomputable def TL (m : ℕ) : ∀ k, LC K k m →ₗ[K] LC K (k + 1) m
  | 0 => 0
  | k + 1 => Finsupp.linearCombination K fun v =>
      cone K (bary v) (k + 1) (Finsupp.single v 1 - TL m k (dL K k m (Finsupp.single v 1)))

variable {K}

theorem SL_zero {m : ℕ} (c : LC K 0 m) : SL K m 0 c = c := rfl

theorem SL_succ_single {m k : ℕ} (v : Fin (k + 2) → Dl m) :
    SL K m (k + 1) (Finsupp.single v 1) =
      cone K (bary v) k (SL K m k (dL K k m (Finsupp.single v 1))) := by
  simp [SL]

theorem TL_zero {m : ℕ} (c : LC K 0 m) : TL K m 0 c = 0 := rfl

theorem TL_succ_single {m k : ℕ} (v : Fin (k + 2) → Dl m) :
    TL K m (k + 1) (Finsupp.single v 1) = cone K (bary v) (k + 1)
      (Finsupp.single v 1 - TL K m k (dL K k m (Finsupp.single v 1))) := by
  simp [TL]

theorem lc_ext {ι M : Type*} [AddCommGroup M] [Module K M] {f g : (ι →₀ K) →ₗ[K] M}
    (h : ∀ v, f (Finsupp.single v 1) = g (Finsupp.single v 1)) : f = g :=
  Finsupp.lhom_ext' fun v => LinearMap.ext_ring (h v)

theorem dL_SL {m : ℕ} : ∀ (k : ℕ) (c : LC K (k + 1) m),
    dL K k m (SL K m (k + 1) c) = SL K m k (dL K k m c)
  | 0, c => by
    have : dL K 0 m ∘ₗ SL K m 1 = SL K m 0 ∘ₗ dL K 0 m := lc_ext fun v => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, SL_succ_single, dL_cone_zero, SL_zero,
        aug_dL, zero_smul, sub_zero]
    exact congrArg (fun φ => φ c) this
  | k + 1, c => by
    have : dL K (k + 1) m ∘ₗ SL K m (k + 2) = SL K m (k + 1) ∘ₗ dL K (k + 1) m := lc_ext fun v => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, SL_succ_single, dL_cone_succ,
        dL_SL k, dL_dL, map_zero, map_zero, sub_zero]
    exact congrArg (fun φ => φ c) this

theorem dL_TL {m : ℕ} : ∀ (k : ℕ) (c : LC K (k + 1) m),
    dL K (k + 1) m (TL K m (k + 1) c) + TL K m k (dL K k m c) = c - SL K m (k + 1) c
  | 0, c => by
    have : dL K 1 m ∘ₗ TL K m 1 + TL K m 0 ∘ₗ dL K 0 m = LinearMap.id - SL K m 1 :=
      lc_ext fun v => by
        rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, TL_succ_single,
          TL_zero, sub_zero, dL_cone_succ, LinearMap.sub_apply, LinearMap.id_apply,
          SL_succ_single, SL_zero, add_zero]
    exact congrArg (fun φ => φ c) this
  | k + 1, c => by
    have : dL K (k + 2) m ∘ₗ TL K m (k + 2) + TL K m (k + 1) ∘ₗ dL K (k + 1) m =
        LinearMap.id - SL K m (k + 2) := lc_ext fun v => by
      have ih := dL_TL k (dL K (k + 1) m (Finsupp.single v 1))
      rw [dL_dL, map_zero, add_zero] at ih
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, TL_succ_single,
        dL_cone_succ, map_sub, ih, LinearMap.sub_apply, LinearMap.id_apply, SL_succ_single]
      abel
    exact congrArg (fun φ => φ c) this

theorem SL_push {m p : ℕ} (u : Fin (m + 1) → Dl p) : ∀ (k : ℕ) (c : LC K k m),
    SL K p k (push K (linC u) k c) = push K (linC u) k (SL K m k c)
  | 0, c => rfl
  | k + 1, c => by
    have : SL K p (k + 1) ∘ₗ push K (linC u) (k + 1) = push K (linC u) (k + 1) ∘ₗ SL K m (k + 1) :=
      lc_ext fun v => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, push_single, SL_succ_single,
          SL_succ_single, ← push_single, dL_push, SL_push u k, ← linC_bary, cone_push]
    exact congrArg (fun φ => φ c) this

theorem TL_push {m p : ℕ} (u : Fin (m + 1) → Dl p) : ∀ (k : ℕ) (c : LC K k m),
    TL K p k (push K (linC u) k c) = push K (linC u) (k + 1) (TL K m k c)
  | 0, c => by simp [TL_zero]
  | k + 1, c => by
    have : TL K p (k + 1) ∘ₗ push K (linC u) (k + 1) =
        push K (linC u) (k + 2) ∘ₗ TL K m (k + 1) :=
      lc_ext fun v => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, push_single, TL_succ_single,
          TL_succ_single, ← push_single, dL_push, TL_push u k, ← map_sub, ← linC_bary, cone_push]
    exact congrArg (fun φ => φ c) this

/-! ### Subdivision of singular chains -/

variable (K)

/-- Barycentric subdivision of singular chains. -/
noncomputable def SdF (X : TopCat.{u}) (k : ℕ) : (Simp X k →₀ K) →ₗ[K] (Simp X k →₀ K) :=
  Finsupp.linearCombination K fun σ => act K σ k (SL K k k (Finsupp.single (vert k) 1))

/-- The chain homotopy between the identity and `SdF`. -/
noncomputable def TF (X : TopCat.{u}) (k : ℕ) : (Simp X k →₀ K) →ₗ[K] (Simp X (k + 1) →₀ K) :=
  Finsupp.linearCombination K fun σ => act K σ (k + 1) (TL K k k (Finsupp.single (vert k) 1))

variable {K} {X : TopCat.{u}}

theorem simp_ext {k k' : ℕ} {Y : TopCat.{u}} {f g : (Simp X k →₀ K) →ₗ[K] (Simp Y k' →₀ K)}
    (h : ∀ σ, f (Finsupp.single σ 1) = g (Finsupp.single σ 1)) : f = g :=
  Finsupp.lhom_ext' fun v => LinearMap.ext_ring (h v)

theorem SdF_single {k : ℕ} (σ : Simp X k) :
    SdF K X k (Finsupp.single σ 1) = act K σ k (SL K k k (Finsupp.single (vert k) 1)) := by
  simp [SdF]

theorem TF_single {k : ℕ} (σ : Simp X k) :
    TF K X k (Finsupp.single σ 1) = act K σ (k + 1) (TL K k k (Finsupp.single (vert k) 1)) := by
  simp [TF]

theorem SdF_act {m k : ℕ} (σ : Simp X m) (c : LC K k m) :
    SdF K X k (act K σ k c) = act K σ k (SL K m k c) := by
  have : SdF K X k ∘ₗ act K σ k = act K σ k ∘ₗ SL K m k := lc_ext fun w => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, act_single, SdF_single, ← act_push,
      ← SL_push, push_single, linC_comp_vert]
  exact congrArg (fun φ => φ c) this

theorem TF_act {m k : ℕ} (σ : Simp X m) (c : LC K k m) :
    TF K X k (act K σ k c) = act K σ (k + 1) (TL K m k c) := by
  have : TF K X k ∘ₗ act K σ k = act K σ (k + 1) ∘ₗ TL K m k := lc_ext fun w => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, act_single, TF_single, ← act_push,
      ← TL_push, push_single, linC_comp_vert]
  exact congrArg (fun φ => φ c) this

theorem dF_SdF {k : ℕ} (g : Simp X (k + 1) →₀ K) :
    dF K X k (SdF K X (k + 1) g) = SdF K X k (dF K X k g) := by
  have : dF K X k ∘ₗ SdF K X (k + 1) = SdF K X k ∘ₗ dF K X k := simp_ext fun σ => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, SdF_single, dF_act, dL_SL, ← SdF_act,
      ← dF_act, act_vert]
  exact congrArg (fun φ => φ g) this

theorem SdF_zero (g : Simp X 0 →₀ K) : SdF K X 0 g = g := by
  have : SdF K X 0 = LinearMap.id := simp_ext fun σ => by
    rw [SdF_single, SL_zero, act_vert, LinearMap.id_apply]
  rw [this, LinearMap.id_apply]

theorem TF_zero (g : Simp X 0 →₀ K) : TF K X 0 g = 0 := by
  have : TF K X 0 = 0 := simp_ext fun σ => by
    rw [TF_single, TL_zero, map_zero, LinearMap.zero_apply]
  rw [this, LinearMap.zero_apply]

theorem dF_TF {k : ℕ} (g : Simp X (k + 1) →₀ K) :
    dF K X (k + 1) (TF K X (k + 1) g) + TF K X k (dF K X k g) = g - SdF K X (k + 1) g := by
  have : dF K X (k + 1) ∘ₗ TF K X (k + 1) + TF K X k ∘ₗ dF K X k =
      LinearMap.id - SdF K X (k + 1) := simp_ext fun σ => by
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, TF_single, dF_act,
      ← act_vert σ, dF_act, TF_act, ← map_add, dL_TL, map_sub, act_vert, LinearMap.sub_apply,
      LinearMap.id_apply, SdF_single]
  exact congrArg (fun φ => φ g) this

theorem SdF_iterate_single {k : ℕ} (σ : Simp X k) (r : ℕ) :
    (SdF K X k)^[r] (Finsupp.single σ 1) = act K σ k ((SL K k k)^[r] (Finsupp.single (vert k) 1)) := by
  induction r with
  | zero => exact (act_vert σ 1).symm
  | succ r ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, SdF_act]

section Supported

variable {α : Type u} [TopologicalSpace α]

theorem act_supported {A : Set α} {m k : ℕ} {σ : Simp (TopCat.of α) m} (hσ : σ ∈ onSet A m)
    (c : LC K k m) : act K σ k c ∈ Finsupp.supported K K (onSet A k) := by
  classical
  rw [Finsupp.mem_supported]
  intro τ hτ
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.1
    (Finsupp.mapDomain_support (f := fun w => σ.comp (linC w)) (s := c) (Finset.mem_coe.1 hτ))
  rintro _ ⟨t, rfl⟩
  exact hσ ⟨_, rfl⟩

theorem map_supported_of_single {A : Set α} {k k' : ℕ}
    (f : (Simp (TopCat.of α) k →₀ K) →ₗ[K] (Simp (TopCat.of α) k' →₀ K))
    (hf : ∀ σ ∈ onSet A k, f (Finsupp.single σ 1) ∈ Finsupp.supported K K (onSet A k'))
    {g : Simp (TopCat.of α) k →₀ K} (hg : g ∈ Finsupp.supported K K (onSet A k)) :
    f g ∈ Finsupp.supported K K (onSet A k') := by
  rw [Finsupp.supported_eq_span_single] at hg
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨σ, hσ, rfl⟩
    exact hf σ hσ
  · simp
  · intro a b _ _ ha hb
    rw [map_add]
    exact add_mem ha hb
  · intro c a _ ha
    rw [map_smul]
    exact Submodule.smul_mem _ c ha

theorem SdF_supported {A : Set α} {k : ℕ} {g : Simp (TopCat.of α) k →₀ K}
    (hg : g ∈ Finsupp.supported K K (onSet A k)) :
    SdF K _ k g ∈ Finsupp.supported K K (onSet A k) :=
  map_supported_of_single _ (fun σ hσ => by rw [SdF_single]; exact act_supported hσ _) hg

theorem TF_supported {A : Set α} {k : ℕ} {g : Simp (TopCat.of α) k →₀ K}
    (hg : g ∈ Finsupp.supported K K (onSet A k)) :
    TF K _ k g ∈ Finsupp.supported K K (onSet A (k + 1)) :=
  map_supported_of_single _ (fun σ hσ => by rw [TF_single]; exact act_supported hσ _) hg

theorem dF_supported {A : Set α} {k : ℕ} {g : Simp (TopCat.of α) (k + 1) →₀ K}
    (hg : g ∈ Finsupp.supported K K (onSet A (k + 1))) :
    dF K _ k g ∈ Finsupp.supported K K (onSet A k) := by
  refine map_supported_of_single _ (fun σ hσ => ?_) hg
  simp only [dF, Finsupp.linearCombination_single, one_smul]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ ?_
  refine Finsupp.single_mem_supported K _ ?_
  rintro _ ⟨t, rfl⟩
  exact hσ ⟨_, rfl⟩

end Supported

/-! ### Iterated subdivision makes simplices small -/

section Small

/-- All edges of the affine simplex `w` have length at most `ρ` in barycentric coordinates. -/
def Small {k m : ℕ} (ρ : ℝ) (w : Fin (k + 1) → Dl m) : Prop := ∀ i j, ‖ew (w i) - ew (w j)‖ ≤ ρ

theorem weights_nonneg' {k : ℕ} (t : Dl k) (i : Fin (k + 1)) : 0 ≤ t.weights i := t.nonneg i

theorem weights_sum {k : ℕ} (t : Dl k) : ∑ i, t.weights i = 1 := StdSimplex.total_of_fintype t

theorem norm_wsum_sub_le {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : Fin (k + 1) → E) (t s : Dl k) :
    ‖∑ i, t.weights i • a i - ∑ j, s.weights j • a j‖ ≤
      ∑ i, ∑ j, t.weights i * s.weights j * ‖a i - a j‖ := by
  have h1 : ∑ i, ∑ j, (t.weights i * s.weights j) • a i = ∑ i, t.weights i • a i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul, ← Finset.mul_sum, weights_sum, mul_one]
  have h2 : ∑ i, ∑ j, (t.weights i * s.weights j) • a j = ∑ j, s.weights j • a j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul, ← Finset.sum_mul, weights_sum, one_mul]
  have h : ∑ i, t.weights i • a i - ∑ j, s.weights j • a j =
      ∑ i, ∑ j, (t.weights i * s.weights j) • (a i - a j) := by
    simp only [smul_sub, Finset.sum_sub_distrib, h1, h2]
  rw [h]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun j _ => ?_))
  rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (weights_nonneg' t i) (weights_nonneg' s j))]

theorem ew_linC {k m : ℕ} (w : Fin (k + 1) → Dl m) (t : Dl k) :
    ew (linC w t) = ∑ i, t.weights i • ew (w i) := ew_affineMapMk w t

theorem dist_hull_le {k m : ℕ} {M : ℝ} {v : Fin (k + 1) → Dl m} (hv : Small M v) {p q : Dl m}
    (hp : p ∈ range (linC v)) (hq : q ∈ range (linC v)) : ‖ew p - ew q‖ ≤ M := by
  obtain ⟨t, rfl⟩ := hp
  obtain ⟨s, rfl⟩ := hq
  rw [ew_linC, ew_linC]
  refine (norm_wsum_sub_le _ t s).trans ?_
  calc ∑ i, ∑ j, t.weights i * s.weights j * ‖ew (v i) - ew (v j)‖
      ≤ ∑ i, ∑ j, t.weights i * s.weights j * M := Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hv i j)
          (mul_nonneg (weights_nonneg' t i) (weights_nonneg' s j))
    _ = M := by
        simp only [← Finset.sum_mul, ← Finset.mul_sum, weights_sum, mul_one, one_mul]

theorem dist_bary_le {k m : ℕ} {M : ℝ} {v : Fin (k + 1) → Dl m} (hv : Small M v) {p : Dl m}
    (hp : p ∈ range (linC v)) : ‖ew (bary v) - ew p‖ ≤ (k / (k + 1)) * M := by
  obtain ⟨s, rfl⟩ := hp
  rw [bary, ew_linC, ew_linC]
  refine (norm_wsum_sub_le _ _ s).trans ?_
  have hb : ∀ i, (StdSimplex.barycenter (K := ℝ) (M := Fin (k + 1))).weights i = (k + 1 : ℝ)⁻¹ := by
    intro i
    rw [StdSimplex.weights_barycenter_apply, Fintype.card_fin]
    push_cast
    ring
  have hinner : ∀ j, ∑ i, (k + 1 : ℝ)⁻¹ * ‖ew (v i) - ew (v j)‖ ≤ (k / (k + 1)) * M := by
    intro j
    rw [← Finset.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), sub_self, norm_zero,
      zero_add]
    have hM : 0 ≤ M := (norm_nonneg _).trans (hv j j)
    calc (k + 1 : ℝ)⁻¹ * ∑ i ∈ Finset.univ.erase j, ‖ew (v i) - ew (v j)‖
        ≤ (k + 1 : ℝ)⁻¹ * ∑ i ∈ Finset.univ.erase j, M :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hv i j) (by positivity)
      _ = (k / (k + 1)) * M := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast
          field_simp
  calc ∑ i, ∑ j, (StdSimplex.barycenter (K := ℝ) (M := Fin (k + 1))).weights i * s.weights j *
        ‖ew (v i) - ew (v j)‖
      = ∑ j, s.weights j * ∑ i, (k + 1 : ℝ)⁻¹ * ‖ew (v i) - ew (v j)‖ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hb]
        ring
    _ ≤ ∑ j, s.weights j * ((k / (k + 1)) * M) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hinner j) (weights_nonneg' s j)
    _ = (k / (k + 1)) * M := by rw [← Finset.sum_mul, weights_sum, one_mul]

theorem range_linC_face {k m : ℕ} (v : Fin (k + 2) → Dl m) (i : Fin (k + 2)) :
    range (linC (v ∘ i.succAbove)) ⊆ range (linC v) := by
  rw [← linC_face]
  rintro _ ⟨t, rfl⟩
  exact ⟨_, rfl⟩

theorem mem_supported_sum {ι : Type*} {s : Finset ι} {S : Set ((Fin (k + 1) → Dl m))}
    (f : ι → LC K k m) (hf : ∀ i ∈ s, f i ∈ Finsupp.supported K K S) :
    ∑ i ∈ s, f i ∈ Finsupp.supported K K S :=
  Submodule.sum_mem _ hf

theorem SL_single_supported {m : ℕ} {M : ℝ} (hM : 0 ≤ M) : ∀ (k : ℕ) (v : Fin (k + 1) → Dl m),
    Small M v → SL K m k (Finsupp.single v 1) ∈ Finsupp.supported K K
      {w | (∀ i, w i ∈ range (linC v)) ∧ Small ((k / (k + 1)) * M) w}
  | 0, v, _ => by
    rw [SL_zero]
    refine Finsupp.single_mem_supported K _ ⟨fun i => ⟨StdSimplex.single i, linC_single v i⟩,
      fun i j => ?_⟩
    rw [Subsingleton.elim (α := Fin 1) i j, sub_self, norm_zero]
    simp
  | k + 1, v, hv => by
    rw [SL_succ_single, dL_single, map_sum, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul, map_zsmul]
    refine Submodule.smul_of_tower_mem _ _ ?_
    have ih := SL_single_supported hM k (v ∘ i.succAbove) fun a b => hv _ _
    have hcone : ∀ c : LC K k m, cone K (bary v) k c ∈ Finsupp.supported K K
        ((fun w : Fin (k + 1) → Dl m => (Fin.cons (bary v) w : Fin (k + 2) → Dl m)) ''
          (↑c.support : Set _)) := fun c => by
      classical
      rw [Finsupp.mem_supported]
      intro x hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support
        (f := fun w : Fin (k + 1) → Dl m => (Fin.cons (bary v) w : Fin (k + 2) → Dl m)) (s := c)
        (Finset.mem_coe.1 hx))
      exact ⟨w, hw, rfl⟩
    refine Finsupp.supported_mono ?_ (hcone _)
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨hw1, hw2⟩ := ih hw
    have hk : (k / (k + 1) : ℝ) * M ≤ ((k + 1 : ℕ) / ((k + 1 : ℕ) + 1)) * M := by
      refine mul_le_mul_of_nonneg_right ?_ hM
      push_cast
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hb : ∀ j, ‖ew (bary v) - ew (w j)‖ ≤ ((k + 1 : ℕ) / ((k + 1 : ℕ) + 1)) * M :=
      fun j => by
        have := dist_bary_le hv (range_linC_face v i (hw1 j))
        exact_mod_cast this
    refine ⟨fun j => Fin.cases (bary_mem v) (fun j => range_linC_face v i (hw1 j)) j,
      fun a b => ?_⟩
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
    · simp only [Fin.cons_zero, sub_self, norm_zero]
      positivity
    · simpa using hb b
    · simpa [norm_sub_rev] using hb a
    · simpa using (hw2 a b).trans hk

theorem small_vert (k : ℕ) : Small 1 (vert k) := by
  intro i j
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun l => ?_
  change ‖Finsupp.single i (1 : ℝ) l - Finsupp.single j (1 : ℝ) l‖ ≤ 1
  simp only [Finsupp.single_apply, Real.norm_eq_abs]
  split_ifs <;> norm_num

theorem SL_iterate_supported (k : ℕ) (n : ℕ) :
    (SL K k k)^[n] (Finsupp.single (vert k) 1) ∈
      Finsupp.supported K K {w | Small (((k : ℝ) / (k + 1)) ^ n) w} := by
  induction n with
  | zero =>
    refine Finsupp.single_mem_supported K _ ?_
    simpa using small_vert k
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rw [Finsupp.supported_eq_span_single] at ih
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ih
    · rintro _ ⟨w, hw, rfl⟩
      refine Finsupp.supported_mono ?_ (SL_single_supported (by positivity) k w hw)
      rintro w' ⟨-, h⟩
      simpa [pow_succ, mul_comm] using h
    · simp
    · intro a b _ _ ha hb
      rw [map_add]
      exact add_mem ha hb
    · intro c a _ ha
      rw [map_smul]
      exact Submodule.smul_mem _ c ha

end Small

theorem supported_map_le {ι M : Type*} [AddCommGroup M] [Module K M] (f : (ι →₀ K) →ₗ[K] M)
    (S : Set ι) (P : Submodule K M) (h : ∀ i ∈ S, f (Finsupp.single i 1) ∈ P) :
    (Finsupp.supported K K S).map f ≤ P := by
  rw [Finsupp.supported_eq_span_single, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
  exact h i hi

theorem small_range {k m : ℕ} {ρ : ℝ} {w : Fin (k + 1) → Dl m} (hw : Small ρ w) (t : Dl k) :
    ‖ew (linC w t) - ew (w 0)‖ ≤ ρ :=
  dist_hull_le hw ⟨t, rfl⟩ ⟨StdSimplex.single 0, linC_single w 0⟩

/-- After enough subdivisions, every simplex of `σ` lies in `U` or in `V`. -/
theorem sdF_iterate_small {α : Type u} [TopologicalSpace α] {k : ℕ} (σ : Simp (TopCat.of α) k)
    {U V : Set α} (hU : IsOpen U) (hV : IsOpen V) (hσ : range σ ⊆ U ∪ V) :
    ∃ n, (SdF K _ k)^[n] (Finsupp.single σ 1) ∈ Finsupp.supported K K (onSet U k ∪ onSet V k) := by
  have hemb := isEmbedding_ew k
  obtain ⟨OU, hOU, hOU'⟩ := hemb.isInducing.isOpen_iff.1 (hU.preimage σ.continuous)
  obtain ⟨OV, hOV, hOV'⟩ := hemb.isInducing.isOpen_iff.1 (hV.preimage σ.continuous)
  let c : Bool → Set (Fin (k + 1) → ℝ) := fun b => if b then OU else OV
  have hc : ∀ b, IsOpen (c b) := fun b => by cases b <;> simpa [c]
  have hS : range (ew : Dl k → _) ⊆ ⋃ b, c b := by
    rintro _ ⟨t, rfl⟩
    rcases hσ ⟨t, rfl⟩ with h | h
    · exact mem_iUnion.2 ⟨true, by
        show ew t ∈ OU
        rw [← mem_preimage, hOU']
        exact h⟩
    · exact mem_iUnion.2 ⟨false, by
        show ew t ∈ OV
        rw [← mem_preimage, hOV']
        exact h⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (isCompact_range hemb.continuous) hc hS
  have hr : ((k : ℝ) / (k + 1)) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hr
  refine ⟨n, ?_⟩
  rw [SdF_iterate_single]
  refine supported_map_le (act K σ k) _ _ (fun w hw => ?_) ⟨_, SL_iterate_supported k n, rfl⟩
  obtain ⟨b, hb⟩ := hball (ew (w 0)) ⟨_, rfl⟩
  have hin : ∀ t, linC w t ∈ ew ⁻¹' c b := fun t => hb (by
    rw [Metric.mem_ball, dist_eq_norm]
    exact (small_range hw t).trans_lt hn)
  rw [act_single]
  cases b
  · refine Finsupp.single_mem_supported K _ (Or.inr ?_)
    rintro _ ⟨t, rfl⟩
    have := hin t
    simp only [c, Bool.false_eq_true, ite_false] at this
    rw [hOV'] at this
    exact this
  · refine Finsupp.single_mem_supported K _ (Or.inl ?_)
    rintro _ ⟨t, rfl⟩
    have := hin t
    simp only [c, ite_true] at this
    rw [hOU'] at this
    exact this

end ConleyCheck.Conley
