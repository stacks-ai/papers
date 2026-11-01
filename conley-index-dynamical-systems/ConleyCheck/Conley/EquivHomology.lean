import ConleyCheck.Conley.Equivariant
import ConleyCheck.Conley.PairNatural
import ConleyCheck.Conley.Nested

/-!
# Actions of involutions on the homology of index pairs

For an index pair `(N, L)` invariant under a continuous map `r`, `pairAct K r` is the induced map
on `H_k(N, L)`. This file transports a computation `r_* = ε` from one index pair to another along
an equivariant pointed homotopy equivalence of the index spaces (`act_transfer`), through the
natural isomorphisms `H_k(N, L) ≅ H_k(N/L, [L])` that exist for collared pairs (`projMap_bijective`)
and for deformation-collared pairs (`projMap_bijective_of_deform`). It also computes the action in
the two model cases of `prop:boundary`:

* `pairAct_chart_neg`: a reflection of an arc `(J, ∂J)` acts by `-1` on
  `H_k(N × J, L × J ∪ N × ∂J)`, through `cylRefl_neg`;
* `pairAct_eq_self_of_homotopy`: a map that is homotopic to the identity through maps of pairs
  acts by `+1`.
-/

namespace ConleyCheck.Conley

open CategoryTheory Set Topology unitInterval

universe u

section Transfer

variable (K : Type u) [Ring K]

theorem smul_of_surjective {M₁ M₂ : ModuleCat.{u} K} (φ : M₁ ⟶ M₂)
    (hφ : Function.Surjective φ.hom) {a : M₁ ⟶ M₁} {b : M₂ ⟶ M₂} (hab : a ≫ φ = φ ≫ b) (ε : K)
    (ha : ∀ x, a.hom x = ε • x) (y : M₂) : b.hom y = ε • y := by
  obtain ⟨x, rfl⟩ := hφ y
  have h := congrArg (fun ψ => ψ.hom x) hab
  change φ.hom (a.hom x) = b.hom (φ.hom x) at h
  rw [← h, ha, map_smul]

theorem smul_of_injective {M₁ M₂ : ModuleCat.{u} K} (φ : M₁ ⟶ M₂)
    (hφ : Function.Injective φ.hom) {a : M₁ ⟶ M₁} {b : M₂ ⟶ M₂} (hab : a ≫ φ = φ ≫ b) (ε : K)
    (hb : ∀ y, b.hom y = ε • y) (x : M₁) : a.hom x = ε • x := by
  apply hφ
  have h := congrArg (fun ψ => ψ.hom x) hab
  change φ.hom (a.hom x) = b.hom (φ.hom x) at h
  rw [h, hb, map_smul]

variable {α β : Type u} [TopologicalSpace α] [TopologicalSpace β]

/-- The action of `r` on `H_k(N, L)`. -/
noncomputable def pairAct {N L : Set α} (r : C(α, α)) (hN : RInv r N) (hL : RInv r L) (k : ℤ) :
    singH K α k N L ⟶ singH K α k N L :=
  singMap K r hN.mapsTo (fun _ _ hx => hL.mapsTo hx) k

/-- The action of `r` on `H_k(N, L)`, computed in the ambient space `N`. -/
noncomputable def pairActN {N L : Set α} (r : C(α, α)) (hN : RInv r N) (hL : RInv r L) (k : ℤ) :
    singH K N k univ (subL N L) ⟶ singH K N k univ (subL N L) :=
  singMap K (restrictC r hN.mapsTo) (mapsTo_univ _ _) (fun _ _ hx => hL.mapsTo hx) k

/-- The action of `r` on `H_k(N/L, [L])`. -/
noncomputable def pairActQ {N L : Set α} (r : C(α, α)) (hN : RInv r N) (hL : RInv r L) (k : ℤ) :
    singH K (IndexSpace N L) k univ {IndexSpace.pt N L} ⟶
      singH K (IndexSpace N L) k univ {IndexSpace.pt N L} :=
  singMap K (IndexSpace.mapC r hN.mapsTo hL.mapsTo) (mapsTo_univ _ _)
    (fun _ _ hx => by rw [mem_singleton_iff.1 hx]; rfl) k

/-- `H_k(N, L)` computed in the ambient space `N` maps to `H_k(N, L)`. -/
noncomputable def valMap (N L : Set α) (k : ℤ) : singH K N k univ (subL N L) ⟶ singH K α k N L :=
  singMap K (valN N) (B := univ) (A := subL N L) (B' := N) (A' := L) (fun x _ => x.2)
    (fun _ _ hx => hx) k

theorem valMap_bijective (N L : Set α) (k : ℤ) : Function.Bijective (valMap K N L k).hom :=
  valN_bijective K N k (A := L)

theorem pairActN_valMap {N L : Set α} (r : C(α, α)) (hN : RInv r N) (hL : RInv r L) (k : ℤ) :
    pairActN K r hN hL k ≫ valMap K N L k = valMap K N L k ≫ pairAct K r hN hL k := by
  unfold pairActN valMap pairAct
  exact singMap_square K _ _ _ _ (by ext; rfl) _ _ _ _ _ _ _ _ k

theorem pairActN_projMap {N L : Set α} (r : C(α, α)) (hN : RInv r N) (hL : RInv r L) (k : ℤ) :
    pairActN K r hN hL k ≫ projMap K N L k = projMap K N L k ≫ pairActQ K r hN hL k := by
  unfold pairActN projMap pairActQ
  exact singMap_square K _ _ _ _ (by ext; rfl) _ _ _ _ _ _ _ _ k

theorem hMap_restrict_univ_bijective {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hf : ∀ n, Function.Bijective (hMap K f n).hom) (n : ℕ) :
    Function.Bijective (hMap K (restrictC f (mapsTo_univ f univ)) n).hom := by
  have hsq : (restrictC f (mapsTo_univ f univ)).comp univC = univC.comp f :=
    ContinuousMap.ext fun _ => rfl
  have h1 : (hMap K (restrictC f (mapsTo_univ f univ)) n).hom ∘ (hMap K univC n).hom =
      (hMap K univC n).hom ∘ (hMap K f n).hom := funext fun a => by
    simp only [Function.comp_apply]
    rw [hMap_comp_apply, hMap_comp_apply, hsq]
  exact (Function.Bijective.of_comp_iff _ (hMap_univC_bijective K n)).1
    (h1 ▸ (hMap_univC_bijective K n).comp (hf n))

/-- The map `H_k(X, x₀) → H_k(Y, y₀)` of a pointed homotopy equivalence. -/
noncomputable def PointedHomotopyEquiv.hmap {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] {x₀ : X} {y₀ : Y} (e : PointedHomotopyEquiv X Y x₀ y₀) (k : ℤ) :
    singH K X k univ {x₀} ⟶ singH K Y k univ {y₀} :=
  singMap K e.toFun (mapsTo_univ _ _)
    (fun _ _ hx => by rw [mem_singleton_iff.1 hx, mem_singleton_iff]; exact e.map_pt) k

theorem PointedHomotopyEquiv.hmap_bijective {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] {x₀ : X} {y₀ : Y} (e : PointedHomotopyEquiv X Y x₀ y₀) (k : ℤ) :
    Function.Bijective (e.hmap K k).hom := by
  have hpt : MapsTo e.toFun {x₀} {y₀} := fun x hx => by
    rw [mem_singleton_iff.1 hx, mem_singleton_iff]; exact e.map_pt
  have hpt' : MapsTo e.invFun {y₀} {x₀} := fun x hx => by
    rw [mem_singleton_iff.1 hx, mem_singleton_iff]; exact e.inv_pt
  refine singMap_bijective_of_abs K e.toFun (singleton_subset_iff.2 (mem_univ _))
    (singleton_subset_iff.2 (mem_univ _)) (mapsTo_univ _ _) hpt
    (hMap_restrict_univ_bijective K _ (hMap_bijective_of_homotopy_inverse K e.toFun e.invFun
      e.left.homotopic e.right.homotopic)) (fun n => ?_) k
  refine hMap_bijective_of_homotopy_inverse K _ (restrictC e.invFun hpt') ?_ ?_ n
  · have : (restrictC e.invFun hpt').comp (restrictC e.toFun hpt) = ContinuousMap.id _ :=
      ContinuousMap.ext fun _ => Subsingleton.elim _ _
    rw [this]
  · have : (restrictC e.toFun hpt).comp (restrictC e.invFun hpt') = ContinuousMap.id _ :=
      ContinuousMap.ext fun _ => Subsingleton.elim _ _
    rw [this]

/-- Transport of the action of an involution along an equivariant pointed homotopy equivalence
of index spaces, for pairs on which `H_*(N, L) → H_*(N/L, [L])` is an isomorphism. -/
theorem act_transfer {N L : Set α} {N' L' : Set β} {r : C(α, α)} {r' : C(β, β)}
    (hN : RInv r N) (hL : RInv r L) (hN' : RInv r' N') (hL' : RInv r' L')
    (e : PointedHomotopyEquiv (IndexSpace N L) (IndexSpace N' L') (IndexSpace.pt N L)
      (IndexSpace.pt N' L'))
    (he : e.Commutes (IndexSpace.mapC r hN.mapsTo hL.mapsTo)
      (IndexSpace.mapC r' hN'.mapsTo hL'.mapsTo))
    (k : ℤ) (hp : Function.Bijective (projMap K N L k).hom)
    (hp' : Function.Bijective (projMap K N' L' k).hom) (ε : K)
    (hε : ∀ z, (pairAct K r hN hL k).hom z = ε • z) (z : singH K β k N' L') :
    (pairAct K r' hN' hL' k).hom z = ε • z := by
  have s1 := smul_of_injective K _ (valMap_bijective K N L k).1 (pairActN_valMap K r hN hL k) ε hε
  have s2 := smul_of_surjective K _ hp.2 (pairActN_projMap K r hN hL k) ε s1
  have hsq : pairActQ K r hN hL k ≫ e.hmap K k = e.hmap K k ≫ pairActQ K r' hN' hL' k := by
    unfold pairActQ PointedHomotopyEquiv.hmap
    exact singMap_square K _ _ _ _ (by refine ContinuousMap.ext fun x => ?_; exact he x)
      _ _ _ _ _ _ _ _ k
  have s3 := smul_of_surjective K _ (e.hmap_bijective K k).2 hsq ε s2
  have s4 := smul_of_injective K _ hp'.1 (pairActN_projMap K r' hN' hL' k) ε s3
  exact smul_of_surjective K _ (valMap_bijective K N' L' k).2 (pairActN_valMap K r' hN' hL' k) ε
    s4 z

/-- `H_*(N, L) → H_*(N/L, [L])` is an isomorphism for a deformation-collared pair. -/
theorem projMap_bijective_of_deform {N L : Set α} (hLc : IsClosed L) (hLN : L ⊆ N)
    (hc : IsDeformCollared N L) (k : ℤ) : Function.Bijective (projMap K N L k).hom := by
  obtain ⟨V, O, G, hO, hLO, hON, hVN, hG0, hGL, hGV, hG1⟩ := hc
  have hLV : L ⊆ V := fun x hx => hON ⟨hLO hx, hLN hx⟩
  let Hα : C(I × V, V) := ⟨fun p => ⟨G (p.1, ⟨p.2, hVN p.2.2⟩), hGV _ _ p.2.2⟩, by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp (G.continuous.comp (continuous_fst.prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk _)))⟩
  have hsV : ∀ k, Subsingleton (singH K α k V L) := singH_subsingleton_of_deform K hLV Hα
    (fun x => Subtype.ext (by
      show (G (0, ⟨x, hVN x.2⟩) : α) = x
      rw [hG0]))
    (fun x => hG1 _ x.2)
    (fun s x hx => hGL s _ hx)
  have b1 := singIncl_bijective_of_subsingleton K hLV hVN hsV k
  have b2 := excision K hVN (sdiff_subset : N \ L ⊆ N) hO hLc.isOpen_compl
    (fun x _ => by
      by_cases h : x ∈ L
      · exact Or.inl (hLO h)
      · exact Or.inr h)
    hON (fun x hx => ⟨hx.2, hx.1⟩) k
  have b3 := singMap_bijective K (valN N) (B := offL N L) (A := {x : N | (x : α) ∈ V})
    (B' := N \ L) (A' := V) (fun x hx => ⟨x.2, hx⟩) (fun y hy => ⟨⟨y, hy.1⟩, hy.2, rfl⟩)
    (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal) (fun x _ => Iff.rfl) k
  have b4 := singMap_bijective K (IndexSpace.proj N L) (B := offL N L)
    (A := {x : N | (x : α) ∈ V}) (B' := {IndexSpace.pt N L}ᶜ) (A' := liftSet N L V)
    (fun x hx h => hx ((IndexSpace.proj_eq_pt_iff x).1 h)) (fun y hy => exists_proj_of_ne_pt hy)
    (isEmbedding_proj_offL hLc) (fun x _ => (proj_mem_liftSet hLV x).symm) k
  have b5 := excision K (subset_univ (liftSet N L V)) (subset_univ ({IndexSpace.pt N L}ᶜ))
    (isOpen_liftSet hLO hO) (isOpen_compl_pt hLc)
    (fun z _ => by
      by_cases h : z = IndexSpace.pt N L
      · exact Or.inl (Or.inl h)
      · exact Or.inr h)
    (by
      rintro z ⟨h | ⟨x, hx, rfl⟩, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨x, hON ⟨hx, x.2⟩, rfl⟩)
    (fun z hz => hz.1) k
  have hpV : ({IndexSpace.pt N L} : Set (IndexSpace N L)) ⊆ liftSet N L V := by
    rintro _ rfl
    exact pt_mem_liftSet V
  let GQ : C(I × IndexSpace N L, IndexSpace N L) := descendProd (IndexSpace.pt N L)
    ((IndexSpace.proj N L).comp G) (fun s y hy => IndexSpace.proj_eq_pt (hGL s y hy))
  have hmem : ∀ (s : I) {z}, z ∈ liftSet N L V →
      GQ (s, z) ∈ liftSet N L V ∧ (s = 1 → GQ (s, z) = IndexSpace.pt N L) := by
    intro s z hz
    rcases hz with rfl | ⟨x, hx, rfl⟩
    · exact ⟨pt_mem_liftSet V, fun _ => rfl⟩
    · refine ⟨(proj_mem_liftSet hLV _).2 (hGV s x hx), fun hs => ?_⟩
      subst hs
      exact IndexSpace.proj_eq_pt (hG1 x hx)
  have hGQ0 : ∀ z, GQ (0, z) = z := by
    intro z
    induction z using Quotient.inductionOn with
    | h a =>
      rcases a with y | u
      · show IndexSpace.proj N L (G (0, y)) = IndexSpace.proj N L y
        rw [hG0]
      · rfl
  let HQ : C(I × liftSet N L V, liftSet N L V) :=
    ⟨fun p => ⟨GQ (p.1, p.2), (hmem p.1 p.2.2).1⟩, by
      refine Continuous.subtype_mk ?_ _
      exact GQ.continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩
  have hsQ : ∀ k, Subsingleton (singH K (IndexSpace N L) k (liftSet N L V) {IndexSpace.pt N L}) :=
    singH_subsingleton_of_deform K hpV HQ (fun z => Subtype.ext (hGQ0 z))
      (fun z => (hmem 1 z.2).2 rfl)
      (fun s z hz => by
        rw [mem_singleton_iff] at hz ⊢
        show GQ (s, (z : IndexSpace N L)) = _
        rw [hz]
        rfl)
  have b6 := singIncl_bijective_of_subsingleton K hpV (subset_univ _) hsQ k
  have v1 := valN_bijective K N k (A := L)
  have v2 := valN_bijective K N k (A := V)
  have hLVN : subL N L ⊆ {x : N | (x : α) ∈ V} := fun x hx => hLV hx
  have iN : Function.Bijective (singIncl K k (subset_refl (univ : Set N)) hLVN).hom := by
    refine bijective_of_square_left K _ _ _ _ ?_ v2 v1 b1
    rw [singIncl_eq_singMap, singIncl_eq_singMap]
    exact singMap_square K _ _ _ _ (by ext; rfl) _ _ _ _ _ _ _ _ k
  have eN : Function.Bijective (singIncl K k (subset_univ (offL N L))
      (subset_refl {x : N | (x : α) ∈ V})).hom := by
    refine bijective_of_square_left K _ _ _ _ ?_ v2 b3 b2
    rw [singIncl_eq_singMap, singIncl_eq_singMap]
    exact singMap_square K _ _ _ _ (by ext; rfl) _ _ _ _ _ _ _ _ k
  let pV := singMap K (IndexSpace.proj N L) (B := (univ : Set N)) (A := {x : N | (x : α) ∈ V})
    (B' := univ) (A' := liftSet N L V) (mapsTo_univ _ _)
    (fun x _ hx => (proj_mem_liftSet hLV x).2 hx) k
  have hpVb : Function.Bijective pV.hom := by
    refine bijective_of_square_right K _ pV _ _ ?_ eN b4 b5
    rw [singIncl_eq_singMap, singIncl_eq_singMap]
    exact singMap_square K _ _ _ _ (by ext; rfl) _ _ _ _ _ _ _ _ k
  refine bijective_of_square_left K (projMap K N L k) _ _ _ ?_ b6 iN hpVb
  rw [projMap, singIncl_eq_singMap, singIncl_eq_singMap]
  exact singMap_square K _ _ _ _ (by ext; rfl) _ _ _ _ _ _ _ _ k

/-- A map of pairs connected to the identity through two homotopies of maps of pairs acts by
`+1`. -/
theorem pairAct_eq_self_of_homotopy {N L : Set α} (hLN : L ⊆ N) {r c : C(α, α)}
    (hN : RInv r N) (hL : RInv r L) (F G : C(I × α, α)) (hF0 : ∀ x, F (0, x) = r x)
    (hF1 : ∀ x, F (1, x) = c x) (hG0 : ∀ x, G (0, x) = x) (hG1 : ∀ x, G (1, x) = c x)
    (hFN : ∀ s, ∀ x ∈ N, F (s, x) ∈ N) (hFL : ∀ s, ∀ x ∈ L, F (s, x) ∈ L)
    (hGN : ∀ s, ∀ x ∈ N, G (s, x) ∈ N) (hGL : ∀ s, ∀ x ∈ L, G (s, x) ∈ L) (k : ℤ)
    (z : singH K α k N L) : (pairAct K r hN hL k).hom z = (1 : K) • z := by
  have hcN : MapsTo c N N := fun x hx => by rw [← hF1]; exact hFN 1 x hx
  have hcL : ∀ x ∈ N, x ∈ L → c x ∈ L := fun x _ hx => by rw [← hF1]; exact hFL 1 x hx
  have e1 := singMap_eq_of_homotopy K r c F hF0 hF1 hLN hFN hFL hN.mapsTo
    (fun _ _ hx => hL.mapsTo hx) hcN hcL k
  have e2 := singMap_eq_of_homotopy K (ContinuousMap.id α) c G hG0 hG1 hLN hGN hGL
    (mapsTo_id N) (fun _ _ h => h) hcN hcL k
  rw [one_smul]
  unfold pairAct
  rw [e1, ← e2, singMap_id_apply]

end Transfer

/-! ### Reflection of an arc -/

section Chart

variable (K : Type u) [Ring K] {X : Type u} [TopologicalSpace X] {Z : Type} [TopologicalSpace Z]
  [T2Space Z] {J D : Set Z}

/-- If the chart of an arc `(J, ∂J)` intertwines `t ↦ 1 - t` with `ρ`, then `id × ρ` acts by
`-1` on `H_k(N × J, L × J ∪ N × ∂J)`. -/
theorem pairAct_chart_neg (ch : IntervalChart J D) {ρ : C(Z, Z)}
    (hρe : ∀ t, ch.e (1 - t) = ρ (ch.e t)) (hJ : RInv ρ J) (hD : RInv ρ D) {N L : Set X}
    (hLN : L ⊆ N) (k : ℤ) (z : singH K (X × Z) k (N ×ˢ J) (L ×ˢ J ∪ N ×ˢ D)) :
    (pairAct K (rprod ρ) (hJ.prod N) ((hJ.prod L).union (hD.prod N)) k).hom z = (-1 : K) • z := by
  have hB : MapsTo ((ContinuousMap.id X).prodMap ch.e) (cylN N) (N ×ˢ J) :=
    fun p hp => ⟨hp.1, ch.mem_J hp.2⟩
  have hA : ∀ p ∈ cylN N, p ∈ cylL N L →
      (ContinuousMap.id X).prodMap ch.e p ∈ L ×ˢ J ∪ N ×ˢ D := fun p hp hpA => by
    rcases hpA with ⟨hxL, -⟩ | ⟨-, ht'⟩
    · exact Or.inl ⟨hxL, ch.mem_J hp.2⟩
    · exact Or.inr ⟨hp.1, (ch.mem_iff _ hp.2).2 ht'⟩
  have hsq : singMap K cylRefl (cylRefl_mapsTo_N N) (fun _ _ h => cylRefl_mapsTo_L N L h) k ≫
      singMap K ((ContinuousMap.id X).prodMap ch.e) hB hA k =
      singMap K ((ContinuousMap.id X).prodMap ch.e) hB hA k ≫
        pairAct K (rprod ρ) (hJ.prod N) ((hJ.prod L).union (hD.prod N)) k := by
    unfold pairAct
    exact singMap_square K _ _ _ _
      (by refine ContinuousMap.ext fun p => Prod.ext rfl ?_; exact hρe p.2) _ _ _ _ _ _ _ _ k
  refine smul_of_surjective K _ (ch.singMap_bijective K N L k hB hA).2 hsq (-1) (fun x => ?_) z
  rw [cylRefl_neg K hLN, neg_one_smul]

end Chart

end ConleyCheck.Conley
