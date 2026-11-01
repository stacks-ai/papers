import ConleyCheck.Conley.Regular

/-!
# Deformation collars, products, and the suspension shift

An index pair `(N, L)` with a deformation collar (`IsDeformCollared`) satisfies
`H_*(N, L) ≅ H̃_*(N/L)` (`deformCollarEquiv_nonempty`), by the argument of `collarEquiv` with the
flow replaced by the deformation. Deformation collars are stable under products
(`IsDeformCollared.prod`), and every isolated invariant set has an index pair with one
(`exists_deformCollared_indexPair`), so `CH_*(S) ≅ H_*(N, L)` for such pairs
(`homologyIndex_equiv_of_deformCollared`).

The pair-level suspension `H_{k+1}(N × [0, 1], L × [0, 1] ∪ N × {0, 1}) ≅ H_k(N, L)`
(`singH_suspension`) follows from the exact sequences of triples, excision, and deformations.
-/

namespace ConleyCheck.Conley

open CategoryTheory Set Topology unitInterval

universe u

/-! ### `H_*(N, L) ≅ H̃_*(N/L)` for deformation collars -/

section Equiv

variable (K : Type u) [Ring K] {α : Type u} [TopologicalSpace α]

theorem deformCollarEquiv_nonempty {N L : Set α} (hLc : IsClosed L) (hLN : L ⊆ N)
    (hc : IsDeformCollared N L) (n : ℕ) :
    Nonempty (singH K α (Int.ofNat n) N L ≃ₗ[K] redH K (IndexSpace N L) (IndexSpace.pt N L) n) := by
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
  have b1 := singIncl_bijective_of_subsingleton K hLV hVN hsV (Int.ofNat n)
  have b2 := excision K hVN (sdiff_subset : N \ L ⊆ N) hO hLc.isOpen_compl
    (fun x _ => by
      by_cases h : x ∈ L
      · exact Or.inl (hLO h)
      · exact Or.inr h)
    hON (fun x hx => ⟨hx.2, hx.1⟩) (Int.ofNat n)
  let valC : C(N, α) := ⟨Subtype.val, continuous_subtype_val⟩
  have b3 := singMap_bijective K valC (B := offL N L) (A := {x : N | (x : α) ∈ V})
    (B' := N \ L) (A' := V) (fun x hx => ⟨x.2, hx⟩) (fun y hy => ⟨⟨y, hy.1⟩, hy.2, rfl⟩)
    (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal) (fun x _ => Iff.rfl) (Int.ofNat n)
  have b4 := singMap_bijective K (IndexSpace.proj N L) (B := offL N L)
    (A := {x : N | (x : α) ∈ V}) (B' := {IndexSpace.pt N L}ᶜ) (A' := liftSet N L V)
    (fun x hx h => hx ((IndexSpace.proj_eq_pt_iff x).1 h)) (fun y hy => exists_proj_of_ne_pt hy)
    (isEmbedding_proj_offL hLc) (fun x _ => (proj_mem_liftSet hLV x).symm) (Int.ofNat n)
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
    (fun z hz => hz.1) (Int.ofNat n)
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
  have b6 := singIncl_bijective_of_subsingleton K hpV (subset_univ _) hsQ (Int.ofNat n)
  exact ⟨(LinearEquiv.ofBijective _ b1).trans ((LinearEquiv.ofBijective _ b2).symm.trans
    ((LinearEquiv.ofBijective _ b3).symm.trans ((LinearEquiv.ofBijective _ b4).trans
    ((LinearEquiv.ofBijective _ b5).trans ((LinearEquiv.ofBijective _ b6).symm.trans
    (redHEquiv K (IndexSpace.pt N L) n).symm)))))⟩

variable [T2Space α] {ϕ : Flow ℝ α}

/-- `CH_n(S) ≅ H_n(N, L)` for an index pair `(N, L)` of `S` with a deformation collar. -/
theorem homologyIndex_equiv_of_deformCollared {S N L : Set α} (hS : IsIsolatedInvariantSet ϕ S)
    (hP : IsIndexPair ϕ S N L) (hc : IsDeformCollared N L) (n : ℕ) :
    Nonempty (homologyIndex K ϕ hS n ≃ₗ[K] singH K α (Int.ofNat n) N L) :=
  ⟨(homologyIndexIso K hS hP n).some.toLinearEquiv.trans
    (deformCollarEquiv_nonempty K hP.isCompact_L.isClosed hP.subset hc n).some.symm⟩

end Equiv

/-! ### Products -/

section Prod

variable {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]

/-- The product of deformation collars `(N₁, L₁)` and `(N₂, L₂)` is a deformation collar of
`(N₁ × N₂, L₁ × N₂ ∪ N₁ × L₂)`. -/
theorem IsDeformCollared.prod {N₁ L₁ : Set X} {N₂ L₂ : Set B} (h₁ : IsDeformCollared N₁ L₁)
    (h₂ : IsDeformCollared N₂ L₂) :
    IsDeformCollared (N₁ ×ˢ N₂) (L₁ ×ˢ N₂ ∪ N₁ ×ˢ L₂) := by
  obtain ⟨V₁, O₁, G₁, hO₁, hLO₁, hON₁, hVN₁, hG0₁, hGL₁, hGV₁, hG1₁⟩ := h₁
  obtain ⟨V₂, O₂, G₂, hO₂, hLO₂, hON₂, hVN₂, hG0₂, hGL₂, hGV₂, hG1₂⟩ := h₂
  let p₁ : C(N₁ ×ˢ N₂, N₁) := ⟨fun z => ⟨(z : X × B).1, z.2.1⟩,
    (continuous_fst.comp continuous_subtype_val).subtype_mk _⟩
  let p₂ : C(N₁ ×ˢ N₂, N₂) := ⟨fun z => ⟨(z : X × B).2, z.2.2⟩,
    (continuous_snd.comp continuous_subtype_val).subtype_mk _⟩
  let G : C(I × (N₁ ×ˢ N₂ : Set (X × B)), N₁ ×ˢ N₂) :=
    ⟨fun q => ⟨((G₁ (q.1, p₁ q.2) : X), (G₂ (q.1, p₂ q.2) : B)),
      (G₁ (q.1, p₁ q.2)).2, (G₂ (q.1, p₂ q.2)).2⟩, by
      refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
      · exact continuous_subtype_val.comp (G₁.continuous.comp
          (continuous_fst.prodMk (p₁.continuous.comp continuous_snd)))
      · exact continuous_subtype_val.comp (G₂.continuous.comp
          (continuous_fst.prodMk (p₂.continuous.comp continuous_snd)))⟩
  refine ⟨V₁ ×ˢ N₂ ∪ N₁ ×ˢ V₂, O₁ ×ˢ univ ∪ univ ×ˢ O₂, G,
    (hO₁.prod isOpen_univ).union (isOpen_univ.prod hO₂), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨x, b⟩ (⟨hx, -⟩ | ⟨-, hb⟩)
    · exact Or.inl ⟨hLO₁ hx, trivial⟩
    · exact Or.inr ⟨trivial, hLO₂ hb⟩
  · rintro ⟨x, b⟩ ⟨⟨hx, -⟩ | ⟨-, hb⟩, hxN, hbN⟩
    · exact Or.inl ⟨hON₁ ⟨hx, hxN⟩, hbN⟩
    · exact Or.inr ⟨hxN, hON₂ ⟨hb, hbN⟩⟩
  · rintro ⟨x, b⟩ (⟨hx, hb⟩ | ⟨hx, hb⟩)
    · exact ⟨hVN₁ hx, hb⟩
    · exact ⟨hx, hVN₂ hb⟩
  · intro z
    apply Subtype.ext
    show ((G₁ (0, p₁ z) : X), (G₂ (0, p₂ z) : B)) = (z : X × B)
    rw [hG0₁, hG0₂]
    rfl
  · rintro s z (⟨hx, -⟩ | ⟨-, hb⟩)
    · exact Or.inl ⟨hGL₁ s (p₁ z) hx, (G₂ (s, p₂ z)).2⟩
    · exact Or.inr ⟨(G₁ (s, p₁ z)).2, hGL₂ s (p₂ z) hb⟩
  · rintro s z (⟨hx, -⟩ | ⟨-, hb⟩)
    · exact Or.inl ⟨hGV₁ s (p₁ z) hx, (G₂ (s, p₂ z)).2⟩
    · exact Or.inr ⟨(G₁ (s, p₁ z)).2, hGV₂ s (p₂ z) hb⟩
  · rintro z (⟨hx, -⟩ | ⟨-, hb⟩)
    · exact Or.inl ⟨hG1₁ (p₁ z) hx, (G₂ (1, p₂ z)).2⟩
    · exact Or.inr ⟨(G₁ (1, p₁ z)).2, hG1₂ (p₂ z) hb⟩

end Prod

/-! ### The suspension shift -/

section Suspension

variable (K : Type u) [Ring K] {X : Type u} [TopologicalSpace X]

/-- If `H_*(N, M) = 0`, then `H_*(M, L) ≅ H_*(N, L)`. -/
theorem singIncl_bijective_of_subsingleton' {N M L : Set X} (hLM : L ⊆ M) (hMN : M ⊆ N)
    (hs : ∀ k, Subsingleton (singH K X k N M)) (k : ℤ) :
    Function.Bijective (singIncl K k hMN (subset_refl L)).hom := by
  have := hs (k + 1)
  have := hs k
  exact bijective_of_exact_of_subsingleton (sing_exact_δ' K k hLM hMN) (sing_exact_incl K k hLM hMN)

/-- If `H_*(N, L) = 0`, the connecting map `H_{k+1}(N, M) → H_k(M, L)` is bijective. -/
theorem singδ_bijective_of_subsingleton {N M L : Set X} (hLM : L ⊆ M) (hMN : M ⊆ N)
    (hs : ∀ k, Subsingleton (singH K X k N L)) (k : ℤ) :
    Function.Bijective (singδ K k N M L).hom := by
  have := hs (k + 1)
  have := hs k
  exact bijective_of_exact_of_subsingleton (sing_exact_δ K k hLM hMN) (sing_exact_δ' K k hLM hMN)

/-- The cylinder `N × [0, 1]`. -/
def cylN (N : Set X) : Set (X × ℝ) := N ×ˢ Icc 0 1

/-- Its relative boundary `L × [0, 1] ∪ N × {0, 1}`. -/
def cylL (N L : Set X) : Set (X × ℝ) := L ×ˢ Icc 0 1 ∪ N ×ˢ {t | t = 0 ∨ t = 1}

/-- A map `I × W → X × ℝ` keeping the first coordinate and moving the second continuously, as a
self-map of `W`. -/
def cylDeform (W : Set (X × ℝ)) (f : I → ℝ → ℝ) (hf : Continuous fun p : I × ℝ => f p.1 p.2)
    (hW : ∀ s, ∀ p ∈ W, (p.1, f s p.2) ∈ W) : C(I × W, W) :=
  ⟨fun q => ⟨((q.2 : X × ℝ).1, f q.1 (q.2 : X × ℝ).2), hW q.1 _ q.2.2⟩, by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · exact continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
    · exact hf.comp (continuous_fst.prodMk
        (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))⟩

theorem cylDeform_apply (W : Set (X × ℝ)) (f : I → ℝ → ℝ)
    (hf : Continuous fun p : I × ℝ => f p.1 p.2) (hW : ∀ s, ∀ p ∈ W, (p.1, f s p.2) ∈ W)
    (s : I) (p : W) :
    (cylDeform W f hf hW (s, p) : X × ℝ) = ((p : X × ℝ).1, f s (p : X × ℝ).2) := rfl

/-- Deforming `W` into `Y` along the second coordinate. -/
theorem singH_subsingleton_of_cylDeform {Y W : Set (X × ℝ)} (hYW : Y ⊆ W) (f : I → ℝ → ℝ)
    (hf : Continuous fun p : I × ℝ => f p.1 p.2) (hW : ∀ s, ∀ p ∈ W, (p.1, f s p.2) ∈ W)
    (h0 : ∀ t, f 0 t = t) (h1 : ∀ p ∈ W, (p.1, f 1 p.2) ∈ Y)
    (hY : ∀ s, ∀ p ∈ Y, (p.1, f s p.2) ∈ Y) : ∀ k, Subsingleton (singH K (X × ℝ) k W Y) :=
  singH_subsingleton_of_deform K hYW (cylDeform W f hf hW)
    (fun p => Subtype.ext (by rw [cylDeform_apply, h0]))
    (fun p => h1 _ p.2) (fun s p hp => hY s _ hp)

/-- The suspension shift `H_{k+1}(N × [0, 1], L × [0, 1] ∪ N × {0, 1}) ≅ H_k(N, L)`. -/
theorem singH_suspension {N L : Set X} (hLN : L ⊆ N) (k : ℤ) :
    Nonempty (singH K (X × ℝ) (k + 1) (cylN N) (cylL N L) ≃ₗ[K] singH K X k N L) := by
  -- the triple `Q₁ ⊆ Q ⊆ P` with `H_*(P, Q₁) = 0`
  let Q₁ : Set (X × ℝ) := L ×ˢ Icc 0 1 ∪ N ×ˢ {0}
  have hQ₁Q : Q₁ ⊆ cylL N L := by
    rintro p (h | ⟨hx, ht⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hx, Or.inl ht⟩
  have hQP : cylL N L ⊆ cylN N := by
    rintro p (⟨hx, ht⟩ | ⟨hx, ht | ht⟩)
    · exact ⟨hLN hx, ht⟩
    · exact ⟨hx, by rw [mem_Icc, ht]; norm_num⟩
    · exact ⟨hx, by rw [mem_Icc, ht]; norm_num⟩
  have hfc : Continuous fun p : I × ℝ => (1 - (p.1 : ℝ)) * p.2 :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul continuous_snd
  have hmul : ∀ (s : I) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → (1 - (s : ℝ)) * t ∈ Icc (0 : ℝ) 1 :=
    fun s t ht => ⟨mul_nonneg (by linarith [s.2.2]) ht.1,
      (mul_le_of_le_one_left ht.1 (by linarith [s.2.1])).trans ht.2⟩
  have hs1 : ∀ k, Subsingleton (singH K (X × ℝ) k (cylN N) Q₁) :=
    singH_subsingleton_of_cylDeform K (hQ₁Q.trans hQP) (fun s t => (1 - (s : ℝ)) * t) hfc
      (fun s p hp => ⟨hp.1, hmul s _ hp.2⟩) (fun t => by simp)
      (fun p hp => Or.inr ⟨hp.1, by simp⟩)
      (by
        rintro s p (⟨hx, ht⟩ | ⟨hx, ht⟩)
        · exact Or.inl ⟨hx, hmul s _ ht⟩
        · refine Or.inr ⟨hx, ?_⟩
          rw [mem_singleton_iff] at ht ⊢
          simp [ht])
  have b1 := singδ_bijective_of_subsingleton K hQ₁Q hQP hs1 k
  -- excision of `{t < 2/3}` from `Q`
  let B₀ : Set (X × ℝ) := L ×ˢ Icc (1 / 2) 1 ∪ N ×ˢ {1}
  have hB₀Q : B₀ ⊆ cylL N L := by
    rintro p (⟨hx, ht⟩ | ⟨hx, ht⟩)
    · exact Or.inl ⟨hx, ⟨by linarith [ht.1], ht.2⟩⟩
    · exact Or.inr ⟨hx, Or.inr ht⟩
  have b2 := excision K hQ₁Q hB₀Q (isOpen_lt continuous_snd continuous_const :
      IsOpen {p : X × ℝ | p.2 < 2 / 3})
    (isOpen_lt continuous_const continuous_snd : IsOpen {p : X × ℝ | 1 / 2 < p.2})
    (fun p _ => by
      by_cases h : p.2 < 2 / 3
      · exact Or.inl h
      · exact Or.inr (show 1 / 2 < p.2 by linarith [not_lt.1 h]))
    (by
      rintro p ⟨hp, ⟨hx, ht⟩ | ⟨hx, ht | ht⟩⟩
      · exact Or.inl ⟨hx, ht⟩
      · exact Or.inr ⟨hx, ht⟩
      · exfalso
        have : p.2 < 2 / 3 := hp
        rw [ht] at this
        norm_num at this)
    (by
      rintro p ⟨hp, ⟨hx, ht⟩ | ⟨hx, ht | ht⟩⟩
      · exact Or.inl ⟨hx, ⟨le_of_lt hp, ht.2⟩⟩
      · exfalso
        have : 1 / 2 < p.2 := hp
        rw [ht] at this
        norm_num at this
      · exact Or.inr ⟨hx, ht⟩) k
  -- `H_*(B₀, Q₁) ≅ H_*(B₀, L × [1/2, 1])`
  let A₂ : Set (X × ℝ) := L ×ˢ Icc (1 / 2) 1
  have b3 := singMap_bijective K (ContinuousMap.id (X × ℝ)) (B := B₀) (A := Q₁) (B' := B₀)
    (A' := A₂) (fun p hp => hp) (fun p hp => ⟨p, hp, rfl⟩) IsEmbedding.subtypeVal
    (by
      intro p hp
      show p ∈ Q₁ ↔ p ∈ A₂
      rcases hp with ⟨hx, ht⟩ | ⟨hx, ht⟩
      · refine ⟨fun _ => ⟨hx, ht⟩, fun _ => Or.inl ⟨hx, ⟨by linarith [ht.1], ht.2⟩⟩⟩
      · rw [mem_singleton_iff] at ht
        constructor
        · rintro (⟨hx', -⟩ | ⟨-, ht'⟩)
          · exact ⟨hx', by rw [ht]; norm_num⟩
          · rw [mem_singleton_iff, ht] at ht'
            norm_num at ht'
        · rintro ⟨hx', -⟩
          exact Or.inl ⟨hx', by rw [mem_Icc, ht]; norm_num⟩) k
  -- `H_*(B₀, L × {1}) ≅ H_*(B₀, A₂)`
  let L₁ : Set (X × ℝ) := L ×ˢ {1}
  let N₁ : Set (X × ℝ) := N ×ˢ {1}
  have hL₁A₂ : L₁ ⊆ A₂ := fun p hp => ⟨hp.1, by rw [mem_singleton_iff.1 hp.2]; norm_num⟩
  have hA₂B₀ : A₂ ⊆ B₀ := fun p hp => Or.inl hp
  have hgc : Continuous fun p : I × ℝ => p.2 + (p.1 : ℝ) * (1 - p.2) :=
    continuous_snd.add ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_const.sub continuous_snd))
  have hup : ∀ (s : I) (t : ℝ), t ∈ Icc (1 / 2 : ℝ) 1 → t + (s : ℝ) * (1 - t) ∈ Icc (1 / 2 : ℝ) 1 :=
    fun s t ht => ⟨by linarith [mul_nonneg s.2.1 (sub_nonneg.2 ht.2), ht.1],
      by linarith [mul_le_of_le_one_left (sub_nonneg.2 ht.2) s.2.2]⟩
  have hs4 : ∀ k, Subsingleton (singH K (X × ℝ) k A₂ L₁) :=
    singH_subsingleton_of_cylDeform K hL₁A₂ (fun s t => t + (s : ℝ) * (1 - t)) hgc
      (fun s p hp => ⟨hp.1, hup s _ hp.2⟩) (fun t => by simp)
      (fun p hp => ⟨hp.1, by simp⟩)
      (fun s p hp => ⟨hp.1, by rw [mem_singleton_iff.1 hp.2]; simp⟩)
  have b4 := singIncl_bijective_of_subsingleton K hL₁A₂ hA₂B₀ hs4 k
  -- `H_*(N × {1}, L × {1}) ≅ H_*(B₀, L × {1})`
  have hL₁N₁ : L₁ ⊆ N₁ := fun p hp => ⟨hLN hp.1, hp.2⟩
  have hN₁B₀ : N₁ ⊆ B₀ := fun p hp => Or.inr hp
  have hs5 : ∀ k, Subsingleton (singH K (X × ℝ) k B₀ N₁) :=
    singH_subsingleton_of_cylDeform K hN₁B₀ (fun s t => t + (s : ℝ) * (1 - t)) hgc
      (by
        rintro s p (⟨hx, ht⟩ | ⟨hx, ht⟩)
        · exact Or.inl ⟨hx, hup s _ ht⟩
        · exact Or.inr ⟨hx, by rw [mem_singleton_iff.1 ht]; simp⟩)
      (fun t => by simp)
      (by
        rintro p (⟨hx, -⟩ | ⟨hx, -⟩)
        · exact ⟨hLN hx, by simp⟩
        · exact ⟨hx, by simp⟩)
      (fun s p hp => ⟨hp.1, by rw [mem_singleton_iff.1 hp.2]; simp⟩)
  have b5 := singIncl_bijective_of_subsingleton' K hL₁N₁ hN₁B₀ hs5 k
  -- `H_*(N, L) ≅ H_*(N × {1}, L × {1})`
  let i₁ : C(X, X × ℝ) := ⟨fun x => (x, 1), continuous_id.prodMk continuous_const⟩
  have b6 := singMap_bijective K i₁ (B := N) (A := L) (B' := N₁) (A' := L₁)
    (fun x hx => ⟨hx, rfl⟩)
    (fun p hp => ⟨p.1, hp.1, Prod.ext rfl (mem_singleton_iff.1 hp.2).symm⟩)
    ((isEmbedding_prodMkLeft (1 : ℝ)).comp IsEmbedding.subtypeVal)
    (fun x _ => ⟨fun h => ⟨h, rfl⟩, fun h => h.1⟩) k
  exact ⟨(LinearEquiv.ofBijective _ b1).trans ((LinearEquiv.ofBijective _ b2).symm.trans
    ((LinearEquiv.ofBijective _ b3).trans ((LinearEquiv.ofBijective _ b4).symm.trans
    ((LinearEquiv.ofBijective _ b5).symm.trans (LinearEquiv.ofBijective _ b6).symm))))⟩

end Suspension

end ConleyCheck.Conley
