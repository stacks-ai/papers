import ConleyCheck.ON.Blocks
import ConleyCheck.Conley.MorseHomology
import ConleyCheck.Conley.SphereHomology

/-!
# Corollary `cor:ON`(ii), (iii): homology indices and connecting orbits of the `O(N)` model

For `N ≠ 4` the four fixed points form a Morse decomposition of `B_N` with the order
`Σ_G < Σ_I, s < o`, where `s` is the second saddle and `o` the source (`s = Σ_H`, `o = Σ_C` for
`N > 4` and `s = Σ_C`, `o = Σ_H` for `1 < N < 4`), and the two saddles are unrelated.

* `isMorseDecomp_diamond`: the Morse decomposition. Orbits between the saddles are excluded since
  they would lie on the invariant line through their `α`-limit.
* `cor_ON_ii`, `cor_ON_iii`: over any ring `K` the homology indices are `K[0], K[1], K[1], K[2]`,
  and each of the four pairs `(Σ_G, Σ_I)`, `(Σ_G, s)`, `(Σ_I, o)`, `(s, o)` is an
  attractor–repeller pair in an isolated invariant set with trivial homology index, so that all its
  connecting homomorphisms are isomorphisms.
* `cor_ON_ii_orbits`, `cor_ON_iii_orbits`: bounded solutions running from the source to both
  saddles.
-/

open Set Filter Topology

namespace ConleyCheck.ON

open ConleyCheck.Conley ConleyCheck.ODE ConleyCheck.Gubser

variable {N : ℝ}

/-! ## The Morse decomposition with unrelated saddles -/

theorem isMorseDecomp_diamond (hN : 1 < N) (h4 : N ≠ 4) {σ : Fin 4 → Fin 4}
    (hσ : Function.Injective σ) (hσ0 : σ 0 = 0) (hσ1 : σ 1 = 1)
    (hVs : Vp N (pts N (σ 2)) < Vp N (pts N (σ 3))) (hVI : Vp N ptI < Vp N (pts N (σ 3)))
    (hs2 : (pts N (σ 2)).2 ≠ 0) {k a b : ℝ}
    (hid : ∀ y₁ y₂, f₂ N y₁ y₂ - k * f₁ N y₁ y₂ = -(y₂ - k * y₁) * (1 + a * y₁ + b * y₂))
    (hsl : (pts N (σ 2)).2 = k * (pts N (σ 2)).1)
    (hpos : 0 < 1 + a * (pts N (σ 2)).1 + b * (pts N (σ 2)).2) (hk : k ≠ 0) :
    IsMorseDecomp (flowON N) (boundedOrbits N) (fun i => {pts N (σ i)}) diamond where
  isolated := isIsolatedInvariantSet_B hN
  isolated_M i := isIsolated_zero hN (isZero_pts hN (σ i))
  subset i := singleton_subset_iff.2 (zero_mem_B hN (isZero_pts hN (σ i)))
  disjoint i j hij := disjoint_singleton.2 fun h => hij (hσ (pts_injective hN h4 h))
  irrefl := diamond_irrefl
  trans := diamond_trans
  connecting x hx hM := by
    have hxR : x ∈ Inv (flowON N) blockR := by rw [Inv_R_eq hN]; exact hx
    obtain ⟨p, q, hp, hq, hpT, hqT⟩ := tendsto_of_mem_Inv hN hxR
    have hsurj : Function.Surjective σ := Finite.injective_iff_surjective.1 hσ
    have hex : ∀ z, IsZero N z → ∃ i, pts N (σ i) = z := fun z hz => by
      obtain ⟨i', hi'⟩ := exists_pts_eq hN hz
      obtain ⟨i, rfl⟩ := hsurj i'
      exact ⟨i, hi'⟩
    obtain ⟨i, rfl⟩ := hex p hp
    obtain ⟨j, rfl⟩ := hex q hq
    refine ⟨i, j, ?_, fun z hz => eq_of_tendsto_of_mem_omegaLim hpT hz,
      fun z hz => eq_of_tendsto_of_mem_alphaLim hqT hz⟩
    have hlt : Vp N (pts N (σ i)) < Vp N (pts N (σ j)) := by
      by_contra hle
      push Not at hle
      obtain ⟨m, hm⟩ := hex x (isZero_of_V_le hN hxR hpT hqT hle)
      exact hM m hm.symm
    have hij : i ≠ j := by rintro rfl; exact lt_irrefl _ hlt
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [hσ0, pts_zero, (Vp_pts hN).1] at hlt
      exact absurd hlt (not_lt.2 (Vp_nonneg_of_zero hN (isZero_pts hN _)))
    have hi3 : i ≠ 3 := by
      rintro rfl
      rcases LBox.fin4 j with rfl | rfl | rfl | rfl
      · exact hj0 rfl
      · rw [hσ1, pts_one] at hlt; linarith
      · linarith
      · exact hij rfl
    have h12 : ¬ (i = 1 ∧ j = 2) := by
      rintro ⟨rfl, rfl⟩
      rw [hσ1, pts_one] at hpT
      have hline := on_line_of_tendsto_atBot hid hxR hqT hsl hpos
      have h1 := (continuous_fst.tendsto ptI).comp hpT
      have h2 := (continuous_snd.tendsto ptI).comp hpT
      have h2' : Tendsto (fun t => (flowON N t x).2) atTop (𝓝 ptI.2) := h2
      rw [show (fun t => (flowON N t x).2) = fun t => k * (flowON N t x).1 from
        funext hline] at h2'
      have := tendsto_nhds_unique h2' (h1.const_mul k)
      simp only [ptI] at this
      exact hk (by linarith)
    have h21 : ¬ (i = 2 ∧ j = 1) := by
      rintro ⟨rfl, rfl⟩
      rw [hσ1, pts_one] at hqT
      have hline := on_line_of_tendsto_atBot axis_identity hxR hqT (by simp [ptI])
        (by simp [ptI]; norm_num)
      have h1 := (continuous_fst.tendsto _).comp hpT
      have h2 := (continuous_snd.tendsto _).comp hpT
      have h2' : Tendsto (fun t => (flowON N t x).2) atTop (𝓝 (pts N (σ 2)).2) := h2
      rw [show (fun t => (flowON N t x).2) = fun t => 0 * (flowON N t x).1 from
        funext hline] at h2'
      have := tendsto_nhds_unique h2' (h1.const_mul 0)
      exact hs2 (by rw [this, zero_mul])
    unfold diamond
    omega

/-! ## Trivial homology of the attractors `{Σ_G, Σ_I}` and `{Σ_G, s}` -/

theorem morseAttr_pts {σ : Fin 4 → Fin 4} (hσ0 : σ 0 = 0) (k : Fin 4) :
    morseAttr (flowON N) (boundedOrbits N) (fun i => {pts N (σ i)}) {0, k} =
      attrPts N {ptG, pts N (σ k)} := by
  ext x
  constructor
  · rintro ⟨hx, j, hj, hα⟩
    rcases hj with rfl | rfl
    · have hα' : alphaLim (flowON N) x ⊆ {pts N (σ 0)} := hα
      exact ⟨hx, ptG, Or.inl rfl, by rwa [hσ0] at hα'⟩
    · exact ⟨hx, _, Or.inr rfl, hα⟩
  · rintro ⟨hx, q, hq, hα⟩
    rcases hq with rfl | rfl
    · refine ⟨hx, 0, Or.inl rfl, ?_⟩
      show alphaLim (flowON N) x ⊆ {pts N (σ 0)}
      rwa [hσ0]
    · exact ⟨hx, k, Or.inr rfl, hα⟩

theorem morseAttr_pts_id (k : Fin 4) :
    morseAttr (flowON N) (boundedOrbits N) (fun i => {pts N i}) {0, k} =
      attrPts N {ptG, pts N k} :=
  morseAttr_pts (σ := id) rfl k

/-! ## Bounded solutions through points of `B_N` -/

theorem isSol_of_mem_B (hN : 1 < N) {x : ℝ × ℝ} (hx : x ∈ boundedOrbits N) :
    IsSol (field N) (fun t => flowON N t x) ∧
      Bornology.IsBounded (range fun t => flowON N t x) := by
  have hxR : x ∈ Inv (flowON N) blockR := by rw [Inv_R_eq hN]; exact hx
  refine ⟨fun t => ?_, isCompact_Inv_R.isBounded.subset
    (range_subset_iff.2 fun t => flow_mem_Inv hxR t)⟩
  rw [← cutField_eq_on_R (hxR t)]
  exact hasDerivAt_flowON N x t

/-- An orbit of `B_N` with `ω`-limit in `{p}` and `α`-limit in `{q}` converges to `p` and `q`. -/
theorem tendsto_of_limits (hN : 1 < N) {x p q : ℝ × ℝ} (hx : x ∈ boundedOrbits N)
    (hω : omegaLim (flowON N) x ⊆ {p}) (hα : alphaLim (flowON N) x ⊆ {q}) :
    Tendsto (fun t => flowON N t x) atTop (𝓝 p) ∧
      Tendsto (fun t => flowON N t x) atBot (𝓝 q) := by
  have hxR : x ∈ Inv (flowON N) blockR := by rw [Inv_R_eq hN]; exact hx
  obtain ⟨p', q', -, -, hpT, hqT⟩ := tendsto_of_mem_Inv hN hxR
  have hp : p' = p := hω ((mem_omegaLimit_singleton_iff_mapClusterPt (f := atTop)
    (ϕ := (flowON N).toFun) x p').2 hpT.mapClusterPt)
  have hq : q' = q := hα (tendsto_mem_alphaLim hqT)
  exact ⟨hp ▸ hpT, hq ▸ hqT⟩

/-! ## The case `N > 4` -/

/-- The order `Σ_G, Σ_I, Σ_H, Σ_C` of the fixed points for `N > 4`. -/
def σgt : Fin 4 → Fin 4 := ![0, 1, 3, 2]

theorem Vp_H_lt_C (hN : 4 < N) : Vp N (ptH N) < Vp N (ptC N) := by
  have hN1 : 1 < N := by linarith
  obtain ⟨-, -, hC, hH⟩ := Vp_pts hN1
  rw [hC, hH, div_lt_div_iff₀ (by positivity) (by positivity)]
  have : 0 < (N + 2) * (N - 4) ^ 3 := by
    have : 0 < N - 4 := by linarith
    positivity
  nlinarith [this]

theorem Vp_I_lt_C (hN : 2 < N) : Vp N ptI < Vp N (ptC N) := by
  obtain ⟨-, hI, hC, -⟩ := Vp_pts (N := N) (by linarith)
  rw [hI, hC, div_lt_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

theorem ptH_pos (hN : 4 < N) : 0 < 1 + 9 * (ptH N).1 + 3 * (ptH N).2 := by
  simp only [ptH]
  rw [show 1 + 9 * (-1 / (N + 8)) + 3 * (-1 / (N + 8)) = (N - 4) * (1 / (N + 8)) by
    field_simp; ring]
  have : 0 < N - 4 := by linarith
  have : 0 < N + 8 := by linarith
  positivity

theorem isMorseDecomp_gt (hN : 4 < N) :
    IsMorseDecomp (flowON N) (boundedOrbits N) (fun i => {pts N (σgt i)}) diamond :=
  isMorseDecomp_diamond (by linarith) (by linarith) (by decide) rfl rfl (Vp_H_lt_C hN)
    (Vp_I_lt_C (by linarith))
    (by simp only [σgt, pts]; simp only [ptH]; exact div_ne_zero (by norm_num) (by linarith))
    diagonal_identity (ptH_line N) (ptH_pos hN) one_ne_zero

/-- Corollary `cor:ON`(ii). For `N > 4` the fixed points `Σ_G < Σ_I, Σ_H < Σ_C` form a Morse
decomposition of `B_N` in which the saddles `Σ_I` and `Σ_H` are unrelated, with homology indices
`K[0], K[1], K[1], K[2]` over any ring `K`. Each of the pairs `(Σ_G, Σ_I)`, `(Σ_G, Σ_H)`,
`(Σ_I, Σ_C)`, `(Σ_H, Σ_C)` is an attractor–repeller pair in an isolated invariant set with trivial
homology index, so all of its connecting homomorphisms are isomorphisms. -/
theorem cor_ON_ii (hN : 4 < N) (K : Type) [Ring K] :
    ∃ h : IsMorseDecomp (flowON N) (boundedOrbits N) (fun i => {pts N (σgt i)}) diamond,
      HasHomologyIndex K (h.isolated_M 0) 0 ∧ HasHomologyIndex K (h.isolated_M 1) 1 ∧
      HasHomologyIndex K (h.isolated_M 2) 1 ∧ HasHomologyIndex K (h.isolated_M 3) 2 ∧
      IsTrivialPair K (flowON N) {ptG} {ptI} ∧ IsTrivialPair K (flowON N) {ptG} {ptH N} ∧
      IsTrivialPair K (flowON N) {ptI} {ptC N} ∧ IsTrivialPair K (flowON N) {ptH N} {ptC N} := by
  have hN1 : 1 < N := by linarith
  have h := isMorseDecomp_gt hN
  have hS : HasTrivialHomologyIndex K h.isolated := (prop_ON_c hN1 K).2
  have h0 : HasHomologyIndex K (h.isolated_M 0) 0 :=
    HasIndex.homologyIndex_sphere K _ (hasIndex_G hN1)
  have h01 : ∀ hA : IsIsolatedInvariantSet (flowON N)
      (morseAttr (flowON N) (boundedOrbits N) (fun i => {pts N (σgt i)}) {0, 1}),
      HasTrivialHomologyIndex K hA := fun hA =>
    hasTrivialHomologyIndex_of_indexPair hA
      (by rw [morseAttr_pts rfl]; exact isIndexPair_I hN1) pointedContractible_I
  have h02 : ∀ hA : IsIsolatedInvariantSet (flowON N)
      (morseAttr (flowON N) (boundedOrbits N) (fun i => {pts N (σgt i)}) {0, 2}),
      HasTrivialHomologyIndex K hA := fun hA =>
    hasTrivialHomologyIndex_of_indexPair hA
      (by rw [morseAttr_pts rfl]; exact isIndexPair_H hN) pointedContractible_H
  exact ⟨h, h0, diamond_middle h h0 h01 h02 (Or.inl rfl), diamond_middle h h0 h01 h02 (Or.inr rfl),
    diamond_top h hS h0 h01 h02, diamond_trivialPair_bottom h h01 h02 (Or.inl rfl),
    diamond_trivialPair_bottom h h01 h02 (Or.inr rfl),
    diamond_trivialPair_top h hS h01 h02 (Or.inl ⟨rfl, rfl⟩),
    diamond_trivialPair_top h hS h01 h02 (Or.inr ⟨rfl, rfl⟩)⟩

/-- Corollary `cor:ON`(ii), connecting orbits. For `N > 4` there are bounded solutions running from
`Σ_C` to `Σ_I` and from `Σ_C` to `Σ_H`. -/
theorem cor_ON_ii_orbits (hN : 4 < N) :
    (∃ γ, IsSol (field N) γ ∧ Bornology.IsBounded (range γ) ∧
      Tendsto γ atBot (𝓝 (ptC N)) ∧ Tendsto γ atTop (𝓝 ptI)) ∧
    (∃ γ, IsSol (field N) γ ∧ Bornology.IsBounded (range γ) ∧
      Tendsto γ atBot (𝓝 (ptC N)) ∧ Tendsto γ atTop (𝓝 (ptH N))) := by
  have hN1 : 1 < N := by linarith
  have h := isMorseDecomp_gt hN
  have hS : HasTrivialHomologyIndex ℤ h.isolated := (prop_ON_c hN1 ℤ).2
  have h0 : HasHomologyIndex ℤ (h.isolated_M 0) 0 :=
    HasIndex.homologyIndex_sphere ℤ _ (hasIndex_G hN1)
  have h01 : ∀ hA : IsIsolatedInvariantSet (flowON N)
      (morseAttr (flowON N) (boundedOrbits N) (fun i => {pts N (σgt i)}) {0, 1}),
      HasTrivialHomologyIndex ℤ hA := fun hA =>
    hasTrivialHomologyIndex_of_indexPair hA
      (by rw [morseAttr_pts rfl]; exact isIndexPair_I hN1) pointedContractible_I
  have h02 : ∀ hA : IsIsolatedInvariantSet (flowON N)
      (morseAttr (flowON N) (boundedOrbits N) (fun i => {pts N (σgt i)}) {0, 2}),
      HasTrivialHomologyIndex ℤ hA := fun hA =>
    hasTrivialHomologyIndex_of_indexPair hA
      (by rw [morseAttr_pts rfl]; exact isIndexPair_H hN) pointedContractible_H
  have key : ∀ l : Fin 4, (l = 1 ∨ l = 2) → ∃ γ, IsSol (field N) γ ∧
      Bornology.IsBounded (range γ) ∧ Tendsto γ atBot (𝓝 (ptC N)) ∧
      Tendsto γ atTop (𝓝 (pts N (σgt l))) := by
    intro l hl
    have hkl : (l = 1 ∧ (3 - l : Fin 4) = 2) ∨ (l = 2 ∧ (3 - l : Fin 4) = 1) := by
      rcases hl with rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    obtain ⟨x, hx, -, -, hω, hα⟩ := diamond_orbit_top h hS h0 h01 h02 hkl
    obtain ⟨hsol, hb⟩ := isSol_of_mem_B hN1 hx
    obtain ⟨hpT, hqT⟩ := tendsto_of_limits hN1 hx hω hα
    exact ⟨_, hsol, hb, hqT, hpT⟩
  exact ⟨key 1 (Or.inl rfl), key 2 (Or.inr rfl)⟩

/-! ## The case `1 < N < 4` -/

theorem Vp_C_lt_H (h1 : 1 < N) (hN : N < 4) : Vp N (ptC N) < Vp N (ptH N) := by
  obtain ⟨-, -, hC, hH⟩ := Vp_pts h1
  have hN0 : 0 < N := by linarith
  rw [hC, hH, div_lt_div_iff₀ (by positivity) (by positivity)]
  have : 0 < (N + 2) * (4 - N) ^ 3 := by
    have : 0 < 4 - N := by linarith
    positivity
  nlinarith [this]

theorem Vp_I_lt_H (h1 : 1 < N) (hN : N < 10) : Vp N ptI < Vp N (ptH N) := by
  obtain ⟨-, hI, -, hH⟩ := Vp_pts h1
  rw [hI, hH, div_lt_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

theorem ptC_pos (h1 : 1 < N) (hN : N < 4) : 0 < 1 + 9 * (ptC N).1 + (N - 1) * (ptC N).2 := by
  have hN0 : 0 < N := by linarith
  simp only [ptC]
  rw [show 1 + 9 * (-(N - 1) / (9 * N)) + (N - 1) * (-1 / (3 * N)) = (4 - N) / (3 * N) by
    field_simp; ring]
  have : 0 < 4 - N := by linarith
  positivity

theorem isMorseDecomp_lt (h1 : 1 < N) (hN : N < 4) :
    IsMorseDecomp (flowON N) (boundedOrbits N) (fun i => {pts N i}) diamond :=
  isMorseDecomp_diamond (σ := id) h1 (by linarith) Function.injective_id rfl rfl
    (Vp_C_lt_H h1 hN) (Vp_I_lt_H h1 (by linarith))
    (by simp only [id, pts_two, ptC]; exact div_ne_zero (by norm_num) (by positivity))
    (third_identity h1) (ptC_line h1) (ptC_pos h1 hN) (div_ne_zero (by norm_num) (by linarith))

/-- Corollary `cor:ON`(iii). For `1 < N < 4` the fixed points `Σ_G < Σ_I, Σ_C < Σ_H` form a Morse
decomposition of `B_N` in which the saddles `Σ_I` and `Σ_C` are unrelated, with homology indices
`K[0], K[1], K[1], K[2]` over any ring `K`. Each of the pairs `(Σ_G, Σ_I)`, `(Σ_G, Σ_C)`,
`(Σ_I, Σ_H)`, `(Σ_C, Σ_H)` is an attractor–repeller pair in an isolated invariant set with trivial
homology index, so all of its connecting homomorphisms are isomorphisms. -/
theorem cor_ON_iii (h1 : 1 < N) (hN : N < 4) (K : Type) [Ring K] :
    ∃ h : IsMorseDecomp (flowON N) (boundedOrbits N) (fun i => {pts N i}) diamond,
      HasHomologyIndex K (h.isolated_M 0) 0 ∧ HasHomologyIndex K (h.isolated_M 1) 1 ∧
      HasHomologyIndex K (h.isolated_M 2) 1 ∧ HasHomologyIndex K (h.isolated_M 3) 2 ∧
      IsTrivialPair K (flowON N) {ptG} {ptI} ∧ IsTrivialPair K (flowON N) {ptG} {ptC N} ∧
      IsTrivialPair K (flowON N) {ptI} {ptH N} ∧ IsTrivialPair K (flowON N) {ptC N} {ptH N} := by
  have h := isMorseDecomp_lt h1 hN
  have hS : HasTrivialHomologyIndex K h.isolated := (prop_ON_c h1 K).2
  have h0 : HasHomologyIndex K (h.isolated_M 0) 0 :=
    HasIndex.homologyIndex_sphere K _ (hasIndex_G h1)
  have h01 : ∀ hA : IsIsolatedInvariantSet (flowON N)
      (morseAttr (flowON N) (boundedOrbits N) (fun i => {pts N i}) {0, 1}),
      HasTrivialHomologyIndex K hA := fun hA =>
    hasTrivialHomologyIndex_of_indexPair hA
      (by rw [morseAttr_pts_id]; exact isIndexPair_I h1) pointedContractible_I
  have h02 : ∀ hA : IsIsolatedInvariantSet (flowON N)
      (morseAttr (flowON N) (boundedOrbits N) (fun i => {pts N i}) {0, 2}),
      HasTrivialHomologyIndex K hA := fun hA =>
    hasTrivialHomologyIndex_of_indexPair hA
      (by rw [morseAttr_pts_id]; exact isIndexPair_C h1 hN) pointedContractible_C
  exact ⟨h, h0, diamond_middle h h0 h01 h02 (Or.inl rfl), diamond_middle h h0 h01 h02 (Or.inr rfl),
    diamond_top h hS h0 h01 h02, diamond_trivialPair_bottom h h01 h02 (Or.inl rfl),
    diamond_trivialPair_bottom h h01 h02 (Or.inr rfl),
    diamond_trivialPair_top h hS h01 h02 (Or.inl ⟨rfl, rfl⟩),
    diamond_trivialPair_top h hS h01 h02 (Or.inr ⟨rfl, rfl⟩)⟩

/-- Corollary `cor:ON`(iii), connecting orbits. For `1 < N < 4` there are bounded solutions running
from `Σ_H` to `Σ_I` and from `Σ_H` to `Σ_C`. -/
theorem cor_ON_iii_orbits (h1 : 1 < N) (hN : N < 4) :
    (∃ γ, IsSol (field N) γ ∧ Bornology.IsBounded (range γ) ∧
      Tendsto γ atBot (𝓝 (ptH N)) ∧ Tendsto γ atTop (𝓝 ptI)) ∧
    (∃ γ, IsSol (field N) γ ∧ Bornology.IsBounded (range γ) ∧
      Tendsto γ atBot (𝓝 (ptH N)) ∧ Tendsto γ atTop (𝓝 (ptC N))) := by
  have h := isMorseDecomp_lt h1 hN
  have hS : HasTrivialHomologyIndex ℤ h.isolated := (prop_ON_c h1 ℤ).2
  have h0 : HasHomologyIndex ℤ (h.isolated_M 0) 0 :=
    HasIndex.homologyIndex_sphere ℤ _ (hasIndex_G h1)
  have h01 : ∀ hA : IsIsolatedInvariantSet (flowON N)
      (morseAttr (flowON N) (boundedOrbits N) (fun i => {pts N i}) {0, 1}),
      HasTrivialHomologyIndex ℤ hA := fun hA =>
    hasTrivialHomologyIndex_of_indexPair hA
      (by rw [morseAttr_pts_id]; exact isIndexPair_I h1) pointedContractible_I
  have h02 : ∀ hA : IsIsolatedInvariantSet (flowON N)
      (morseAttr (flowON N) (boundedOrbits N) (fun i => {pts N i}) {0, 2}),
      HasTrivialHomologyIndex ℤ hA := fun hA =>
    hasTrivialHomologyIndex_of_indexPair hA
      (by rw [morseAttr_pts_id]; exact isIndexPair_C h1 hN) pointedContractible_C
  have key : ∀ l : Fin 4, (l = 1 ∨ l = 2) → ∃ γ, IsSol (field N) γ ∧
      Bornology.IsBounded (range γ) ∧ Tendsto γ atBot (𝓝 (ptH N)) ∧
      Tendsto γ atTop (𝓝 (pts N l)) := by
    intro l hl
    have hkl : (l = 1 ∧ (3 - l : Fin 4) = 2) ∨ (l = 2 ∧ (3 - l : Fin 4) = 1) := by
      rcases hl with rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    obtain ⟨x, hx, -, -, hω, hα⟩ := diamond_orbit_top h hS h0 h01 h02 hkl
    obtain ⟨hsol, hb⟩ := isSol_of_mem_B h1 hx
    obtain ⟨hpT, hqT⟩ := tendsto_of_limits h1 hx hω hα
    exact ⟨_, hsol, hb, hqT, hpT⟩
  exact ⟨key 1 (Or.inl rfl), key 2 (Or.inr rfl)⟩

end ConleyCheck.ON
