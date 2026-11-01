import ConleyCheck.ON.RampMorse
import ConleyCheck.Conley.FaceUniform

/-!
# Index data of the parameter shift

Proposition `prop:ONramp`(iii), over any ring `K`. In the Morse decomposition of `S♮` by the eight
fixed points of the double (`Ramp.isMorseDecomp`),

* `(Σ_G^+, Σ_G^-)` and `(Σ_I^+, Σ_I^-)` are attractor–repeller pairs in isolated invariant sets
  with trivial homology index, so their connecting homomorphisms are isomorphisms
  (`trivialPair_G`, `trivialPair_I`);
* the Morse set `M_A` of the interval `{Σ_I^+, Σ_C^+, Σ_H^+}` and `Σ_H^-` form an attractor–repeller
  pair in an isolated invariant set with trivial homology index, so the connecting homomorphisms
  `CH_{k+1}(Σ_H^-) → CH_k(M_A)` are isomorphisms (`trivialPair_H`).

The sets with trivial index come from two further common blocks, the square `B_G` around `Σ_G`,
which has empty exit set, and the strip `B_I = {y ∈ R | |y_2| ≤ e}` along the axis, together with
`R` itself and the Morse set of `{Σ_I^-, Σ_C^-}` in the UV row. An orbit of `S♮` lies in `B_G♮`
exactly if it comes from `Σ_G^±`, and in `B_I♮` exactly if it comes from `Σ_G^±` or `Σ_I^±`, by the
rigidity statements `eq_zero_of_tendsto_atBot` and `snd_eq_zero_of_tendsto_atBot`.
-/

open Set Filter Topology Metric Function

namespace ConleyCheck.ON

open ConleyCheck.Conley ConleyCheck.ODE

section Aux

variable {K : Type} [Ring K] {α : Type} [TopologicalSpace α] [T2Space α] {ϕ : Flow ℝ α}

theorem trivial_congr {S T : Set α} (e : S = T) {hS : IsIsolatedInvariantSet ϕ S}
    {hT : IsIsolatedInvariantSet ϕ T} (h : HasTrivialHomologyIndex K hS) :
    HasTrivialHomologyIndex K hT := by
  subst e; exact h

theorem trivial_R {S A R : Set α} (hp : IsAttractorRepellerPair ϕ S A R)
    (hS : HasTrivialHomologyIndex K hp.isolated) (hA : HasTrivialHomologyIndex K hp.isolated_A) :
    HasTrivialHomologyIndex K hp.isolated_R := by
  obtain ⟨h0, d, hd⟩ := exists_connecting_iso_of_trivial hp hS
  intro n
  cases n with
  | zero => exact h0
  | succ n =>
    have := hA n
    exact (hd n).1.subsingleton

theorem trivial_A {S A R : Set α} (hp : IsAttractorRepellerPair ϕ S A R)
    (hS : HasTrivialHomologyIndex K hp.isolated) (hR : HasTrivialHomologyIndex K hp.isolated_R) :
    HasTrivialHomologyIndex K hp.isolated_A := by
  obtain ⟨-, d, hd⟩ := exists_connecting_iso_of_trivial hp hS
  intro n
  have := hR (n + 1)
  exact (hd n).2.subsingleton

end Aux

theorem Inv_boxG {N M : ℝ} (hN : 1 < N) (hNM : N ≤ M) : Inv (flowON N) (boxG M).set = {ptG} := by
  have hsub : (boxG M).set ⊆ (boxG N).set := fun p hp => by
    obtain ⟨h1, h2, h3, h4⟩ := mem_boxG.1 hp
    have : eG M ≤ eG N := by
      unfold eG; exact one_div_le_one_div_of_le (by linarith) (by linarith)
    exact mem_boxG.2 ⟨by linarith, by linarith, by linarith, by linarith⟩
  refine subset_antisymm ((Inv_mono hsub).trans (Inv_G hN).subset) ?_
  rintro _ rfl t
  rw [flowON_eq_of_zero hN (isZero_G N)]
  have := eG_pos (hN.trans_le hNM)
  exact mem_boxG.2 ⟨by simp [ptG]; linarith, by simp [ptG]; linarith, by simp [ptG]; linarith,
    by simp [ptG]; linarith⟩

theorem idx_of_snd {N M : ℝ} (hN : 1 < N) (hNM : N ≤ M) {i : Fin 4} (h : -eG M ≤ (pts N i).2) :
    i = 0 ∨ i = 1 := by
  have hC : eG M < 1 / (3 * N) := by
    unfold eG; rw [div_lt_div_iff₀ (by linarith) (by linarith)]; linarith
  have hH : eG M < 1 / (N + 8) := by
    unfold eG; rw [div_lt_div_iff₀ (by linarith) (by linarith)]; linarith
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exfalso
    change -eG M ≤ (ptC N).2 at h
    simp only [ptC] at h
    have : -1 / (3 * N) = -(1 / (3 * N)) := by ring
    linarith
  · exfalso
    change -eG M ≤ (ptH N).2 at h
    simp only [ptH] at h
    have : -1 / (N + 8) = -(1 / (N + 8)) := by ring
    linarith

theorem idx_of_mem_boxG {N M : ℝ} (hN : 1 < N) (hNM : N ≤ M) {i : Fin 4}
    (h : pts N i ∈ (boxG M).set) : i = 0 := by
  obtain ⟨h1, -, -, h4⟩ := mem_boxG.1 h
  have hle := eG_le (hN.trans_le hNM)
  rcases idx_of_snd hN hNM h4 with h0 | rfl
  · exact h0
  · exfalso
    change -eG M ≤ ptI.1 at h1
    simp only [ptI] at h1
    linarith

namespace Ramp

variable (P : Ramp)

/-! ## Common blocks of the parameter shift -/

theorem N_le_bN (b : Tau) : P.N b ≤ P.bN := (le_abs_self _).trans (P.abs_N_le b.2)

theorem one_lt_bN : 1 < P.bN := P.one_lt_top.trans_le (P.N_le_bN Tau.top)

theorem eG_mul_le (b : Tau) : (P.N b + 8) * eG P.bN ≤ 1 / 100 := by
  have h := eG_mul P.one_lt_bN
  have := P.N_le_bN b
  have := eG_pos P.one_lt_bN
  nlinarith

theorem hasDerivAt_g_Φ (B : LBox) {p : ℝ × ℝ} (hp : ‖p‖ ≤ 1) (b : Tau) (k : Fin 4) :
    HasDerivAt (fun s => B.g k (P.Φ s (p, b)).1) (B.D (P.N b) k p) 0 := by
  have h1 := P.hasDerivAt_fst_zero hp b
  have h2 := P.hasDerivAt_snd_zero hp b
  have hl : HasDerivAt (fun s => B.lam (P.Φ s (p, b)).1) (B.lamF (P.N b) p) 0 :=
    (h1.const_mul B.l₁).add (h2.const_mul B.l₂)
  have hw : HasDerivAt (fun s => B.wc (P.Φ s (p, b)).1) (B.wF (P.N b) p) 0 :=
    (h1.const_mul B.w₁).add (h2.const_mul B.w₂)
  rcases LBox.fin4 k with rfl | rfl | rfl | rfl
  · exact hl.const_sub B.b
  · exact hl.sub_const B.t
  · exact hw.sub_const B.e
  · exact hw.neg.sub_const B.e

/-- A box crossed outward on `λ = b` and inward on its other faces, for every frozen system, is a
common block with exit set `λ = b`. -/
theorem isUniformBlock_box (B : LBox) (hball : ∀ p ∈ B.set, ‖p‖ ≤ 1)
    (h0 : ∀ b : Tau, ∀ p ∈ B.set, B.lam p = B.b → B.lamF (P.N b) p < 0)
    (h1 : ∀ b : Tau, ∀ p ∈ B.set, B.lam p = B.t → B.lamF (P.N b) p < 0)
    (h2 : ∀ b : Tau, ∀ p ∈ B.set, B.wc p = B.e → B.wF (P.N b) p < 0)
    (h3 : ∀ b : Tau, ∀ p ∈ B.set, B.wc p = -B.e → 0 < B.wF (P.N b) p) :
    IsUniformBlock P.Φ B.set B.exit := by
  refine isUniformBlock_of_faces (D := fun k p b => B.D (P.N b) k p) (E := {0})
    B.continuous_g (B.isCompact_set hball) (fun k p b hp => P.hasDerivAt_g_Φ B (hball p hp) b k)
    (fun k hk p b hp hk0 => ?_) (fun k hk p b hp hk0 => ?_)
  · rw [mem_singleton_iff.1 hk] at hk0 ⊢
    have : B.b - B.lam p = 0 := hk0
    show 0 < -B.lamF (P.N b) p
    linarith [h0 b p hp (by linarith)]
  · rcases LBox.fin4 k with rfl | rfl | rfl | rfl
    · exact absurd rfl hk
    · have : B.lam p - B.t = 0 := hk0
      exact h1 b p hp (by linarith)
    · have : B.wc p - B.e = 0 := hk0
      exact h2 b p hp (by linarith)
    · have : -B.wc p - B.e = 0 := hk0
      show -B.wF (P.N b) p < 0
      linarith [h3 b p hp (by linarith)]

/-- A box crossed inward on all four faces, for every frozen system, is a common block with empty
exit set. -/
theorem isUniformBlock_box_attr (B : LBox) (hball : ∀ p ∈ B.set, ‖p‖ ≤ 1)
    (h0 : ∀ b : Tau, ∀ p ∈ B.set, B.lam p = B.b → 0 < B.lamF (P.N b) p)
    (h1 : ∀ b : Tau, ∀ p ∈ B.set, B.lam p = B.t → B.lamF (P.N b) p < 0)
    (h2 : ∀ b : Tau, ∀ p ∈ B.set, B.wc p = B.e → B.wF (P.N b) p < 0)
    (h3 : ∀ b : Tau, ∀ p ∈ B.set, B.wc p = -B.e → 0 < B.wF (P.N b) p) :
    IsUniformBlock P.Φ B.set ∅ := by
  have he : {p | (∀ k, B.g k p ≤ 0) ∧ ∃ k ∈ (∅ : Set (Fin 4)), B.g k p = 0} = ∅ := by
    ext p; simp
  rw [← he]
  refine isUniformBlock_of_faces (D := fun k p b => B.D (P.N b) k p) (E := ∅)
    B.continuous_g (B.isCompact_set hball) (fun k p b hp => P.hasDerivAt_g_Φ B (hball p hp) b k)
    (fun k hk => absurd hk (notMem_empty k)) (fun k _ p b hp hk0 => ?_)
  rcases LBox.fin4 k with rfl | rfl | rfl | rfl
  · have : B.b - B.lam p = 0 := hk0
    show -B.lamF (P.N b) p < 0
    linarith [h0 b p hp (by linarith)]
  · have : B.lam p - B.t = 0 := hk0
    exact h1 b p hp (by linarith)
  · have : B.wc p - B.e = 0 := hk0
    exact h2 b p hp (by linarith)
  · have : -B.wc p - B.e = 0 := hk0
    show -B.wF (P.N b) p < 0
    linarith [h3 b p hp (by linarith)]

/-- The square `B_G = [-e, e]²`, `e = 1/(100(N̄+8))`, with `N̄` a bound for `N`. -/
noncomputable def BG : LBox := boxG P.bN

/-- The strip `B_I = [-1/8, δ] × [-e, e]` of `R` along the axis. -/
noncomputable def BI : LBox := ⟨1, 0, 0, 1, -1 / 8, δ, eG P.bN⟩

theorem mem_BI {p : ℝ × ℝ} :
    p ∈ P.BI.set ↔ -1 / 8 ≤ p.1 ∧ p.1 ≤ δ ∧ p.2 ≤ eG P.bN ∧ -eG P.bN ≤ p.2 := by
  rw [LBox.mem_set]; simp [BI, LBox.lam, LBox.wc]

theorem BG_sub_R : P.BG.set ⊆ blockR := fun p hp => by
  obtain ⟨h1, h2, h3, h4⟩ := mem_boxG.1 hp
  have := eG_le P.one_lt_bN
  exact ⟨⟨by linarith, by simp only [δ]; linarith⟩, by linarith, by simp only [δ]; linarith⟩

theorem BI_sub_R : P.BI.set ⊆ blockR := fun p hp => by
  obtain ⟨h1, h2, h3, h4⟩ := P.mem_BI.1 hp
  have := eG_le P.one_lt_bN
  exact ⟨⟨h1, h2⟩, by linarith, by simp only [δ]; linarith⟩

theorem isUniformBlock_G : IsUniformBlock P.Φ P.BG.set ∅ := by
  have he := eG_pos P.one_lt_bN
  have hle := eG_le P.one_lt_bN
  refine P.isUniformBlock_box_attr P.BG (fun p hp => norm_le_boxG P.one_lt_bN hp) ?_ ?_ ?_ ?_ <;>
    intro b p hp hface <;> obtain ⟨h1, h2, h3, h4⟩ := mem_boxG.1 hp <;>
    have hm := P.eG_mul_le b <;> have hn := P.one_lt b b.2 <;>
    simp only [BG, boxG, LBox.lam, LBox.wc, LBox.lamF, LBox.wF, one_mul, zero_mul, add_zero,
      zero_add] at hface ⊢ <;> simp only [f₁, f₂]
  · rw [hface]
    have hsq : p.2 ^ 2 ≤ eG P.bN ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ P.N b - 1),
      mul_le_mul_of_nonneg_left hm he.le]
  · rw [hface]; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ P.N b - 1) (sq_nonneg p.2)]
  · rw [hface]
    have : 0 < 1 + 6 * p.1 + (P.N b + 2) * eG P.bN := by nlinarith
    nlinarith [mul_pos he this]
  · rw [hface]
    have : 0 < 1 + 6 * p.1 - (P.N b + 2) * eG P.bN := by nlinarith
    nlinarith [mul_pos he this]

theorem norm_le_BI {p : ℝ × ℝ} (hp : p ∈ P.BI.set) : ‖p‖ ≤ 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := P.mem_BI.1 hp
  have := eG_le P.one_lt_bN
  simp only [δ] at h2
  exact norm_le_one_of_abs (abs_le.2 ⟨by linarith, by linarith⟩)
    (abs_le.2 ⟨by linarith, by linarith⟩)

theorem isUniformBlock_I : IsUniformBlock P.Φ P.BI.set P.BI.exit := by
  have he := eG_pos P.one_lt_bN
  have hle := eG_le P.one_lt_bN
  refine P.isUniformBlock_box P.BI (fun p hp => P.norm_le_BI hp) ?_ ?_ ?_ ?_ <;>
    intro b p hp hface <;> obtain ⟨h1, h2, h3, h4⟩ := P.mem_BI.1 hp <;>
    have hm := P.eG_mul_le b <;> have hn := P.one_lt b b.2 <;>
    simp only [BI, LBox.lam, LBox.wc, LBox.lamF, LBox.wF, one_mul, zero_mul, add_zero,
      zero_add] at hface ⊢
  · rw [hface]; exact face_left hn
  · rw [hface]; simp only [f₁, δ]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ P.N b - 1) (sq_nonneg p.2)]
  · rw [hface]; simp only [f₂]
    have : 0 < 1 + 6 * p.1 + (P.N b + 2) * eG P.bN := by nlinarith
    nlinarith [mul_pos he this]
  · rw [hface]; simp only [f₂]
    have : 0 < 1 + 6 * p.1 - (P.N b + 2) * eG P.bN := by nlinarith
    nlinarith [mul_pos he this]

/-- `S_G = Inv(B_G × [-1, 1])`. -/
abbrev SG : Set ((ℝ × ℝ) × Tau) := Inv P.Φ (P.BG.set ×ˢ univ)

/-- `S_I = Inv(B_I × [-1, 1])`. -/
abbrev SI : Set ((ℝ × ℝ) × Tau) := Inv P.Φ (P.BI.set ×ˢ univ)

theorem isIsolated_SG : IsIsolatedInvariantSet P.Φ P.SG :=
  ⟨_, (IsUniformBlock.slab P.isUniformBlock_G).isIsolatingNbhd, rfl⟩

theorem isIsolated_SI : IsIsolatedInvariantSet P.Φ P.SI :=
  ⟨_, (IsUniformBlock.slab P.isUniformBlock_I).isIsolatingNbhd, rfl⟩

theorem SG_top : {x | (x, Tau.top) ∈ P.SG} = {ptG} := by
  rw [SG, ← Inv_fiber_block P.isSkew_Φ Tau.top (base_top P.isHeight_θ), fiber_top]
  exact Inv_boxG P.one_lt_top (P.N_le_bN Tau.top)

theorem SG_bot : {x | (x, Tau.bot) ∈ P.SG} = {ptG} := by
  rw [SG, ← Inv_fiber_block P.isSkew_Φ Tau.bot (base_bot P.isHeight_θ), fiber_bot]
  exact Inv_boxG P.one_lt_bot (P.N_le_bN Tau.bot)

/-! ## The pair `(Σ_G^+, Σ_G^-)` -/

/-- Proposition `prop:ONramp`(iii), first pair. `(Σ_G^+, Σ_G^-)` is an attractor–repeller pair in
`S_G♮`, which has trivial homology index over any ring, so every connecting homomorphism
`CH_{k+1}(Σ_G^-) → CH_k(Σ_G^+)` is an isomorphism. -/
theorem trivialPair_G (K : Type) [Ring K] :
    IsTrivialPair K P.D {P.pt (false, 0)} {P.pt (true, 0)} := by
  obtain ⟨-, hp⟩ := snat_attractorRepeller P.isSkew_Φ P.isHeight_θ P.isIsolated_SG
  rw [P.SG_top, P.SG_bot, singleton_prod_singleton, singleton_prod_singleton] at hp
  exact ⟨_, hp, rate_snat_trivial P.isSkew_Φ P.isHeight_θ K P.isUniformBlock_G hp.isolated⟩

/-! ## Morse sets as blocks -/

variable {P}

theorem mem_attr_iff (h4m : 4 < P.N (-1)) (h4p : P.N 1 < 4) {Q : Set Lab}
    {x : (ℝ × ℝ) × Dbl} (hx : x ∈ snat P.S) {b : Lab}
    (hb : Tendsto (fun t => P.D t x) atBot (𝓝 (P.pt b))) :
    x ∈ morseAttr P.D (snat P.S) (fun a => {P.pt a}) Q ↔ b ∈ Q := by
  constructor
  · rintro ⟨-, j, hj, hα⟩
    rw [alphaLim_eq_of_tendsto hb, singleton_subset_iff, mem_singleton_iff] at hα
    rwa [P.pt_injective h4m h4p hα]
  · exact fun hbQ => ⟨hx, b, hbQ, (alphaLim_eq_of_tendsto hb).subset⟩

theorem mem_rep_iff (h4m : 4 < P.N (-1)) (h4p : P.N 1 < 4) {Q : Set Lab}
    {x : (ℝ × ℝ) × Dbl} (hx : x ∈ snat P.S) {a : Lab}
    (ha : Tendsto (fun t => P.D t x) atTop (𝓝 (P.pt a))) :
    x ∈ morseRep P.D (snat P.S) (fun a => {P.pt a}) Q ↔ a ∈ Q := by
  constructor
  · rintro ⟨-, j, hj, hω⟩
    rw [omegaLim_eq_of_tendsto ha, singleton_subset_iff, mem_singleton_iff] at hω
    rwa [P.pt_injective h4m h4p hω]
  · exact fun haQ => ⟨hx, a, haQ, (omegaLim_eq_of_tendsto ha).subset⟩

theorem tendsto_fst_atBot {x : (ℝ × ℝ) × Dbl} {b : Lab}
    (hb : Tendsto (fun t => P.D t x) atBot (𝓝 (P.pt b))) :
    Tendsto (fun s => (P.Φ s (dblQ x)).1) atBot (𝓝 (P.pt b).1) :=
  (continuous_fst.tendsto _).comp hb

theorem pt_fst (b : Lab) : ∃ N, 1 < N ∧ N ≤ P.bN ∧ (P.pt b).1 = pts N b.2 := by
  rcases b with ⟨_ | _, i⟩
  · exact ⟨_, P.one_lt_top, P.N_le_bN Tau.top, rfl⟩
  · exact ⟨_, P.one_lt_bot, P.N_le_bN Tau.bot, rfl⟩

/-- An orbit of `S♮` lies in `S_G♮` exactly if it comes from `Σ_G^-` or `Σ_G^+`. -/
theorem attr_G (h4m : 4 < P.N (-1)) (h4p : P.N 1 < 4) :
    morseAttr P.D (snat P.S) (fun a => {P.pt a}) {a | a.2 = 0} = snat P.SG := by
  ext x
  constructor
  · intro hx
    have hxS := hx.1
    obtain ⟨a, b, -, hb, -⟩ := P.limits h4m h4p hxS
    have hbQ : b.2 = 0 := (mem_attr_iff h4m h4p hxS hb).1 hx
    obtain ⟨N, -, -, hN⟩ := P.pt_fst b
    have hB := tendsto_fst_atBot hb
    rw [hN, hbQ, pts_zero] at hB
    have hz := P.eq_zero_of_tendsto_atBot hxS.1 hB
    refine ⟨fun t => ⟨?_, mem_univ _⟩, hxS.2⟩
    show (P.Φ t (dblQ x)).1 ∈ P.BG.set
    rw [hz t]
    have := eG_pos P.one_lt_bN
    exact mem_boxG.2 ⟨by simp; linarith, by simp; linarith, by simp; linarith, by simp; linarith⟩
  · intro hx
    have hxS : x ∈ snat P.S := ⟨fun t => ⟨P.BG_sub_R (hx.1 t).1, mem_univ _⟩, hx.2⟩
    obtain ⟨a, b, -, hb, -⟩ := P.limits h4m h4p hxS
    refine (mem_attr_iff h4m h4p hxS hb).2 ?_
    have hmem : (P.pt b).1 ∈ P.BG.set := P.BG.isClosed_set.mem_of_tendsto (tendsto_fst_atBot hb)
      (Eventually.of_forall fun t => (hx.1 t).1)
    obtain ⟨N, hN1, hNM, hN⟩ := P.pt_fst b
    rw [hN] at hmem
    exact idx_of_mem_boxG hN1 hNM hmem

/-- An orbit of `S♮` lies in `S_I♮` exactly if it comes from `Σ_G^±` or `Σ_I^±`. -/
theorem attr_I (h4m : 4 < P.N (-1)) (h4p : P.N 1 < 4) :
    morseAttr P.D (snat P.S) (fun a => {P.pt a}) {a | a.2 = 0 ∨ a.2 = 1} = snat P.SI := by
  ext x
  constructor
  · intro hx
    have hxS := hx.1
    obtain ⟨a, b, -, hb, -⟩ := P.limits h4m h4p hxS
    have hbQ : b.2 = 0 ∨ b.2 = 1 := (mem_attr_iff h4m h4p hxS hb).1 hx
    obtain ⟨N, -, -, hN⟩ := P.pt_fst b
    have hB := tendsto_fst_atBot hb
    rw [hN] at hB
    have hz : ∀ t, ((P.Φ t (dblQ x)).1).2 = 0 := by
      rcases hbQ with h | h
      · rw [h, pts_zero] at hB
        exact fun t => by rw [P.eq_zero_of_tendsto_atBot hxS.1 hB t]; rfl
      · rw [h, pts_one] at hB
        exact P.snd_eq_zero_of_tendsto_atBot hxS.1 hB
    refine ⟨fun t => ⟨?_, mem_univ _⟩, hxS.2⟩
    obtain ⟨⟨h1, h2⟩, -, -⟩ := P.mem_R hxS.1 t
    have := eG_pos P.one_lt_bN
    exact P.mem_BI.2 ⟨h1, h2, by rw [hz t]; linarith, by rw [hz t]; linarith⟩
  · intro hx
    have hxS : x ∈ snat P.S := ⟨fun t => ⟨P.BI_sub_R (hx.1 t).1, mem_univ _⟩, hx.2⟩
    obtain ⟨a, b, -, hb, -⟩ := P.limits h4m h4p hxS
    refine (mem_attr_iff h4m h4p hxS hb).2 ?_
    have hmem : (P.pt b).1 ∈ P.BI.set := P.BI.isClosed_set.mem_of_tendsto (tendsto_fst_atBot hb)
      (Eventually.of_forall fun t => (hx.1 t).1)
    obtain ⟨N, hN1, hNM, hN⟩ := P.pt_fst b
    rw [hN] at hmem
    exact idx_of_snd hN1 hNM (P.mem_BI.1 hmem).2.2.2

/-! ## The pair `(Σ_I^+, Σ_I^-)` -/

theorem down_G : IsDown rel {a : Lab | a.2 = 0} := by unfold IsDown rel; decide

theorem down_GI : IsDown rel {a : Lab | a.2 = 0 ∨ a = (false, 1)} := by unfold IsDown rel; decide

theorem down_I : IsDown rel {a : Lab | a.2 = 0 ∨ a.2 = 1} := by unfold IsDown rel; decide

variable (P)

theorem trivial_attr_G (h4m : 4 < P.N (-1)) (h4p : P.N 1 < 4) (K : Type) [Ring K]
    (hA : IsIsolatedInvariantSet P.D
      (morseAttr P.D (snat P.S) (fun a => {P.pt a}) {a | a.2 = 0})) :
    HasTrivialHomologyIndex K hA :=
  trivial_congr (attr_G h4m h4p).symm
    (rate_snat_trivial P.isSkew_Φ P.isHeight_θ K P.isUniformBlock_G
      (snat_attractorRepeller P.isSkew_Φ P.isHeight_θ P.isIsolated_SG).1)

theorem trivial_attr_I (h4m : 4 < P.N (-1)) (h4p : P.N 1 < 4) (K : Type) [Ring K]
    (hA : IsIsolatedInvariantSet P.D
      (morseAttr P.D (snat P.S) (fun a => {P.pt a}) {a | a.2 = 0 ∨ a.2 = 1})) :
    HasTrivialHomologyIndex K hA :=
  trivial_congr (attr_I h4m h4p).symm
    (rate_snat_trivial P.isSkew_Φ P.isHeight_θ K P.isUniformBlock_I
      (snat_attractorRepeller P.isSkew_Φ P.isHeight_θ P.isIsolated_SI).1)

/-- Proposition `prop:ONramp`(iii), second pair. `(Σ_I^+, Σ_I^-)` is an attractor–repeller pair
in the Morse set of the interval `{Σ_I^+, Σ_I^-}`, which has trivial homology index over any ring,
so every connecting homomorphism `CH_{k+1}(Σ_I^-) → CH_k(Σ_I^+)` is an isomorphism. -/
theorem trivialPair_I (h4m : 4 < P.N (-1)) (h4p : P.N 1 < 4) (K : Type) [Ring K] :
    IsTrivialPair K P.D {P.pt (false, 1)} {P.pt (true, 1)} := by
  have h := P.isMorseDecomp h4m h4p
  have p1 := h.isAttractorRepellerPair down_I down_G
    (fun a (ha : a.2 = 0) => Or.inl ha)
  have tR := trivial_R p1 (P.trivial_attr_I h4m h4p K _) (P.trivial_attr_G h4m h4p K _)
  have p2 := h.isAttractorRepellerPair_interval down_I down_GI down_G
    (fun a (ha : a.2 = 0) => Or.inl ha)
    (fun a (ha : a.2 = 0 ∨ a = (false, 1)) => by rcases ha with ha | rfl; exact Or.inl ha; exact Or.inr rfl)
  rw [h.attr_inter_rep_eq down_GI down_G (k := (false, 1)) (Or.inr rfl) (by decide)
      (by decide),
    h.attr_inter_rep_eq down_I down_GI (k := (true, 1)) (Or.inr rfl) (by decide)
      (by decide)] at p2
  exact ⟨_, p2, tR⟩

/-! ## The pair `(M_A, Σ_H^-)` -/

theorem down_D1 : IsDown rel {a : Lab | a.1 = false ∨ a.2 = 0 ∨ a.2 = 3} := by
  unfold IsDown rel; decide

theorem down_IR : IsDown rel {a : Lab | a.1 = false ∨ a.2 = 0} := by unfold IsDown rel; decide

variable {P}

/-- Orbits of `S♮` off the UV row end in the IR row. -/
theorem fst_of_fwd {x : (ℝ × ℝ) × Dbl} (hx : x ∈ snat P.S) (hu : (x.2 : ℝ) < 1) {a : Lab}
    (ha : Tendsto (fun t => P.D t x) atTop (𝓝 (P.pt a))) : a.1 = false := by
  have h2 : Tendsto (fun t => dblFlow P.isHeight_θ t x.2) atTop (𝓝 (P.pt a).2) :=
    (continuous_snd.tendsto _).comp ha
  have h0 : Tendsto (fun t => dblFlow P.isHeight_θ t x.2) atTop (𝓝 Dbl.zero) := by
    rcases hx.2.1.eq_or_lt with h | h
    · have : x.2 = Dbl.zero := Subtype.ext h.symm
      rw [this]; simp only [dblFlow_zero]; exact tendsto_const_nhds
    · exact P.tendsto_dbl_zero h hu
  have e := tendsto_nhds_unique h2 h0
  rcases a with ⟨_ | _, i⟩
  · rfl
  · exfalso
    have := congrArg Subtype.val e
    change (1 : ℝ) = 0 at this
    norm_num at this

/-- The Morse set of `{Σ_I^-, Σ_C^-}` is the corresponding Morse set of `f_-` in the UV row. -/
theorem rep_U (h4m : 4 < P.N (-1)) (h4p : P.N 1 < 4) :
    morseAttr P.D (snat P.S) (fun a => {P.pt a}) univ ∩
        morseRep P.D (snat P.S) (fun a => {P.pt a}) {a : Lab | a.1 = false ∨ a.2 = 0 ∨ a.2 = 3}ᶜ =
      (morseAttr (flowON (P.N (-1))) (boundedOrbits (P.N (-1)))
          (fun i => {pts (P.N (-1)) (σgt i)}) univ ∩
        morseRep (flowON (P.N (-1))) (boundedOrbits (P.N (-1)))
          (fun i => {pts (P.N (-1)) (σgt i)}) ({0, 2} : Set (Fin 4))ᶜ) ×ˢ {Dbl.one} := by
  have h := P.isMorseDecomp h4m h4p
  have hm := isMorseDecomp_gt h4m
  rw [h.attr_univ, hm.attr_univ]
  ext ⟨y, u⟩
  constructor
  · rintro ⟨hx, hr⟩
    obtain ⟨a, b, ha, -, -⟩ := P.limits h4m h4p hx
    have haQ := (mem_rep_iff h4m h4p hx ha).1 hr
    change ¬ (a.1 = false ∨ a.2 = 0 ∨ a.2 = 3) at haQ
    have hu1 : u = Dbl.one := by
      by_contra hne
      have hlt : (u : ℝ) < 1 := lt_of_le_of_ne hx.2.2 fun e => hne (Subtype.ext e)
      exact haQ (Or.inl (fst_of_fwd hx hlt ha))
    subst hu1
    have hy : y ∈ boundedOrbits (P.N (-1)) := by
      rw [← P.Km_eq]
      show (y, Tau.bot) ∈ P.S
      rw [← tentT_one]; exact hx.1
    rcases a with ⟨_ | _, j⟩
    · exact absurd (Or.inl rfl) haQ
    · have key : ∀ j : Fin 4, ¬((true, j).1 = false ∨ (true, j).2 = 0 ∨ (true, j).2 = 3) →
          j = 1 ∨ j = 2 := by decide
      have hj := key j haQ
      have hf : Tendsto (fun t => flowON (P.N (-1)) t y) atTop (𝓝 (pts (P.N (-1)) j)) := by
        have := (continuous_fst.tendsto _).comp ha
        simp only [Function.comp_def, D_one] at this
        exact this
      refine ⟨⟨hy, hy, σgt j, ?_, fun z hz => ?_⟩, rfl⟩
      · change ¬ (σgt j = 0 ∨ σgt j = 2)
        rcases hj with rfl | rfl <;> decide
      · rw [omegaLim_eq_of_tendsto hf] at hz
        show z ∈ ({pts (P.N (-1)) (σgt (σgt j))} : Set (ℝ × ℝ))
        rw [σgt_σgt]; exact hz
  · rintro ⟨⟨hy, -, k, hk, hω⟩, hu⟩
    obtain rfl : u = Dbl.one := hu
    change ¬ (k = 0 ∨ k = 2) at hk
    have hx : (y, Dbl.one) ∈ snat P.S := by
      have hy' : y ∈ {x | (x, Tau.bot) ∈ P.S} := P.Km_eq ▸ hy
      refine ⟨?_, ?_⟩
      · show (y, tentT Dbl.one) ∈ P.S
        rw [tentT_one]; exact hy'
      · show (1 : ℝ) ∈ Icc (0 : ℝ) 1
        exact ⟨zero_le_one, le_rfl⟩
    obtain ⟨p, -, -, -, hp, -⟩ := tendsto_of_mem_Inv P.one_lt_bot
      (by rwa [Inv_R_eq P.one_lt_bot])
    have e1 : p = pts (P.N (-1)) (σgt k) :=
      hω (by rw [omegaLim_eq_of_tendsto hp]; exact mem_singleton _)
    subst e1
    have ha : Tendsto (fun t => P.D t (y, Dbl.one)) atTop (𝓝 (P.pt (true, σgt k))) := by
      simp only [D_one]; exact hp.prodMk_nhds tendsto_const_nhds
    refine ⟨hx, (mem_rep_iff h4m h4p hx ha).2 ?_⟩
    change ¬ (true = false ∨ σgt k = 0 ∨ σgt k = 3)
    have key : ∀ k : Fin 4, ¬ (k = 0 ∨ k = 2) → ¬ (true = false ∨ σgt k = 0 ∨ σgt k = 3) := by
      decide
    exact key k hk

variable (P)

/-- The Morse set of `{Σ_I^-, Σ_C^-}` has trivial homology index, by Proposition `prop:boundary`
and the corresponding statement for `f_-`. -/
theorem trivial_U (h4m : 4 < P.N (-1)) (h4p : P.N 1 < 4) (K : Type) [Ring K]
    (hU : IsIsolatedInvariantSet P.D (morseAttr P.D (snat P.S) (fun a => {P.pt a}) univ ∩
      morseRep P.D (snat P.S) (fun a => {P.pt a}) {a : Lab | a.1 = false ∨ a.2 = 0 ∨ a.2 = 3}ᶜ)) :
    HasTrivialHomologyIndex K hU := by
  have hm := isMorseDecomp_gt h4m
  have hN := P.one_lt_bot
  have pm := hm.isAttractorRepellerPair (P := univ) (Q := {0, 2}) (fun _ _ _ _ => mem_univ _)
    down02 (subset_univ _)
  have tS : HasTrivialHomologyIndex K pm.isolated :=
    trivial_congr hm.attr_univ.symm (prop_ON_c hN K).2
  have tA : HasTrivialHomologyIndex K pm.isolated_A :=
    hasTrivialHomologyIndex_of_indexPair pm.isolated_A
      (by rw [morseAttr_pts rfl]; exact isIndexPair_H h4m) pointedContractible_H
  have tR := trivial_R pm tS tA
  obtain ⟨MU, hMU, hInvU⟩ := pm.isolated_R
  have hM : IsIsolatingNbhd (fiberFlow P.isSkew_Φ Tau.bot (base_bot P.isHeight_θ)) MU := by
    rw [P.fiber_bot]; exact hMU
  have eInv : Inv (fiberFlow P.isSkew_Φ Tau.bot (base_bot P.isHeight_θ)) MU =
      morseAttr (flowON (P.N (-1))) (boundedOrbits (P.N (-1)))
          (fun i => {pts (P.N (-1)) (σgt i)}) univ ∩
        morseRep (flowON (P.N (-1))) (boundedOrbits (P.N (-1)))
          (fun i => {pts (P.N (-1)) (σgt i)}) ({0, 2} : Set (Fin 4))ᶜ := by
    rw [P.fiber_bot, hInvU]
  have hS : IsIsolatedInvariantSet P.D
      (Inv (fiberFlow P.isSkew_Φ Tau.bot (base_bot P.isHeight_θ)) MU ×ˢ {Dbl.one}) := by
    rw [eInv, ← rep_U h4m h4p]; exact hU
  have hK : IsIsolatedInvariantSet (fiberFlow P.isSkew_Φ Tau.bot (base_bot P.isHeight_θ))
      (Inv (fiberFlow P.isSkew_Φ Tau.bot (base_bot P.isHeight_θ)) MU) := ⟨MU, hM, rfl⟩
  have tK : HasTrivialHomologyIndex K hK := fun n => by
    obtain ⟨e⟩ := homologyIndex_congr K P.fiber_bot eInv hK pm.isolated_R n
    have := tR n
    exact e.toEquiv.subsingleton
  have tS' : HasTrivialHomologyIndex K hS := fun n => by
    cases n with
    | zero => exact dbl_boundary_UV_zero P.isSkew_Φ P.isHeight_θ K hM hS hK
    | succ n =>
      obtain ⟨e⟩ := dbl_boundary_UV P.isSkew_Φ P.isHeight_θ K hM hS hK n
      have := tK n
      exact e.toEquiv.subsingleton
  exact trivial_congr (by rw [eInv, ← rep_U h4m h4p]) tS'

/-- Proposition `prop:ONramp`(iii), third pair. Let `M_A` be the Morse set of the interval
`{Σ_I^+, Σ_C^+, Σ_H^+}`. Then `(M_A, Σ_H^-)` is an attractor–repeller pair in an isolated invariant
set with trivial homology index over any ring, so every connecting homomorphism
`CH_{k+1}(Σ_H^-) → CH_k(M_A)` is an isomorphism. -/
theorem trivialPair_H (h4m : 4 < P.N (-1)) (h4p : P.N 1 < 4) (K : Type) [Ring K] :
    IsTrivialPair K P.D
      (morseAttr P.D (snat P.S) (fun a => {P.pt a}) {a | a.1 = false ∨ a.2 = 0} ∩
        morseRep P.D (snat P.S) (fun a => {P.pt a}) {a | a.2 = 0}ᶜ) {P.pt (true, 3)} := by
  have h := P.isMorseDecomp h4m h4p
  have p0 := h.isAttractorRepellerPair (P := univ) (Q := {a : Lab | a.1 = false ∨ a.2 = 0 ∨ a.2 = 3})
    (fun _ _ _ _ => mem_univ _) down_D1 (subset_univ _)
  have t0 : HasTrivialHomologyIndex K p0.isolated := trivial_congr h.attr_univ.symm
    (rate_snat_trivial P.isSkew_Φ P.isHeight_θ K P.isUniformBlock_R P.isIsolated_snat)
  have tD1 := trivial_A p0 t0 (P.trivial_U h4m h4p K _)
  have p1 := h.isAttractorRepellerPair down_D1 down_G
    (fun a (ha : a.2 = 0) => Or.inr (Or.inl ha))
  have tP := trivial_R p1 tD1 (P.trivial_attr_G h4m h4p K _)
  have p2 := h.isAttractorRepellerPair_interval down_D1 down_IR down_G
    (fun a (ha : a.2 = 0) => Or.inr ha)
    (fun a (ha : a.1 = false ∨ a.2 = 0) => by
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha))
  rw [h.attr_inter_rep_eq down_D1 down_IR (k := (true, 3)) (Or.inr (Or.inr rfl)) (by decide)
    (by decide)] at p2
  exact ⟨_, p2, tP⟩

/-- Proposition `prop:ONramp`(iii). For `N_- > 4` and `1 < N_+ < 4`, over any ring `K`, the pairs
`(Σ_G^+, Σ_G^-)`, `(Σ_I^+, Σ_I^-)` and `(M_A, Σ_H^-)`, with `M_A` the Morse set of
`{Σ_I^+, Σ_C^+, Σ_H^+}`, are attractor–repeller pairs in isolated invariant sets with trivial
homology index. -/
theorem prop_ONramp_iii (h4m : 4 < P.N (-1)) (h4p : P.N 1 < 4) (K : Type) [Ring K] :
    IsTrivialPair K P.D {P.pt (false, 0)} {P.pt (true, 0)} ∧
      IsTrivialPair K P.D {P.pt (false, 1)} {P.pt (true, 1)} ∧
      IsTrivialPair K P.D
        (morseAttr P.D (snat P.S) (fun a => {P.pt a}) {a | a.1 = false ∨ a.2 = 0} ∩
          morseRep P.D (snat P.S) (fun a => {P.pt a}) {a | a.2 = 0}ᶜ) {P.pt (true, 3)} :=
  ⟨P.trivialPair_G K, P.trivialPair_I h4m h4p K, P.trivialPair_H h4m h4p K⟩

end Ramp

end ConleyCheck.ON
