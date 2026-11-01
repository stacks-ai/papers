import ConleyCheck.Conley.Rate
import ConleyCheck.Conley.Conjugacy

/-!
# Common blocks after a fiberwise change of coordinates

Let `e : X × [-1, 1] ≃ Y × [-1, 1]` be a homeomorphism that preserves `τ`, for instance
`(x, τ) ↦ (M(τ) x, τ)`. It conjugates the skew product `Φ` to the skew product `e Φ e⁻¹` over the
same base. A common block `(N, L_out)` for `e Φ e⁻¹` is a block whose fibers `e_τ⁻¹(N)` move with
`τ`, and Theorem `thm:rate` holds for `Φ` with `S = Inv(e⁻¹(N × [-1, 1]))`.

* `isSkew_conjFlow`, `fiberHomeo`, `dblHomeo`: the conjugate skew product, the fiber maps and the
  induced homeomorphism of the doubles, which conjugates the two doubles (`dblHomeo_comm`).
* `conj_index`: `S` is isolated, and `(N, L_out)` computes the indices of `K_±`.
* `conj_snat_trivial`, `rate_transport_conj`: `CH_*(S♮) = 0` and `Ψ` is an isomorphism.
-/

namespace ConleyCheck.Conley

open Set Function
open scoped unitInterval

universe u

section Conj

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {Φ : Flow ℝ (X × Tau)}
  {θ : Flow ℝ Tau} (hΦ : IsSkew Φ θ) (e : X × Tau ≃ₜ Y × Tau) (he : ∀ p, (e p).2 = p.2)

include he in
theorem symm_snd_of_fiberwise (q : Y × Tau) : (e.symm q).2 = q.2 := by
  have := he (e.symm q)
  rw [e.apply_symm_apply] at this
  exact this.symm

include hΦ he in
theorem isSkew_conjFlow : IsSkew (conjFlow Φ e) θ := fun t q => by
  rw [conjFlow_apply, he, hΦ, symm_snd_of_fiberwise e he]

include he in
theorem fiberwise_mk (x : X) (b : Tau) : ((e (x, b)).1, b) = e (x, b) := Prod.ext rfl (he (x, b)).symm

include he in
theorem fiberwise_symm_mk (y : Y) (b : Tau) : ((e.symm (y, b)).1, b) = e.symm (y, b) :=
  Prod.ext rfl (symm_snd_of_fiberwise e he (y, b)).symm

theorem conjFlow_comm (t : ℝ) (p : X × Tau) : e (Φ t p) = conjFlow Φ e t (e p) := by
  rw [conjFlow_apply, e.symm_apply_apply]

/-- The restriction `e_b` of `e` to the fiber over `b`. -/
noncomputable def fiberHomeo (b : Tau) : X ≃ₜ Y where
  toFun x := (e (x, b)).1
  invFun y := (e.symm (y, b)).1
  left_inv x := by
    show (e.symm ((e (x, b)).1, b)).1 = x
    rw [fiberwise_mk e he, e.symm_apply_apply]
  right_inv y := by
    show (e ((e.symm (y, b)).1, b)).1 = y
    rw [fiberwise_symm_mk e he, e.apply_symm_apply]
  continuous_toFun :=
    continuous_fst.comp (e.continuous.comp (continuous_id.prodMk continuous_const))
  continuous_invFun :=
    continuous_fst.comp (e.symm.continuous.comp (continuous_id.prodMk continuous_const))

theorem fiberHomeo_apply (b : Tau) (x : X) : fiberHomeo e he b x = (e (x, b)).1 := rfl

theorem fiberHomeo_comm (b : Tau) (hb : ∀ t, θ t b = b) (t : ℝ) (x : X) :
    fiberHomeo e he b (fiberFlow hΦ b hb t x) =
      fiberFlow (isSkew_conjFlow hΦ e he) b hb t (fiberHomeo e he b x) := by
  rw [fiberHomeo_apply, fiberHomeo_apply, fiberFlow_apply, fiberFlow_apply, fiberwise_mk e he]
  have h : ((Φ t (x, b)).1, b) = Φ t (x, b) := Prod.ext rfl (by rw [hΦ, hb])
  rw [h, conjFlow_comm]

theorem fiberHomeo_preimage (b : Tau) (M : Set (Y × Tau)) :
    fiberHomeo e he b ⁻¹' {y | (y, b) ∈ M} = {x | (x, b) ∈ e ⁻¹' M} := by
  ext x
  simp only [mem_preimage, mem_ofPred_eq, fiberHomeo_apply, fiberwise_mk e he]

/-- The homeomorphism `(x, u) ↦ (e_{cos π u}(x), u)` of the doubles. -/
noncomputable def dblHomeo : X × Dbl ≃ₜ Y × Dbl where
  toFun q := ((e (q.1, tentT q.2)).1, q.2)
  invFun q := ((e.symm (q.1, tentT q.2)).1, q.2)
  left_inv q := by
    show ((e.symm ((e (q.1, tentT q.2)).1, tentT q.2)).1, q.2) = q
    rw [fiberwise_mk e he, e.symm_apply_apply]
  right_inv q := by
    show ((e ((e.symm (q.1, tentT q.2)).1, tentT q.2)).1, q.2) = q
    rw [fiberwise_symm_mk e he, e.apply_symm_apply]
  continuous_toFun := (continuous_fst.comp (e.continuous.comp
    (continuous_fst.prodMk (continuous_tentT.comp continuous_snd)))).prodMk continuous_snd
  continuous_invFun := (continuous_fst.comp (e.symm.continuous.comp
    (continuous_fst.prodMk (continuous_tentT.comp continuous_snd)))).prodMk continuous_snd

theorem dblHomeo_apply (q : X × Dbl) : dblHomeo e he q = ((e (q.1, tentT q.2)).1, q.2) := rfl

theorem dblQ_dblHomeo (q : X × Dbl) : dblQ (dblHomeo e he q) = e (dblQ q) := by
  rw [dblHomeo_apply, dblQ_apply, dblQ_apply, fiberwise_mk e he]

variable (hθ : IsHeight θ (fun b => (b : ℝ)))

theorem dblHomeo_comm (t : ℝ) (q : X × Dbl) :
    dblHomeo e he (dblΦ hΦ hθ t q) =
      dblΦ (isSkew_conjFlow hΦ e he) hθ t (dblHomeo e he q) := by
  rw [dblΦ_apply, dblΦ_apply, dblQ_dblHomeo, ← conjFlow_comm, dblHomeo_apply]
  have h : ((Φ t (dblQ q)).1, tentT (dblFlow hθ t q.2)) = Φ t (dblQ q) :=
    Prod.ext rfl (by rw [tentT_dblFlow, hΦ, dblQ_apply])
  simp only [h]
  rfl

theorem dblHomeo_preimage_snat (S : Set (Y × Tau)) :
    dblHomeo e he ⁻¹' snat S = snat (e ⁻¹' S) := by
  ext q
  simp only [snat, mem_preimage, mem_ofPred_eq, dblQ_dblHomeo]
  rfl

theorem IsIsolatingNbhd.preimage_conj {ϕ : Flow ℝ X} {ψ : Flow ℝ Y} {h : X ≃ₜ Y}
    (hc : ∀ t x, h (ϕ t x) = ψ t (h x)) {M : Set Y} (hM : IsIsolatingNbhd ψ M) :
    IsIsolatingNbhd ϕ (h ⁻¹' M) :=
  ⟨h.isCompact_preimage.2 hM.1, by
    rw [Inv_preimage hc, ← h.preimage_interior]
    exact preimage_mono hM.2⟩

variable [T2Space Y]

include he in
/-- `S = Inv(e⁻¹(N × [-1, 1]))` is isolated, and `(N, L_out)` computes the Conley indices of
`K_± = {x : (x, ±1) ∈ S}`. -/
theorem conj_index {N Lo : Set Y} (hB : IsUniformBlock (conjFlow Φ e) N Lo) :
    IsIsolatingNbhd Φ (e ⁻¹' (N ×ˢ univ)) ∧
      HasIndex (fiberFlow hΦ Tau.top (base_top hθ))
        {x | (x, Tau.top) ∈ Inv Φ (e ⁻¹' (N ×ˢ univ))} (IndexSpace N Lo) (IndexSpace.pt N Lo) ∧
      HasIndex (fiberFlow hΦ Tau.bot (base_bot hθ))
        {x | (x, Tau.bot) ∈ Inv Φ (e ⁻¹' (N ×ˢ univ))} (IndexSpace N Lo) (IndexSpace.pt N Lo) := by
  have hΦ' := isSkew_conjFlow hΦ e he
  have hfib : ∀ (b : Tau) (hb : ∀ t, θ t b = b),
      HasIndex (fiberFlow hΦ b hb) {x | (x, b) ∈ Inv Φ (e ⁻¹' (N ×ˢ univ))}
        (IndexSpace N Lo) (IndexSpace.pt N Lo) := fun b hb => by
    have hP := (IsUniformBlock.fiber hΦ' hB b hb).isIndexPair
    rw [Inv_fiber_block hΦ' b hb] at hP
    have hP' := hP.preimage (fiberHomeo_comm hΦ e he b hb)
    rw [fiberHomeo_preimage, ← Inv_preimage (conjFlow_comm e)] at hP'
    exact ⟨_, _, hP', ⟨IndexSpace.preimageEquiv _ N Lo⟩⟩
  exact ⟨IsIsolatingNbhd.preimage_conj (conjFlow_comm e) (IsUniformBlock.slab hB).isIsolatingNbhd,
    hfib _ _, hfib _ _⟩

variable [T2Space X]

include he in
/-- `CH_*(S♮) = 0`. -/
theorem conj_snat_trivial (K : Type u) [Ring K] {N Lo : Set Y}
    (hB : IsUniformBlock (conjFlow Φ e) N Lo)
    (hSn : IsIsolatedInvariantSet (dblΦ hΦ hθ) (snat (Inv Φ (e ⁻¹' (N ×ˢ univ))))) (k : ℕ) :
    Subsingleton (homologyIndex K _ hSn k) := by
  have hΦ' := isSkew_conjFlow hΦ e he
  have hP := (IsUniformBlock.dbl hΦ' hθ hB).isIndexPair
  have hInv : Inv (dblΦ hΦ' hθ) (N ×ˢ blockJ) = snat (Inv (conjFlow Φ e) (N ×ˢ univ)) := by
    have e' : nnat (N ×ˢ (univ : Set Tau)) = N ×ˢ blockJ := by
      ext p
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, mem_univ _⟩, h.2⟩⟩
    rw [← e']
    exact (snat_isolated hΦ' hθ (IsUniformBlock.slab hB).isIsolatingNbhd).2
  rw [hInv] at hP
  have hP' := hP.preimage (dblHomeo_comm hΦ e he hθ)
  rw [dblHomeo_preimage_snat, ← Inv_preimage (conjFlow_comm e)] at hP'
  obtain ⟨iso⟩ := homologyIndexIso K hSn hP' k
  have hc := IndexSpace.prod_pointedContractible (N₁ := N) (L₁ := Lo)
    (N₂ := blockJ) (L₂ := blockE) blockH
    (fun b => Subtype.ext (Subtype.ext (by
      show _ + ((0 : I) : ℝ) * _ = _
      simp)))
    (fun b => show ((b : Dbl) : ℝ) + ((1 : I) : ℝ) * (3 / 2 - ((b : Dbl) : ℝ)) = 3 / 2 by
      simp only [Set.Icc.coe_one, one_mul]; ring)
    (fun s b (hb : ((b : Dbl) : ℝ) = 3 / 2) =>
      show ((b : Dbl) : ℝ) + (s : ℝ) * (3 / 2 - ((b : Dbl) : ℝ)) = 3 / 2 by rw [hb]; ring)
  have := redH_subsingleton K
    (PointedContractible.of_equiv (IndexSpace.preimageEquiv (dblHomeo e he) _ _) hc) k
  exact iso.toLinearEquiv.toEquiv.subsingleton

variable [TopologicalSpace.MetrizableSpace X]

include he in
/-- Theorem `thm:rate`(ii) for a moving block: `CH_*(S♮) = 0` and `Ψ` is an isomorphism. -/
theorem rate_transport_conj (K : Type u) [Ring K] {N Lo : Set Y}
    (hB : IsUniformBlock (conjFlow Φ e) N Lo) :
    ∃ (hSn : IsIsolatedInvariantSet (dblΦ hΦ hθ) (snat (Inv Φ (e ⁻¹' (N ×ˢ univ)))))
      (hKp : IsIsolatedInvariantSet (fiberFlow hΦ Tau.top (base_top hθ))
        {x | (x, Tau.top) ∈ Inv Φ (e ⁻¹' (N ×ˢ univ))})
      (hKm : IsIsolatedInvariantSet (fiberFlow hΦ Tau.bot (base_bot hθ))
        {x | (x, Tau.bot) ∈ Inv Φ (e ⁻¹' (N ×ˢ univ))})
      (Ψ : ∀ k, homologyIndex K _ hKm k →ₗ[K] homologyIndex K _ hKp k)
      (i : ∀ k, homologyIndex K _ hKp k →ₗ[K] homologyIndex K _ hSn k)
      (p : ∀ k, homologyIndex K _ hSn (k + 1) →ₗ[K] homologyIndex K _ hKm k),
      (∀ k, Exact (Ψ k) (i k)) ∧ (∀ k, Exact (i (k + 1)) (p k)) ∧
        (∀ k, Exact (p k) (Ψ k)) ∧ (∀ k, Subsingleton (homologyIndex K _ hSn k)) ∧
        ∀ k, Bijective (Ψ k) := by
  have hS : IsIsolatedInvariantSet Φ (Inv Φ (e ⁻¹' (N ×ˢ univ))) :=
    ⟨_, (conj_index hΦ e he hθ hB).1, rfl⟩
  obtain ⟨hSn, hKp, hKm, Ψ, i, p, h1, h2, h3, -⟩ := transport hΦ hθ K hS
  have hz := conj_snat_trivial hΦ e he hθ K hB hSn
  refine ⟨hSn, hKp, hKm, Ψ, i, p, h1, h2, h3, hz, fun k => ⟨?_, ?_⟩⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨y, rfl⟩ := ((h3 k) x).1 hx
    have := hz (k + 1)
    rw [Subsingleton.elim y 0, map_zero]
  · intro y
    have := hz k
    exact ((h1 k) y).1 (Subsingleton.elim _ _)

include hΦ he hθ in
/-- Theorem `thm:rate`(iii) for a moving block: if `H̃_*(N/L_out) ≠ 0`, some orbit of
`S = Inv(e⁻¹(N × [-1, 1]))` with `-1 < τ < 1` runs from `K_-` to `K_+`. -/
theorem rate_connection_conj [TopologicalSpace.MetrizableSpace Y] (K : Type u) [Ring K]
    {N Lo : Set Y} (hB : IsUniformBlock (conjFlow Φ e) N Lo)
    (hnt : ∃ k, Nontrivial (redH K (IndexSpace N Lo) (IndexSpace.pt N Lo) k)) :
    ∃ p ∈ Inv Φ (e ⁻¹' (N ×ˢ univ)), (p.2 : ℝ) ∈ Ioo (-1) 1 ∧
      omegaLim Φ p ⊆ Inv Φ (e ⁻¹' (N ×ˢ univ)) ∩ (fun q => (q.2 : ℝ)) ⁻¹' {1} ∧
      alphaLim Φ p ⊆ Inv Φ (e ⁻¹' (N ×ˢ univ)) ∩ (fun q => (q.2 : ℝ)) ⁻¹' {-1} := by
  have hΦ' := isSkew_conjFlow hΦ e he
  obtain ⟨q, hq, hτ, -⟩ := rate_connection hΦ' hθ K hB hnt
  have hS : IsIsolatedInvariantSet Φ (Inv Φ (e ⁻¹' (N ×ˢ univ))) :=
    ⟨_, (conj_index hΦ e he hθ hB).1, rfl⟩
  have hARs := (hΦ.isHeight hθ).isAttractorRepellerPair hS
  have hp : e.symm q ∈ Inv Φ (e ⁻¹' (N ×ˢ univ)) := by
    rw [Inv_preimage (conjFlow_comm e)]
    show e (e.symm q) ∈ Inv (conjFlow Φ e) (N ×ˢ univ)
    rw [e.apply_symm_apply]
    exact hq
  have hτ' : ((e.symm q).2 : ℝ) ∈ Ioo (-1) 1 := by rw [symm_snd_of_fiberwise e he]; exact hτ
  exact ⟨e.symm q, hp, hτ', hARs.connecting _ hp (fun h => hτ'.2.ne h.2) (fun h => hτ'.1.ne' h.2)⟩

end Conj

end ConleyCheck.Conley
