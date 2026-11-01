import ConleyCheck.Gubser.TCIndex

/-!
# The index of an attractor with a contractible block

If `(N, ∅)` is an index pair of `S` and `N` deforms to a point, then `h(S) = S⁰`.
-/

namespace ConleyCheck.Conley

open Set unitInterval ConleyCheck.Gubser

/-- The point of `S⁰` other than the base point. -/
noncomputable def Sphere.npt : Sphere 0 :=
  ⟨EuclideanSpace.single 0 (-1), by simp⟩

theorem Sphere.npt_ne_pt : Sphere.npt ≠ Sphere.pt 0 := fun h => by
  have := congrArg (fun p : Sphere 0 => (p : EuclideanSpace ℝ (Fin 1)) 0) h
  simp [Sphere.npt, Sphere.pt] at this
  norm_num at this

theorem Sphere.eq_npt {p : Sphere 0} (hp : p ≠ Sphere.pt 0) : p = Sphere.npt := by
  obtain ⟨v, hv⟩ := p
  have hn : ‖v‖ = 1 := mem_sphere_zero_iff_norm.1 hv
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _),
    Real.norm_eq_abs] at hn
  have hext : ∀ w : EuclideanSpace ℝ (Fin 1), w 0 = v 0 → w = v := fun w h => by
    ext i
    fin_cases i
    exact h
  rcases (abs_eq zero_le_one).1 hn with h | h
  · refine absurd (Subtype.ext ?_) hp
    exact (hext (EuclideanSpace.single 0 1) (by simp [h])).symm
  · exact Subtype.ext (hext (EuclideanSpace.single 0 (-1)) (by simp [h])).symm

variable {α : Type*} [TopologicalSpace α] {ϕ : Flow ℝ α}

/-- If `(N, ∅)` is an index pair of `S` and `N` deforms to a point inside `N`, then
`h(S) = S⁰`. -/
theorem hasIndex_sphere_zero_of_deform {S N : Set α} {x₀ : α} (hx₀ : x₀ ∈ N)
    (hP : IsIndexPair ϕ S N ∅) (H : C(I × N, N)) (h0 : ∀ x, H (0, x) = x)
    (h1 : ∀ x, (H (1, x) : α) = x₀) : HasIndex ϕ S (Sphere 0) (Sphere.pt 0) := by
  refine ⟨N, ∅, hP, ⟨(retractEquiv (N' := {x₀}) (singleton_subset_iff.2 hx₀) H h0
    (fun _ _ h => h.elim) (fun x => h1 x)
    (fun x hx => Subtype.ext (by rw [h1]; exact (mem_singleton_iff.1 hx).symm))).trans
    (sphereEquivOf isCompact_singleton (ContinuousMap.const _ Sphere.npt) (fun _ => ?_)
      (fun x y _ _ => Subtype.ext (x.2.trans y.2.symm))
      (fun p hp => ⟨⟨x₀, rfl⟩, (Sphere.eq_npt hp).symm⟩))⟩⟩
  simp only [ContinuousMap.const_apply, mem_empty_iff_false, iff_false]
  exact Sphere.npt_ne_pt

/-- If `(N, ∅)` is an index pair of `S` with `N` convex and nonempty, then `h(S) = S⁰`. -/
theorem hasIndex_sphere_zero_of_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ϕ : Flow ℝ E} {S N : Set E} {x₀ : E} (hx₀ : x₀ ∈ N) (hc : Convex ℝ N)
    (hP : IsIndexPair ϕ S N ∅) : HasIndex ϕ S (Sphere 0) (Sphere.pt 0) := by
  let H : C(I × N, N) :=
    { toFun := fun q => ⟨(q.2 : E) + (q.1 : ℝ) • (x₀ - q.2),
        hc.add_smul_sub_mem q.2.2 hx₀ ⟨q.1.2.1, q.1.2.2⟩⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        have h2 : Continuous fun q : I × N => (q.2 : E) := continuous_subtype_val.comp continuous_snd
        exact h2.add (((continuous_subtype_val.comp continuous_fst)).smul
          (continuous_const.sub h2)) }
  refine hasIndex_sphere_zero_of_deform hx₀ hP H (fun x => Subtype.ext ?_) (fun x => ?_)
  · show (x : E) + ((0 : I) : ℝ) • (x₀ - x) = x
    simp
  · show (x : E) + ((1 : I) : ℝ) • (x₀ - x) = x₀
    simp

end ConleyCheck.Conley
