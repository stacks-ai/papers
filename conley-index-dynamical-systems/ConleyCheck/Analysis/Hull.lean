import Mathlib

/-!
# The hull of an asymptotically autonomous vector field

Lemma `lem:hull`. Let `f ∈ C(ℝ × X, E)` converge to `f_±` uniformly on compact subsets of `X` as
`t → ±∞`. In the compact-open topology, `s ↦ f_s = f(s + ·, ·)` extends to a continuous map
`[-∞, ∞] → C(ℝ × X, E)` with `±∞ ↦ f_±`, whose image is the hull, i.e. the closure of the set of
translates, and equals `{f_s : s ∈ ℝ} ∪ {f_-, f_+}`. If `f` is not autonomous and `f_- ≠ f_+`, the
extension is a closed embedding, hence a homeomorphism onto the hull.
-/

namespace ConleyCheck

open Set Filter Topology

variable {X E : Type*} [TopologicalSpace X] [MetricSpace E]

/-- The translates `s ↦ f_s`, `f_s(t, x) = f(s + t, x)`. -/
def transl (f : C(ℝ × X, E)) : C(ℝ, C(ℝ × X, E)) :=
  ContinuousMap.curry ⟨fun q : ℝ × (ℝ × X) => f (q.1 + q.2.1, q.2.2),
    f.continuous.comp ((continuous_fst.add (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd))⟩

theorem transl_apply (f : C(ℝ × X, E)) (s : ℝ) (p : ℝ × X) : transl f s p = f (s + p.1, p.2) :=
  rfl

/-- A time-independent field as a field on `ℝ × X`. -/
def auto (φ : C(X, E)) : C(ℝ × X, E) := φ.comp ⟨Prod.snd, continuous_snd⟩

/-- `f(t, ·) → f_±` uniformly on compact sets as `t → ±∞`. -/
def IsAsymptoticallyAutonomous (f : C(ℝ × X, E)) (fm fp : C(X, E)) : Prop :=
  (∀ K, IsCompact K → TendstoUniformlyOn (fun t x => f (t, x)) fp atTop K) ∧
    ∀ K, IsCompact K → TendstoUniformlyOn (fun t x => f (t, x)) fm atBot K

/-- `f` does not depend on `t`. -/
def IsAutonomous (f : C(ℝ × X, E)) : Prop := ∃ φ : X → E, ∀ t x, f (t, x) = φ x

/-- The extension of `s ↦ f_s` to `[-∞, ∞]`. -/
noncomputable def hullMap (f : C(ℝ × X, E)) (fm fp : C(X, E)) (s : EReal) : C(ℝ × X, E) :=
  if s = ⊤ then auto fp else if s = ⊥ then auto fm else transl f s.toReal

variable {f : C(ℝ × X, E)} {fm fp : C(X, E)}

theorem hullMap_coe (s : ℝ) : hullMap f fm fp s = transl f s := by
  simp [hullMap]

theorem hullMap_top : hullMap f fm fp ⊤ = auto fp := by simp [hullMap]

theorem hullMap_bot : hullMap f fm fp ⊥ = auto fm := by simp [hullMap]

theorem tendsto_transl_atTop
    (h : ∀ K, IsCompact K → TendstoUniformlyOn (fun t x => f (t, x)) fp atTop K) :
    Tendsto (transl f) atTop (𝓝 (auto fp)) := by
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  obtain ⟨M, hM⟩ := (hK.image continuous_fst).isBounded.exists_norm_le
  have hu := h _ (hK.image continuous_snd)
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hu ε hε)
  filter_upwards [eventually_ge_atTop (T + M)] with s hs p hp
  have h1 : |p.1| ≤ M := by simpa using hM _ ⟨p, hp, rfl⟩
  have h2 : T ≤ s + p.1 := by linarith [neg_abs_le p.1]
  exact hT (s + p.1) h2 p.2 ⟨p, hp, rfl⟩

theorem tendsto_transl_atBot
    (h : ∀ K, IsCompact K → TendstoUniformlyOn (fun t x => f (t, x)) fm atBot K) :
    Tendsto (transl f) atBot (𝓝 (auto fm)) := by
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  obtain ⟨M, hM⟩ := (hK.image continuous_fst).isBounded.exists_norm_le
  have hu := h _ (hK.image continuous_snd)
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  obtain ⟨T, hT⟩ := eventually_atBot.1 (hu ε hε)
  filter_upwards [eventually_le_atBot (T - M)] with s hs p hp
  have h1 : |p.1| ≤ M := by simpa using hM _ ⟨p, hp, rfl⟩
  have h2 : s + p.1 ≤ T := by linarith [le_abs_self p.1]
  exact hT (s + p.1) h2 p.2 ⟨p, hp, rfl⟩

/-- A periodic asymptotically autonomous field is autonomous. -/
theorem isAutonomous_of_periodic
    (h : ∀ K, IsCompact K → TendstoUniformlyOn (fun t x => f (t, x)) fp atTop K) {p : ℝ}
    (hp : p ≠ 0) (hper : ∀ t x, f (t + p, x) = f (t, x)) : IsAutonomous f := by
  obtain ⟨q, hq, hperq⟩ : ∃ q : ℝ, 0 < q ∧ ∀ t x, f (t + q, x) = f (t, x) := by
    rcases hp.lt_or_gt with hn | hpos
    · refine ⟨-p, by linarith, fun t x => ?_⟩
      have := hper (t + -p) x
      rw [neg_add_cancel_right] at this
      exact this.symm
    · exact ⟨p, hpos, hper⟩
  refine ⟨fp, fun t x => ?_⟩
  have hn : ∀ n : ℕ, f (t + n * q, x) = f (t, x) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, hperq, ih]
  have hlim : Tendsto (fun n : ℕ => f (t + n * q, x)) atTop (𝓝 (fp x)) :=
    ((h {x} isCompact_singleton).tendsto_at (mem_singleton x)).comp
      (tendsto_atTop_add_const_left _ t (tendsto_natCast_atTop_atTop.atTop_mul_const hq))
  simp only [hn] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-- Lemma `lem:hull`. -/
theorem lem_hull (hf : IsAsymptoticallyAutonomous f fm fp) :
    Continuous (hullMap f fm fp) ∧ (∀ s : ℝ, hullMap f fm fp s = transl f s) ∧
      hullMap f fm fp ⊤ = auto fp ∧ hullMap f fm fp ⊥ = auto fm ∧
      range (hullMap f fm fp) = range (transl f) ∪ {auto fm, auto fp} ∧
      range (hullMap f fm fp) = closure (range (transl f)) ∧
      (¬ IsAutonomous f → fm ≠ fp → IsClosedEmbedding (hullMap f fm fp)) := by
  have hcoe : hullMap f fm fp ∘ Real.toEReal = transl f := funext fun s => hullMap_coe s
  have hc : ∀ s : ℝ, ContinuousAt (hullMap f fm fp) s := fun s => by
    rw [← EReal.isOpenEmbedding_coe.continuousAt_iff, hcoe]
    exact (transl f).continuous.continuousAt
  have htop : ContinuousAt (hullMap f fm fp) ⊤ := by
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, EReal.nhdsWithin_top,
      tendsto_map'_iff, hcoe, hullMap_top]
    exact tendsto_transl_atTop hf.1
  have hbot : ContinuousAt (hullMap f fm fp) ⊥ := by
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, EReal.nhdsWithin_bot,
      tendsto_map'_iff, hcoe, hullMap_bot]
    exact tendsto_transl_atBot hf.2
  have hcont : Continuous (hullMap f fm fp) := continuous_iff_continuousAt.2 fun s => by
    induction s using EReal.rec with
    | bot => exact hbot
    | coe s => exact hc s
    | top => exact htop
  refine ⟨hcont, hullMap_coe, hullMap_top, hullMap_bot, ?_, ?_, fun hna hne => ?_⟩
  · ext g
    constructor
    · rintro ⟨s, rfl⟩
      induction s using EReal.rec with
      | bot => exact Or.inr (Or.inl hullMap_bot)
      | coe s => exact Or.inl ⟨s, (hullMap_coe s).symm⟩
      | top => exact Or.inr (Or.inr hullMap_top)
    · rintro (⟨s, rfl⟩ | rfl | rfl)
      · exact ⟨s, hullMap_coe s⟩
      · exact ⟨⊥, hullMap_bot⟩
      · exact ⟨⊤, hullMap_top⟩
  · refine Subset.antisymm ?_ (closure_minimal ?_ (isCompact_range hcont).isClosed)
    · rintro _ ⟨s, rfl⟩
      induction s using EReal.rec with
      | bot =>
        rw [hullMap_bot]
        exact mem_closure_of_tendsto (tendsto_transl_atBot hf.2)
          (Eventually.of_forall fun s => mem_range_self s)
      | coe s => exact subset_closure ⟨s, (hullMap_coe s).symm⟩
      | top =>
        rw [hullMap_top]
        exact mem_closure_of_tendsto (tendsto_transl_atTop hf.1)
          (Eventually.of_forall fun s => mem_range_self s)
    · rintro _ ⟨s, rfl⟩
      exact ⟨s, hullMap_coe s⟩
  · have hauto : ∀ s : ℝ, transl f s ≠ auto fp ∧ transl f s ≠ auto fm := fun s => by
      constructor
      · intro h
        refine hna ⟨fp, fun t x => ?_⟩
        have := DFunLike.congr_fun h (t - s, x)
        simpa [transl_apply, auto] using this
      · intro h
        refine hna ⟨fm, fun t x => ?_⟩
        have := DFunLike.congr_fun h (t - s, x)
        simpa [transl_apply, auto] using this
    have htb : auto fp ≠ auto fm := fun h => hne (ContinuousMap.ext fun x => by
      simpa [auto] using (DFunLike.congr_fun h (0, x)).symm)
    refine hcont.isClosedEmbedding fun a b hab => ?_
    induction a using EReal.rec <;> induction b using EReal.rec
    all_goals simp only [hullMap_coe, hullMap_top, hullMap_bot] at hab
    · rfl
    · exact absurd hab.symm (hauto _).2
    · exact absurd hab htb.symm
    · exact absurd hab (hauto _).2
    · rename_i s s'
      by_contra hss
      refine hna (isAutonomous_of_periodic hf.1 (p := s' - s)
        (sub_ne_zero.2 fun h => hss (by rw [h])) fun t x => ?_)
      have := DFunLike.congr_fun hab (t - s, x)
      simp only [transl_apply] at this
      rw [show s + (t - s) = t by ring, show s' + (t - s) = t + (s' - s) by ring] at this
      exact this.symm
    · exact absurd hab (hauto _).1
    · exact absurd hab htb
    · exact absurd hab.symm (hauto _).1
    · rfl

end ConleyCheck
