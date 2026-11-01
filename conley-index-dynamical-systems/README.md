# ConleyCheck

Lean 4 / Mathlib formalization of the results of
*Conley index theory for asymptotically autonomous systems and UV→IR connections*.
Every module is imported in `ConleyCheck.lean`. `lake build` succeeds with no `sorry`, and the main
theorems depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

Module docstrings cite the paper by its LaTeX labels (for example `thm:slab` for Theorem 4.7 and
`prop:palmer`(ii) for Proposition 4.14(ii)). Run `rg "thm:slab" ConleyCheck` to find every place a given
result is used or proved.

## Status of the paper's results

Status values:

- **Formalized**: every claim of the statement is proved in Lean.
- **Conditional**: proved in Lean, except for a cited external theorem that enters as an explicit
  hypothesis. The citation is given in the last column.
- **Partial**: part of the statement is proved; the rest is described in the notes.
- **Not formalized**: no Lean counterpart.
- **No claim**: definitions, hypotheses, or remarks with no mathematical assertion to prove.

Files are relative to `ConleyCheck/`.

### Section 1: main theorems

| Paper | Status | Lean | Notes / citations |
|---|---|---|---|
| Theorem A (Transport map) | Formalized | `transport`, `transport_finrank` (`Conley/Double.lean`) | Summary of Theorem 4.8. Invariance under continuation is the field-coefficient statement of Theorem 4.8(iii). |
| Theorem B (Common blocks and rate independence) | Formalized | `rate_index`, `rate_index_collared`, `rate_transport`, `rate_connection` (`Conley/Rate.lean`); moving blocks: `rate_transport_conj` (`Conley/RateConj.lean`), `moving_saddle` (`Conley/MovingSaddle.lean`) | Summary of Theorem 4.12 and Corollary 4.13. `K_± = Inv(N, f_±)` is part of `rate_index`. The common block is `IsUniformBlock`. |

### Sections 2 and 4, Appendix A: compactification, the double, transport

| Paper | Status | Lean | Notes / citations |
|---|---|---|---|
| Definition 2.1 (Skew-product flow) | No claim | `IsSkew` (`Conley/Skew.lean`) | Encoded as a flow on `X × B` whose second component follows the base flow. |
| Definition 2.2 (asymptotically autonomous) | No claim | `IsAsymptoticallyAutonomous` (`Analysis/Hull.lean`) | |
| Lemma 2.3 | Formalized | `lem_hull` (`Analysis/Hull.lean`) | Hull construction follows [Sell 1971]. |
| Hypothesis 2.4 | No claim | `IsHeight` (`Conley/Height.lean`), hypotheses of `Conley/Slab.lean` | `ON/Ramp.lean` and `BjorkenFlow.lean` need only Lipschitz `g`, `N`. |
| Proposition 2.5 (When Hypothesis 2.4 holds) | Formalized | (i) `prop_Hcrit_i` (`Analysis/HcritI.lean`, `Warmup.lean`); (ii) `prop_Hcrit_ii` (`Analysis/Hcrit.lean`) | |
| Lemma 4.1 | Formalized | `lem_G` (`Analysis/LemG.lean`) | |
| Definition 4.2 (Double) | No claim | `dblΦ` (`Conley/Double.lean`), `circΦ`, `cR` (`Conley/Circle.lean`) | |
| Lemma 4.3 | Formalized | (a) `isSkew_dbl`, `dblQ_dblΦ` (`Conley/Double.lean`); (b) `cR_circΦ`, `cR_eq_self_iff`, `cq_eq_cq_iff` (`Conley/Circle.lean`) | |
| Lemma 4.4 | Formalized | (a) `fiber_isolating` (`Conley/Slab.lean`); (b) `snat_isolated`, `circ_isolated`; (c) `snat_attractorRepeller`, `circ_attractorRepeller` | |
| Proposition 4.5 (Boundary indices) | Formalized | `slab_top_hasIndex`, `slab_bot_indexTrivial` (`Conley/Slab.lean`); `dbl_boundary_IR`, `dbl_boundary_UV` (`Conley/Double.lean`); `circ_index_attractor`, `circ_index_repeller` and the `R_* = ±1` signs (`Conley/CircleSign.lean`); `skew_suspension` (`Conley/Suspension.lean`) | The UV suspension `h_D(K × {π}) ≅ Σ h_{f₋}(K)` is proved in homology, `CH_{n+1}(K × {π}) ≅ CH_n(K; f₋)`, which is the form used later. |
| Remark 4.6 (The boundary isomorphisms) | Formalized | `s_k`: `snat_repeller_index`, from `dbl_boundary_UV` and `skew_suspension`; `a_k`: `snat_attractor_index`, from `dbl_boundary_IR` (`Conley/Double.lean`, `Conley/Suspension.lean`) | Built along the route of the remark: continuation to the product flow on `N_K × J`, then the product with the base index. Lean works with homology indices, so the space-level top row of the diagram (`− ∧ S¹`, `Σ h_{f₋}(K₋) ≃ h_D(K₋ × {π})`) is not stated. |
| Theorem 4.7 (Index in the extended phase space) | Formalized | `slab_index` (`Conley/Slab.lean`, `Conley/Height.lean`) | |
| Theorem 4.8 (Transport map) | Formalized | `transport`, `transport_split`, `transport_finrank` (`Conley/Double.lean`); `finrank_middle` (`Algebra/ExactSeq.lean`) | The last conjunct of `transport` is the defining square `Ψ_k = a_k⁻¹ ∘ ∂_{k+1} ∘ s_k`, with `∂` the connecting homomorphism of the attractor–repeller sequence of `S♮`. (iii) is proved over a field, as stated. Invariance of `Ψ` over `ℤ` under continuation is stronger than the paper's claim and is not formalized. |
| Remark 4.9 (The transport map as a connecting homomorphism) | Formalized | last conjunct of `transport` (`Conley/Double.lean`) | `Ψ_k = a_k⁻¹ ∘ ∂_{k+1} ∘ s_k`, with `∂` the connecting homomorphism of `(K_+ × {0}, K_- × {π})`. The comparison with the connecting homomorphism of Jänig's nonautonomous index [Jänig 2019a; Jänig 2019b; Jänig 2020] is an open question in the paper and has no Lean counterpart. |
| Remark 4.10 (Ψ in terms of the extended phase space) | Not formalized | — | A sketch that the paper says is not used. |
| Remark 4.11 (Transition matrices and continuation maps) | No claim | — | Comparison with [Reineck 1988], [Franzosa–Mischaikow 1998], [McCord–Mischaikow 1992]. |
| Theorem 4.12 (Common strict entrance/exit blocks) | Formalized | `rate_index`, `rate_index_collared`, `rate_transport`, `rate_connection` (`Conley/Rate.lean`) | The common block is `IsUniformBlock`. The discussion after the theorem, that a common block with `∂^out = ∅` is forward invariant at every rate, is `IsUniformBlock.forward_of_exit_empty`. |
| Corollary 4.13 (Moving blocks) | Formalized | `rate_transport_conj` (`Conley/RateConj.lean`); `moving_saddle` (`Conley/MovingSaddle.lean`) | `moving_saddle` is the statement with `N/∂^out N ≃ S^k`. |
| Proposition 4.14 (Fredholm index and transversality) | Formalized | (i) `prop_palmer_i_flow`, `dblCutFlow`, `hasDerivAt_dblCutFlow`, `dblCutFlow_eq_of_sol`, `prop_palmer_i` (`Palmer/DoubleEnds.lean`); `hasFDerivAt_flow` (`Conley/Linearization.lean`); (ii), (iii) `palmer`, `isFredholm`, `index_eq`, `transversal_iff_surjective` (`Palmer/Fredholm.lean`) | (i) constructs the flow of the double. It is the global flow of the field cut off outside a ball containing `p±`, and it agrees with the double on that ball. No regularity of the time-`t` maps is assumed: their differentiability at the equilibrium follows from Grönwall's inequality. A cut-off is needed because, for a general `C¹` field `F`, solutions of the double can blow up in finite time. (ii)–(iii) prove [Palmer 1984, 1988] in Lean. |
| Remark A.1 (Geometric transversality) | Partial | `rem_palmergeom`, `transversal_double_iff` (`Palmer/DoubleVariation.lean`) | The linear part is proved. Identifying `E^u_D`, `E^s_D` with the tangent spaces of `W^u`, `W^s` needs the stable manifold theorem, which is not in Mathlib. |
| Theorem 4.15 (Equivariant structure) | Partial | (i) `equivariant_i` (`Conley/Circle.lean`), quotients in `Conley/EquivQuotient.lean`; (ii) `equivariant_ii`, `circ_sign_attractor`, `circ_sign_repeller` (`Conley/CircleSign.lean`); (iii) `equivariant_iii` (`Conley/EquivEuler.lean`), `fixed_homology`, `euler_fixed`, `equivariant_iii_fixed`, `euler_rel_fixed` (`Conley/EquivWedge.lean`) | (i) and (iii) are formalized. For (ii), Lean proves `R_* = +1` on the attractor index and `R_* = -1` on the repeller index, `2∂ = 0` over every coefficient ring, and `∂ = 0` with exact short sequences when `CH_*(K_+; f_+; Λ)` has no `2`-torsion. The paper's stronger claim, `∂ = 0` and a split sequence over every coefficient ring (proved with the projection `q` and Theorem 4.7), is not formalized. |
| Remark A.2 (Borel cohomology) | Not formalized | — | Restates Theorem 4.15(i) and (iii) in Borel cohomology [Borel 1960; tom Dieck 1987; Allday–Puppe 1993]. The paper says it is not used. |
| Theorem 4.16 (Duality) | Conditional | `isIsolated_image`, `homologyIndex_image`, `duality`, `duality_euler`, `duality_euler_odd` (`Conley/Duality.lean`); `euler_reflect` (`Algebra/ExactSeq.lean`) | Proved: `𝒮(K)` is isolated and `h(𝒮(K), ψ) ≅ h(K, ψ⁻¹)`. McCord duality `dim CH_k(K, ψ⁻¹) = dim CH_{n-k}(K, ψ)` [McCord 1992, *Poincaré–Lefschetz duality for the homology Conley index*] is the hypothesis `hMc`; Mathlib has no Poincaré–Lefschetz duality. |
| Remark 4.17 | No claim | — | A caveat explaining why Theorem 4.16 is not applied on manifolds with boundary. |

### Section 5: Gubser flow on the torus

| Paper | Status | Lean | Notes / citations |
|---|---|---|---|
| Proposition 5.1 (Torus compactification) | Conditional | (i) `prop_torus_equilibria`, `prop_torus_i`; (ii) `prop_torus_ii`; (iii) `prop_torus_iii`, `prop_torus_iii_chains` (`Gubser/Torus.lean`); `Dtorus` (`Algebra/ConnectionMatrices.lean`) | Everything except "the connection matrix is forced" is unconditional. For that clause, existence and the axioms of connection matrices [Franzosa 1989] are hypotheses, and Lean checks the linear algebra. |
| Proposition 5.2 | Formalized | `prop_transversal`, `prop_transversal_ker` (`Gubser/Separatrix.lean`); `prop_transversal_palmer` (`Palmer/GubserApp.lean`) | |
| Remark 5.3 (Splitting of E^u and E^s) | Partial | `rem_gap` (`Gubser/Gap.lean`); `integral_cosh_rpow_neg` (`Analysis/CoshBeta.lean`) | `E^u`, `E^s` and the closed form of `Δ(c)` are proved. The decimal value `Δ(c) ≈ 0.892/c` is not. |
| Corollary 5.4 | Formalized | `cor_gubserB_i`, `cor_gubserB_i_int`, `cor_gubserB_ii`, `cor_gubserB_iii`, `cor_gubserB_iv` (`Gubser/Separatrix.lean`) | The face inequalities used in the proof are those of Lemma B.1(a). |
| Lemma B.1 (The moving block of the separatrix) | Formalized | identities `eq:xieta-dot`: `Dxi_eq`, `Deta_eq`, `lem_gubser_block_deriv`; remainder bounds `abs_Rξ_le`, `abs_Rη_le`; (a) `lem_gubser_block_a`; (b) `lem_gubser_block_b` (`Gubser/SepBlock.lean`); last assertion: `lem_gubser_block_inv` (`Gubser/SepBlock.lean`), `inv_sep` (`Gubser/Separatrix.lean`) | The last assertion, that only `ξ = η = 0` stays in `N_B` for the compactified and the frozen flows, is proved from the triangular structure of the system in the coordinates `(T/c, π + a)` rather than from the cone estimate (b). |

### Section 6: Bjorken flow

| Paper | Status | Lean | Notes / citations |
|---|---|---|---|
| Proposition 6.1 | Formalized | `prop_bjorken_index`, `prop_bjorken_exists`, `prop_bjorken_unique`, `prop_bjorken_ker` (`BjorkenFlow.lean`); `prop_bjorken_invertible` (`Palmer/BjorkenApp.lean`); algebraic checks in `Bjorken.lean` | Holds for every rate `g`. The asymptotic form `c_1^*(w) = -8θ₀/(3w) + O(w⁻²)` stated before the proposition is not formalized. |

### Section 7 and Appendix C: Gubser flow on `D² × S¹`

| Paper | Status | Lean | Notes / citations |
|---|---|---|---|
| Remark 7.1 | Not formalized | — | A heuristic connection-matrix argument. Its conclusion, that the six-point set is not isolated, is `cor_gubserB_iv`. |
| Lemma 7.2 | Formalized | `lem_TC_i`, `lem_TC_ii`, `lem_TC_iii` (`Gubser/TCIndex.lean`); `lem_TC_ii_minus`, `lem_TC_iii_minus` (`Gubser/TCMinus.lean`); `lem_TC_*_homology` (`Gubser/TCHomology.lean`) | |
| Remark 7.3 (Exploratory numerics) | Not formalized | — | Exploratory numerics that the paper says are not used. The Morse decomposition in (a) is proved as Theorem 7.4. |
| Lemma C.1 (Equilibria at infinity and barriers) | Formalized | (i) `Gubser/Infinity.lean`; (ii) `lem_barrier_ii_pos`, `lem_barrier_ii_zero`, `lem_barrier_ii_neg`; (iii) `lem_barrier_iii` (`Gubser/Barrier.lean`) | |
| Lemma C.2 (The fiber flows) | Formalized | (i) `Gubser/Fiber.lean`, `IC_saddle` (`Gubser/Infinity.lean`); (ii) `lem_fiber_ii`; (iii) `lem_fiber_iii` (`Gubser/Fiber.lean`) | |
| Theorem 7.4 (Global Morse decomposition) | Formalized | (i) `indexTrivial_Mm`, `indexTrivial_Mp` (`Gubser/MIndex.lean`); (ii) `fixed_mem_Mm`, `fixed_mem_Mp`; (iii) `thmM_morse`, `no_conn_Mm_Mp` (`Gubser/ThmM.lean`); conditions on `δ`: `KHyp` (`Gubser/MBlocks.lean`) | Lean proves the precise form stated in Appendix C: explicit conditions (k1)–(k3) on `δ`, and the stronger (ii) that every equilibrium with `y₂ < 0` lies in `M⁻` and every one with `y₂ > a y₃` lies in `M⁺`, which covers the points and complexes `X^∓` listed in (ii). |
| Connection matrix of Theorem 7.4 (`Δ Σ_U(A) = TC⁻`) | Conditional | `DM`, `DM_forced` (`Algebra/ConnectionMatrices.lean`) | Connection-matrix theory [Franzosa 1989] enters as hypotheses. |
| Connecting orbit `Σ_U(A) → TC⁻` and `CH_*(Σ_U(A)) ≅ Λ[3]` | Formalized | `exists_conn_SUA_TCm`, `homologyIndex_SUA`, `hasIndex_SIA_reverse`, `subsingleton_CH3_univ` (`Gubser/Connection.lean`) | Proved from two attractor–repeller sequences and the reversor, without connection matrices. |
| Corollary 7.5 (Attractor indices) | Formalized | `cor_attractors` (`Gubser/Attractors.lean`) | |

### Section 8: `O(N)` model with cubic anisotropy

| Paper | Status | Lean | Notes / citations |
|---|---|---|---|
| Lemma 8.1 (Structure of the one-loop flow) | Formalized | (i), (ii) `ON/Model.lean`; (iii) `lem_ONstructure_iii`; (iv) `lem_ONstructure_iv_fst`, `lem_ONstructure_iv_snd` (`ON/Structure.lean`) | The Morse indices on both sides of `N = 4` are `morse_indices_gt4`, `morse_indices_lt4`. That the unlabeled Morse polynomial is unchanged while the indices of `Σ_C` and `Σ_H` are exchanged is `morse_exchange` (`ON/Model.lean`). |
| Proposition 8.2 (A uniform isolating block) | Formalized | (a) `prop_ON_a`, `prop_ON_c` (`ON/Flow.lean`); (b) `prop_ON_b_chain` (`ON/Chain.lean`), `prop_ON_b_tendsto`, `prop_ON_b_morse`, `prop_ON_b_connecting` (`ON/Limits.lean`) | |
| Corollary 8.3 (Connection data of the `O(N)` model) | Formalized | `cor_ON_i` (`ON/Structure.lean`); `cor_ON_ii`, `cor_ON_ii_orbits`, `cor_ON_iii`, `cor_ON_iii_orbits` (`ON/Connection.lean`) | |
| Remark 8.4 (Connection matrices) | Conditional | `DON` (`Algebra/ConnectionMatrices.lean`) | Existence and axioms of connection matrices [Franzosa 1989] are hypotheses. |
| Proposition 8.5 (Transition data of a parameter shift through `N=4`) | Formalized | (i) `prop_ONramp_i_index` (`ON/Ramp.lean`), `ON/RampMorse.lean`; (ii) `not_tendsto_I_or_C` (`ON/RampDiagonal.lean`), `ON/Diagonal.lean`, `transversal_G`, `transversal_I` (`Palmer/ONApp.lean`); (iii) `prop_ONramp_iii` (`ON/RampIndex.lean`) | |
| Remark 8.6 (Connection matrices of the shift) | Conditional | `Dshift`, `Dshift_sq`, `Dshift_eq_Dlam`, `Dlam_conj`, `Dlam_H_ne_zero` (`Algebra/ConnectionMatrices.lean`) | Existence and axioms of connection matrices [Franzosa 1989] are hypotheses. Every connection matrix is `Δ₋ ⊕ Δ₊ + T_λ`, and all `T_λ` are conjugate by a filtered change of basis. |
| Non-uniqueness of the transition matrix (discussion after Remark 8.6) | Conditional | `Dlam_common`, `Dlam_one`, `Tblk`, `Tblk_rank_zero`, `Tblk_rank_of_ne`, `Tblk_not_equiv`, `Tblk_zero_C`, `label_preserving_excluded` (`Algebra/ConnectionMatrices.lean`) | The full connection matrices `Δ_λ` are conjugate (`Dlam_conj`), but the blocks `T_λ` are not: `T_0` has rank `2`, `T_1` has rank `4`, and `T_0` has no entry from `Σ_C⁻` and none into `Σ_C⁺`. The data shared by all `T_λ` are `T Σ_G⁻ = Σ_G⁺`, `T Σ_I⁻ = -Σ_I⁺` and `a + b = -1`. `Dlam_one` is the representative `T_1`, and no representative preserves all labels. Uniqueness of connection matrices only up to filtered chain isomorphism [Spendlove–Vandervorst 2026] is not formalized. The isomorphism `CH_{k+1}(Σ_H⁻) → CH_k(M_A)` is `prop_ONramp_iii`, which does not use connection matrices. |

## Summary of gaps

- Inputs cited from the literature and taken as hypotheses:
  - McCord duality, for Theorem 4.16 [McCord 1992];
  - connection-matrix theory, for Proposition 5.1(iii), Remarks 8.4 and 8.6 and the discussion
    after Remark 8.6, and the connection matrix of Theorem 7.4 [Franzosa 1989].
- Not formalized:
  - the stable-manifold half of Remark A.1;
  - the decimal value in Remark 5.3;
  - the vanishing of `∂` in Theorem 4.15(ii) over coefficient rings in which `CH_*(K_+; f_+)` has
    `2`-torsion (Lean has `2∂ = 0` in general and `∂ = 0` without `2`-torsion);
  - the asymptotic form of the Bjorken attractor solution in Section 6;
  - Remarks 4.10, 7.1, 7.3 and A.2. We have not used any of these in a proof in the paper;
  - the comparison with Jänig's nonautonomous index in Remark 4.9 and Section 1, which the paper
    leaves open.

## References (as cited in the paper)

- [Allday–Puppe 1993] C. Allday, V. Puppe, *Cohomological Methods in Transformation Groups*, CUP (1993).
- [Borel 1960] A. Borel, *Seminar on Transformation Groups*, Ann. of Math. Stud. 46 (1960).
- [Franzosa 1989] R. Franzosa, *The connection matrix theory for Morse decompositions*, Trans. AMS 311 (1989) 561.
- [Franzosa–Mischaikow 1998] R. Franzosa, K. Mischaikow, *Algebraic transition matrices in the Conley index theory*, Trans. AMS 350 (1998) 889.
- [Jänig 2019a] A. Jänig, *Nonautonomous Conley index theory. The homology index and attractor-repeller decompositions*, Topol. Methods Nonlinear Anal. 53 (2019) 57.
- [Jänig 2019b] A. Jänig, *Nonautonomous Conley index theory: the connecting homomorphism*, Topol. Methods Nonlinear Anal. 53 (2019) 427.
- [Jänig 2020] A. Jänig, *Equilibrium-like solutions of asymptotically autonomous differential equations*, J. Dyn. Differ. Equ. 32 (2020) 1249.
- [McCord 1988] C. McCord, *The connection map for attractor-repeller pairs*, Trans. AMS 307 (1988) 195.
- [McCord 1992] C. McCord, *Poincaré–Lefschetz duality for the homology Conley index*, Trans. AMS 329 (1992) 233.
- [McCord–Mischaikow 1992] C. McCord, K. Mischaikow, *Connected simple systems, transition matrices, and heteroclinic bifurcations*, Trans. AMS 333 (1992) 397.
- [Palmer 1984] K.J. Palmer, *Exponential dichotomies and transversal homoclinic points*, JDE 55 (1984) 225.
- [Palmer 1988] K.J. Palmer, *Exponential dichotomies and Fredholm operators*, Proc. AMS 104 (1988) 149.
- [Reineck 1988] J.F. Reineck, *Connecting orbits in one-parameter families of flows*, Ergodic Theory Dynam. Systems 8* (1988) 359.
- [Sell 1971] G.R. Sell, *Topological Dynamics and Ordinary Differential Equations*, Van Nostrand Reinhold (1971).
- [Spendlove–Vandervorst 2026] K. Spendlove, R. Vandervorst, *Graded differential vector spaces, Cartan–Eilenberg systems and conjectures in Conley index theory*, J. Dyn. Differ. Equ. 38 (2026) 695.
- [tom Dieck 1987] T. tom Dieck, *Transformation Groups*, De Gruyter (1987).
