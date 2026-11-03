# Infra review 2: statement review of newly landed Foundations (Task 6a)

Auditor: `wt-orch`. Date: 2026-11-03. Tree: `w/orch` at `187ca2e` (fast-forward of `main`).
Scope: the `WaveTurbulence/Foundations/**` files changed since Infra-review-1's base `0956996`. That is 184 files,
about 22.1k inserted lines.

**Method.** The same as Infra-review-1: statements, not proofs. I looked for:
- normalizations;
- junk values (`tsum`, Bochner integrals, `ncard`, truncated subtraction);
- hypotheses that cannot be discharged at the use site;
- uniformity of constants;
- the `ContDiff ℝ ⊤` = analytic pitfall (F44).

I compared against TARGET (`paper/source/WKE-Longer_times_Final_arXiv.tex`, sha256 `493eef6b…727cb`), the frozen
anchors, and the Wave B snapshot I audited in stages 1–2.

**Coverage.**
- **Read in detail** (definitions and every public statement):
  - `WKE/{Lifespan, Existence, Uniqueness, Taylor}`, plus the headers of `TaylorSeries` and `TaylorCoeff`;
  - `NLS/{AkSystem, AkClass, AkUnique, Reduction, UniformDecay, Symmetry}`;
  - `Fourier/{Chi0, Chi0Gevrey, Gevrey, TimeFourier, TimeWeights, TimeBasic, TimeProduct, TimeInterpolation,
    MixedNorm, CutoffMultiplication, SchwartzNorm, LinearChange, FourierL1Product, CutoffFourierDecay,
    TensorFourierDecay}`;
  - `Cumulant/{Products, ProductsFormula, Gaussian}`;
  - `Resonant/Integral`;
  - `LinAlg/LatticeRepresentatives` (`finitelem`);
  - `Analysis/{HeapOrderVolume, SimplexVolume, TimeForest, TimeForestVolume}`.
- **Headlines and module docstrings only:**
  - `NLS/{AkMass, AkPersistence, AkGronwall, GoodCurve, SpaceTimeSeries, Convolution, SeriesDeriv}`;
  - the remaining `Fourier/*`;
  - `Resonant/*` (principal-value toolkit);
  - `WKEL2/*` (partial; its HANDOFF claims no milestone);
  - `WeylSums/*` (GAUSSSUM handoff);
  - `NumberTheory/*` (NT-CIRCLE-v2 handoff);
  - `Counting/*`, `LinAlg/*`, `Combinatorics/*`, the rest of `Analysis/*`;
  - `Cumulant/{Coarsening, CoarseningWeight, PartitionLift, Refinement}`.
- **Diffed against Infra-review-1** for statement changes: the modules reviewed there. The changes are
  namespacing plus new `_mom` and nonempty-set variants.
- **`Foundations/Probability/**`, named in TASK6, does not exist** in this tree.

## Verdict

**No wrong statement found.** Every directly consumed object checks out against TARGET and the frozen anchors:
- τ_max, `wkelwp_conj12`, and the WKE Taylor expansion and bound;
- the NLS → a-system reduction and the classed a-system;
- χ₀ with F41;
- the 𝔛, 𝔖 and restriction norms;
- `propertycm`;
- the resonant integral.

**F44 is clean.** No occurrence of `ContDiff ℝ ⊤` (or any `ContDiff… ⊤`, `ω`, `AnalyticOn`) in the code base.
Smoothness is written `∞` or `(⊤ : ℕ∞)` throughout.

**One REQUIRED item (bookkeeping, licence):**
- **L1.** `Counting/MonotoneIntervals.lean` is adapted from salt but is not listed in `docs/THIRD-PARTY.md`. It is
  derived from `Salt/ExpSum/VdCorput2.lean`, its header names Jason Hickey, and it points to `SALT-LICENSE`.

**Infra-review-1 items now closed:**
- **N1 is closed.** The class `IsAkBounded` is inside `IsAkSolution`.
- **W2 is resolved.** `taylorbound` has C₁ = 2ρ(d, B), independent of (Λ₁, Λ₂).

**Eight SHOULD items (S1–S8)** concern integration with the Wave B drafts. Several Wave B snapshot definitions now
have landed Foundations twins and must be unified or bridged before the Wave B freeze. These are inputs to Task 6b.

## Table

| Module | Declaration(s) | Verdict | Issue | Fix |
|---|---|---|---|---|
| WKE/Lifespan | `tauMax` = ⨆_{τ>0, ∃φ IsWKESolution φin τ φ} ofReal τ | OK | This is the supremum of closed-interval existence times. Conjunct 1 of the frozen `wkelwp` determines τ_max uniquely given 0 < τ_max (it characterizes {τ★ : ofReal τ★ < τ_max}), so instantiating the frozen existential with `tauMax` is forced. | — |
| WKE/Lifespan | `isWKESolution_mono`, `isWKESolution_glue`, `exists_isWKESolution_of_lt_tauMax` | OK | Gluing at T uses the one-sided derivatives within `Icc`, as in the frozen `IsWKESolution`. | — |
| WKE/Existence | `exists_isWKESolution` (d ≥ 2), `tauMax_pos`, `lt_tauMax_iff`, **`wkelwp_conj12`** | OK, exact | `wkelwp_conj12` reproduces conjuncts 1–2 of the frozen anchor **verbatim** (same binders, same `ENNReal.ofReal τ★ < τmax ↔ ∃ φ, …`, same uniqueness on `Icc 0 τ★`), for d ≥ 2 ⊇ the frozen 3 ≤ d. Conjunct 3 (blow-up in Z_s) is not landed; it is still the GIT20 gap (F32; my GIT20-general-d audit and the WKEL2 HANDOFF). | — |
| WKE/Uniqueness | `isWKESolution_unique` (d ≥ 2) | OK | Exactly conjunct 2. | — |
| WKE/Taylor | `taylorU` (𝒰ₙ(t) = (δ(t−p))ⁿ aₙ[φ(pδ)]), `wketaylor`, `wketaylor2_zero`, `wketaylor2_succ`, `taylorbound` | OK | (wketaylor) holds for δ ≤ `taylorStep d B` and (p+1)δ ≤ T, with B a bound for (1+\|y\|)^{2d+1}\|φ(τ,y)\| on [0,T]. B is supplied by `exists_lowNorm_bound` and is ≤ 𝔆. (wketaylor2) is proved for **every** t, as Σ over ordered triples n₁+n₂+n₃ = m (nested antidiagonals) of ∫_p^t 𝒦(𝒰_{n₁},𝒰_{n₂},𝒰_{n₃}) with the factor δ. (taylorbound): `∃ C₂` comes after δ, Λ₁, Λ₂ (TARGET lets C₂ depend on δ), and the base C₁ = 2·taylorRate(d, 2d+1, B) depends only on d and B. The seminorm (1+\|y\|)^{Λ₂}‖Dʳ·‖, r ≤ Λ₁, dominates 𝔖^{Λ₁,Λ₂}. This closes Infra-review-1 W2: the Λ-dependence enters only through a polynomial factor (2n+1)^{Λ₁+Λ₂}, which `Mq·2ⁿ` absorbs into C₂ at the cost of the factor 2 in C₁. | S4 (bridge to Wave B's `wkeTaylorTerm`) |
| NLS/AkSystem | `IsAkBounded`, `IsAkSolution` (now `a 0 = c ∧ IsAkBounded ∧ ∂ₜa = 𝒞₊(a,ā,a)`), in namespace **`WaveTurbulence.NLS`** | OK; **closes N1** | The weight (1+‖n/L‖²)^{(d+1)/2} = ⟨n/L⟩^{d+1} is exactly the Wave B class (Q16). The `aNonlin` `tsum` is then absolutely summable (`AkClass`). | S2 (Wave B must follow the namespace and drop its duplicate class) |
| NLS/AkClass, AkUnique | `IsAkBounded.exists_norm_le`, `summable_inv_one_add_norm_pow`, `IsAkSolution.eq_add_integral`, **`IsAkSolution.eq_of_eq`** (0 < L) | OK | The class is part of the definition, so uniqueness holds exactly in the class B1.1 uses. | — |
| NLS/AkMass, AkPersistence | `tsum_normSq_eq` (mass), `tsum_weight_le`, `exists_uniform_decay` | OK (headlines) | Mass conservation is the integrability source for `AnsatzAt` (1) (stage-2 table). | — |
| NLS/Reduction | `massAvg`, `wickGauge` (v = e^{−2iαMt}u with M = ⨍\|u(0)\|²), `reducedCoeff` (a_k(t) = e^{−πiδL^{2γ}\|k\|²t} v̂(δT_kin t, k)), `hasDerivWithinAt_reducedCoeff`, `reducedCoeff_zero`, `norm_reducedCoeff` | OK | (reducedcoef) L543 is literal with T_kin = `kineticTime (L^{−γ})` = L^{2γ}/2 (frozen). M is taken at t = 0, which is legitimate by mass conservation (L540: "the conserved mass"). The derivative is `aNonlin … 1` with the middle input conjugated, on `Icc 0 𝔇`, under T = δ·T_kin·𝔇, δ ≥ 0, L > 0. These are dischargeable at the B1.4 use site. | — |
| NLS/UniformDecay | `IsSmoothNLSSolution.exists_uniform_decay`, `…_reducedCoeff`, **`IsSmoothNLSSolution.isAkSolution`** | OK | The forward reduction from the **frozen** `IsSmoothNLSSolution L (L^{−γ}) T c u` (C^∞ via `(⊤ : ℕ∞)`) into the classed `IsAkSolution L γ δ 𝔇 c (reducedCoeff …)`. This is B1.4 item 1 exactly. The backward direction (`NLS/Backward`, named in `GoodCurve`'s docstring) is not landed. | — |
| NLS/Symmetry | `smoothDataSet`, `solvableEvent_eq_preimage` (`rfl`), `mem_smoothDataSet_gauge_iff`, `mem_smoothDataSet_translate_iff`, `reducedCoeff_gauge`, `reducedCoeff_translate` | OK | The translation law c_n ↦ e^{−2πi⟨n/L, x₀⟩}c_n is exactly Wave B's `IsSymmetricEvent` (Q5 initial-data reading). `solvableEvent = initialCoeff⁻¹(smoothDataSet)` with an invariant set, so the Q5 form is immediate, **except** for the `MeasurableSet A` conjunct. | S5 |
| Fourier/Chi0, Chi0Gevrey, Gevrey | `chi0 x = ψ(2−2x)·ψ(2+2x)` (ψ = `Real.smoothTransition`), `chi0Tensor`, `chiInfinity*`, `GevreyTwoBound f C A` (\|f^{(m)}\| ≤ C·A^m·(2m)!), **`chi0_gevreyTwoBound`** (C = e⁴, A = 16+16e²), `chi0Tensor_line_gevreyTwoBound` | OK (F41) | All the L617–L623 properties are proved. The Gevrey bound is the F41 / Q6 reading with explicit absolute constants. **It equals the Wave B draft's χ₀ pointwise**: probe `fourier_chi0_eq_abs : Fourier.chi0 x = ψ(2 − 2\|x\|)`, sorry-free (§Probes). The line version gives every directional derivative; mixed partials of the tensor follow by the product rule. | S1 |
| Fourier/TimeFourier, TimeWeights | `timeFourier` (e^{−2πiλ·t}, L579), `timeBracket` = max(1, max_j⟨ξ_j⟩), `timeWeight θ` = ofReal(timeBracket^θ), `timeFourierNorm` (⊤ unless `Integrable`), `timeRestrictionNorm` (⨅ over whole-space extensions; f : B → ℂ) | OK | (normX1) with **(max ⟨ξ_j⟩)^θ, correct for θ < 0**. This is already the content of my stage-2 R3 fix. The r = 0 convention is weight 1. The integrability guard is the same reading as Wave B (stage-2 O1), disclosed. Weights: `timeBracket_add_le_mul` and `timeWeight_add_le_abs` (Peetre with 2^{\|θ\|}). | S3 |
| Fourier/MixedNorm | `momentumBracket`, `momentumDerivative` (coordinate words via `iteratedFDeriv`), `momentumSupNorm`, `spatialNorm` (𝔖; ⊤ unless C^{Λ₁}), `mixedFourierNorm` (𝔛; admissible = slices integrable ∧ ∀ᵐξ F̂(ξ,·) ∈ C^{Λ₁}), `mixedRestrictionNorm` (any K ⊆ ℝ^d), `spatialRestrictionNorm` | OK | The derivative maximum is outside the frequency integral and the momentum supremum inside, as (normX) L581 has it. The a.e. admissibility is equivalent to Wave B's pointwise ⊤-integrand convention: an integrand that is ⊤ on a null set contributes nothing to `∫⁻`. **`spatialRestrictionNorm` supplies the 𝔖-on-ℤ_L^d variant** that stage-2 O6 found missing in Wave B. | S3 |
| Fourier/TimeBasic, TimeProduct, TimeInterpolation, CutoffMultiplication, SchwartzNorm, LinearChange | triangle, scaling and modulation bounds; `timeFourier_mul_eq`; `timeFourierNorm_mul_le` (θ ≥ 0, 2^θ); `…_asymmetric_le` (all θ, 2^{\|θ\|}, \|θ\| on g); `integrable_timeFourier_of_norm_lt_top` (θ ≥ 0 only, correctly); Hölder interpolation; `timeFourierNorm_mul_cutoff_le` (every θ ∈ ℝ); Schwartz finiteness; \|det A\| = 1 invariance at θ = 0 | OK | Constants are explicit and depend only on θ (and on the cutoff). The `Continuous g` hypotheses select the inversion representative and are dischargeable for the kernel cutoffs. | — |
| Fourier/FourierL1Product, FourierL1Sobolev, ProductFourier, BlockCoordinates, TimeSobolev, TimeEuclidean | `fourierL1_product_comp_matrix_le`: ‖∏ f_i(blocks of A z)‖_{𝔛⁰} ≤ C(d)ⁿ ∏ W^{d+1,1}(f_i) for \|det A\| = 1 | OK | This is TARGET L1007–L1012 with the one-factor constant depending only on the block dimension d. It holds for real A with \|det\| = 1, stronger than the integer unimodular case. | — |
| Fourier/CutoffFourierDecay, TensorFourierDecay | \|𝓕χ₀(ξ)\| ≤ 8e⁴ exp(−c√\|ξ\|), and the tensor version | OK | Stretched-exponential decay from Gevrey 2, with explicit constants. | — |
| Cumulant/Products, ProductsFormula | `IsIrreduciblePartition I S P` (no nonempty proper A ⊆ I with ∪_{A}S_i a union of blocks), **`cumulant_prod`** (eqncm3) | OK (F30) | This is Lemma `propertycm` L2343 with the approved F30 corrections: nonempty proper subfamilies, nonempty groups, pairwise disjoint groups. It holds for an **unnormalized** μ, which is what `μ.restrict F_p` needs (L576 and stage 2). The empty-I case is covered (both sides 1). It is purely algebraic in the totalized moments, so it is junk-consistent; consumers supply integrability (`AnsatzAt` (1)). | — |
| Cumulant/Gaussian | `cumulant_signed_eq_gaussianPairWeight`, `…_zero_of_card_ne_two`, `…_zero_of_no_opposite_pair`, `cumulant_signed_pair` | OK | The vanishing is stated for nonempty sets, because the literal 𝕂(∅) = 1. | — |
| Cumulant/Symmetry (changed) | `…_translation_invariant_mom` (charges in `Mom d`) | OK; C1 unchanged | It still needs `Measurable (X j)`. Wave B now asserts `Measurable` in B1.1 (C1 resolved on the consumer side). | — |
| Resonant/Integral | `resonantIntegral Ψ k = ∫ (2‖ℓ‖)⁻¹ ∫_{ℓ^⊥} Ψ(k+ℓ, k+ℓ+w, k+w)`, `collisionOp_eq_resonantIntegral` (`rfl`), `tendsto_mollified_resonantIntegral_k` | OK | The same D6 hyperplane reading as the frozen `collisionOp`, characterized again by mollifying the energy delta (with its sign). | — |
| Resonant/PrincipalValue*, BilinearFourier*, Sine*, Slice*, Localized* (headlines) | `energyPrincipalValue_spec`, `norm_bilinearFourierTruncation_le` (C(d,χ)·D·R^{2d}, uniform in both centres, both frequencies and the cutoff scale) | OK (headlines) | The docstrings are careful about what is *not* claimed (frequency uniformity where absent). DH21 Lemma 6.3(1) is on the square torus. | — |
| WKEL2/* (partial) | `resonantMeasure` (includes \|a\|⁻¹, omits the ½), `weight_transfer` (frozen `weightedL2Norm` multiplier, 2^{s/2}), `radial_cauchy_schwarz`, exponent windows | OK (headlines); **no milestone claimed** | The normalization differs from `collisionOp` by the documented factor ½, as in GIT20-general-d Lemma 1. The HANDOFF states that Lemma 1 for general Borel kernels, Props 5–7, Theorem 7 and `wkelwp_blowup` are **not** proved, so there is nothing yet to consume. | — |
| WeylSums/* | `exists_coprime_approx` (Dirichlet), `norm_gaussSum_le_of_approx` (128K(1+log K)/(√q(1+K√\|s−a/q\|))), `exists_norm_smoothGaussSum_le` (no log; any fixed C_c^∞ χ; uniform in L ≥ 1, s, r, h, a, q ≤ L) | OK (headlines) | Uniformity is in the quantifiers, as NT.gaussSum needs. The lattice `tsum` is justified by `HasSum`, not by a junk convention. `smoothGaussSum` requires `ContDiff ℝ ∞ χ` (∞, not ⊤). | — |
| NumberTheory/* (salt-derived toolkit) | `kusmin_landau_discrete` (constant 1 under a fixed strip [m+δ, m+1−δ]), `van_der_corput_second_difference` (8(c(b−a)√λ + 1/√λ)), the continuous derivative tests, `weyl_vdC_expSum`, `norm_sawtoothRem_le` | OK (headlines); **L1** | Standard forms. Constant 1 is valid since cot(πδ/2) < 1/δ. The handoff states that goal 2 (circle discrepancy) is incomplete and claims no circle, annulus or `estcross` theorem. `SmoothingBounds` has its frequency estimate as an explicit premise, honestly labelled. | L1 |
| Counting/* | NT-CIRCLE-v2 goal-2 pieces: exact lattice discs, dyadic blocks, Euler–Maclaurin, semicircle sawtooth (326r², radius r³), annulus–line collinearity, quadratic strips; `ExponentAudit` (F3) | OK (headlines) | No discrepancy theorem is asserted (docstrings say so). No `ncard`/`Nat.card` of possibly infinite sets appears in any statement; finite `Finset.card` throughout. | L1 (`MonotoneIntervals`) |
| LinAlg/LatticeRepresentatives, FiniteRepresentatives | `exists_lattice_representatives` (2 ≤ L ≤ M; \|ℜ𝔢𝔭\| ≤ M^{4d²+6d}; the (represent) equivalence and equality) | OK | This is Lemma `finitelem` L2435's conclusion (represent), with the explicit C₀ = 4d²+6d and k* ∈ ℤ_L^d. The exact-count version without 2 ≤ L ≤ M is also given. | — |
| LinAlg/MaxVolume, BoundedSpanning | `lincomblem` with coefficients ≤ 1 | OK (stronger than the source's 2^{d−1}) | Maximal-volume selection. | — |
| Combinatorics/* | `combineq` pieces (DH21 Lemma A.4) | OK (headlines) | Uniform in the number of coordinates. | — |
| Analysis/HeapOrderVolume, SimplexVolume, TwoChainBound, FactorialExponential, OrderedSimplex | `volume_heapOrderRegion` = #(linear extensions)·Dⁿ/n!; `volume_orderedSimplex` = Dⁿ/n!; the two-chain 2^z loss | OK | The heap-volume formula is exact for any relation R; a cyclic R gives 0 extensions and an empty region. The truncated-subtraction caveat is handled explicitly (`…_of_one_le`). | — |
| Analysis/TimeForest, TimeForestVolume | `TimeForest n` (parent index < child), `timeDomain` (gaps σ ≥ 0; roots below t), `integral` (phase e^{πiα_v s_v}, DH21 Lemma 10.2), `enorm_integral_le_heapVolume` | OK | The phase convention matches the kernels' e^{πiζδL^{2γ}Ωt}. The docstring says the carrier is independent of the frozen tree API. | S6 |
| Analysis/{CubeSobolev, CovariantCubeSobolev, Morrey*, Riesz*, Square*, Cutoff*, Oscillatory*, Radial*, Cauchy*, ResonantConvolution, Permutation/OrderChambers} | Sobolev, Morrey and oscillatory tools | OK (headlines) | `RieszKernel` is adapted from the owner's own elliptic-regularity library, so it needs no third-party notice. | — |

## REQUIRED

**L1. Add `Counting/MonotoneIntervals.lean` to `docs/THIRD-PARTY.md`.**
- **The gap.**
  - The file's header reads: "Copyright (c) 2026 Jason Hickey, Scott Armstrong … see ../NumberTheory/SALT-LICENSE".
  - Its docstring cites `Salt/ExpSum/VdCorput2.lean` at commit `3d72740…`.
  - The THIRD-PARTY row lists only eight `NumberTheory/*` files.
  - The source glob `Salt/ExpSum/*` already covers VdCorput2. Only the file list is incomplete.
- **Fix.** Extend the row's file list with `WaveTurbulence/Foundations/Counting/MonotoneIntervals.lean` (parts). Add a
  check to the release checklist: `grep -rl "SALT-LICENSE" WaveTurbulence` must equal the THIRD-PARTY file list.

## SHOULD (integration with Wave B; inputs to the 6b delta audit)

- **S1. χ₀: two definitions.**
  - The Wave B draft defines its own `WaveTurbulence.chi0 x = ψ(2−2|x|)` and `chi0Vec` on `Mom d`.
  - Foundations has `WaveTurbulence.Fourier.chi0` (equal pointwise; probe below) and `chi0Tensor` on `Fin d → ℝ`, with
    the F41 Gevrey bound proved.
  - **Recommendation.** Freeze the Foundations `Fourier.chi0`. Define Wave B's `chi0Vec x := Fourier.chi0Tensor (fun i
    => x i)`, or prove `chi0 = Fourier.chi0` and `chi0Vec x = chi0Tensor (WithLp.ofLp x)` next to the Wave B
    definition.
  - Update WAVE-B §2.6 item 5 (L251–L252), which still states the literal "|χ₀^{(m)}| ≤ (2m)!"; F41 supersedes it.
- **S2. The a-system: namespace and class.**
  - `epsCoef`, `resonance`, `aNonlin`, `IsAkBounded` and `IsAkSolution` moved to `WaveTurbulence.NLS`, and
    `IsAkSolution` now contains the class.
  - Wave B's `IsASolution := IsAkSolution ∧ (class)` is therefore redundant, and its references to the unqualified
    names no longer resolve.
  - **Recommendation.** Use `NLS.IsAkSolution` directly in B1.1 and B1.4 (or `abbrev IsASolution := NLS.IsAkSolution`),
    and `open NLS`.
- **S3. Norms: two parallel families.**
  - Wave B has `SNorm`/`XNorm`/`XNorm00`/`*Restr`; Foundations has `spatialNorm`, `mixedFourierNorm`,
    `timeFourierNorm` and the restriction norms.
  - They agree in reading, once stage-2 R3 is applied:
    - the ⊤ guards;
    - (max⟨ξ⟩)^θ;
    - the derivative maximum outside and the momentum supremum inside the integral;
    - pointwise momentum suprema.
  - They differ in carriers:
    - momentum words versus multi-indices;
    - f : B → ℂ versus agreement on B;
    - an a.e. versus a pointwise C^{Λ₁} guard;
    - Foundations has no 𝔛^{θ,0,0} with an arbitrary vector-variable type V.
  - **Recommendation.** Before the Wave B freeze, define the Wave B norms through the Foundations ones, or prove
    equality lemmas, so that the provers' estimates (the cutoff multiplier, products, interpolation, Fourier-L¹)
    apply to the frozen statements. B1.6 `sumint` needs a V-valued 𝔛^{θ,0,0}(𝓑): add `mixedFourierNorm00` over a
    general V, or the bridge.
- **S4. Taylor terms.**
  - Wave B's `wkeTaylorTerm (φ(pδ)) δ p n` and Foundations' `taylorU hd φ δ p n` satisfy the same recursion
    (wketaylor2) for all t. One enumerates triples with `antidiagonalTuple 3`, the other with nested antidiagonals.
  - **Recommendation.** Add the bridge `wkeTaylorTerm (φ (p*δ)) δ p n t = taylorU hd φ δ p n t`, by induction plus a
    reindexing of the antidiagonals. Then B1.5 `wkeTaylor` follows from `wketaylor`, `wketaylor2_*` and
    `taylorbound`, with C₁ = 2ρ(d, 𝔆-bound).
  - B1.5's integrability conjunct (0) is automatic for `taylorU`: the integrand is (t′−p)^m times a constant.
- **S5. Measurability of `smoothDataSet`.**
  - Wave B's `IsSymmetricEvent` (Q5) needs `MeasurableSet A`, here A = `smoothDataSet L α T` in the product σ-algebra.
    No such lemma is landed.
  - Wave A's `main` asserts `MeasurableSet (solvableEvent …)` as a conclusion, proved by the selection device.
  - **Recommendation.** Land `measurableSet_smoothDataSet` (the same Borel-selection argument, on the coefficient
    side) before B1.1 is attempted. Otherwise B1.1's existential event cannot be the solvability event.
- **S6. `TimeForest` and the Wave B trees.**
  - `Analysis/TimeForest` is a local carrier: parent-indexed, with branching vertices only.
  - The Wave B kernels integrate over `GBranch` with `kDomain`.
  - **Recommendation.** COMB-CORE should provide the map from a `TTree`/garden to a `TimeForest`, with
    `kDomain`/`treeTimeDomain` matched to `timeDomain t 0`. The heap-volume and oscillation lemmas then apply.
  - Watch the strict versus non-strict inequalities and the layer constraints 𝔏 < t < 𝔏+1. These are an extra box
    intersection that `TimeForest` does not model.
- **S7. wkelwp conjunct 3.** It is not landed (F32). `wkelwp_conj12` plus `tauMax` is everything needed for
  conjuncts 1–2. Conjunct 3 needs the GIT20 Z_s theory (WKEL2 in progress; none of its milestones is claimed).
- **S8. TASK6 scope.** There is no `Foundations/Probability/**`. If a probability packet was expected (for example
  the Gaussian data measurability or `stdComplexGaussian` tails), it has not landed.

## Notes for consumers

- **B1.4 (`nlsAkBridge`):**
  - `IsSmoothNLSSolution.isAkSolution` gives the forward direction in the class.
  - `norm_reducedCoeff` gives |a_k(t)| = |û(δT_kin t, k)|.
  - `IsAkSolution.eq_of_eq` gives uniqueness.
  - The backward direction is still open.
- **B1.1 (`propansatz`), item (1):**
  - mass conservation (`AkMass`) gives the integrability of all finite products;
  - `cumulant_prod` (unnormalized μ) supplies the cumulant algebra;
  - `Cumulant/Symmetry` supplies gauge and translation vanishing once `Measurable` is available.
- **Wave A `main`:** `wkelwp_conj12` discharges the frozen conjuncts 1–2 verbatim.

## Probes

`scratch/Infra2-chi0-bridge.lean` (untracked, sha256 `0aba172f…2886e`). It imports
`WaveTurbulence.Foundations.Fourier.Chi0`, compiled with `lake env lean -o`, and proves:

```lean
theorem fourier_chi0_eq_abs (x : ℝ) :
    WaveTurbulence.Fourier.chi0 x = Real.smoothTransition (2 - 2 * |x|)
```

Axioms: `[propext, Classical.choice, Quot.sound]`. This is the S1 bridge.

The F44 check is `grep -rn "ContDiff ℝ ⊤\|ContDiffOn ℝ ⊤\|ContDiffAt ℝ ⊤\|ContDiff 𝕜 ⊤\|ContDiffWithinAt ℝ ⊤\|ContDiff ℝ ω\|AnalyticOn"`
over `WaveTurbulence/`, which finds no match.
