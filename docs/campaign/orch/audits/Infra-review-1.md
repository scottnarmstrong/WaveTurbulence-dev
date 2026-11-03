# Infra review 1: statement review of landed Foundations code (Task 4c)

Auditor: `wt-orch`. Date: 2026-11-03. Tree: `w/orch` after `git merge main` (`0956996`), `WaveTurbulence/Foundations/**`
(≈12.3k lines).

**Scope.** I reviewed statements only, not proofs. For each module's main results I compared the Lean statement with
the source formula cited in its docstring, looking for:

- hypotheses that cannot be discharged at the use site;
- junk values (`tsum`, integrals, division);
- missing uniformity of constants;
- wrong normalizations.

**Coverage.** All public theorems and definitions in the priority directories (Cumulant, Gaussian/Isserlis*, Torus,
NLS, WKE). The headline results only in Analysis, Counting, WeylSums, NumberTheory and Gaussian/Hypercontractivity.

**Verdict.**

- **No wrong statement found.** All checked normalizations agree with the sources: TARGET (1.2), L285, (akeqn2),
  (defcoef0), (res), (COL), (schappend5–7); DH21 Lemma A.2 and Lemma A.3.
- **One REQUIRED item, for the a-system definition** (N1): `IsAkSolution` has no solution class, so its `tsum` can
  silently take a junk value.
- **Three SHOULD items:**
  - C1: measurability hypotheses are stronger than what B1.1 supplies;
  - W1: a mislabelled docstring;
  - W2: the WKE packet should record why the 3^s tame constant suffices, and F10's wording should be relaxed.
- **Not yet landed, so not reviewed:** `propertycm` (Leonov–Shiryaev, with the F30 ranges), the NLS↔a-system
  reduction, and GIT20's Z_s trilinear estimate.

## Table

| Module | Declaration(s) | Verdict | Issue | Fix |
|---|---|---|---|---|
| Cumulant/Basic | `cumulant` | OK | Literal (eqncm) against an unnormalized μ, so `μ = P.restrict F` gives TARGET's "assuming F" = E[1_F ·] (L576), consistent with Wave A. 𝕂(∅) = 1 is disclosed. | — |
| Cumulant/Basic | `cumulant_mul`, `cumulant_singleton` | OK | — | — |
| Cumulant/Inversion | `integral_prod_eq_sum_cumulant` (eqncm2, L573) | OK | Purely algebraic in the totalized moments, so no integrability is needed and it is junk-consistent (non-integrable moments are 0 on both sides). Nonempty s, correctly. | — |
| Cumulant/Symmetry | `cumulant_congr_map`, `*_eq_zero_of_map_mul`, `*_gauge_invariant`, `*_translation_invariant` (gaugeinv, L567–L576) | OK, with friction C1 | Charges: gauge q_j = ζ_j; translation q_j = −2πζ_jk_j (phase `e^{−2πik·x₀}`), so Σq ≠ 0 ⟺ Σζ_jk_j ≠ 0. For cumulants, every partition has a block of nonzero charge, so the conclusion is right. **C1:** the hypotheses require `Measurable (X j)` for every j. At the use site, X_j = a_{k_j}(t)^{ζ_j} on `P.restrict F_p`, and B1.1 asserts only *a.e.-strong measurability* of ω ↦ a ω t n for `P.restrict (F p)`. | Provide `AEMeasurable` versions w.r.t. μ, with the law equality stated for `μ.map` of an a.e.-measurable family. Alternatively, make B1.1 assert `Measurable` (it can, by choosing a measurable selection). |
| Gaussian/ComplexGaussian | `integral_monomial_stdComplexGaussian` (E z^a z̄^b = a!·δ_{ab}), `integral_norm_sq_…` (= 1), `charFunDual_…` (exp(−(L1² + Li²)/4)), `map_rotation_…`, `hasLaw_…_eval`, `iIndepFun_…_eval` | OK | The normalization matches DH21 L297 (𝔼\|g\|² = 1) and the Wave A `stdComplexGaussian` (Re, Im ∼ N(0,½)). The characteristic-function variance ½ checks. | — |
| Gaussian/Isserlis | `integral_signed_prod_eq_sum_pairings` (DH21 Lemma A.2) | OK | Sum over bijections from + to − positions (empty when the counts differ, giving 0), with weight ∏1_{k=k′}. Repeated indices are allowed. The hypotheses (`iIndepFun`, `HasLaw`) follow from the Wave A hypotheses: `Measurable` + map gives `HasLaw`. | — |
| Gaussian/IsserlisMoments, …Pairings, …Partitions, …Polynomial | the factorial product form; the pairing ↔ opposite-sign partition equivalence; the polynomial-moment recursion | OK | The bijection with `Finpartition`s into opposite-sign pairs matches DH21's pairing language. | — |
| Gaussian/Hypercontractivity, LargeDeviation (off-route, F34) | `integral_norm_rpow_multiGauss_le` (DH21 (A.4)), the exponential tail | OK | E\|X\|^q ≤ (q−1)^{nq/2}(E\|X\|²)^{q/2} for degree-n Gaussian polynomials, repeated indices included, as DH21 Lemma A.3 needs. | — |
| Torus/Basic, Inversion, Series | `torusFourierCoeff_eq_mFourierCoeff`, `hasSum_torusFourier_series`, `torusFourierCoeff_torusChar` (L^{d/2}δ), `hasSum_sq_torusFourierCoeff` (Parseval), `eq_of_torusFourierCoeff_eq`, `torusFourierCoeff_torusSeries`, `contDiff_torusSeries` | OK | Normalization (1.2): coefficient L^{−d/2}∫ f·e^{−2πik·x}; series L^{−d/2}Σ f̂ e^{2πik·x}; Parseval with no extra factor; characters e^{+2πi(n/L)·x}. All consistent with the frozen `torusFourierCoeff`. `IsRapidDecay` uses the sup norm on ℤ^d, which is harmless. | — |
| Torus/Derivative | `torusFourierCoeff_partialDeriv` (2πi n_j/L), `torusFourierCoeff_normLaplacian` (−2π\|n/L\|²) | OK | (2π)^{−1}Σ(2πi n_j/L)² = −2π\|k\|², matching TARGET L285 and the frozen `normLaplacian`. | — |
| Torus/Product | `hasSum_torusFourierCoeff_mul` (L^{−d/2} convolution), `…_conj` (conj ĝ(−n)), `…_mul_conj_mul(_resonant)` (L^{−d}Σ_{n₁−n₂+n₃=n}) | OK | The cubic convolution has the right L^{−d} factor and parametrization. | — |
| Torus/TimeDerivative | `hasDerivWithinAt_torusFourierCoeff`, `IsSmoothNLSSolution.hasDerivWithinAt_torusFourierCoeff` | OK | One-sided within `Icc 0 T`, matching the frozen `IsSmoothNLSSolution`. For T = 0 the set is a singleton and the statement is degenerate but true; no consumer relies on it. | — |
| NLS/FourierEquation | `cubicConv`, `IsSmoothNLSSolution.derivWithin_eq`, `…hasDerivWithinAt_torusFourierCoeff_eq`: ∂ₜû = i(2π\|k\|²û + α·cubicConv(û)) | OK | Derived from `(i∂ₜ−Δ)u + α\|u\|²u = 0` with Δ̂ = −2π\|k\|². Correct sign. **Cross-check:** substituting v = e^{−2iαMt}u and a_k(t) = e^{−πiδL^{2γ}\|k\|²t}·v̂(δT_kin t, k) reproduces exactly `aNonlin` with ζ = +1, i.e. prefactor δT_kin·α·L^{−d} = δ/(2L^{d−γ}) and phase e^{πiδL^{2γ}Ωt}. The landed normalizations are therefore mutually consistent with (akeqn2). | — |
| NLS/AkSystem | `epsCoef` (defcoef0), `resonance` (res), `resonance_eq_inner` (Ω = 2⟨k₁−k, k−k₃⟩), `aNonlin` (akeqn2), `wickConv`, `epsCoef_add_indicators`, `cubicConv_sub_two_mul_eq_wickConv` | OK | ε: +1 if n₂ ∉ {n₁, n₃}, −1 if all three are equal, 0 otherwise. The indicator identity ε + 1_{n₂=n₁} + 1_{n₁=n} = 1 (with n₃ = n−n₁+n₂) is correct and gives the Wick identity with M = L^{−d}Σ\|b\|² (= ⨍\|v\|² by Parseval). Prefactor `L^((d:ℝ)−γ)` (rpow) and the factor (iζ) are as in (akeqn2). | — |
| NLS/AkSystem | `IsAkSolution` | **REQUIRED (N1)** | **Junk hazard.** `aNonlin` is a `tsum` over the resonant set and equals 0 when the triple sum is not summable. `IsAkSolution` imposes no solution class. For example, if the data c are such that the sums diverge, then a ≡ c "solves" with zero right-hand side. So uniqueness, bridge and measurability statements built on `IsAkSolution` alone are unsound. B1.1 (D4) already states uniqueness "in the class of §2.3.2 (Q16)". | Put the class into the definition: `∃ Λ > d, sup_{t∈[0,𝔇]} sup_n ⟨n⟩_L^Λ ‖a t n‖ < ∞` (Z^Λ([0,𝔇]); this also makes the sums absolutely summable), or add a separate `IsAkSolutionIn Λ` and use only that in uniqueness and bridge statements. Make sure the Wave B §2.3.2 frozen definition and this Foundations definition are the same object, or prove an equivalence lemma. |
| NLS/Energy | `IsSmoothNLSSolution.integral_normSq_eq` (mass, L540/L818), `…hasSum_normSq_torusFourierCoeff`, `…norm_torusFourierCoeff_sq_le` (the L818–L820 bound), `IsSmoothNLSSolution.eq_of_eq` (uniqueness), `eq_of_mem_solvableEvent` (selection independence, F8) | OK | They need `0 < L` and `t ∈ Icc 0 T`, which hold at the use site (L ≥ L₀ > 0). Uniqueness is for smooth periodic solutions on `[0,T]`, exactly what the frozen `main`'s ∀U device needs. | — |
| WKE/DeltaReading, Hyperplane, CollisionOp | `deltaInt`, `sliceEquiv` (measure-preserving), `integral_eq_integral_slice`, `hypConst`, `integrable_collisionOp_outer` and `…_perp` (no junk at either level), `collisionOp_eq_sum` (𝒦 = 𝒦₀ − 𝒦₁ + 𝒦₂ − 𝒦₃, L2491) | OK | The no-junk lemmas need `CollisionInputs` (continuous, decay N > 2d) and d ≥ 2, which Schwartz inputs supply (`collisionInputs_of_schwartz`). The `j = 0…3` kernels match (schappend1–4) in the variables of (schappend5). | — |
| WKE/Characterization | `tendsto_mollified_collisionOp_k`, `…_schwartz` | OK, and important | In the (COL) variables, with k₂ = k₁+k₃−k, ε⁻¹ψ(Ω/ε) → `collisionOp`, with Ω = \|k₁\|²−\|k₂\|²+\|k₃\|²−\|k\|² *unscaled*. This independently confirms the Wave A reading of the energy delta and its (2\|ℓ₁\|)⁻¹ factor (Task 1 §1a). The mollifier class (continuous, compactly supported, ∫ = 1, no sign or evenness) is the general one. | — |
| WKE/Multilinear | `collisionTerm_translate`, `collisionTerm_sub_sub_sub` (telescoping), `weight_collisionTerm_zero` (schappend7) | OK | (schappend7) signs (+,−,+) for 𝒦₀ match L2509–L2511. | — |
| WKE/Leibniz | `hasFDerivAt_collisionTerm` (schappend6), `schwartz_taylor`, `abs_collisionTerm_remainder_le` | OK | — | — |
| WKE/Trilinear | `abs_collisionTerm_le_tame`, `abs_collisionOp_le_tame`: (1+\|k\|)^s\|𝒦\| ≤ C(d,s₀)·3^s·(H₁L₂L₃ + L₁H₂L₃ + L₁L₂H₃), s₀ > 2d; `abs_collisionTerm_le` (L^∞_s, s > 2d) | OK; SHOULD (W1, W2) | **W1:** the docstring calls this the "weighted-L^∞ form of TARGET (schappend8)". (schappend8) is the **L²-based Z_s** estimate (GIT20 Lemmas 4.1–4.3, Remark 2.6, s > d/2−1), which route R10 / Wave A `wkelwp` (blow-up in Z_s) needs and which is still a gap (F32). This weighted-L^∞ estimate (s₀ > 2d) is the analogue of GIT20's `PropLinfty` and does not replace it. **W2:** the constant 3^s multiplies the high-norm terms. That does *not* break (taylorbound) with a base C₁ independent of 𝔇 (B1.5): the high norm enters each term linearly, so the Taylor coefficients satisfy H_n ≤ (c(s)/n)Σ_{m<n}(n−m)·C_L^{n−1−m}·H_m, whose generating function is exp(c z/(1−z)) times the low-norm geometric series. So H_n ≤ C₂(s,ε)·(C_L(1+ε))^n, with the base set by the 𝔖^{40d,40d} norms and the s-dependence absorbed into C₂. Conversely, F10/`GAP.wkeTame`'s requirement "constant independent of Λ in the linear part" is stronger than needed and probably false for convolution-type weights: (1+\|k\|)^s against (1+\|kᵢ\|)^s loses c^s in general. | W1: relabel as "GIT20 PropLinfty analogue (weighted L^∞_s, s₀ > 2d)" and keep `GIT.trilinear` (Z_s) as a separate open node. W2: relax the wording of F10 / `GAP.wkeTame` to "tame (linear in the high norm), with an arbitrary constant C(Λ)". Record the sub-exponential-growth argument as the route to (taylorbound). The k-derivative part of 𝔖^{Λ,Λ} still needs a Moser-type interpolation, and the same argument applies. |
| Analysis/IntervalSobolev, CubeSobolev, WeightedSobolev | `norm_le_interval_sobolev_L2` (sobolev, L2314: constant 1 on unit intervals), the lattice/ℓ² version, `enorm_le_cubeSobolevL1` (DH21 (10.5)), `norm_le_radial_weighted_sobolev` (incohproof4, L998: constant (2π)^n) | OK | Explicit constants, uniform in the function and the index set. | — |
| Counting/ExponentAudit | the 2/3-exponent audit lemmas (F3) | OK | These are the arithmetic facts behind F3 (revised). They are consistent with my GRAPH-topology I12. | — |
| WeylSums, NumberTheory (Dirichlet, Gauss-sum differencing, Kusmin–Landau, van der Corput A-process `weyl_vdC_expSum`, sawtooth (7.2)) | building blocks of NT1 / NT-EXPSUM | OK (light) | Standard statements with explicit constants. `not_gaussSum_bound_log_one` correctly records that DH23's "K log K" form needs K ≥ 2. | — |

## Notes for consumers and packets

- **(N1 follow-up)** The NLS↔a-system bridge (B1.4 `nlsAkBridge`) and B1.1's uniqueness clause must quantify over the
  *classed* solution notion. If the Foundations name `IsAkSolution` stays unclassed, rename it (e.g.
  `IsAkSolutionRaw`) so that no frozen statement picks it up by accident.
- **(C1 follow-up)** The cumulant-symmetry lemmas will be consumed by `T.gaugeinv` (B3). Either their hypotheses are
  weakened to a.e.-measurability, or B1.1 item 1 strengthens "a.e.-strongly measurable" to `Measurable`. The second is
  cheap and avoids duplicate APIs.
- `propertycm` with the F30 range condition, the NLS reduction, and GIT20's Z_s estimate are not yet landed. I will
  review them when they land.
