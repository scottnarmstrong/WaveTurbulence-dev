# PL1 working handoff — carrier interface

Status: **in progress**, 2026-11-04. This is the requested C2 instantiation interface, not a `READY pl1-core` claim. The couple analytic core, including canonical source agreement, is complete. Stage 1 still needs the exact tree phase/source identity and final interpolation; Stages 2–3 remain open.

## Structural data

All declarations below are in `WaveTurbulence.Incoh`. No structure has an estimate or a conclusion-shaped field.

| declaration | fields / data | meaning for C2 |
|---|---|---|
| `LinkParameters d` (`LinkFactor.lean`) | `leftCenter`, `rightCenter`, `leftShift`, `rightShift : Mom d` | The two cutoff centers and two linear Fourier frequencies after localization. These are universally quantified analytic parameters, not garden assumptions. |
| `LayerLink d` (`LayerLink.lean`) | extends `LinkParameters d`; `leftLayer`, `rightLayer : ℤ`; `orientation : ℤˣ` | The integer layers of the two linked branching nodes and the chosen node's sign. |
| `Q : Fin n → LayerLink d` | an actual finite link family | C2 enumerates the code's links. Each link has two time coordinates `Fin 2`. |
| `RootCoordinates n r` (`RootCoordinates.lean`) | `restCount : ℕ`; `permutation : Fin (n * 2) ≃ (Fin r ⊕ Fin restCount)` | A finite permutation selecting the external/frozen vertex times. `r` defaults to `2` for the two couple roots. Boundary marginals may select more vertices. The measurable equivalence and its measure preservation are proved, not fields. |
| `I : Set (Fin n → Fin 2 → ℝ)` | `MeasurableSet I`; `I ⊆ Set.univ.pi (fun i => linkBox (Q i))` | The actual internal time-order domain. These are structural measurability and containment obligations, not analytic bounds. |

`linkBox Q = Icc ![Q.leftLayer,Q.rightLayer] ![Q.leftLayer+1,Q.rightLayer+1]`, with integer layers cast to reals. `LayerLink.IsIncoherent Q` is the literal inequality of those two integers. `incoherenceCount Q` is the cardinality of the filtered finite family; it is not an assumed kernel bound.

`RootCoordinates.rootVertex` and `rootLinks` compute the selected vertices and the links they touch from `permutation`. Their cardinality bound, root/internal unit-box decomposition, untouched-link independence and marginal bounds are proved. `RootCoordinates.linkDensity` is the actual integral of `normalizedLinkIntegrand` over the nonselected coordinates.

The layer-range premise is `∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D`. This bounds the actual frequency window. The analytic standing parameters are `d ≥ 3`, `0 < γ < 1`, positive small `η`, `0 < δ ≤ 1`, and a positive layer range `D`. The incoherence count is computed from `Q`; results needing nontrivial incoherence explicitly require `1 ≤ incoherenceCount Q`.

## Literal link and F62

`linkEpsilon x y = 1 - 1_{x=0} - 1_{y=0}` remains the **single-branching-node** coefficient. It takes values `1,0,-1`, matching C2's `epsXY_eq_cases`.

**The actual per-link coefficient is its square**, to match C2 `epsDec_eq_prod_links`: `linkWickFactor x y = (linkEpsilon x y)^2`, with values `1,0,1`. `linkAmplitude` uses this squared factor. The localized lattice factor is the literal sum of `linkAmplitude * WeylSums.e linkPhase` over the pair lattice. Its time frequency is `orientation * δ * L^(2γ) * (t_left-t_right)`.

F62 is the source defect at TARGET `(incohproof10)`: the product over all branching nodes contributes both equal endpoint coefficients of every link. The squared factor is required for exact instantiation. Mask removal uses the two coordinate axes **with the origin omitted**, retaining an `O(L^d)` correction. The F62 correction has been rebuilt through `CoupleExtension.lean` (`d240a9b`, corrected mask committed in `7943955`). The punctured-axis proof retains the same explicit `2(5L)^d` error bound.

The source normalization is literal: `(δ / (2 * L^(d-γ)))^(2n)`. A global unit sign/phase of the garden is not stored in these analytic data and may multiply the kernel without changing the norm.

## C2 consumption

The reported C2 packet is `/home/scott/wt-scratch/links`, with `src/LinksDraft/Incoh1.lean` and `HANDOFF.md`. Its relevant outputs are `incoh_relation`, `incoh_unimodular`, `linkCoords_surjective`, `node_linear`, `decEquiv`, and `epsDec_eq_prod_links`; tree link/layer results are available separately. They are not imported here from scratch, and no B2 draft or characterization stub is an analytic dependency.

The coupling from C2 to this analytic core needs:

1. enumerate the actual links and choose their endpoint time-coordinate ordering;
2. fill the two integer layers and the unit orientation;
3. identify C2's single-node epsilon with `linkEpsilon` and its paired product with `linkWickFactor`;
4. select root/boundary vertex coordinates by a finite permutation;
5. supply the actual measurable internal time domain and its unit-box containment.

The cutoff centers/Fourier shifts arise in PL1 localization and remain free in the core estimates. The leaf-function product, unimodular coordinate change and Fourier localization carrier for Stage 2 are not yet added here; the landed C2 scratch results are the intended inputs. No tree analogue of the couple unimodular theorem is assumed.

## Proven milestones and checks

Before F62, focused gated builds passed for the literal short- and long-time bounds, product decay, exact coupling cancellation, actual selected-density bounds, and the common root-density endpoints. Milestones include `ad41e46`, `ac012d7`, `197ab9a`, `a371bbf`, and `46898cd`. `nice -n 5 lake build WaveTurbulence.Foundations.Incoh.<Module>` was used, one targeted build at a time through `wt-throttled`; no whole-library or Mathlib rebuild was requested.

The scratch audit `/home/scott/wt-scratch/wke-l2s/pl1/AxiomsFrequency.lean` printed exactly `[propext, Classical.choice, Quot.sound]` for `exists_shortTime_box_bounds`, `exists_longTime_box_bounds`, `mixedFourierNorm00_interpolate`, and `eLpNorm_le_of_one_and_pointwise`. This audit will be repeated after the F62 rebuild and for the final assembled results.

The corrected-mask `RootDensityLp.lean` and `CoupleExtension.lean` now build, proving the physical interpolation and positive couple Fourier estimate. `/home/scott/wt-scratch/wke-l2s/pl1/AxiomsSquared.lean` rechecked the corrected mask, both frequency box bounds, root endpoints, physical Lp bound, couple Fourier bound, and mixed interpolation: every result uses exactly `[propext, Classical.choice, Quot.sound]`. Commit `88f1def` proves `cumulativeKernel_eq_setIntegral`, `cumulativeKernel_eq_localBoxIntegral`, `coupleExtension_agrees` on the full root box, and `exists_cumulativeKernel_timeRestriction_bound` with exponent `γ₁−100dη`. The focused `CoupleExtensionAgreement` build passed. The scratch audit `AxiomsCouple.lean` checked all four declarations: each uses exactly `[propext, Classical.choice, Quot.sound]`. The full core theorem, tree Fourier/derivative assembly, localization, and abstract `proplayer1` are not yet claimed proved. No `READY` milestone is claimed by this working handoff.


## Tree boundary milestone

Commits `d8b519c` and `cc3405d` prove the phase estimates for **literal rectangular time fibers**, with arbitrary momentum-dependent endpoints and phases. The smoothing windows have variation at most two per coordinate and converge pointwise to half-open interval indicators. Their mixed derivative mass is at most four. Bounded convergence for ordered integrals, Fourier dominated convergence, and mixed-norm Fatou pass the landed smooth phase lemma to the hard boundaries. The momentum supremum remains inside the frequency integral throughout. Both focused `SmoothRectanglePhase` and `RectanglePhaseBound` builds passed. `AxiomsRectangle.lean` audited the six main smoothing/limit/phase results: all use exactly `[propext, Classical.choice, Quot.sound]`.

This is a rigorous reading of the terse derivative step in TARGET `(incohproof27)`: hard interval indicators are handled by uniformly bounded smooth approximations, rather than asserted to be smooth. The remaining tasks include mixing these rectangular phase kernels against the actual internal link amplitudes, accounting for the selected-link expansion, proving source agreement for both tree cases and layer endpoints, and the negative/positive norm interpolation. No tree-core completion is claimed yet.


## Causal tree kernels with every selected layer bound

The current direct route uses `causalBoxKernel` (`CausalBoxKernel.lean`), with two selected clocks at `m=0` or four at `m=2`. The amplitude contains the literal half-open interval indicator for **every** selected clock, the fixed smooth cutoff, a balanced phase tuple, and the strict causal ordering of those clocks. This also handles reversed external clocks: `CausalOrderingZero.lean` proves the kernel is zero there.

`CausalBoxData m` (`CausalBoxData.lean`) is the measurable subtype of three real vectors of length `m+2`:

| field / invariant | exact content | C2 obligation |
|---|---|---|
| `phase` | `Fin (m+2) → ℝ` | Actual selected-link temporal frequencies, with signs determined by the endpoint ordering. |
| `phase_sum` | `∑ j, phase j = 0` | Each completely selected link contributes its positive and negative frequency once. |
| `lower`, `upper` | `Fin (m+2) → ℝ` | Actual interval bounds after fixing the remaining clocks, including all selected vertex layer boxes. |
| `lower_le_upper` | coordinatewise `lower ≤ upper` | A zero-width interval represents an empty fiber. |

These are the only data/invariants of this carrier. There are no analytic norm or decay fields. `universalCausalBoxKernel` includes all such parameters; it is jointly measurable and has one common integrable time dominator. The mixed norm theorem now allows **any** vector parameter carrier, retaining its supremum inside the frequency integral.

Commit `8f0241a` proves the direct quarter-regularity estimate by reusing the landed eight-moment and joint-frequency estimates. A common clock shift differentiates each localized interval factor only once; the balanced phase and smooth causal-ordering weight contribute zero. The uniformly bounded first variation passes to the hard indicators by dominated convergence and Fatou. This keeps the printed `1/4` regularity and all selected clock bounds. The separate fixed-time trace results in `7c1af3b` are also valid, but are not needed to discard any layer constraint in this direct route.

Focused builds passed for `CausalBoxBound`, `RootCausalSource`, and the supporting moment/measurability modules. `AxiomsCausalBoxes.lean` audited the first-variation, common-shift, smooth and hard causal box bounds, both trace bounds and the ordered-domain integral identity; all eight use exactly `[propext, Classical.choice, Quot.sound]`. `AxiomsCausal.lean` audited the actual negative tree norm and source agreement, with the same three axioms. The generic parameter-carrier extension has subsequently rebuilt through `CausalKernelMeasurable`.

The remaining structural bridge must identify the actual tree time domain, after selecting the complete root link(s), with its remaining-clock domain and selected-clock rectangular fibers plus causal ordering. The phase expansion and the actual mixture amplitude mass are already proved; their exact integration identity with that source domain, the final common-extension interpolation, and Stages 2–3 remain in progress. The strict/half-open conventions will be related to any closed source endpoints by the corresponding null-boundary identity; no change in the source integral is intended. No `READY pl1-core` claim is made yet.

## Exact phase and tree-fiber interfaces

`SelectedLinkClocks n r` adds only `coordinates : RootCoordinates n r`, a finite equivalence
`pairing : Fin r ≃ ({i // i ∈ coordinates.rootLinks} × Fin 2)`, and the equality identifying
`coordinates.rootVertex` with that pair. Complete selection proves `2 * card(rootLinks) = r`
(up to commutation), at most two selected links for `r ≤ 4`, and zero total signed temporal
frequency. `SelectedClockPhase` identifies its linear phase with the literal product of link
exponentials, in reconstructed original vertex coordinates.

`TreeClockFibers m Q` contains:

- `selection : SelectedLinkClocks n (m+2)`;
- `remainingDomain` in the nonselected clock coordinates, with its measurability;
- measurable `lower` and `upper` vectors depending on the remaining clocks, with `lower ≤ upper`;
- containment of the remaining domain in `restBox Q`, and containment of each half-open interval
  fiber in `rootBox Q`.

Its `timeDomain` is defined from these data: remaining-domain membership, all selected intervals,
and strict adjacent descendant ordering. Measurability and containment in the original full link
box are theorems. The two source cases use `m=0` and `m=2`. These fields contain no analytic bounds.
The actual tree instantiation must identify this defined domain with the source time domain up to
null clock boundaries. This identification is not claimed by the abstract carrier alone.

`PhaseCoordinateIntegral` recovers each selected lattice sum and their finite product by integrating
against the literal counting/Dirac measures. `PhaseTimeSplit` proves that the actual product mixture
measure separates into phase arrays and Lebesgue clock arrays, and proves Fubini with the phases
integrated first. Focused builds passed for these modules, `SelectedLinkClocks`,
`SelectedClockPhase`, and `TreeClockFibers`. The common-extension identity and final tree
interpolation are still in progress.

`ExpandedLinkIntegral.integral_source_eq_expandedMixture` now proves the exact identity between
the literal source product integral on any measurable domain inside the layer box and the actual
selected-phase mixture. Temporal phase restoration is proved integrable, not assumed.
`TreeFiberParameters.mixtureParameters` constructs the actual balanced phases and interval endpoints
from `TreeClockFibers`; its measurability is proved. The probes `AxiomsPhaseRecovery.lean` and
`AxiomsExpanded.lean` (scratch `pl1/`, logs `axioms-phase-recovery.log`, `axioms-expanded.log`)
check twelve recovery, finite-pair, measure-split and fiber-interface results: all use exactly
`[propext, Classical.choice, Quot.sound]`. Focused builds passed for all modules named above.

`CausalAmplitudeSource` and `CausalKernelSource` prove exact hard-amplitude and forward kernel
source-domain formulas. `SelectedClockDomain.mem_causalDomain_equiv_symm` identifies the full
source causal domain with the remaining-clock domain and selected ordered fiber, assuming only
that the external root/lone-parent vertices are the first/last selected vertices.
`SelectedMixtureFactorization` proves the literal amplitude factorization and that integration of
the dummy selected clocks contributes precisely one. `SelectedMixtureIntegral`,
`SelectedClockIntegral`, and `SelectedPhaseMixture` prove the corresponding Fubini identities for
arbitrary integrable clock amplitudes; their integrability premises are typing obligations on
generic integral identities, not substitute decay estimates.

Focused builds passed for all these modules. `AxiomsSelectedSource.lean` audited the amplitude,
kernel and causal-domain identities, the selected factorization, unit dummy integral and full
phase-mixture collapse: all six use exactly `[propext, Classical.choice, Quot.sound]`.
The assembled common-extension and interpolation theorem is still pending.

## Global common tree extension proved

`treeCausalExtension_eq_phaseKernel` (`TreeCommonExtension.lean`) now proves global equality
between the literal root-marginal causal extension and the normalized causal phase mixture.
It holds on all external clock pairs; both sides are proved zero on reversed pairs from the
actual strict descendant order. Its hypotheses are the structural fiber carrier, identification
of root/lone-parent with first/last selected vertices, and cutoffs equal to one on their layer boxes.
There are no assumed norm bounds or representation identities.

`TreeSourcePhaseFibers` proves the full literal source integral's phase/remaining-clock formula.
`TreeCausalMixtureSource` matches the actual causal mixture to it; `TreeNormalizedMixtureSource`
retains the exact source coupling. All focused builds through `TreeCommonExtension` passed.
`AxiomsCommonExtension.lean` audited the full source phase formula, unnormalized and normalized
source identities, reverse support and global extension equality: all five use exactly
`[propext, Classical.choice, Quot.sound]`. The final norm interpolation and Stages 2–3 are pending.

## Stage 1 analytic core complete

`exists_treeCausalExtension_decay` (`TreeExtensionDecay.lean`) proves TARGET (incohproof24)
for the actual common extension, with exponent `γ₁−100dη`, a dimensional base constant chosen
before every analytic parameter, and a threshold chosen before `n`, `g`, all link data and time
domains. It covers both `m=0` and `m=2` source cases (the theorem allows `m≤2`), arbitrary
momentum-dependent link parameters and fiber endpoints, and `g≥1`, `0<η≤1/100`. The selected
link set is structurally fixed across momentum. All source cutoffs are equal to one on the
appropriate selected/root layer boxes. This is the literal source extension; no endpoint bound
is a field of the carrier.

The common negative endpoint retains bulk loss `2ηg`; the quarter endpoint pays only `L^{2d}`.
The proved interpolation helper costs `16dη`, and one cutoff-prefactor absorption costs `ηg`.
These fit the printed `100dηg` budget. The couple theorem remains
`exists_cumulativeKernel_timeRestriction_bound` on the literal root box.

Exact check: `nice -n 5 lake build WaveTurbulence.Foundations.Incoh.TreeExtensionDecay`:
`Build completed successfully (9407 jobs)`. `AxiomsTreeCore.lean` audited the actual tree quarter
bound, conditional interpolation inequality, final source tree decay, and couple restriction
bound. Every result printed exactly `[propext, Classical.choice, Quot.sound]`. No whole-library
build, dependency rebuild, or budget override was used.

Stage 1 status: READY pl1-core. Stages 2–3 remain active. C2 still supplies the code-level
instantiation of the listed finite structural fields and the null-boundary identification of
its closed source time conventions. The only reported source erratum remains F62; the hard
indicator derivative step was resolved by the documented uniform first-variation argument.
