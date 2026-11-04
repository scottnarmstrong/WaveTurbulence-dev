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

## Steps 1–2: integer coordinates, source input bounds, finite localization

`IntegerLeafCoordinates n` is a local interface to C2 `incoh_unimodular`. Its fields are the
`(2n+1)×(2n+1)` integer matrices `forward` and `backward`, their two inverse identities,
`root_column : forward i 0 = 1`, and membership of the inverse root row in `{-1,0,1}`.
These are finite coordinate data/certificates, not analytic estimates. C2 supplies them after
enumerating plus leaves and placing its `none` root coordinate at `0`. `sigma` is defined to
be the backward root row. Its sum is proved to be `1`. `LeafCoordinateRelation` proves root
recovery, the translated leaf relation, the root-plus-link formula, and exact scalar/vector
integer lattice equivalences and summation reindexing. `abs_det_blockMatrix` proves volume
preservation in all spatial dimensions from the actual inverse matrices.

`LocalizationTree` is an auxiliary ternary shape with computed `order`, `nodes`, `leaves` and
`branching`; `IsDecoration` is the literal alternating parent/three-child relation. It has no
bound fields. `TreeLocalization.exists_finite_localization` proves TARGET treelemma (2), using
C2's statement-independent bottom-up finite-ball-cover proof. C2 maps its source shape to this
auxiliary shape; no B1/B2 scratch module is imported.

`LeafProductFourier` and `LeafFourierRepresentation` prove the Fourier-L¹ bound and exact
pointwise Fourier inversion of the literal product in these coordinates, reusing the landed
Fourier product theorem. `SpatialInputBounds` and `SpatialDerivativeIntegrals` derive all
coordinate/operator derivative and derivative-integral bounds from the actual landed
`Fourier.spatialNorm`. `LeafSpatialFourierBound.fourierL1_momentumLeafProduct_le` therefore
assumes only those source spatial norms (finite smoothness order `K≥d+1`, decay order `M>d`).
It does not assume a Fourier norm or extra smoothness as a carrier field.

Focused builds passed for all modules above. Scratch `AxiomsLeafLocalization.lean` and
`AxiomsSpatialLeaf.lean`, logs `axioms-leaf-localization.log` and `axioms-spatial-leaf.log`,
audited twelve determinant/relation/lattice/Fourier/localization/spatial-input results.
Every result printed exactly `[propext, Classical.choice, Quot.sound]`.

Still pending: the smooth cell/center decomposition with summable coefficients, its insertion
into the actual source lattice/time kernel, derivative/weight assembly, and abstract Prop 5.1.

## Smooth localization coefficients proved

`SmoothLeafCells` uses the landed `ApproxNT.thetaMom` partition literally. `hasSum_leafCell`
and `tsum_leafCell` recover the input pointwise; each cell retains the finite source smoothness
and has actual compact support. No hard momentum indicator is used in Fourier inversion.
`LeafCellProfile` proves the translated support and uniform derivative-integral bound.
`SpatialCenterDecay` transfers the literal source Japanese-bracket decay to each cell center.
The support-local extension `derivativeL1Sum_mul_le_on_support` of the landed product estimate
preserves that decay. `LeafCellDerivativeDecay` and `LeafCellFourierDecay` prove the actual cell
Sobolev and Fourier-L¹ bounds, with explicit constants independent of the center.

`CellCenterSummability` proves summability of `1 / ⟨c⟩^M` for `M≥2d` from the landed lattice
weight estimate. In particular `tsum_timeFourierNorm_leafCell_lt_top` proves a finite total
Fourier coefficient over all cells directly from the source spatial norm, without assuming a
Fourier norm bound. Focused build `LeafCellFourierDecay` passed (`9082 jobs`).
`AxiomsSmoothCells.lean` audited exact cell recovery, support-local multiplication, actual cell
Sobolev decay, center summability and both Fourier results: all six printed exactly
`[propext, Classical.choice, Quot.sound]`.

The existing `DominatedFourierMixture` API is the intended couple assembly tool: its amplitude
envelope is pointwise in the spectral variable, so Tonelli keeps the momentum supremum in the
correct order. No change of norm order is needed to recombine the scalar couple kernels.
The source lattice/time identity for the fully recombined localized leaf product and the final
momentum derivative/weight estimates remain open tasks.

## REQUIRED P-1: one-trivial-tree couple case

`WideCoupleExtensionAgreement`, `OneClockCouple`, `OneClockCoupleDecay`, `OneClockSelection`,
and `OneClockVertexDecay` add the missing degenerate source case of TARGET L1049.
The final theorem `exists_vertexClockKernel_timeRestriction_bound` takes only the genuine
root vertex `v : Fin n × Fin 2`, the active external coordinate `a : Fin 2` (either choice),
and the passive unit-interval base. Its literal kernel is the normalized source product over
`I ∩ {w | w v.1 v.2 ≤ t a}`. There is no second-root-clock premise in this final statement.
The result is the full `𝔛^η` temporal restriction bound with exponent `γ₁−100dη`.

The proof constructs a finite permutation putting `v` in the requested selected position.
The other selected branching clock is auxiliary and need not be a root of any source tree.
Nontrivial incoherence gives `n≥1`, so this completion is available. A passive external
translation raises its upper limit above its whole source layer. A fixed wider cutoff,
one on `[-2,2]`, then gives exact pointwise source agreement; temporal translation preserves
the Fourier norm. The final source box uses the genuine root's actual layer and an arbitrary
passive external unit interval. No artificial link or coupling factor is introduced.

P-1 checks: `nice -n 5 lake build WaveTurbulence.Foundations.Incoh.OneClockVertexDecay` passed
(`9312 jobs`). Scratch `AxiomsOneClock.lean`, log `axioms-one-clock.log`, audited selection,
full auxiliary-clock reduction, exact extension agreement, norm translation and both final
restriction bounds. All six printed exactly `[propext, Classical.choice, Quot.sound]`.

## Stage 2: finite smooth link localization and C2 interface

`MomentumTreeData n m w` is the additional local carrier for C2. Its fields are:
`tree : Fin w → LocalizationTree`, total `order_eq : ∑ order = 2n`;
integer `nodeRow` and `inputRow` over `Option (Fin n × Fin 2)` (root is `none`);
`input_root_column = 1`; `leafInput` identifying each leaf with an input or the lone root;
`root_row`, the alternating three-child `parent_row`, and `leaf_row`;
`chosenTree`, `chosenPath`, membership of that node and its children 0 and 2;
and `link_x_row`, `link_y_row` identifying child0−parent and parent−child2 with the two
free coordinate rows. These are finite structural identities, with no analytic estimate fields.
C2's `node_linear` and `linkCoords_surjective` should supply these rows and equalities.
The already committed `IntegerLeafCoordinates` remains the unimodular input-coordinate carrier.

The node decoration, actual input momenta, root coefficient one and link differences are
computed and proved in `MomentumTreeData` / `MomentumTreeInputs`. `TreeLocalizationRadius`
and `TreeForestLocalization` reuse the landed unit-radius tree localization at radius `sqrt d`.
`MomentumTreeLocalization` then covers all link momenta by at most `C_d^(2n)` products of
radius `2 sqrt d` balls whenever the actual leaf-cell product is nonzero.

P-2 uses the literal smooth profiles `thetaMom (2x−z)` with half-integer centers.
`HalfLinkCells` proves exact insertion of the analytic lattice cutoff, including zero cells
and boundaries. `HalfLinkCellCover`, `HalfCellArrays`, and `FiniteLinkCellLocalization`
produce a finite set of all active link-cell arrays, with cardinal at most `C_d^n`.
`LocalizedLeafDecomposition.exists_localizedLeafWeight_decomposition` is the resulting exact
finite decomposition of the actual localized source input product, everywhere in momentum.
Thus the unit-ball versus cutoff-scale issue is resolved without a hard Fourier cutoff.

`LeafLocalizationMass` and `LeafArrayLocalization` quantify the sum of actual cell Fourier
norms, including the whole input-cell array sum. `CoupleSpectralMixtureDecay` is explicitly a
conditional transport helper (joint measurability/integrability are typing premises), not the
final source identity. `GardenSign` retains the literal global Circle factor and proves exact
norm invariance; inserting it in the final source identity remains part of assembly.
The final source lattice/time exchange and momentum derivative/weight estimates remain open.

Checks for this localization milestone: targeted builds `LocalizedLeafDecomposition`
(`9158 jobs`) and `CoupleSpectralMixtureDecay LeafArrayLocalization GardenSign` (`9329 jobs`)
passed. Scratch `AxiomsFiniteLocalization.lean`, log `axioms-finite-localization.log`, prints
nine main results: each depends exactly on `[propext, Classical.choice, Quot.sound]`.
No new source errata or weakened estimates were introduced. This is a stage-2 milestone,
not completion of the source operator assembly.

## Stage 2: literal signed spectral decomposition

`HalfLinkCellFourier` proves smoothness, compact support, exact translation, finite Fourier
norms and pointwise Fourier-amplitude invariance of the actual half-width profiles.
`CellFourierInversion` uses finite source smoothness for actual leaf-cell inversion.
`FiniteCellProductFourier` is the finite-product inversion/integrability transport helper;
`LocalizedCellProfiles` discharges its continuity and Fourier integrability premises directly
from the source spatial norm.

`LocalizedSpectralIdentity` proves the exact signed Fourier integral identity for the actual
localized input product times a link-cell array, and proves its spectral integrability.
`LocalizedSpectralEnvelope` identifies its pointwise amplitude with an actual reference density
independent of all momenta and all link-cell centers. `LocalizedSpectralMass` factors its mass
into the actual one-cell norms. `LocalizedSpectralMassBound` proves the full countable
leaf-array coefficient bound `C_half^(2n) (C_leaf B)^m`. These facts retain the source supremum
order. `FiniteSpectralDecomposition` combines the actual finite localization with these literal
spectral densities; the finite cover is chosen before the functions, sign and momentum variables.
P-3's global sign is present in both this identity and its spectral integrands.

The lattice/time interchange, identification of spectral shifts with the analytic link factors,
and final spatial derivative/weight assembly remain to be completed. These modules do not
claim the final Prop 5.1 estimate or assume it as an interface field.

Spectral milestone checks: `nice -n 5 lake build
WaveTurbulence.Foundations.Incoh.FiniteSpectralDecomposition` passed (`9181 jobs`).
Scratch `AxiomsSpectralLocalization.lean`, log `axioms-spectral-localization.log`, audited
seven main identities, integrability, envelope and total-mass results. Each prints exactly
`[propext, Classical.choice, Quot.sound]`. No source errata or additional source hypotheses.

## Stage 2: exact normalized source-to-link-kernel identity

`LocalizedLatticeSupport` computes a common finite lattice set from the actual inserted
analytic cutoff. `LinkArrayCutoff` proves exact cutoff insertion and vanishing outside this
set. `LocalizedLatticeFourierExchange` proves actual lattice/Fourier exchange, with an arbitrary
coefficient transport parameter that can include the literal temporal phase and Wick factors.
`SourceTemporalPhase` defines that literal factor, with squared Wick coefficients, and proves
continuity, modulus at most one, and time integrability on every source layer subdomain.
`LocalizedSourceIntegral` defines the literal coupling-normalized localized source lattice/time
operator and proves its spectral identity; neither representation nor an estimate is assumed.

`MomentumSpectralShift` computes the transpose integer momentum map. `SpectralPhaseFactorization`
proves the exact root and link character factorization of the actual density. `SpectralLinkParameters`
computes the analytic link centers/shifts and retains the original layers, orientation and
incoherence count exactly. `LinkArraySummation`, `SpectralArraySummand`, and `SpectralLinkIntegral`
identify the actual shifted lattice/time factors with the analytic product integral.

The main equality `MomentumTreeData.localizedSourceIntegral_eq_linkKernelMixture` in
`SourceLinkKernelIdentity` is TARGET (incohproof8–10) for the actual local structural carrier:
the normalized source operator equals the integral of its computed signed/root-modulated
Fourier amplitude times `normalizedLinkIntegral` with those computed analytic link parameters.
The source input premise remains finite `spatialNorm K M`, with `d+1≤K`, and no Fourier norm
or kernel representation premise. The time domain need only be contained in the source layer
box for this equality. No new source errata or weakened bounds.

Source identity milestone checks: `nice -n 5 lake build
WaveTurbulence.Foundations.Incoh.SourceLinkKernelIdentity` passed (`9195 jobs`).
Scratch `AxiomsSourceIdentity.lean`, log `axioms-source-identity.log`, audited seven main source
identities and phase/summation results. Each prints `[propext, Classical.choice, Quot.sound]`.

## Stage 3: actual couple extension with all spectral typing premises discharged

`SpectralLinkContinuity` and `SpectralRootMeasurability` prove joint continuity of the link
factors and strong measurability of the actual root marginals. `ParametricIntervalIntegral`
and `ParametricDoubleIntegral` prove measurable moving-endpoint integration; the resulting
`SpectralCoupleMeasurability` applies directly to the literal spectral couple extension.
`CutoffDoubleL1` / `CouplePhysicalL1` reuse the landed bounded-kernel estimates to bound the
physical L¹ norm of that extension by the root marginal. `UniformL1MixtureIntegrability`
is an explicitly conditional Fubini helper. `SourceCoupleJointIntegrability` applies it to the
actual source amplitude; the independently proved root L¹ bound supplies its remaining premise.
`SourceAmplitudeIntegrability` proves actual amplitude continuity, integrability and the common
pointwise envelope directly from the finite source spatial norms.

`SourceCoupleExtension` defines the actual localized extension and proves exact agreement
with `localizedSourceIntegral` on `I ∩ rootCut t` throughout the genuine source root box.
`SourceCoupleDecay.exists_sourceCoupleExtension_bound` is its actual `𝔛^{η,0,0}` estimate with
exponent `γ₁−100dη`, multiplied by the already proved summable actual spectral mass. It has no
assumed Fourier norm, root norm, joint measurability or integrability premise. Those are proved
from source hypotheses inside the theorem.

`CoupleMomentumLocalization` and `CoupleLinkCellLocalization` strengthen P-2 for couples:
when every leaf is an actual input (including the leaf of a trivial tree), the finite cover is
chosen before every root momentum. This is an explicit structural condition on `leafInput`,
not an analytic estimate. A tree's root-valued lone leaf is handled separately in the tree case.
Full countable recombination, spatial derivative/weight estimates, and the corresponding actual
source tree mixture assembly remain open; this is not yet READY pl1.

Actual couple milestone checks: targeted builds `SourceCoupleDecay CoupleLinkCellLocalization`
passed (`9381 jobs`). Scratch `AxiomsActualCoupleDecay.lean`, log
`axioms-actual-couple-decay.log`, audited seven main results. Every result uses exactly
`[propext, Classical.choice, Quot.sound]`. No new source errata or weakened decay estimates.

## Stage 3: countable cell recombination estimate

`SourceCellMeasure` defines the actual selected cell index as the discrete countable sigma
family of leaf cells and finite selected link cells, with counting measure times spectral
Lebesgue measure. It proves sigma-finiteness and the exact mass formula including the literal
finite fiber cardinal. `SourceCellMassBound` bounds this full coefficient by
`C_local^n (C_leaf B)^m C_half^(2n)` directly from the input spatial norms.
`AllCellSourceFamily` proves amplitude and kernel joint measurability on this measure.
`AllCellAmplitudeL1` proves full amplitude integrability. `AllCellCoupleFubini` discharges
joint time/cell/spectral integrability from the proved uniform physical root bound.

`AllCellCoupleDecay.exists_allCellSourceCoupleExtension_bound` proves the actual countable-cell
spectral extension estimate with that explicit exponential coefficient and the decay exponent
`γ₁−100dη`. No supremum/integral order is changed and no Fourier or Fubini premise is assumed.
Its finite cell family is arbitrary subject to its cardinal bound; the previously proved
momentum-uniform source cover supplies the appropriate family. Exact identification of this
full countable integral with the unlocalized raw source lattice sum still needs the absolute
convergence/recombination argument. The final spatial derivative/weight and actual tree source
assembly remain open.

Countable-cell estimate checks: targeted build `AllCellCoupleDecay` passed (`9384 jobs`).
Scratch `AxiomsAllCellDecay.lean`, log `axioms-all-cell-decay.log`, audited five main mass,
Fubini and decay results, each using exactly `[propext, Classical.choice, Quot.sound]`.

## Exact raw source localization and absolute convergence

`SourcePointwiseLocalization` defines the literal unlocalized input product `sourceLeafWeight`
and the actual selected-cell weight. `hasSum_sourceCellWeight` proves exact pointwise recovery
of the raw input product with an actual finite pointwise support, for the momentum-uniform
cover condition. No convergence premise is assumed.
`LinkArrayCutoffMass` tensorizes the landed center-independent cutoff mass `(5L)^d`.
`SourceCellLatticeMajorant` uses the proved actual Fourier inversion to bound each cell by
its computed spectral mass, then inserts the analytic cutoff exactly to obtain a summable
lattice majorant. `SourceAbsoluteConvergence.summable_norm_sourceLeafWeight_lattice` proves
absolute convergence of the literal raw source lattice series from the input spatial norm,
finite cover and its cardinal bound. This absolute estimate is used only for rearrangements;
it does not replace the oscillatory decay bound.

Raw convergence milestone checks: `SourceAbsoluteConvergence` built successfully (`9205 jobs`),
and rebuilding `AllCellCoupleDecay SourceAbsoluteConvergence` after the discrete cell-index
API refinement passed (`9388 jobs`). Scratch `AxiomsSourceAbsolute.lean`, log
`axioms-source-absolute.log`, audited pointwise reconstruction, raw absolute convergence,
full cell/lattice mass and uniform cutoff mass. All four results use only
`[propext, Classical.choice, Quot.sound]`.

## Tree source assembly: arbitrary parameters and moving cell support

`GeneralTriangleNegativeNorm` reuses the landed scalar N3 pointwise Fourier bound and its
integrable envelope for arbitrary parameter carriers. `ParameterTreeExtension` reuses the
landed global common-extension identity slice by slice. `ParameterTreeNegativeBound`,
`ParameterTreeQuarterBound`, and `ParameterTreeDecay` give the same actual tree extension
bound with arbitrary vector/spectral/discrete parameters, with exact fixed selected-link data.
The endpoint loss remains `L^(2d)` and the final exponent remains `γ₁−100dη`.

`UniformParameterMixture` proves transport through a kernel family whose mixed Fourier
supremum includes every vector and spectral parameter. Its uniform-mass version allows the
amplitude localization support to move with root momentum; a common pointwise amplitude
envelope is unnecessary. This is a conditional transport helper, not a source estimate.
`ParametricTriangleIntegral` / `SpectralTreeMeasurability` prove actual causal-family strong
measurability. `CutoffTriangleL1` reuses the landed physical bounded-kernel estimate.
`SpectralTreeClocks` transports the actual tree clock data to the computed spectral link
parameters while retaining the literal source time domain exactly (`rfl`).

Tree parameter checks: targeted builds `ParameterTreeDecay` (`9410 jobs`),
`UniformParameterMixture SpectralTreeMeasurability CutoffTriangleL1` (`9451 jobs`), and
`SpectralTreeClocks` (`9187 jobs`) passed. Scratch `AxiomsParameterTree.lean`, log
`axioms-parameter-tree.log`, audited five main norm, identity, measurability and mixture
results: each uses exactly `[propext, Classical.choice, Quot.sound]`.

## Actual moving-cell tree recombination estimate

`UnrestrictedCellMeasure` fixes counting measure on all integer leaf/link cell pairs times
spectral Lebesgue measure. The moving finite selection is an actual indicator in
`MovingCellAmplitude`, whose uniform mass and integrability are proved from source spatial
norms and the finite cardinal bound. No measurability of the selection in root momentum is
needed at order zero. `MovingTreeFamily` proves joint spectral/time measurability and Fubini
for the literal causal kernel using the independently proved root L¹ estimate.

`MovingTreeDecay.exists_movingCellSourceTreeExtension_bound` proves `𝔛^{η,0,0}` decay of the
actual moving-cell tree extension, with the same explicit localization coefficient as the
couple estimate and exponent `γ₁−100dη`. The arbitrary-parameter tree core controls all centers
and Fourier shifts simultaneously; the uniform-mass mixture inequality retains the momentum
supremum inside the frequency integral. Original tree time fibers are transported exactly by
`SpectralTreeClocks`. The original finite tree cover supplies the moving selection, including
the root-valued lone leaf. No analytic estimate is assumed as a carrier field.

Moving-tree checks: targeted build `MovingTreeDecay` passed (`9483 jobs`). Scratch
`AxiomsMovingTree.lean`, log `axioms-moving-tree.log`, audited the final mixed norm bound,
actual spectral Fubini, uniform actual amplitude mass, and fixed-measure indicator formula.
All four use exactly `[propext, Classical.choice, Quot.sound]`. No weakened exponent or new
source errata were introduced.

## Actual raw couple restriction bound (spatial order zero)

`RawSourceIntegral` defines the original unlocalized normalized source lattice/time operator,
retaining the global sign and actual source inputs. Source spatial norms prove its absolute
lattice convergence and continuous time dependence. `RawSourceCellSeries` and
`RawSourceCellIntegral` prove exact pointwise lattice/cell and time/cell rearrangements, with
absolute convergence justified by the actual source majorant. `SourceCellTimeIntegrand`
proves finite lattice support, continuity and a clock-independent majorant for every cell.

`CutoffPointwiseL1` / `CouplePointwiseL1` reuse the landed bounded kernels to give a pointwise
physical root-mass bound. `AllCellCouplePointwise` proves spectral/counting Fubini at every
external clock pair. `RawCoupleAgreement` identifies the full recombined spectral extension
with the literal raw couple kernel on the entire source root box, including boundaries.

`RawCoupleRestrictionDecay.exists_rawCoupleKernel_restriction_bound` now proves actual
`𝔛^{η,0,0}` restriction decay of that raw unlocalized source couple kernel. Its only input
premises are structural source data, source layer/domain conditions, incoherence, and finite
spatial input norms. The dimensional finite localization cover, Fourier bounds, all Fubini
conditions and exact extension agreement are proved internally. Its displayed coefficient is
still `C_local^n (C_leaf B)^m C_half^(2n)` before the final exponential absorption and spatial
order `30d` / weight `30d` assembly. The one-clock analytic source case remains supplied by
P-1 above and must be retained through final source assembly.

Raw-couple checks: targeted build `RawCoupleRestrictionDecay` passed (`9401 jobs`), including
`RawSourceCellIntegral` (`9209 jobs`) and `AllCellCouplePointwise` (`9388 jobs`). Scratch
`AxiomsRawCouple.lean`, log `axioms-raw-couple.log`, audited six final raw restriction, exact
recombination, pointwise Fubini and physical bound results: each uses exactly
`[propext, Classical.choice, Quot.sound]`.

## Actual raw tree restriction bound (spatial order zero)

The pointwise localization and raw reconstruction APIs now include `of_cover_at` versions:
they require the cover only at the actual root momentum being evaluated. The former uniform
cover theorem names and statements are retained as wrappers, and the raw couple bound was
rebuilt successfully against them. This is the natural source reading for a tree with a
root-valued lone leaf.

`FiniteSelectionIntegral` proves exact counting/Lebesgue Fubini over selected finite fibers.
`MovingTreePointwise` proves integrability at every external clock pair and exact forward
agreement of the scalar causal spectral kernel with its literal source causal cut.
`RawTreeAgreement` defines `sourceTreeKernel` as the original unlocalized normalized source
operator over `I ∩ causalRootCut t` and proves exact pointwise agreement of the full moving-cell
spectral extension on the external causal source box.

`RawTreeRestrictionDecay.exists_rawTreeKernel_restriction_bound` proves actual raw
`𝔛^{η,0,0}` restriction decay, including the lone leaf, with exponent `γ₁−100dη` and explicit
localization coefficient `C_local^n (C_leaf B)^m C_half^(2n)`. The finite cover is generated
inside the proof, and no Fourier norm, kernel representation, integrability or analytic root
bound is assumed. Remaining Prop 5.1 work: full spatial order `30d`, couple weight `30d`,
retaining P-1 through the raw source one-clock assembly, and final constant/exponent absorption.

Raw-tree checks: targeted build `RawTreeRestrictionDecay` passed (`9499 jobs`), and the raw
couple compatibility target `RawCoupleRestrictionDecay` rebuilt successfully (`9401 jobs`).
Scratch `AxiomsRawTree.lean`, log `axioms-raw-tree.log`, audited five final raw restriction,
exact recovery and finite-selection Fubini results. Each uses only
`[propext, Classical.choice, Quot.sound]`.

Finite spatial derivative milestone (continuing assembly): `NestedDerivativeNorm`,
`CoordinateDerivativeComponent`, and `SpatialDerivativeInputBound` prove actual iterated
coordinate derivatives retain the remaining finite smoothness and decay budget. Explicitly,
`j + K ≤ N` and `M' ≤ M` imply an `Sf^{K,M'}` bound by
`max(1,d)^N B` for the actual derivative input. No infinite smoothness is assumed.
`FinalExponentLoss` proves `100d η ≤ sqrt η` under `(100d)^2 η ≤ 1`, and hence the
printed final incoherence exponent from the analytic core's exponent.

Checks: targeted build `SpatialDerivativeInputBound` passed (`9055 jobs`);
`FinalExponentLoss` passed in the preceding targeted build. Scratch
`AxiomsSpatialDerivative.lean` / `axioms-spatial-derivative.log` audited five results;
all depend only on `[propext, Classical.choice, Quot.sound]`. No new source deviation.
The full spatial mixed-norm assembly and raw one-clock assembly are still outstanding.

P-1 raw-source milestone: the required degenerate couple is now covered through actual
localization, spectral recombination, raw-source recovery and final order-zero restriction decay.
`RawVertexClockRestrictionDecay.exists_rawVertexClockKernel_restriction_bound` selects only
the genuine branching vertex `v` and the active external coordinate `a`. It has no premise
providing a second source root. Its raw source domain is literally
`I ∩ {w | w v.1 v.2 ≤ t a}`. The external box is the genuine root layer times an arbitrary
passive unit interval. The auxiliary branching clock is constructed by `oneClockSelection`
and fully integrated internally. All finite cover, source Fourier bounds, absolute lattice
convergence and Fubini conditions are proved from the same structural/spatial input hypotheses.
The global `ζ : Circle` is retained exactly. The exponent and explicit localization coefficient
are unchanged from the two-clock raw theorem. Full spatial order/weight assembly remains.

Files: `AllCellCutoffCoupleFamily`, `AllCellCutoffCoupleFubini`,
`CutoffCoupleSpectralMixtureDecay`, `AllCellCutoffCoupleDecay`,
`AllCellCutoffCouplePointwise` provide the existing actual-source pipeline with any fixed
smooth compact cutoff. `ParameterTimeTranslation` transports the complete parameter supremum
norm under a common time shift. `RawOneClockAgreement`, `RawOneClockRestrictionDecay`,
`RawVertexClockRestrictionDecay` implement the required source reduction.

Checks: targeted `nice -n 5 lake build
WaveTurbulence.Foundations.Incoh.RawVertexClockRestrictionDecay` passed (`9409 jobs`).
Scratch `AxiomsRawOneClock.lean` / `axioms-raw-one-clock.log` audits five results, including
both final raw one-clock bounds and exact source recovery; every result uses only
`[propext, Classical.choice, Quot.sound]`. No new erratum or source deviation.

Spatial assembly inputs milestone (continuing): `RootInputWeight` proves the printed root-weight
transfer directly from the finite integer root row. `WeightedFourierL1` and
`LeafCellFourierMoment` prove actual degree-`J` Fourier moments using only `d+1+J` source
derivatives, with the full summable localization-center decay retained. `SpectralMomentProfiles`
and `SpectralMomentMass` factor the actual higher-moment reference density over its leaf/link
profiles and prove its actual integrability and mass bound. Link profiles require no moments.
`MomentumModulation`, `SourceRootFrequency`, `SourceAmplitudeDerivative`, and
`SourceAmplitudeDerivativeMeasurable` prove actual source-amplitude derivatives and their spectral
continuity. The root frequency is exactly the sum of leaf-profile frequencies; its `J`-th power
is controlled by the product of the individual `(1+|ξ_a|)^J` moments. This spectral proof uses
the available finite source smoothness budget and introduces no infinite-smoothness premise
on the input functions. `SmoothParameterIntegral` and `IteratedDerivativeIntegral` provide
conditional calculus transport for actual finite derivatives under integrable envelopes.

Checks: focused targets `RootInputWeight` (`9053 jobs`), `LeafCellFourierMoment` (`9074 jobs`),
`IteratedDerivativeIntegral` (`9049/9050` success in the focused modulation build),
`SpectralMomentMass` (`9184 jobs`), and `SourceAmplitudeDerivativeMeasurable` (`9201 jobs`)
compiled successfully. Scratch `AxiomsSpatialAssemblyInputs.lean` / corresponding log audits
seven principal results; each uses only `[propext, Classical.choice, Quot.sound]`.
Full spatial mixed-norm assembly remains outstanding; these are its proved inputs, not a
claim that Proposition 5.1 is complete. No new source erratum or weakened estimate.

Full raw couple spatial milestone (continuing):
`FullRawCoupleRestrictionDecay.exists_rawCoupleKernel_fullRestriction_bound` proves actual
`mixedRestrictionNorm eta J W` decay of the literal unlocalized couple kernel. The input
conditions are `d+1+J ≤ K` and `W+2d ≤ M` on actual `Sf^{K,M}` input norms. Consequently
`J=W=30d`, `K=M=40d` fits the source budget for `d≥3`. The constant is explicit:
`C_mask(d,m,J,W) C_local^n (C_weighted_moment B)^m C_half^(2n)` times the analytic
core's `(C0 delta)^n L^{-(gamma1-100d eta)g}`. No derivative identity, Fourier estimate,
Fubini condition or analytic estimate is assumed by the final raw theorem.

P-1 is also retained at full spatial order and weight:
`FullRawVertexClockRestrictionDecay.exists_rawVertexClockKernel_fullRestriction_bound`
selects only the genuine vertex, with literal domain `I ∩ {w | w v.1 v.2 ≤ t a}` and the
genuine/passive unit box. Its second clock is constructed internally. The source norm has
all the same spatial orders and input budgets as the two-clock result.

Additional finite carrier data needed for the couple root weight, in `RootInputCoordinates P`:
- `sigma : Fin m → Z`;
- `abs_sigma_le : ∀ a, |sigma a| ≤ 1`;
- `root_row : (sum a, sigma a • P.inputRow a) = momentumUnitRow none`.
These are finite integer identities supplied by the source unimodular leaf coordinates.
Evaluation proves the actual real root relation, and `sum_sigma=1` follows from P's
existing input root columns. No analytic fields were added to `MomentumTreeData`.

Approach: insert a smooth root mask fixed by each source leaf-center array, of width
`2 (2+sqrt d)^m prod_a <c_a>`. The finite root row proves it is exactly one wherever the
actual localized source can be nonzero. Its scale is independent of derivative order, so
one actual extension controls all derivatives. The actual spectral amplitude derivatives
are bounded by products of individual leaf Fourier moments. Paying the root weight at
every center leaves exactly `M-W` powers of summable decay. The full spatial spectral
transport theorem keeps the momentum supremum inside the time-frequency integral.
`AllCellMaskedCoupleDecay` is uniform in an arbitrary common external time translation;
this supplies P-1's passive-clock shift without any spatial norm translation assumption.
The global garden sign is retained in every actual source and amplitude.

Files added for this milestone: `ParameterIteratedDerivative`, `CountableSliceMeasurability`,
`RootInputCoordinates`, `SourceRootMask`, `SourceRootMaskBounds`, `SourceRootMaskAgreement`,
`SpectralMomentContinuity`, `SpectralMomentSummability`, `WeightedSpectralMomentMass`,
`MaskedSourceAmplitude`, `MaskedSourceDerivativeBound`, `MaskedCellEnvelope`, `MaskedCellFamily`,
`SpatialNormParameterIntegral`, `SpatialSpectralIntegral`, `MixedSpatialEnvelope`,
`SpectralSpatialMixture`, `AllCellMaskedCoupleDecay`, `MaskedCouplePointwise`,
`MaskedRawCoupleAgreement`, `MaskedRawOneClockAgreement`, `FullRawCoupleRestrictionDecay`,
`FullRawOneClockRestrictionDecay`, `FullRawVertexClockRestrictionDecay`.

Checks: focused build of `FullRawVertexClockRestrictionDecay` and
`FullRawCoupleRestrictionDecay` passed (`9450 jobs`), including all dependencies above.
`AxiomsFullCouple.lean` / `axioms-full-couple.log` audits eight principal results, including
both final raw spatial bounds. All use only `[propext, Classical.choice, Quot.sound]`.
No new erratum, hidden smoothness premise, changed Wick sign, or weakened source estimate.

Remaining packet work: absorb the explicit order-dependent coefficients into `C1^n`, apply
the proved final square-root eta loss, complete the tree's full `30d` spatial derivatives
(the literal tree order-zero bound is already done), and package the abstract Prop 5.1
couple/tree statement. The full Prop 5.1 packet is not yet claimed complete.

Printed couple rate milestone (continuing tree assembly): `CouplePropositionRate` and
`VertexClockPropositionRate` now prove the exact printed rate
`(C1 delta)^n L^{-(gamma1-sqrt eta)g}` for the raw two-clock and intrinsic one-clock
couple kernels in `X^{eta,30d,30d}`. They use actual `Sf^{40d,40d}` input bounds,
the source finite root row, and the cardinal typing inequality `m≤3n` (in particular
`m=2n+1`, since incoherence implies `n≥1`). The eta condition is explicitly
`(100d)^2 eta≤1`, in addition to the analytic core's eta hypotheses.
`ExponentialCoefficientAbsorption` absorbs every printed localization/spatial coefficient;
`FinalExponentLoss` supplies the exact final exponent. The lattice threshold precedes every
order, object, input function and root momentum set.

Tree preparation: `MomentumTreeRootInput` appends the finite unit root row as one additional
input, converting the lone leaf to an indexed input without changing any original node/link
row. All source leaf-ball localization premises then apply. `RootInputSourceIdentity`
proves the literal raw causal source kernel is multiplied exactly by the appended input's
root value. This temporary input will be removed with the landed root partition of unity;
no decay assumption has been added to the tree's lone leaf.

Checks: focused couple rate build passed (`9454 jobs`), and root-input source identity
build passed (`9500 jobs`). Scratch `AxiomsPropositionRates.lean` /
`axioms-proposition-rates.log` audited both final printed couple rates, the coefficient
absorption, the appended finite root-row certificate and its exact raw tree source identity.
Each uses only `[propext, Classical.choice, Quot.sound]`. No new erratum or deviation.
The packet still requires the tree's full spatial derivative bound and final joint packaging.
