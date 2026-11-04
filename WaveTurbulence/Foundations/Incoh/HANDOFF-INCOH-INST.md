# INCOH-INST working handoff

Status: in progress. Main merged first to `7b8b80c`; PL1 landed.

Pinned exact target: `/home/scott/wt-scratch/waveb2-snap-final/WaveB2-Statements.lean`,
`WaveTurbulence.incoherentDecay`, SHA256
`82e42b2bfa16289ef6fadc35f2fbc8375cf28eda18658b35faef2b89556d99a4`.
Exact type saved as `/home/scott/wt-scratch/incoh-inst/anchor-type.txt`, type SHA256
`767dcebdce1a275d9b8fa595c2ef42dc9ac7c58f6f6d9ced5f1156f8775c11b3`.
B2 Regular is `4d7f81ef...`; B1 Core/System are `0b8477d9...` / `59365906...`.
The existing MEXP base stack has byte-identical copies of these inputs, with LINKS,
ENHANCED, LAYERREG and REG-STRUCT proofs available for reuse.

Files/progress:
- Scratch `/home/scott/wt-scratch/incoh-inst/src/IncohInst/TreeShape.lean`:
  exact source ternary tree → analytic tree, preserving order/nodes/leaves/branching.
- Scratch `CoupleRows.lean`: actual C2 integer node rows, exact evaluation against
  `decOfParams` in every coefficient group, root/parent/pair/link coordinate identities.
- Scratch `CoupleCarrier.lean`: every `MomentumTreeData` field constructed from the actual
  decoded source couple, with exactly its positive input leaves and computed link count.
- Scratch `CoupleRoot.lean`: C2's signed leaf relation gives `RootInputCoordinates`; all leaves
  carry inputs and their number is exactly `2n+1`.
- Scratch `TreeRows.lean`: actual ENHANCED tree rows and their root/parent/pair/link identities.
- Tree lone-leaf assignment and full tree carrier are under construction.

Foundations additions:
- `CoupleCutoffUniformDecay.lean`: the exponential constant is chosen before eta and the
  arbitrary smooth compact clock cutoff. Its scalar time integration factor is kept outside
  the order power and absorbed into the existing exponent slack via the lattice threshold.
- `AllCellCoupleCutoffUniformDecay.lean`: the same uniformity after full actual spatial
  differentiation and counted spectral mixture.
This is needed because B2's external box can lie above its roots' actual layers. A cutoff
spanning the finite layer range must affect the threshold, not the source exponential constant.
No gamma restriction beyond `0<gamma<1` was introduced.

Checks so far:
- Narrow scratch module builds passed for TreeShape, CoupleRows, CoupleCarrier, CoupleRoot,
  TreeRows, using `nice -n 5 lake env bash .../build-one.sh <module>`.
- `nice -n 5 lake build WaveTurbulence.Foundations.Incoh.CoupleCutoffUniformDecay`:
  build completed successfully (9303 jobs).
- `nice -n 5 lake build WaveTurbulence.Foundations.Incoh.AllCellCoupleCutoffUniformDecay`:
  build completed successfully (9410 jobs).
- `nice -n 5 lake env lean /home/scott/wt-scratch/incoh-inst/check-foundations.lean`:
  both new main Foundations results use `[propext, Classical.choice, Quot.sound]` only.

Remaining: full source tree carrier, layer/count and time-domain identities, exact original
kernel equality (including lattice decoration equivalence, phase, squared Wick factor and
normalization), upper external time boxes, uniform inputs and parameter prefix, exact anchor
text/Expr comparison, final axiom check. No claim of anchor completion yet.

No new source errata or deviations; F62's squared Wick factor remains in force.

Further structural checkpoint:
- Scratch `TreeLeafRows`, `TreeCarrier`, `CoupleLinkCoordinates`, `CoupleLayers`,
  `TreeLinkCoordinates`, `TreeLayers` all pass their focused scratch builds.
- Both actual source carriers are now constructed, with the tree lone leaf represented
  by `none` and proved to carry exactly the root row; source input counts are `2n+1` / `2n`.
- Both link endpoint maps are proved bijections onto all source branching nodes.
  The actual analytic layer families have exactly the source incoherence count and the
  source layer-span bound. No decoding or analytic bound was assumed in place of these proofs.
- `CoupleUpperBoxAgreement` builds (9308 jobs): scalar exact agreement above root layers.
- `MaskedRawCoupleUpperAgreement` builds (9431 jobs): full counted, masked spectral extension
  agrees with the raw source on the larger external box, using the actual cutoff.
- The O1–O5 proofs are being checked from the final-candidate REG-STRUCT rebuild in
  wt-orch's `t32/build`, after MEXP's byte-identical final definitions in the search path.

Upper-box analytic checkpoint:
- `TreeUpperBoxAgreement`, `MaskedRawTreeUpperAgreement`, `TreeRootUpperAgreement` build
  successfully (9559 jobs). The external time condition is exactly forward clocks and cutoff
  equal to one at the external endpoints; they need not lie in the selected internal root box.
- `FullRawCoupleUpperRestrictionDecay` builds (9437 jobs): any external set above the actual
  root layers and covered by the chosen cutoff, with the exponential constant before cutoff.
- `FullRawTreeUpperRestrictionDecay` builds (9563 jobs): any external forward-clock set
  covered by the chosen cutoff; all root-partition spatial derivatives are preserved.
- Scratch `NormBridge` checks `XNormRestr ≤ mixedRestrictionNorm` at arbitrary spatial weight,
  including the exact B2 smoothness guards; it does not change the restriction domain.
- Scratch `DecorationEquivalences` checks exact bijections of the original B1 `GenDecoration`
  subtypes with C2's couple/tree link-lattice coordinates. No convergence hypothesis enters
  these finite-coordinate bijections.
- `axioms-rows.log`: both source carriers, their root/count identities and the couple link
  equivalence use only `[propext, Classical.choice, Quot.sound]` (8 results).

`check-foundations.lean` / `axioms-foundations.log` now audits seven cutoff-uniform and
upper-box results, including both full raw spatial restriction bounds. Every result uses
only `[propext, Classical.choice, Quot.sound]`. No source estimate was weakened and no
restriction on gamma was added. The exact B2 anchor is still not claimed proved.

Kernel-identity checkpoint:
- `ClockTransport` proves that the actual C2 endpoint reindexings preserve product Lebesgue
  measure, and that each reindexed source endpoint reads exactly its original link clock.
- `WickFactors` proves exact per-link squared Wick factors for BOTH couples and paired trees.
  The tree result is proved from the actual endpoint partition and `tree_xy_link`, not assumed.
- `PhaseIdentity.couple_phaseProd_eq_links` proves the exact source couple phase identity,
  retaining B1's pi normalization and the analytic `e(z)=exp(2*pi*i*z)` convention.
- `DecorationEquivalences` uses the actual no-flower constraints of each decoded object to
  identify the literal `GenDecoration` subtype with the C2 integer link coordinates.
- `RootCoordinatesOfEmbedding` constructs the analytic root-time permutation from any actual
  embedding of selected source vertices; its computed root vertices equal the given vertices.
  Narrow build succeeds (9132 jobs).

Further exact identities checked:
- `TreePhaseIdentity.tree_phaseProd_eq_links` now compiles as well.
- `InputProductIdentity` proves the literal analytic input products equal the original B1
  `inputLeaves` products, with every leaf's original layer; both couple and tree cases compile.
- `CosetDecorationIdentity` proves that the C2 real decoration with root `k` and lattice link
  parameters equals exactly B1's `cosetDecoration k` of the integer C2 decoration. It uses the
  frozen `latticePoint` as an actual additive homomorphism, with no scale restrictions.
- Remaining main assembly obligations are time-domain identities/fibers, exact lattice-sum /
  integral interchange, one-clock upper-box transport, uniform inputs and WTPrefix assembly,
  followed by the final type/axiom checks. No mathematical obstruction has been found.

`TemporalSourceIdentity` now compiles for BOTH couples and trees: the original integer
`epsDec` multiplied by the original phase at the original coset decoration is exactly the
analytic `sourceTemporalPhase`, including squared Wick factors and unchanged normalization.
`SourceTimeMeasurability` proves measurability of the original `kDomain` from its literal
layer, parent-child and lone-parent constraints. These are source identities, not estimates.

The two-root source-domain reduction is now checked: `CoupleTimeBoundary` identifies the
strict original domain with `internalTimeDomain ∩` the closed source root cuts almost
everywhere, using `Measure.ae_eval_ne` for the two null root hyperplanes. The internal child
inequalities imply every branch clock is at most its actual root (`TreeTimeOrder`,
`ForestTimeOrder`). `CouplePhaseIntegral` then transports the original phase integral exactly
to the computed analytic internal domain/root cut, by the proved measure-preserving clock map.

`RawSourceTimeFubini` builds (9207 jobs): actual raw leaf summability and finite source time-box
volume prove literal lattice/time interchange. Its summability premise is a conditional helper
premise, to be discharged by `SourceAbsoluteConvergence` at the final source input bounds.

`CoupleKernelIdentity.KQstar_eq_raw_of_summable` now compiles: it identifies the literal B1
`KQstar` with the actual analytic raw source kernel, including the original decoration sum,
coupling power, global garden sign, Wick factor, phase integral and input product. The explicitly
named conditional helper uses summability only for Fubini. `CoupleKernelFromInputs.KQstar_eq_raw`
also compiles and discharges that summability from the actual source `40d,40d` input bounds.
`GardenSign` checks the original garden sign has unit modulus and retains its exact value.
`CoupleUpperPropositionRate` builds (9441 jobs): printed spatial order and square-root eta
loss on upper boxes, with `C1` chosen before eta and the finite layer cutoff.

`axioms-kernel-ingredients.log` checks 14 exact phase/Wick/clock/lattice/input/coset results;
each uses only `[propext, Classical.choice, Quot.sound]`.

Actual original-kernel estimate checkpoint:
- Scratch `CoupleDecay.exists_KQstar_twoRoot_decay` compiles. This is the literal original B1
  `KQstar` estimate on the EXACT B2 `timeBox q q'`, in the exact B2 weighted spatial restriction
  norm, for every decoded couple with two branching roots. All finite carrier fields, lattice/time
  summability, root box conditions and norm bridges are discharged. Its exponential constant is
  chosen before eta, delta and the total number of layers. It remains a component theorem, not
  the final exact B2 anchor (one-clock/tree/prefix assembly remain).
- `FiniteLayerCutoff` is an actual smooth compact cutoff covering the whole finite source range;
  its pointwise equality on the closed range is proved, not assumed.
- `MaskedRawOneClockUpperAgreement`, `FullRawOneClockUpperRestrictionDecay` compile (9439 jobs).
  `OneClockUpperPropositionRate` compiles (9442 jobs): the printed one-clock rate on upper boxes,
  with the same passive-clock translation and cutoff-independent exponential constant.
- The expanded `axioms-foundations.log` checks every new principal analytic upper-box and Fubini
  helper above and the root embedding helper: standard axioms only.
