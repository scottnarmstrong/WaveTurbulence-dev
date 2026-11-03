# WKE-L2S handoff — complete

Branch: `w/wke-l2s`. Integration target:
`WaveTurbulence.Foundations.WKEL2.Packet` (`Packet.lean`). All worker changes
are confined to `WaveTurbulence/Foundations/WKEL2/**`. No push or landing was
performed. The root import, frozen files, shared WKE modules, providers,
manifest, and findings ledger were not edited.

## Files and results

All four brief goals are proved. The packet contains 182 focused Lean
modules; the longest is 137 lines. `Packet.lean` imports the principal exports.

| Goal | Main implementation files / exports |
|---|---|
| Lemma 1, Corollary 2 | `ResonantSymmetry.lean`, `ResonantPolarFull.lean`, `AngularCoordinates.lean`: all nonnegative Borel kernels, infinite integrals, polar densities, angular swap |
| Lemmas 3–4 | `RadialCauchyENN.lean`, `M1.lean`, `M2.lean`: radial Cauchy–Schwarz and `M1.exists_uniform_M1`, `M2.exists_uniform_M2` for every d≥3, s>d/2−1 |
| Propositions 5–7, Theorem 7 | `LossTwoTrilinear.lean`, `LossOneTrilinear.lean`, `LossThreeTrilinear.lean`, `GainTrilinear.lean`, `Trilinear.lean`: `exists_collisionTerm_bound` for all four terms, signed Borel inputs with actual weighted `MemLp 2` membership and the exact frozen norm |
| Full collision bound | `CollisionBound.lean`: `exists_collisionOp_bound` for the actual frozen signed collision operator |
| Picard LWP | `CollisionPicard.lean`, `SchwartzPicard.lean`: inverse-square exact weighted-norm lifespan, uniqueness, mild/differential equivalence, zero trajectory |
| Finite weighted jets | `WeightedSobolevModel.lean`, `JetWordBound.lean`, `JetCollisionBanach.lean`: faithful dense Schwartz cores, actual Banach completions, all-order trilinear bounds |
| Gronwall and persistence | `JetTameCompleted.lean`, `JetAPriori.lean`, `CubicContinuation.lean`, `JetPersistence.lean`: order-independent highest-order coefficient, uniform bounds on all shorter intervals, full-base-interval persistence |
| Supporting fact 1 | `WeightedSobolevLetter.lean`, `JetClosedIdentity.lean`: exact Leibniz and weight identities for completed inputs |
| Supporting fact 2 | `SchwartzSolutionMild.lean`, `SolutionEquivalence.lean`: `isWKESolution_iff_weightedL2Mild` and equality of the reconstructed source and given Banach trajectories |
| Supporting fact 3 | `SchwartzSeminormJetBound.lean`, `SchwartzJetTopology.lean`, `SchwartzReconstruction.lean`: actual Schwartz topology, both convergence directions, reconstruction from all compatible completed jets |
| Canonical norm comparison | `JetCommutator.lean`, `JetNormalOrdering.lean`, `CanonicalJetEquivalence.lean`: same-order bounds between ordered jets and the paper's moment-before-derivative convention, with constants one and `(m+1)!` |
| Maximal-time equality | `MaximalTimeEquality.lean`: `weightedL2TauMax_eq_tauMax`, `weightedSobolevTauMax_eq_tauMax`, both relative to landed `WKE.tauMax` |
| Full blow-up conjunct | `Blowup.lean`: `WaveTurbulence.WKEL2.wkelwp_blowup`, exactly frozen conjunct 3 relative to landed `WKE.tauMax`, including every threshold and every later source solution |

The exact Theorem 7 binder/definition comparison is in `THEOREM7-CHECK.md`.
The blow-up binder, carrier, definition-body, consumption, and supporting-fact
comparison is in `BLOWUP-CHECK.md`. These are worker checks, not an independent
manifest or frozen-anchor promotion.

## Approach

The resonant measure is defined through a measurable hyperplane chart.
Locally finite measure uniqueness promotes compact continuous kernel
symmetry to every Borel kernel. Tonelli and polar integration give the
angular representation. Uniform kernel bounds, Hölder, Cauchy–Schwarz,
Schur estimates and weight transfer prove all four trilinear estimates;
signed absolute convergence and genuine L² membership are retained.

The exact weighted Schwartz image is dense in the base L² Banach space.
Collision extends continuously from that core; quantitative cubic Picard
and uniqueness apply. Ordered derivative/moment jets retain every Leibniz
multiplicity. Tame bounds extend by density; a Gronwall induction bounds
all orders whenever the base norm is bounded. Uniform positive Picard steps
then cover the full base interval in finitely many steps.

A whole-space Sobolev bound controls actual Schwartz seminorms. Compatible
completed jets reconstruct an actual Schwartz function using absolutely
summable seminorm series, without assuming Schwartz completeness. This
proves the exact source/mild correspondence and equality of all maximal
times. Uniform continuation from a bounded endpoint proves the full
`∀M ∃τ₀` limit in `Blowup.lean`.

## Commits and checks

Milestones were committed throughout. Recent principal commits:
`d875a8b` (Gronwall), `538312e` (Schwartz reconstruction), `0f11081`
(source-to-mild), `13b112f` (finite-step continuation), `7d44269` (uniform
shorter intervals), `6ddcd07` (persistence), `b3603ff` (exact blow-up),
`f35a344` (completed identities), `82fc4ac` (maximal-time equality),
`7043f80` (normal ordering), `493cc00` (exact solution equivalence),
`686b82b` (canonical comparison and packet), `6fc93fa` (source Picard lifespan).
Main had landed through `864e5e5`; current main `430d637` was merged at
`c312872`. No frozen or shared WKE API changed in that merge.

All builds used the compile gate, one targeted command at a time. Final checks:

- `nice -n 5 lake build WaveTurbulence.Foundations.WKEL2.Packet`
  exited 0: `Build completed successfully (9247 jobs).` No warnings in the
  final changed modules. Log: `/home/scott/wt-scratch/wke-l2s/packet.log`.
- `nice -n 5 lake env lean /home/scott/wt-scratch/wke-l2s/BlowupAxioms.lean`
  exited 0: thirteen main blow-up/persistence/topology declarations audited.
- `nice -n 5 lake env lean /home/scott/wt-scratch/wke-l2s/FinalAxioms.lean`
  exited 0: eleven final declarations, including Theorem 7, full collision,
  completed identities, solution equivalence, canonical norm comparison,
  maximal-time equality, source lifespan and the exact blow-up theorem.
- Earlier focused Lemma 4, loss-term, Theorem 7, Banach and jet axiom probes
  also exited 0; their details are preserved in branch history and scratch.
- Every printed main result depends exactly on
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx` or custom axiom.
- `git diff --check` passed. Static scans found no forbidden declaration,
  budget override, quarantined import, oversized file, or missing module shape.
  The diff since the integration merge contains only owned WKEL2 paths.

No whole-library build, dependency rebuild, or cleaning command was run.

## Suspected errata, conventions, and uncertainties

TARGET L2522–L2523, (schappend11), says `ι ∈ {−1,0,1}` for a sum indexed by
collected multi-index decompositions. This omits multinomial multiplicities:
two derivatives split between two factors already give coefficient 2.
The implementation indexes ordered histories, retaining every term, and
uses the lower-order count `4*3^m` in place of the printed polynomial count.
The unspecified persistence constant is allowed to depend on m. No source
file or shared findings entry was changed.

The finite-order norm is the supremum over all ordered words; its same-order
comparison with the canonical source convention is proved. Pointwise
collision continuity is obtained from the proved higher-jet Sobolev
estimate instead of the audit's suggested weighted-L∞ route. Neither choice
adds a source premise or changes the claimed result. The frozen norm and
solution definition remain unchanged.

No remaining packet proof obligation or mathematical obstruction is known.
Independent statement/manifest promotion and the root import belong to the
orchestrator; no such promotion is claimed here.

READY wke-l2s
