# Blow-up implementation check (2026-11-03)

This is worker-side source and implementation evidence. It does not promote
a frozen anchor or a manifest node; those remain orchestrator-owned.

## Pinned sources and exact export

- Research proof: `docs/research/git20-general-d.md`, §10 and §12;
  SHA256 `a5be8c25934effaa3876e14da5f306d1cfebb7c9c6b1f2db5eb65eddc26b137f`.
- TARGET Appendix C, lines 2487–2528; SHA256
  `493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb`.
- Audit `docs/campaign/orch/audits/GIT20-general-d.md`, §3.
- Exact export: `WaveTurbulence.WKEL2.wkelwp_blowup` in `Blowup.lean`.
- Maximal time: the actual landed `WaveTurbulence.WKE.tauMax` from
  `Foundations/WKE/Lifespan.lean`, not a replacement maximal time.

The export is exactly frozen `wkelwp` conjunct 3 after substituting
`WKE.tauMax φin` for its existential maximal-time witness. Dimension `d`,
`3 ≤ d`, and Schwartz initial data are the same outer binders. The theorem
assumes only finiteness of this maximal time, then quantifies over every
real exponent above the strict source threshold and every real threshold M.
Its conclusion supplies nonnegative τ₀ strictly below the maximal time and
bounds every later endpoint norm, for every source solution on that closed
interval. The strict inequalities and all quantifier orders are retained.
There is no assumed trilinear estimate, existence theorem, persistence
bound, solution equivalence, or maximal-time equality in its premises.

## Definition-body and carrier checks

The four frozen files are unchanged. SHA256:

| File | SHA256 |
|---|---|
| `Mom.lean` | `22aaac77bd1887265c3d8fec49f6975ae68311e18529151740ba0e74557e5d87` |
| `CollisionOp.lean` | `5246fe71b1082f7aa3f784220e77849dcb9a1debe013ebb06e7e489636a748c4` |
| `IsWKESolution.lean` | `2529844f73ade481a1295d3399c8f3967f98d290e54adb52f00fbf6908c2d178` |
| `WeightedL2Norm.lean` | `92726d25128176c80d96bd3c18b475967dc900fdcec08f9cf5df71c9550fc52f` |

The base Banach model is actual real `Lp 2 volume` of the exact weighted
function. Its Schwartz embedding has norm exactly `weightedL2Norm`.
Finite jet spaces complete the actual faithful Schwartz jet range with its
finite supremum L² norm. Canonical moment-before-derivative bounds imply
ordered-jet bounds with constant `(m+1)!`, and the converse has constant one,
at the same total order (`CanonicalJetEquivalence.lean`).

## Consumption and the three supporting facts

1. `weightedSobolevLetterCLM_collisionTerm` (`JetClosedIdentity.lean`) extends the
   exact coordinate Leibniz and weight identities to all completed inputs,
   using actual bounded closed extensions of moments/derivatives and joint
   Schwartz density. No identity is supplied as a hypothesis.
2. `isWKESolution_iff_weightedL2Mild` (`SolutionEquivalence.lean`) proves equivalence
   of the frozen source class and the genuine base mild equation. For an
   arbitrary base mild curve, `exists_isWKESolution_eq_base_mild` reconstructs
   its actual Schwartz representative with equality of trajectories.
   Pointwise field continuity is proved using the higher-jet Sobolev
   evaluation estimate; a bare L² bound is never treated as point evaluation.
3. `SchwartzJetTopology` proves equivalence with the actual Schwartz topology.
   `exists_schwartz_of_compatible_jets` (`SchwartzReconstruction.lean`) proves every
   compatible family of completed jets has an actual Schwartz representative.
   The construction uses seminorm-absolutely-summable series and does not
   assume a Schwartz completeness instance.

`JetAPriori` proves the tame Gronwall estimate with one constant chosen before
all shorter solution intervals. `CubicContinuation` then uses finitely many
uniform positive Picard steps. `JetPersistence` lifts a base solution over
its entire closed interval to every finite jet order and reconstructs a
source solution. `MaximalTimeEquality` identifies both base and every finite
jet maximal time with `WKE.tauMax`, for every admissible s.

`SchwartzPicard` supplies source Schwartz existence on precisely
`[8(‖collisionBanach‖+1) weightedL2Norm(s,φin)^2]⁻¹` for nonzero initial data;
the zero Banach trajectory is global. `SchwartzContinuation` supplies a
positive extension time uniform over each bounded endpoint base norm.

For the full blow-up conclusion, set R=max(0,M), choose that uniform
extension time δ>0, and take τ₀=max(0,τmax.toReal−δ/2). If a later endpoint
norm were ≤M, uniform continuation and reconstruction would produce a
source solution past τmax, contradicting the defining supremum. This proves
the full eventual lower bound, not merely an unbounded subsequence.

## Validation and limits of this check

The focused `Packet` build exited 0, reporting 9247 jobs. The thirteen-result
`BlowupAxioms.lean` and eleven-result `FinalAxioms.lean` probes exited 0.
Every printed result, including the exact blow-up export, depends exactly on
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` or custom axiom occurs.
No frozen theorem or provider is imported. The root import, manifest,
findings ledger, and frozen anchors were not edited.

This records implementation/source correspondence; independent campaign
statement auditing and landing remain with the orchestrator.
