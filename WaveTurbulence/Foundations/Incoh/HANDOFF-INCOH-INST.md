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
