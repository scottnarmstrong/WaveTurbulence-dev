# Packet RA1-TREES: DH23 Prop 6.1 for regular trees (the RA1Tree obligation of B2.1)

Read `COMMON.md` first.

**Goal.** Prove the `RA1Tree` obligation **word for word**. Its exact statement is in
`/home/scott/wt-scratch/regref/OBLIGATIONS.md`, and `HANDOFF.md` Part 2 there explains how it is used.

- `RA1Tree` is the regular-tree half of DH23 Prop 6.1 (`regcpltreeasymp`, `Revision_Submit.tex` L920–L934, proof
  L945–L1180; trees via DH21 Prop 6.10, L1698–L1710).
- It is stated for orders up to `N_{p+1}^4` (F33).
- The tree remainder is measured in the landed `Fourier.mixedRestrictionNorm`. After snapshot 9 (F80), B1's fixed
  `XNorm` is the same norm.
- The constants `C` and `δ₁` must not depend on the order exponent `A`.

**Why.** wt-torus proved the whole B2.1 anchor `regularAsymptotics` from `RA1Couple` and `RA1Tree`. wt-ansob is proving
`RA1Couple` (couples first, packet RA1). You take the trees half in parallel, which closes B2.1 sooner.

**Inputs.**

| Input | Where |
|---|---|
| DH21 Prop 5.1 for trees (wt-wke, landed) | `Foundations/ClassJR/MCProp51T*`, `HANDOFF-MAINCOEFT.md`; unconditional with REG-STRUCT's tree decoding |
| wt-ansob's RA1 foundations (landed on main) | `WaveTurbulence/Foundations/RegAsymp/*`: `SpecialSign` (F61 sign), `Normalization`, `NormalizedApproximation` (applies the landed `dh23_prop_6_4`), the Gevrey/coefficient envelopes, `CoordinateDerivative`, `WickGain`, `EnvelopePointwise`, `InverseProfile*` |
| wt-ansob's scratch | `/home/scott/wt-scratch/regasymp` (`src/RegAsympDraft`, `PROGRESS.md`) |
| APPROXNT | `Foundations/ApproxNT` |
| wt-torus's REGREF | `/home/scott/wt-scratch/regref`: tree trace argument, leafwise kernels `Leafwise.lean` |
| Your own PL1 / INCOH-INST | carrier and instantiation patterns |

Reuse the RA1 foundations; **never duplicate** them. Coordinate any shared lemma with wt-ansob through its
`PROGRESS.md` / `HANDOFF.md`. Before adding a Foundations file, tell wt-ansob its name, so there are no collisions.

**Where.** Scratch `/home/scott/wt-scratch/ra1-trees/`; Foundations parts under `Foundations/RegAsymp/Tree*.lean` on
your branch. Worktree `/home/scott/WaveTurbulence-worktrees/wke-l2s`. Merge main first.

**Done.** `RA1Tree` proved at its exact type, with no sorry and only standard axioms, plus a HANDOFF. Then report
`READY ra1-trees`.
