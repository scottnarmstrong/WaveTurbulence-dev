# Packet INCOH-INST (pre-freeze): prove the Wave B2 anchor B2.2 `incoherentDecay` at its exact type

Read `COMMON.md` first. This finishes PL1.

**Goal.** Prove the B2.2 anchor `incoherentDecay` (TARGET Prop 5.1 `proplayer1`) **exactly as stated** in the B2 final
candidate `/home/scott/wt-scratch/waveb2-snap-final/WaveB2-Statements.lean`. Do it by instantiating your abstract
Proposition 5.1 (`Foundations/Incoh/Proposition51*.lean`, landed 541d4c8) with the actual layered regular couples and
trees.

The instantiation data comes from wt-torus's C2 LINKS:
- `/home/scott/wt-scratch/links`: links, `incoh_relation`, `incoh_unimodular`, `linkCoords_surjective`,
  `epsDec_eq_prod_links`, the squared Wick factor of F62;
- `/home/scott/wt-scratch/enhanced`: the tree versions of the matrices (`treeDecEquiv`, `treeLinkCoords_surjective`);
- `/home/scott/wt-scratch/layerreg`: coherence and layers.

Your HANDOFF already maps your carrier fields to C2's output. Build the instance and discharge every carrier field.

**Statement checks.**
- Use the NLS-BRIDGE type-audit pattern: a textual comparison plus an elaborated `Expr` comparison against the pinned
  anchor.
- The anchor quantifies over codes. Its meaning relies on the decoding obligations O1–O5 (REG-STRUCT,
  `B2CharacterizationProofs`). Use those exact statements.
- If anything in the anchor is false or unprovable as stated, stop and report it with a counterexample sketch.

**γ.** B2.2 is stated for γ ∈ (0, 1). F69b, the γ ≤ 1/2 issue, lives in the counting chain of `layergarden`, not in
Prop 5.1. If you find any γ-restriction needed here, report it at once.

**Where.** Scratch in `/home/scott/wt-scratch/incoh-inst/`; Foundations parts on your branch. Worktree
`/home/scott/WaveTurbulence-worktrees/wke-l2s`. Merge main first.

**Done.** No sorry, standard axioms only, a HANDOFF, then report `READY incoh-inst`.
