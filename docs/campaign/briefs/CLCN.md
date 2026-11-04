# Packet M3 CLCN (pre-freeze): the (CL)/(CN) dichotomy, block chains, `cnblock`

Read `COMMON.md` first.

## Goal

Blueprint packet M3 (`docs/blueprint/GRAPH.md` §E), with nodes `T.block_clcn` (the (CL)/(CN) dichotomy for blocks and
splicing), `T.blockchainprop` and `T.cnblock` (Prop `cnblock`: general gardens `R ≥ 2`, components, the
`L^{−(R−1)(1/4+…)}` gain). Find them in `~/wave-turbulence/maps/T-part2.md` (search `block_clcn`, `blockchainprop`,
`cnblock`), which gives the TARGET line ranges, consumers and Lean notes. Downstream, `blockchainprop` feeds SUBPRO (S4)
and `cnblock` feeds the congruence step (`defcong`).

## Inputs

- Your MOLE scratch, `/home/scott/wt-scratch/mole/`: molecules, root-compatible decorations, reconstruction, blocks
  and hyper-blocks with the connected convention (FINDINGS F57), and the cut and counting APIs.
- COMB-CORE scratch.
- The B2 draft, `/home/scott/wt-scratch/waveb2/WaveB2-Molecules.lean`. Its ladders now follow B2-CL-3, so
  `maximalLadders` is wt-ansob's `SourceLadder` (FINDINGS F53).
- wt-ansob's DEGEN (`/home/scott/wt-scratch/degen/`). It is read-only for you: copy what you need and record its sha256.
- The landed counting lemmas, `Foundations/CountLemmas/CountTools.lean`.

## Rules

Keep the connected-block convention (F57). Record every reading and erratum in the HANDOFF, as you did for MOLE.

## Where

- Scratch: `/home/scott/wt-scratch/clcn/`, namespace `WaveTurbulence.Mole`. Continue your MOLE conventions, with no
  duplicate names.
- Worktree: `/home/scott/WaveTurbulence-worktrees/nt-circle`. Merge main first.

## Done

- No sorry; standard axioms only.
- `HANDOFF.md` written.
- Report `READY clcn`.
