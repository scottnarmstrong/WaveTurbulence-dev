# Packet LG-SPINE (pre-freeze): the layergarden spine

Read `COMMON.md` first. This plays the role for B1.2 that your INDUCT played for B1.1.

## Goal

Prove the snapshot-7 B1.2 `layergarden` (`/home/scott/wt-scratch/waveb-snap-7/WaveB1-Statements.lean`; TARGET Prop
`layergarden` L761–L779) **from a minimal set of named intermediate statements**. The result is
`layergarden_of_spine : SpineInputs → LayergardenGate`, where `SpineInputs` is a conjunction of exactly stated
propositions, each a faithful transcription of a TARGET (or DH21/DH23) statement used in TARGET's proof of
`layergarden` (§§5–12).

Do the assembly logic yourself: the case splits, sums over gardens, the layering, the reduction chains and the
combination of bounds.

## Spine inputs

Each spine input must be:

- stated literally from its source, with line numbers in its docstring;
- the largest natural unit, since the spine is the map from here to the end;
- one of the Wave B anchors wherever one exists:
  - B2.1 `regularAsymptotics`
  - B2.2 `incoherentDecay` (TARGET Prop 5.1)
  - B2.3 `rigidity` (draft; held out)
  - B1.6 `sumint`
  - B1.7 `countLemma`
  - B1.8 `atomCountLemma`
  - B1.9 `quadExpSum2`
  - B1.10 `quadExpSum3`
  - B1.12 `layergardenFlower`

  They are in snapshot 7 and the B2 final candidate `/home/scott/wt-scratch/waveb2-snap-final`.

Expected inputs beyond the anchors:

- TARGET Props 6.1–6.3 (`proplayer2`–`proplayer4`) and `regref`;
- the vine estimates (`estnormalvine`, `vinechainlem`);
- the reductions (`subpro`, `finalmole`);
- the counting proposition `lgmolect` / (finalcount1) (TARGET L2114, L2192–L2197; DH23 Prop 9.6).

## Warning on `lgmolect` / (finalcount1)

FINDINGS F69b reports that this statement may be **false for 0 < γ ≤ 1/2** (the necklace counterexample; independent
referee in progress; `docs/research/dh23-prop96-case4.md`).

- State it as its own separate spine input.
- Keep the assembly modular, so that a repaired version (T-type blocks spliced as vines, or a restriction to
  γ > 1/2) can be dropped in.

## Output and conventions

`SPINE.md`: a table of every spine input with
- source lines;
- its consumer step in the assembly;
- the packet in `docs/blueprint/GRAPH.md` §E that will prove it, or "unowned".

Conventions:
- Scratch: `/home/scott/wt-scratch/lg-spine/`, namespace `WaveTurbulence.LGSpine`.
- Worktree: `/home/scott/WaveTurbulence-worktrees/cumul`. Merge main first.
- Copy what you need from other scratch dirs with their sha256; never edit them.

## Done

- `layergarden_of_spine` compiles, with no sorry and only the standard axioms.
- The verbatim type check against snapshot 7 passes.
- `SPINE.md` is written.
- Report `READY lg-spine`.
