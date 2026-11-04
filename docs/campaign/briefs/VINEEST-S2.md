# Packet V4 VINEEST-S2 (pre-freeze): vineest Step 2

Read `COMMON.md` first. This continues your V3 REGRED (vineest Step 1).

## Goal

Blueprint packet V4 (`docs/blueprint/GRAPH.md` §E), node `T.vineest.S2`. Map: `~/wave-turbulence/maps/T-part2.md`,
search `T-vineest`.

Step 2 is the garden-level re-parametrization that brings a vine-chain contribution into `sumint` form. The `sumint`
statement (B1.6) is **proved**; see `Foundations/Sumint` after the freeze, or `/home/scott/wt-scratch/sumint` now. So
the output of Step 2 must match the hypotheses of the B1.6 anchor in snapshot 9 exactly.

## Inputs

| Input | Location / status |
|---|---|
| REGRED (yours) | `/home/scott/wt-scratch/regred` |
| VINEPARAM, the molecule-level vine parametrizations (wt-gausssum, M9, in progress) | `/home/scott/wt-scratch/vines` or `/home/scott/wt-scratch/vineparam` |
| sumint (proved) | `/home/scott/wt-scratch/sumint` |
| LINKS, ENHANCED (wt-torus) | done |
| Snapshot 9 | `/home/scott/wt-scratch/waveb-snap-9` |
| B2 final candidate | `/home/scott/wt-scratch/waveb2-snap-final` |

- Take VINEPARAM's statements as named obligations until it lands, matching wt-gausssum's statements word for word.
  Coordinate through its HANDOFF / PROGRESS files, never through its tmux pane.
- The vine family includes the m = 1 vine (II) (FINDINGS F72).
- TARGET Step 2(C-ii) has a sign issue (FINDINGS F79): use the signed core normal forms that wt-gausssum adopts.
- Keep the nonzero-gap / diagonal boundary case separate, as you did for Step 1 (F21).

## Where

- Scratch: `/home/scott/wt-scratch/vineest-s2/`.
- Worktree: `/home/scott/WaveTurbulence-worktrees/resonant`. Merge main first.

## Done

- No sorry, standard axioms only.
- HANDOFF written.
- Report `READY vineest-s2`.
