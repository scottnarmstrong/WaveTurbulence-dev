# Packet M7 LFTWIST (pre-freeze): LF-twists and their cancellation

Read `COMMON.md` first. This continues your M5 MOLECPL and M6 TWIST.

## Goal

Blueprint packet M7 (`docs/blueprint/GRAPH.md` §E): TARGET's LF-twist construction and family cancellation. Search
`T-lftwist` in `~/wave-turbulence/maps/T-part2.md` for the line range, dependencies and consumers.

## Downstream

M7 is on the critical path:

- S1 (stage-1 combinatorics) needs M6 and M7.
- S2a (reduced splice definitions) and S4 (`subpro`) follow.
- G1–G3 (stage 2, excess) and V5 (vine estimates) consume them.

## Inputs

| Input | Location |
|---|---|
| Your TWIST and MOLECPL | `/home/scott/wt-scratch/molecpl` |
| LINKS, ENHANCED, LAYERREG (wt-torus) | `/home/scott/wt-scratch/links`, `/home/scott/wt-scratch/enhanced`, `/home/scott/wt-scratch/layerreg` |
| SKELETON, REGRED (wt-resonant) | `/home/scott/wt-scratch/skeleton`, `/home/scott/wt-scratch/regred` |
| CANON | the CANON scratch |
| COMB-CORE | the COMB-CORE scratch |
| Snapshot 9 | `/home/scott/wt-scratch/waveb-snap-9` |
| B2 final candidate | `/home/scott/wt-scratch/waveb2-snap-final` |

- REGRED records that LF-twist family construction is M7's job; it supplies the actual regional-factor locality you
  will need.
- Copy with sha256; never edit other workers' directories.

## Where

- Scratch: `/home/scott/wt-scratch/lftwist/`.
- Worktree: `/home/scott/WaveTurbulence-worktrees/an-fourier`. Merge main first.

## Done

No sorry, standard axioms only, a HANDOFF, then report `READY lftwist`.

## Possible interruption: signed `sumint`

If wt-gausssum's F79 kernel check confirms the sign issue, I will ask you to prove `SumintSigned`. That is a
generalization of your `sumint` proof with a sign on the nonlinear core form (FINDINGS F79); its exact statement is in
wt-resonant's `/home/scott/wt-scratch/vineest-s2` HANDOFF. You may be asked to interleave it.
