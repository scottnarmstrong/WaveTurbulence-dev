# Packet C3 SKELETON (pre-freeze): prime skeletons of couples and gardens, with uniqueness

Read `COMMON.md` first.

**Goal.** Blueprint packet C3 (`docs/blueprint/GRAPH.md` §E). Its nodes:

| node | source |
|---|---|
| `DH21.reduceprocess` | DH21 Props 4.13–4.16: the reduction process |
| `GAP.skeletonUniq` | the general-couple skeleton uniqueness, DH21 L833; wt-orch's REG-STRUCT audit R15-3 says this argument is not written in DH21 and is this packet's job |
| `DH21.structure2` | DH21 |
| `DH21.corcpl` | DH21 |
| `DH212.skeleton` | DH21-2 Props 4.4–4.6 |
| `T.propstructure2` | TARGET |

Maps: `~/wave-turbulence/maps/DH21.md` and `~/wave-turbulence/maps/T-part1.md` (search `propstructure2`,
`reduceprocess`, `skeleton`); FINDINGS E4 in the blueprint. C3 feeds V3 (REGRED), M7 (LFTWIST) and F2 (PLG).

**Inputs.**

- Your REG-STRUCT scratch (`/home/scott/wt-scratch/reg-struct/`): structure theorem, decoding, legal and dominant
  chains, counts.
- wt-torus's LINKS (`/home/scott/wt-scratch/links/`; read-only, copy with sha256).
- COMB-CORE and CANON scratch.
- The B2 drafts (`/home/scott/wt-scratch/waveb2/`). wt-orch has just edited them (B2-CL-4…CL-11: block connectedness,
  counts, the F61 sign of `specialWeight`). Re-copy and re-hash before you build on them.
- Snapshot 6 (`/home/scott/wt-scratch/waveb-snap-6/`, supersedes snapshot 5).

**Where.**

- Scratch: `/home/scott/wt-scratch/skeleton/`, namespace `WaveTurbulence.Resonant` or your REG-STRUCT namespace.
  Continue your conventions; no duplicate names.
- Worktree: `/home/scott/WaveTurbulence-worktrees/resonant`. Merge main first.

**Done.** No sorry; standard axioms only; HANDOFF written; report `READY skeleton`.
