# Packet V3 REGRED (pre-freeze): skeleton reduction of K_𝒢 and VC-local expressions

Read `COMMON.md` first.

**Goal.** This is blueprint packet V3 (`docs/blueprint/GRAPH.md` §E). Its nodes are `T.regred`, the construction
`𝒦^𝕌_(𝒢)` (TARGET L1724–L1740, the reduction of `𝒦_𝒢` to the skeleton), and `T.vineest.S1`, Step 1 of `vineest`.
The map is `~/wave-turbulence/maps/T-part2.md`: search `T-regred` (L749) and `T-vineest`.

The chain after V3:

- V4 (vineest Step 2: the garden-level re-parametrization into `sumint` form) follows V3.
- V5 (the vine estimates) feeds the reduction, then `layergarden`.
- wt-cumul is building the `layergarden` spine (`/home/scott/wt-scratch/lg-spine`). Match its spine statements where
  they cover regred or vineest.

**Inputs.**

| What | Where | Notes |
|---|---|---|
| Your SKELETON | `/home/scott/wt-scratch/skeleton` | |
| Your REG-STRUCT | `/home/scott/wt-scratch/reg-struct` | |
| MOLE and CLCN | wt-nt, `/home/scott/wt-scratch/mole`, `/home/scott/wt-scratch/clcn` | Read-only. Mind CLCN's integration item C-1: re-point to the current `IsBlock`. |
| VINES | wt-gausssum, `/home/scott/wt-scratch/vines` | In progress. Vine (II) now includes m = 1 (FINDINGS F72, B2-CL-21). |
| SYS-DEFS | the `/home/scott/wt-scratch/sysdefs` and `duhamel` scratch | |
| Snapshot 7 | `/home/scott/wt-scratch/waveb-snap-7` | |
| B2 final candidate | `/home/scott/wt-scratch/waveb2-snap-final` | |

Copy what you need with sha256. Never edit other workers' directories.

**Where.** Scratch `/home/scott/wt-scratch/regred/`; worktree `/home/scott/WaveTurbulence-worktrees/resonant`. Merge
main first.

**Done.** No sorry, standard axioms only, a HANDOFF, then report `READY regred`.
