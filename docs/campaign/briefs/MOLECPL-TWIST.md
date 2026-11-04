# Packets M5 MOLECPL + M6 TWIST (pre-freeze): vines inside couples, and twist cancellation

Read `COMMON.md` first.

**Goal.** Blueprint packets M5 and M6 (`docs/blueprint/GRAPH.md` §E). Search `T-molecpl` and `T-twist` in
`~/wave-turbulence/maps/T-part2.md` for the line ranges and dependencies.

- **M5 MOLECPL.** How a vine (VC) sits inside a couple: the scenarios (II-a)–(II-e) and their analogues for the other
  vine types.
- **M6 TWIST.** The twisted couples: the involution that pairs couples so that their contributions cancel.

These open the critical chain M5 → M6 → M7 (LFTWIST) → S1 → the stage-1 reduction → the excess counts and rigidity.

**Inputs.**

| Source | Location | Notes |
|---|---|---|
| VINES (wt-gausssum) | `/home/scott/wt-scratch/vines` | Done. Templates include the **m = 1 vine (II)** (FINDINGS F72); hyper-block reading F71. |
| MOLE and CLCN (wt-nt) | `/home/scott/wt-scratch/mole`, `/home/scott/wt-scratch/clcn` | Re-point CLCN's IsBlock per its C-1 note. |
| REG-STRUCT, SKELETON (wt-resonant) | — | |
| B2 final candidate | `/home/scott/wt-scratch/waveb2-snap-final` | |
| Snapshot 8 | `/home/scott/wt-scratch/waveb-snap-8` | |
| Mechanical check of scenarios (II-a)–(II-e) at m = 1 | `/home/scott/wt-scratch/vine2-m1/enum_m1.py`, with its output | All 1152 placements fall in the five scenarios; twists are valid involutions that preserve the directed molecule, every bond vector and every phase ζΩ, and flip the sign of u2. Formalize these facts. |
| Research note | `docs/research/vine2-m1.txt` | |

Copy what you need with sha256; never edit other workers' directories.

**Where.** Scratch in `/home/scott/wt-scratch/molecpl/`; worktree `/home/scott/WaveTurbulence-worktrees/an-fourier`.
Merge main first.

**Done.** No sorry and only the standard axioms, plus a HANDOFF. Report `READY molecpl`, then `READY twist`.
