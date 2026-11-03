# wt-orch Task 3 — freeze check, figure-only definitions, F14

First `git merge main` in your worktree (Wave A was frozen at 8d1d2e3, ruling D6 in docs/DECISIONS.md).

## 3a. Freeze check (short)

Verify independently that each of the 15 frozen files in `WaveTurbulence/Frozen/` contains exactly the
declaration text of the approved draft (`/home/scott/WaveTurbulence-dev/scratch/Draft.lean`, sha256 938afa97…,
the same text you audited as v2 plus O6–O8), up to the packaging described in D6 (one declaration per file,
markers, `by sorry` between markers). Run `scripts/check_index.sh` (after `git add -A` of nothing — it checks the
index) and `python3 -I scripts/abi_hash.py --root . --manifest manifest/frozen.json` (check mode). Report in
`docs/campaign/orch/audits/WaveA-freeze-check.md`.

## 3b. Figure-only definitions (main task)

TARGET §7–§8 and DH23 §4–§5 define several objects only by figures (FINDINGS F12, F19, F20, F26). The map
`/home/scott/wave-turbulence/maps/T-part2.md` transcribed them from the PNGs, marked "[from figure]"; DH21/DH23 maps
did likewise for mini-couples/mini-trees. Those transcriptions must be checked before any Lean definition of them is
drafted (Wave B).

You can read images: the figures are in `/home/scott/wave-turbulence/references/src-2311.10082/` (e.g. `Vines.png`,
`vineAnnotated.png`, `Block_Mole.png`, `Cut.png`, `OperAB.png`, `twist_dec.png`, `MiniCpl.png`, `MiniTree.png`,
`Flowertree.png`, `RegChain.png`, `LayerGarden.png`, `CanonGarden.png`) and in the DH23/DH21 source dirs
(`src-2301.07063/`, `src-2104.11204/`). For each figure-defined object used by TARGET (vines (I)–(VIII) with joints
and bond directions, ladders and their insertion rules, (CL)/(CN) vines, unit twists and LF twists with their case
table, cuts, mini-couples/mini-trees and their codes, regular chains, flower trees/gardens, canonical layered
gardens):
1. look at the figure(s) and the surrounding TeX;
2. write a precise textual definition in graph terms (atoms, bonds, directions, labels, degrees, where ladders may be
   inserted, which nodes are free), suitable to become a Lean definition;
3. compare with the map's transcription and list every discrepancy;
4. flag every point where the figure is ambiguous and state the reading you recommend and why (what the proofs need).

Write `docs/campaign/orch/figure-defs.md` (commit on w/orch, section by section so partial work survives).

## 3c. F14

FINDINGS F14: the DH21 map reports a counterexample to DH21-2 Prop 6.3 (χ ≤ m − R/2 for mixed gardens). Check the
claim against DH21-2 (`src-2110.04565/WKE_Hierarchy-Revised.tex`), and determine whether TARGET depends on that
proposition (TARGET L370 and every [DH21-2] citation). Append the verdict to `figure-defs.md` or a separate audit file.

When done print `READY task3` and wait. Same rules as before (no subagents, one `lake env lean` at a time, no pushes).
