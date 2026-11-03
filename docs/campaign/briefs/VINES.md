# Packet M4 VINES (pre-freeze) — vine and ladder templates, groups and coherence, `subsetvc`

Read `COMMON.md` first.

**Goal.** Blueprint packet M4 (`docs/blueprint/GRAPH.md` §E). TARGET Def `defvine` (L1384–L1394) and figure-defs
§1 (`docs/campaign/orch/figure-defs.md`); WAVE-B §3.4 and FINDINGS F19 for the vine/ladder template readings.
Prove:

- the vine templates and their basic structure (degrees, atom and bond counts after rung insertion, which templates
  are bad);
- the group decomposition and the vine coherence index (`T.cohmol`);
- TARGET Lemma `subsetvc`;
- the vine-like objects VC, HVC, DV, HV. These are **not** drafted yet. Draft them first as definitions next to the
  B2 vine draft, following TARGET literally, and record each reading in your HANDOFF.

Packet M9 VINEPARAM (molecule-level vine parametrizations (I)–(VIII) with ladders, F22) follows and is yours too
if M4 finishes.

**Statements to build on (do not edit the pinned copies):**

- the stage-2 B2 draft `/home/scott/wt-scratch/waveb2/WaveB2-Molecules.lean`: `IsLadder`, `IsLadderSet`,
  `VineType`, `VineTemplate`, `VineType.template`, `insertRungs`, `VineType.expand`, `IsVine`; design notes in
  `/home/scott/wt-scratch/waveb2/DESIGN.md` (vines around L194);
- the molecule basics proved by wt-nt (packet M1 MOLE) in `/home/scott/wt-scratch/mole/src/` (`Molecule*.lean`,
  `Garden*.lean`; summary in `/home/scott/wt-scratch/mole/HANDOFF.md`).

wt-nt owns `/home/scott/wt-scratch/mole/`. Never write there. Copy the files you need into your own scratch at
`/home/scott/wt-scratch/vines/`, and record the copied revision (sha256) so later merges are mechanical. Use
namespace `WaveTurbulence.Vine` for new declarations. If you need a molecule lemma that MOLE lacks, prove it
locally under `WaveTurbulence.Vine` and list it in your HANDOFF for dedupe at landing.

**Worktree:** `/home/scott/WaveTurbulence-worktrees/gausssum` (branch `w/count`). Merge main first. COUNT has landed
or is landing. Commit only HANDOFF or docs on the branch, since the Lean work is scratch until the Wave B freeze.

**Done:**

- M4 statements proved with no sorry and only the standard axioms;
- `HANDOFF.md` in `/home/scott/wt-scratch/vines/`;
- you report `READY vines`.

Then continue with M9.
