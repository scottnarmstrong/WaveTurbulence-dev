# Packet C5 ENHANCED (pre-freeze): dominant and enhanced dominant couples and trees, equivalence, encoded trees

Read `COMMON.md` first.

**Goal.** Blueprint packet C5 (`docs/blueprint/GRAPH.md` §E), nodes:

- `DH21.defstd`: dominant couples and trees;
- `DH21.equivcpl`: the equivalence classes;
- `T.defencpl`: TARGET Def 6.4, L1126–L1137, enhanced dominant couples and equivalence;
- `T.defentree`: TARGET Def 6.5, L1138–L1144;
- `DH21.encoded`: encoded trees.

Maps: `~/wave-turbulence/maps/T-part1.md` L1136ff and `~/wave-turbulence/maps/DH21.md` (search `defstd`, `equivcpl`,
`encoded`). C5 is on the critical path. It feeds:

- J4: DH21 Lemmas 7.1–7.3 and Props 7.4, 7.5 (cancellations);
- J5, J6, J7;
- RA2 (TARGET `regref`).

Its definitions are B2 freeze candidates ("freeze if regref1 is frozen"). Draft them literally and record every reading.

**First (small).** The tree version of the incohproof1 integer matrices, which you did not do in LINKS. wt-l2s's PL1
needs the tree case (TARGET L1060–L1092).

**Inputs.**

- Your LINKS scratch (`/home/scott/wt-scratch/links/`).
- REG-STRUCT (`/home/scott/wt-scratch/reg-struct/`, wt-resonant; read-only, copy with sha256).
- The B2 drafts (`/home/scott/wt-scratch/waveb2/`). wt-orch is editing `WaveB2-Molecules.lean` and the §4 statements
  right now (Task 19: block connectedness, counts), so re-copy and re-hash before you build on them.
- Snapshot 6 (`/home/scott/wt-scratch/waveb-snap-6/`). It supersedes snapshot 5; Core and System are byte-identical.

**Coordination.** wt-wke is proving DH21 Prop 5.1 (J3) and will consume your dominant and encoded objects in J4. It
also has the open sign question FINDINGS F61 (DH21 Lemma 7.3 vs 5.8). If your definitions touch the `Z`-expansion
signs, note what you find in your HANDOFF.

**Where.**

- Scratch: `/home/scott/wt-scratch/enhanced/`, namespace `WaveTurbulence.Links`. Continue your conventions.
- Worktree: `/home/scott/WaveTurbulence-worktrees/torus-fourier` (branch `w/approxnt`). Merge main first.

**Done.** No sorry; standard axioms only; HANDOFF written; report `READY enhanced`.
