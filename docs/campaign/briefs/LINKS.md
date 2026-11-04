# Packet C2 LINKS (pre-freeze): links of branching nodes, coherence, auxlem, tree localization

Read `COMMON.md` first.

## Goal

Blueprint packet C2 (`docs/blueprint/GRAPH.md` §E), with these nodes:

| node | source |
|---|---|
| `DH21.branchpair` | DH21 Prop 4.3, L729: existence and uniqueness of the pairing of branching nodes in regular couples |
| `DH21.defchoice` | DH21 |
| `GAP.linkXY` | the (x,y) relation, FINDINGS F16 |
| `T.deflink` | TARGET Prop 4.6, L874–L882 |
| `T.defcoh` | TARGET Def 4.7, L885–L887: coherent layered regular objects and the incoherency index |
| `DH21.auxlem` | DH21 |
| `DH23.explem` | DH23 |
| `T.treelemma` | TARGET L2422: tree localization lemma |

Maps: `~/wave-turbulence/maps/T-part1.md` L857–L930 and `~/wave-turbulence/maps/DH21.md`.

This packet is central. Its consumers are PL1 (TARGET Prop 5.1, now with wt-l2s), J1, C3, C4, C5, L1 and RA1.

## Inputs

- Regular couples and chains: the B2 stage-2 draft `/home/scott/wt-scratch/waveb2/WaveB2-Regular.lean`
  (`RawRegular`, `IsRegularCouple`, `IsRegularTree`, `RegCpl`, `RegChain`, `RegCpl.pairsAt`, …), with notes in
  `/home/scott/wt-scratch/waveb2/DESIGN.md`.
- Snapshot 5: `/home/scott/wt-scratch/waveb-snap-5/` (Core, System).
- The REG-STRUCT structure theorem is in progress with wt-resonant, in `/home/scott/wt-scratch/reg-struct/`.
  That directory is read-only for you: copy what you need and record its sha256. Never write there.
- COMB-CORE and CANON scratch, for garden lemmas.

## Coordination with PL1

wt-l2s is proving TARGET Prop 5.1 against a local link structure in `WaveTurbulence.Incoh`. Its fields will be
listed in `WaveTurbulence/Foundations/Incoh/HANDOFF.md` on branch `w/wke-l2s` once it exists.

- Your link construction (`deflink`) must produce exactly that structure for layered regular couples and trees:
  - the pairing of branching nodes;
  - the variables `x_𝔫 = k_{𝔫1} − k_𝔫` and `y_𝔫 = k_𝔫 − k_{𝔫3}`;
  - the unimodular relation `incohproof1` (TARGET L985);
  - the incoherence index.
- If its fields do not match the source, say so in your HANDOFF and in a QUESTION line, and I will reconcile.

## Where

- Untracked scratch: `/home/scott/wt-scratch/links/`, namespace `WaveTurbulence.Links`.
- Statement-independent lemmas go into Foundations on your branch.

## Worktree

`/home/scott/WaveTurbulence-worktrees/approxnt` (branch `w/approxnt`). Merge main first; APPROXNT is landing now.

## Done

- C2 nodes proved with no sorry and only the standard axioms;
- `HANDOFF.md` written in the scratch directory;
- `READY links`.
