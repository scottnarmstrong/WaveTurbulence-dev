# Packet C4 LAYERREG (pre-freeze): coherent layered regular objects and layering counts

Read `COMMON.md` first.

**Goal.** Blueprint packet C4 (`docs/blueprint/GRAPH.md` §E): TARGET `layerreg1`, `layerreg2` (Props 4.9, 4.10:
coherent layered regular couples and trees, and the counting of layerings). See `~/wave-turbulence/maps/T-part1.md`
(search `T-layerreg1`, `T-layerreg2`; the proof is at L910–L931, by induction via `propstructure`, `deflink` and
`defcoh`).

C4 feeds:
- L3 (TARGET Props 6.1–6.2) and L4 (Prop 6.3), on the critical path through PL23 and PL4;
- M7 (LFTWIST) and F2 (PLG).

**Inputs.**
- Your LINKS and ENHANCED scratch: links, coherence and the incoherency index, the dominant and encoded objects.
- REG-STRUCT (`/home/scott/wt-scratch/reg-struct/`, wt-resonant, done). It is read-only: copy what you need and
  record its sha256.
- CANON (`/home/scott/wt-scratch/canon*`: canonical layered gardens; `canonicalCharacterization` is proved).
- Snapshot 6 (`/home/scott/wt-scratch/waveb-snap-6/`).
- The B2 drafts. wt-orch is finishing CL-12 now, so re-copy them and record the hashes.

**Open reading from ENHANCED.** Your R4 says `ζ*(𝒬)` is B1's `Garden.zeta`, not yet bridged to B2's `zetaOfTrees`
(used in `RegCpl.app`). Prove that bridge in this packet if C4 touches the net sign. Otherwise list it in your HANDOFF.

**Where.** Scratch `/home/scott/wt-scratch/layerreg/`, namespace `WaveTurbulence.Links`. Worktree
`/home/scott/WaveTurbulence-worktrees/torus-fourier`; merge main first.

**Done.**
- No sorry, and only the standard axioms.
- HANDOFF written.
- `READY layerreg` reported.
