# Packet G6 MOLEPROP13 (pre-freeze) — DH23 Propositions 10.1 and 10.3, then G4 APPB-OPS

Read `COMMON.md` first. Blueprint packet G6 (`docs/blueprint/GRAPH.md` §E): DH23 Props 10.1 and 10.3
(`DH23.moleprop1`, `DH23.moleprop3`), the molecule counting propositions of DH23 §10 that consume your DEGEN results
(G0) and the landed counting lemmas (NT8: `WaveTurbulence/Foundations/CountLemmas/`, interface `CountTools.lean`;
`countLemma_bound`, `atomCountLemma_bound`, `dh23_second_pair_bound`). DH23 source: the pinned TeX in
`~/wave-turbulence/sources/` and the map `~/wave-turbulence/maps/DH23*`.

Inputs: your DEGEN scratch (`/home/scott/wt-scratch/degen/src/Degen/`, aggregate `Degen.All`) and wt-nt's MOLE basics
(`/home/scott/wt-scratch/mole/src/`, read-only — copy what you need, record the sha256; never write there). Use the
selected-ladder reading (FINDINGS F53) where ladders enter; do not rely on the B2 draft `IsLadder`'s induced-card
clause. State each proposition as close to DH23 as the molecule carriers allow; record every reading or erratum in
your HANDOFF (and propose a FINDINGS line in it). Scratch: `/home/scott/wt-scratch/moleprop13/`, namespace
`WaveTurbulence.MoleProp`. If MOLE lacks a definition you need, draft it locally and flag it for reconciliation.

Then continue with G4 APPB-OPS (DH23 Appendix B operations TB…2R; the figure-defined groups must be transcribed first,
see `docs/campaign/orch/figure-defs.md`), same scratch conventions, `READY appb-ops`.

Worktree: `/home/scott/WaveTurbulence-worktrees/an-sob` (merge main first). Done: G6 proved with no sorry and the
standard axioms only, HANDOFF written, `READY moleprop13`.
