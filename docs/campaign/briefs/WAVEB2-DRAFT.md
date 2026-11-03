# Packet WAVEB2-DRAFT — exact Lean drafts of the Wave B tier B2 definitions and statements

Same rules as `WAVEB-DRAFT.md` (untracked drafts, never committed; work in `/home/scott/wt-scratch/waveb2/`). Inputs:
`docs/blueprint/WAVE-B.md` §2.7–§2.9 and §4.11–§4.13 (B2: `regularAsymptotics` (regref1), `incoherentDecay`
(proplayer1), `rigidity` (lgmolect)), `docs/campaign/orch/figure-defs.md` (checked textual definitions: mini-couples
and mini-trees with codes, operations A/B, regular chains, links, vines/ladders (F37), twists (F38), cuts with half-edges
(F40)), `docs/campaign/orch/audits/GRAPH-topology.md` (I9: MOL.countq; P5, P6), and your B1 drafts (build on their
carriers; if the B1 audit changes them, adapt).

Stages (report `READY waveb2-stage<k>` after each, then continue):
1. Regular couples and trees: mini-couples/mini-trees, operations A/B, regular couples/trees, structure data (the
   recommended inductive `RegCode` with an injective decoding map, WAVE-B §2.7 item 3), links, 𝒩^ch (DH21 Def 4.11),
   dominant objects, special subsets Z, time factors 𝒥ℬ*, momentum factors ℳ* via the resonant measure (use the landed
   `Foundations/Resonant/**` of wt-resonant), leading terms (K*_Q)_app, coherence/incoherency index.
2. Molecules (half-edge encoding, F40), decorations of molecules, blocks, vines/ladders (F37 reading k ≥ 0), gaps
   SG/LG/ZG, cuts, the counting quantities 𝔈, 𝔄, 𝔇𝔢𝔳 (`MOL.countq`, review I9) — generic in the molecule.
3. Statements B2.1 `regularAsymptotics` (with the order range up to N_{p+1}^4, F33 route R14), B2.2 `incoherentDecay`,
   B2.3 `rigidity` (the abstract hypotheses of the rigidity theorem are a design item: propose them, argue in the memo).
Probes as before (sorry-free non-vacuity, summability/finiteness). Changelog in your DESIGN.md.
