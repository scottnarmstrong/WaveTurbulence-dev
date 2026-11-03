# Packet D3 CANON (pre-freeze) — prove `canonicalCharacterization` (B1.11) and the truncation facts

You drafted the Wave B tier-B1 definitions and B1.11; the final check of snapshot 3 (`/home/scott/wt-scratch/waveb-snap-3/`)
is running and the freeze will follow (the orchestrator will tell you). Blueprint packet D3 (rows `T.canonequiv`,
`GAP.cmattrBij`, `T.defcanon`; near the critical path).

Work in untracked scratch `/home/scott/wt-scratch/canon/` against a local copy of snapshot 3 (do not edit the copied
definitions/statements); after the freeze you move the proofs into `WaveTurbulence/Foundations/Canon/**` (namespace
`WaveTurbulence.Canon`) importing the frozen files, and the orchestrator seals B1.11 from them.

Goals (sorry-free; do not end your turn at milestones):
1. Prove `canonicalCharacterization` exactly as drafted in snapshot 3 (equivalence of the criterion form `IsCanonG/C/H`
   with TARGET Def 3.7's inductive construction, and uniqueness of the construction data for gardens, couples and
   flower gardens (kind 0), with the restricted attachment relation of stage-1 R1).
2. The decoration-shift bridge `truncSum ↔ truncSumC` and the truncation facts the gates use (`truncSum_untruncated`
   and its relatives), as listed in your DESIGN.md glue list.
3. The finiteness/enumeration lemmas for canonical layered gardens of bounded order and depth that later counting
   packets (`T.layerreg2`, M8) need.
Then `READY canon`. (If the B2 audits arrive meanwhile, the orchestrator will tell you whether to fold them in first.)
