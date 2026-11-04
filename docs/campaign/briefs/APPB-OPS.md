# Packet G4 APPB-OPS (pre-freeze): the operations of DH23 Appendix B

Read `COMMON.md` first.

## Goal

Blueprint packet G4 (`docs/blueprint/GRAPH.md` §E). The target is DH23 Appendix B, "The algorithm for large gap
molecules" (`Revision_Submit.tex` L2162–L2292). The map is `~/wave-turbulence/maps/DH23.md` §13. The operations are:

- (TB-1N), (TB-2N): triple bond;
- (BR-N): bridge removal; the map flags a sign inconsistency "Δν = 2" vs "2 − 4 = −2", so check it and record it;
- (3S3-1N…5G), (3D3-1N…6G), (3D4-G), (3S2-G), (3R-1N/2G);
- (2R-1F…4F).

Each operation is a rewrite `M_pre → M_pos`. For each, prove:

- **Graph effect:** the exact change of (χ, ν, V_3, the special-bond count).
- **Deviation bound:** the class N (normal: `≲ (log L)^C`), F (fine: `≲ L^{−η/2}`) or G (good: `≲ L^{−5γ₀/8}`), via
  the basic counting estimates (`basiccount(1)–(4)`) and DH21 Lemma 9.14 for bridges. Your DEGEN work has 9.14's cut
  identity.

Packet G5 APPB-ALG follows: the algorithm loop (L2293–L2342), termination via the potential function, the count of
good operations, and DH23 Prop 10.2.

## Pitfall: the figures

The atomic groups are defined by figures that are **not in the TeX**: `3S3.png`, `3S3New.png`, `3D3.png`, `3D3New.png`,
`3D4.png`, `3S2.png`, `3RProof.png`. Transcribe each group from the operation's text first, with the degree and bond
conditions it states. Check the figures' surviving descriptions in `docs/campaign/orch/figure-defs.md` and FINDINGS
F19–F26. Record every transcription in your HANDOFF as a reading for review.

## Inputs

- **Your MOLE and CLCN scratch:** the molecules, cuts, deviation API, with the connected-block convention (F57).
- **wt-ansob's DEGEN** (`/home/scott/wt-scratch/degen/`), with Lemma 9.14 and the degenerate atoms. Read-only: copy
  what you need and record the sha256.
- **The landed counting lemmas**, `Foundations/CountLemmas/CountTools.lean`.
- **The B2 draft's operation-bound definitions:** `IsDeviation`, `𝔄_pre ≤ ℐ·𝔄_pos` (F59, CL-7).

## Coordination

wt-ansob is proving DH23 Props 10.1 and 10.3 (G6). Its brief listed G4 next; G4 is now **yours**, and wt-ansob has been
told. G7 MOLEPROP4 (DH23 Lemmas ylem1/2, Prop 10.4) will consume your operations.

## Where

- **Scratch:** `/home/scott/wt-scratch/appb/`, namespace `WaveTurbulence.Mole`.
- **Worktree:** `/home/scott/WaveTurbulence-worktrees/nt-circle`. Merge main first.

## Done

- No sorry; standard axioms only.
- `HANDOFF.md` written.
- Report `READY appb-ops`, then continue with G5.
