# Packet J4 CANCEL7: DH21 §7 cancellations (Lemmas 7.1–7.3, Props 7.4, 7.5), with the F61 sign

Read `COMMON.md` first.

## Goal

Blueprint packet J4 (`docs/blueprint/GRAPH.md` §E). The map is `~/wave-turbulence/maps/DH21.md` L333–L340.

- **Lemma 7.1** (`regchaincancel1`, L1715–L1725).
- **Lemma 7.2** (`regchaincancel2`, L1726–L1731): cancellation for non-dominant legal partitions.
- **Lemma 7.3** (L1732–L1746): **with the corrected sign** (FINDINGS F61, CONFIRMED). The χ_∞ part of
  `I_{εα}I_{μ−εα}` is `−χ_∞(α)/(επiα)·I_μ`. Your Lean statement must carry the `−`. The derivation is in wt-wke's trace
  `/home/scott/wt-scratch/wke/F61-sign-trace.md`.
- **Prop 7.4** (`maincancel`, L1748–L1765): for regular non-dominant Q, `𝒥B̃_{Q,Z} = 0`.
- **Prop 7.5** (`regcplcal`, L1767–L1807): for dominant Q and special Z, **corrected**:
  `𝒥B̃_{Q,Z} = (−1)^{|Z|} 𝒥B̃_Q`, with `𝒥B̃_Q` given by the recurrences (recurtype1)/(recurtype2). DH21's
  "independent of Z" is false (F61).

## What is landed and in progress

| item | where |
|---|---|
| class J/R operators, DH21 Lemmas 5.3–5.10 (landed, by wt-wke) | `Foundations/ClassJR/**` |
| `iker_comp_decompP` (the `T₀ = −I_μ` term; audit W1 asked to expose it) | `Lemma58.lean` |
| `lemma510` (Lemma 5.10) | `Chain2.lean` |
| DH21 Prop 5.1 (J3, wt-wke, **in progress** on branch `w/jr-ops`) | — |
| dominant couples, special sets, equivalence, encoded trees, net signs (your C5) | `/home/scott/wt-scratch/enhanced/` |
| links (your LINKS) and layer structure (your LAYERREG) | your scratch dirs |
| regular-couple structure theorem (REG-STRUCT, wt-resonant) | `/home/scott/wt-scratch/reg-struct/` |

Prop 7.4/7.5 consume Prop 5.1's `B̃_{Q,Z}` decomposition. Coordinate with wt-wke:

- read its J3 progress on `w/jr-ops` and its `HANDOFF-JR2.md`;
- state Prop 5.1 exactly as wt-wke states it (or will), as a named obligation if it has not landed;
- **never duplicate** wt-wke's ClassJR declarations;
- use your own namespace (`WaveTurbulence.Cancel`).

## First item (small)

The ζ* bridge you listed as open: B1's `Garden.zeta` vs B2's `zetaOfTrees` in `RegCpl.app`. Prop 7.5's recurrences and
TARGET `regref` use the net sign.

## Where

- **Foundations parts:** statement-independent operator and integral identities go on your branch, under
  `WaveTurbulence/Foundations/Cancel/`.
- **Scratch parts:** parts that need the Wave B garden or couple objects go in `/home/scott/wt-scratch/cancel/`.

Worktree: `/home/scott/WaveTurbulence-worktrees/torus-fourier`. Merge main first.

## Done

- No sorry; standard axioms only.
- `HANDOFF.md` written.
- Report `READY cancel7`.
