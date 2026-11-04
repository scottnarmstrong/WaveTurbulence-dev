# Packet G7 MOLEPROP4 (pre-freeze, revived): DH23 §10.4 with the repairs

Read `COMMON.md` first.

## Goal

Prove DH23 §10.4 (`Revision_Submit.tex` L1930–L1990), in its **repaired** form.

| Item | Statement |
|---|---|
| ylem1′ | Replaces L1937–L1938; exact text in `docs/research/ylem1-investigation.md` §"Proposed repair" (R1). If 𝕄′ is Q or T, then 𝕄 is (1) a vine closure (II)–(VIII), with vine (II) **including m = 1** (FINDINGS F72), or (2) Q or T itself, or (3) T₁, or (4) Z_m(T_n, ℓ′). |
| ylem2 | L1950. Also prove the "not-removed" variant used in Theorem A (`docs/research/case4-gamma-above-half.txt`). |
| Prop 10.4(1) | L1959. Its length-1 omission is exactly the m = 1 vine (II) (F72). |
| Prop 10.4(2)′ | Hypothesis "not Y-exceptional" instead of "not formed from a vine" (repair R2). The proof L1963–L1977 then no longer uses ylem1. |

Background: FINDINGS F69, F72, F75. The referee reports (`docs/research/*referee*.txt`) contain the bookkeeping:
- each (Y) sequence removes exactly 2n free vectors, so Δχ = −2n;
- ylem2 applies without the LG condition;
- the counting order in ylem2's second statement matters.

**Note.** These are the molecule-level lemmas that Theorem A (case (4) of DH23 Prop 9.6 for γ ∈ (1/2, 1)) and DH23
Prop 9.6 case (5) consume. Your A23-HALF lemma, just landed, is Theorem A's counting input.

## Inputs

- **wt-ansob's partial G7 work:** `/home/scott/wt-scratch/moleprop4`. It contains the Y2 lemmas, `YBoundary`,
  `YDegree`, `YOrientation`, `YConnectivity`, `BondInsertion`, `YCircuit`, `YExtraction` and the kernel-checked
  counterexample `ShortYCounterexample`, which stays as a probe. Read its `HANDOFF.md` and `OBLIGATIONS.md`, and copy
  with sha256. That directory is read-only for you.
- **Molecules:** wt-nt's MOLE and CLCN.
- **Operations:** wt-nt's Appendix B operations (APPB-OPS, `/home/scott/wt-scratch/appb`, in progress).
- **Vines:** wt-gausssum's VINES (`/home/scott/wt-scratch/vines`, done; includes the m = 1 vine (II)).
- **Counting:** the landed counting lemmas.

## Where

- Scratch: `/home/scott/wt-scratch/moleprop4-t/`, namespace `WaveTurbulence.MoleProp4`. Avoid duplicate names with
  wt-ansob's copy.
- Worktree: `/home/scott/WaveTurbulence-worktrees/torus-fourier`. Merge main first.

## Done

- No sorry, standard axioms only.
- A HANDOFF, recording each repair as a reading.
- Report `READY moleprop4`.
