# Packet RA1 REGASYMP: DH23 Prop 6.1, asymptotics of regular couples and trees, for orders n ≤ N_{p+1}^4

Read `COMMON.md` first.

## Goal

Blueprint packet RA1 (`docs/blueprint/GRAPH.md` §E), nodes `DH23.regcpltreeasymp` (DH23 Prop 6.1, `Revision_Submit.tex`
L920–L934, proof to about L1180) and `GAP.largeOrder` (FINDINGS F33: TARGET applies it for orders up to
`N_{p+1}^4 = (log L)^{C(𝔇)}`, route R14 (a)). This is on the critical path: it feeds RA2 (TARGET `regref`), then L3,
L4, V5 and the reduction.

The DH23 map is `~/wave-turbulence/maps/DH23.md`. It covers §6 and, in its external-inputs table, E5–E10. Those rows
say which DH21 results Prop 6.1 imports.

The source's split is couples, then trees and derivatives. Do couples first.

## Inputs

**Landed on main:**

| input | where |
|---|---|
| DH23 Prop 6.4 with the large-order extension (your colleague wt-torus; audited PASS for the parameter prefix, `audits/APPROXNT.md`) | `Foundations/ApproxNT` |
| DH21 Lemmas 5.3–5.10, class J/R operators | `Foundations/ClassJR` |
| NTSP, MINOR, the counting lemmas | `Foundations/NTSP`, `WeylSums`, `CountLemmas` |

**In progress elsewhere:**

- **DH21 Prop 5.1** (J3): wt-wke, branch `w/jr-ops`, `HANDOFF-JR2.md`.
- **DH21 §7 cancellations** (J4): wt-torus, `/home/scott/wt-scratch/cancel`.

Until they land, state the exact results you need as named obligations, matching their authors' statements word for
word. Read their branches and handoffs. Never duplicate their declarations. Use your own namespace,
`WaveTurbulence.RegAsymp`.

**Pre-freeze scratch:**

- **Regular-couple structure:** REG-STRUCT (`/home/scott/wt-scratch/reg-struct`).
- **Links:** LINKS (`/home/scott/wt-scratch/links`).

Copy what you need from scratch and record the sha256.

## Sign convention

Use the **corrected** F61 sign throughout: `∏_{𝔫∈Z}(−1)/(ζ_𝔫πi)` per special node. See FINDINGS F61 and
`/home/scott/wt-scratch/wke/F61-sign-trace.md`.

## Consumer

B2.1 `regularAsymptotics` in the Wave B2 freeze candidate (`/home/scott/wt-scratch/waveb2-snap-final` once pinned,
else `/home/scott/wt-scratch/waveb2`). Look at what its items need, so your statements can be bridged to it.

## Where

- **Foundations:** statement-independent analysis goes on your branch under `WaveTurbulence/Foundations/RegAsymp/`.
- **Scratch:** the parts that need Wave B objects go in `/home/scott/wt-scratch/regasymp/`.
- **Worktree:** `/home/scott/WaveTurbulence-worktrees/an-sob`. Merge main first.

## Done

No sorry, standard axioms only, and a HANDOFF.

- Report `READY regasymp-couples` after couples, then keep going.
- Report `READY regasymp` at the end.
