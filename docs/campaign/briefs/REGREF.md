# Packet RA2 REGREF: prove the Wave B2 anchor B2.1 `regularAsymptotics`

Read `COMMON.md` first. This builds directly on your J4–J7.

## Goal

Blueprint packet RA2 (`docs/blueprint/GRAPH.md` §E) has these nodes:

- `GAP.regrefNorm`: the norm translation, F11;
- `GAP.regref5`: corrected (regref1-5);
- `GAP.domTree`: dominant trees;
- `T.regref1`, `T.regref2`, `T.regref3`: TARGET Props 6.6–6.8, L1145–L1240.

Together these are the proof of the **B2.1 anchor `regularAsymptotics`**, in the B2 final candidate
`/home/scott/wt-scratch/waveb2-snap-final`. You already proved item (4) (`regularAsymptotics_item4`).

Target: prove all of B2.1's items **at the exact B2 type**, with the F61-corrected `specialWeight` (CL-11) and the F66
lower limit (CL-13). Use the same type-audit pattern as NLS-BRIDGE: a textual and elaborated comparison against the
pinned candidate.

## Inputs

| input | source |
|---|---|
| DH21 Prop 5.1 for couples, the garden↔code B̃ bridge, and soon Prop 5.1 for trees | wt-wke, MAINCOEF-T in progress, `/home/scott/wt-scratch/btilde`, `/home/scott/wt-scratch/maincoef-t` |
| DH23 Prop 6.1 for orders n ≤ N_{p+1}^4, couples first | wt-ansob, RA1 in progress, `/home/scott/wt-scratch/regasymp` |
| Your C5, LAYERREG, CANCEL7, MEXP, WKE-ID and REGCANCEL | your own work |
| DH23 Prop 6.4 (APPROXNT) | landed |
| The p.v. characterization for decaying kernels (F-5) | landed (PV-DECAY) |

Until RA1 and MAINCOEF-T land, take the results you need from them as named obligations. State them exactly as wt-ansob
and wt-wke state them, and coordinate through their HANDOFFs. The independent B2 audit's probe lemmas
`KTstar_indep_of_le`, `item2_integrand_of_le` and `KTstar_relayer` (`/home/scott/wt-scratch/b2-audit/Q1.lean`,
`Q3.lean`) may help with item (2) for trees.

## Notes

- **B2.1 is about all γ ∈ (0, 1).** The F69b problem (γ ≤ 1/2) is in the counting chain of `layergarden`, not in the
  regular-couple asymptotics. If you find any γ-restriction needed here, report it at once.
- **The vine (II) m = 1 change (F72)** is coming to B2 as CL-21. It touches `IsVine`, which B2.1 should not reach.
  Confirm this.

## Where and done

- **Where:** scratch `/home/scott/wt-scratch/regref/`, plus Foundations parts on your branch. Merge main first.
- **Done:** report `READY regref-couples` when the couple items are proved, then `READY regref` when all items of B2.1
  are proved at the exact type.
