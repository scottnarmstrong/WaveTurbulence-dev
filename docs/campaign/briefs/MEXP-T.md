# Packet J5 MEXP (reassigned to wt-torus): DH21 Props 7.7 and 7.8, then J6/J7

Read `COMMON.md` first. This follows directly from your J4 CANCEL7.

## Goal

**J5 MEXP** covers two results.

- **DH21 Prop 7.7** (`multiexp`, L1814–L1837): `M*_{Q_s}(k)` depends only on the equivalence class `X`, with the type-1
  and type-2 formulas.
- **DH21 Prop 7.8** (`nonemptyZ`, L1838–L1855): for a class `X` with `Z ≠ ∅`, the sum over `(Q,Z) ∈ X` of
  `∏_{𝔫∈Z} 1/(ζ_𝔫 π i) · 𝒥B̃ · M*` vanishes. Use the corrected F61 weight `(−1)/(ζ_𝔫πi)`. `|Z|` is constant on classes,
  as your C5 shows, so the factor `(−1)^{|Z|}` is common.

The map entries are in `~/wave-turbulence/maps/DH21.md` L343–L346. Then continue:

- **J6 WKE-ID:** DH21 Props 7.9, 7.10 and DH23 Prop 6.2, identifying `Σ app` with `𝒰_n`, the WKE Taylor term.
  - The landed WKE Taylor theory and the now-proved `wkeTaylor` gate are in `/home/scott/wt-scratch/wketaylor-gate`.
  - The B1 bridge `wkeTaylorTerm_eq_taylorU` is in snapshot 7's `WaveB1-Bridges.lean`.
- **J7 REGCANCEL.**

## Inputs

- Your C5 ENHANCED and J4 CANCEL7.
- **wt-wke's Prop 5.1 (J3, landed).** wt-wke is now proving the garden ↔ code `B̃` bridge (MCB2) that will discharge
  your `BtRec`. Keep the same `BtRec` interface.
- **Packet N5.** Check its status in `docs/campaign/progress.json`.

## Where

Same conventions as CANCEL7:

- Foundations: `WaveTurbulence/Foundations/Cancel/`.
- Scratch: `/home/scott/wt-scratch/cancel/` (or `/home/scott/wt-scratch/mexp/`).

Merge main first.

## Done

Report each of `READY mexp`, `READY wke-id` and `READY regcancel` as it finishes.
