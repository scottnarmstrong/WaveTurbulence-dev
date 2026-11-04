# Packets: the B̃ bridge, then J5 MEXP (DH21 Props 7.7, 7.8)

Read `COMMON.md` first. This continues your J3 MAINCOEF (DH21 Prop 5.1, done).

## 1. The B̃ bridge

This closes the uncertainty you recorded in J3.

- **Source.** DH21 defines `B_Q` on gardens and couples: (defcoefb2) for the time coefficient over the domain `ℰ`, and
  (deftildeb) for `B̃_Q`, L913–L944. It then "deduces" the type-1 and type-2 recursions (newexp1), (newexp2) at
  L923–L937.
- **What is in the Lean now.** Your Prop 5.1 is about the code-defined `B̃` (recursion on B2 `RegCpl` codes).
- **What to prove.** The garden-defined `B̃_Q`, built from the Wave B objects, equals the code-defined one for every
  regular couple and tree that the code decodes to. This uses REG-STRUCT's `existsUnique_regCpl_decodes` (from
  `/home/scott/wt-scratch/reg-struct`; copy it and record the sha256) and the time-domain definitions (`kDomain`,
  `phaseIntegral`) in snapshot 7 (`/home/scott/wt-scratch/waveb-snap-7`).
- **Downstream.** RA1 (wt-ansob, DH23 Prop 6.1) and the B2.1 proof consume `B̃` through gardens, so this bridge is what
  makes your Prop 5.1 usable there.

## 2. J5 MEXP

DH21 Props 7.7 and 7.8 (map: `~/wave-turbulence/maps/DH21.md`, search `multiexp` and `nonemptyZ`).

- **Corrected sign.** Use the corrected F61 sign. |Z| is constant on equivalence classes (wt-torus's C5 ENHANCED
  proved this), so Prop 7.8's class cancellation survives with a common factor `(−1)^{|Z|}`.
- **Inputs:**
  - J4 CANCEL7 (DH21 Lemmas 7.1–7.3, Props 7.4–7.5), which wt-torus is proving in `/home/scott/wt-scratch/cancel`.
    Take Props 7.4 and 7.5 as named obligations with wt-torus's exact statements, and coordinate through its HANDOFF.
  - wt-torus's C5 objects in `/home/scott/wt-scratch/enhanced`.
  - Packet N5. Check its status in `docs/campaign/progress.json`.

## Where

- Foundations on your branch: `WaveTurbulence.ClassJR`, or `WaveTurbulence.MainCoef` for the new files.
- Scratch: `/home/scott/wt-scratch/btilde` for the parts that need Wave B objects.

## Done

- `READY btilde` after the bridge.
- `READY mexp` after J5.
