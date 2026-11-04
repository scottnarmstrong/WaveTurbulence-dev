# Packets J2 (rest) + J3: DH21 Lemmas 5.9–5.10, then DH21 Proposition 5.1 (maincoef)

Read `COMMON.md` first. This continues JR-OPS: Lemmas 5.3–5.8 and the single 5.9 steps are landed in
`Foundations/ClassJR/**`.

## 1. J2 rest

- **Lemma 5.9.** The induction over a legal partition P of {1..2m}, with
  `I = X_0 I_{β_1+λ_1} X_1 ⋯ I_{β_2m+λ_2m} X_2m`, gives class J + class R, with norms `≤ C^m ∏‖X_a‖`.
- **Lemma 5.10.** The expansion of `I_{β_1+λ_1} ⋯ I_{β_2m+λ_2m}` into at most `2^m` terms
  `∏_{j∈Z} χ_∞(α_j)/(ε_j π i α_j) · (class J + class R)`.
- Both use legal partitions:
  - DH21 Def 4.4 (L739–L740) defines them as non-crossing pairings;
  - DH21 Prop 4.5 (L741–L749) supplies their concatenation/enclosure induction.
- **Reuse, do not redefine.** wt-resonant's REG-STRUCT scratch (`/home/scott/wt-scratch/reg-struct/`, e.g.
  `PartitionDeletion.lean`) and the B2 draft (`/home/scott/wt-scratch/waveb2/WaveB2-Regular.lean`, Catalan-form codes)
  already have legal partitions.
  - Take the definition from there: copy the files you need into Foundations under `WaveTurbulence.ClassJR` and
    record the source sha256.
  - Or prove a bridge if you need a different form for the induction.
  - List the choice in your HANDOFF so the post-freeze move is mechanical.
- The variable bookkeeping between steps (relabelling `Option ι₁ ⊕ Option ι₂ → Option κ` through `ClassJP.reindex`)
  is part of this packet.

## 2. J3 MAINCOEF

DH21 Prop 5.1 (L936–L944), with the DH23 weights (DH23 L955–L969: the bounds (maincoef2) and (maincoef2.5) with weight
`α^{1/8}`). Map: `~/wave-turbulence/maps/DH21.md` L300–L306.

- **Claim.** For Q a regular couple of scale 2n, `B̃_Q(t,s,α[𝒩^ch])` is a sum over `Z ⊂ 𝒩^ch` of the (maincoef1) terms.
- **Proof route.** Induction on the structure of regular couples, through the type-1 and type-2 recursions
  (newexp1), (newexp2) and Lemma 5.10.
- **What it consumes.** It needs the regular-couple structure theorem (DH21 Props 4.7–4.8; packet C1, wt-resonant,
  in progress in `/home/scott/wt-scratch/reg-struct/`). Until that lands, take the structure theorem as an explicit
  named obligation, stated exactly as REG-STRUCT states it (or will). Prove Prop 5.1 from it. Record the obligation in
  your HANDOFF.

## 3. The cutoff (your deviation 5)

Lemma 5.8 was proved with `ρ = ½·1_{[−1,1]}`. DH21 uses a Gevrey-2 cutoff there. The Wave B statements use
`chi0 = smoothTransition(2 − 2|x|)` (Gevrey-2), and Foundations has `chiInfinity = 1 − chi0` (`Fourier/Chi0.lean`).

Before J3, write down in your HANDOFF:
- where the cutoff enters (Def 5.2 class R, Lemma 5.8, 5.10, (maincoef1));
- whether the χ_∞ in Prop 5.1's `∏_{n∈Z} χ_∞(α_n)/(ζ_n π i α_n)` must be the Wave B `chiInfinity` for the consumers:
  - DH21 Prop 7.4 cancellations (J4);
  - DH21 Props 7.9–7.10, the identification with the WKE Taylor term (J6);
  - TARGET `regref`.

If it must, rework Lemma 5.8 with `chiInfinity`, or prove that the two expansions agree. Report what you chose.

## Where

Foundations on your branch (`w/jr-ops`), namespace `WaveTurbulence.ClassJR`.

## Done

- `READY jr2` after 5.9–5.10;
- `READY maincoef` after Prop 5.1.
