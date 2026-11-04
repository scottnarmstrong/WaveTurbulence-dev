# Orchestration rulings by wt-orch (since 2026-11-04, on Scott's instruction to drive the campaign)

These rulings are about proof organization only. Rulings on statements remain Scott's (`docs/DECISIONS.md`).

## R1 — ISSUE-APPCONJ (PL234 / L4 PL4), 2026-11-04 ~18:40 UTC

**Issue.** `/home/scott/wt-scratch/pl234/ISSUE-APPCONJ.md`. The app halves of Prop 6.3 (i)/(ii) are TARGET's
parenthetical at L1119 ("the same holds for the `(⋯)_app` approximations"). They need the `ℓ ↔ w` symmetry of
`resIntegral`, which holds only under integrability of the nested `Mstar` integrands. That integrability is not
available for the gate's inputs.

**Ruling: option B, plus A as a separate node.**
- **`CoherentRealityGate` carries what the consumers use.** That means the kernel halves of (layerregest9) (proved)
  and (layerregest10) (iii), the realness of the app sums (proved for q = q' and q > q').
  - TARGET's only downstream use is vineest Step 4 (L1881, and the twist cancellation through L1925), which uses
    (layerregest10) and the app bounds (layerregest4)–(6) from proplayer2.
- **The app halves of (i)/(ii) become a separate graph node, `PL4.appConj`, with no current consumer.** If a consumer
  ever needs it, its analytic input `MstarResonantIntegrableGate` (proposal A) becomes a graph node of its own,
  owned and proved like any other node. It is never a binder of the gate.
- **PL4 counts as done** for the gate (READY pl4 stands). The `appConj` node stays open, and is unconsumed.

## R2 — V4/V5 boundary (VINEEST-S2), 2026-11-04 ~18:10 UTC

V4 ends at the proved equality of the vine-chain contribution with the exact (tildeK2) `sumint` input form:
- the weights as the actual K* factors;
- the parameters;
- the windows;
- the `sumintBoundary` permutation;
- the algebraic `Admissible` clauses;
- S2 (i) unimodularity and (ii) short sums.

The weight-bound clauses, the bad cases (a)–(d) and the application of `sumint` are V5 (T.vineest.S3).

## R3 — LG-SPINE assembly vs spine inputs, 2026-11-04 ~17:15 UTC

- **Spine input:** a stated TARGET proposition that the layergarden proof cites (`subpro`, `redvine2`, …). It is a
  literal transcription, with line numbers.
- **Assembly:** a construction carried out inside the layergarden argument (Stage 1 class and hinge selection,
  splicing). LG-SPINE does it.
- **Missing lemmas:** these are work, proved locally, not a reason to stop.
- **L2116.** Its non-interiority of hinges is proof text, not a stated proposition, so it is an assembly obligation
  for LG-SPINE.

## R4 — APPB-ALG terminal-rung accounting, 2026-11-04 ~18:30 UTC

The lookahead slack design is approved (proof-internal). As built, the terminal rung is handled by the structural
`pendingSlack` (no scan-mode change needed). `GraphOk` (polylog molecule order) is a recorded deviation: DH23
Prop 10.2 (L1834) states no size bound, but its proof's log losses need one. `η ≤ min(γ, 1−γ)` and
`4·1440061·η ≤ 1` are instances of L438's standing assumption η ≪_{d,γ} 1.

## R5 — FLOWER-SPINE vs LG-SPINE kernel genericity, 2026-11-04 ~18:55 UTC

**No restructuring of LG-SPINE.** Its remaining Stage 1 and counting work is kernel-independent (molecules,
gardens), so FLOWER-SPINE reuses it directly.

**Analytic steps go through a bridge.** `kernelKgen` restricted to a plain pattern (no fixed-time nodes, no removed
phases, unit weights) is shown equal to `kernelK`. Flower-specific analytic statements are proved separately.

**What FLOWER-SPINE does meanwhile** (inputs not blocked by LG-SPINE's final `SpineInputs`):
- the bridge;
- F3, the DH21 Cor 11.3-type `M₂^{−P/9}` gain (L2298);
- F4, stem preservation (L2299–2300);
- F1, the leaf-decay reading (L2293);
- the decay-factor comparison.

## R6 — LG-SPINE second collection: designation and C2 carrier, 2026-11-04 ~19:05 UTC

**(a) One designation per atom set.** In TARGET a vine-like object is an atomic group, so it has one designation. An
atom set with two hyper designations (two parallel joint bonds; the {a,c,b} example in lg-spine/ERRATA.md) is one
object.
- The selection of C1/C2 is assembly (R3), so LG-SPINE fixes a canonical designation per atom set: the least deleted
  bond in a fixed order on bonds. It proves (f)(ii) for that choice.
- This is recorded as a reading (source ambiguity), not as an erratum.
- With this choice, the second disjunct of `source_second_collection_pairs_compatible` (two hyper objects on the same
  atom set) disappears.

**(b) The C2 carrier is the source's.** Define the restricted second collection literally from TARGET L2101–2112, as
`SubproSupport.contained` does if that matches the source: SG objects outside C1, disjoint from the hinges, with
containers disjoint from C1 and the hinges. Re-run the step 1–4 results on it.

**(c) The Stage 1 construction is LG-SPINE's assembly (R3).**
- This means the congruence classes, 𝒱_0, splicing, 𝒢_sb, 𝕄_sb and the hinge atoms, which is the blueprint's S2a.
- It uses S1's results (`vinechainlem`, congruence, `defdiff`; agent in /home/scott/wt-scratch/stage1). Until those
  land, LG-SPINE takes them as named obligations matched word for word.
- `subpro` (TARGET L2040–2051 / DH23 Prop 9.1) is a stated proposition, so it is a spine input, provided by S4.
