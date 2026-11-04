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

## R7 — Stage 1 construction becomes packet S2a; LG-SPINE goes generic, 2026-11-04 ~19:15 UTC (revises R3 / R6(c))

**Why.** LG-SPINE found that the Stage 1 construction is a project of its own:
- the simultaneous splice of the family 𝒱_0;
- 𝒢_sb, 𝕄_sb and the hinges;
- the kernel identification with (redvine);
- the C1 half of L2116.

**S2a REDSPLICE-DEF (new agent, scratch `redsplice`)** builds the actual construction:
- definitions on the whole carrier, no placeholders;
- the simultaneous splice from CLCN's single-block `CLSpliceMoleculeIso` / `ChainSplicedMolecule`;
- S1's `vinechainlem` and `defcong` (named obligations, word for word, until S1 finishes);
- the hinge atoms, and the L2116 C1-side non-interiority (`hingeOutsideFirst`) for the constructed objects.

**S4 SUBPRO (later)** proves `subpro` (TARGET L2040–2051) for that construction.

**LG-SPINE** proves the counting cover and the rest of the assembly over general choice data that satisfies the
subpro conclusions and L2116. These are conditional helpers with distinct names. The final `layergarden_of_spine`
instantiates them with S2a's construction, S4's `subpro`, and the literal (redvine2/3) identities as stated spine
inputs.
- No construction is ever replaced by an existential.
- `SpineInputs` is published as soon as its list is fixed, because FLOWER-SPINE waits on it.

**Interface note.** LG-SPINE session 8 changed the body of `CountingChoices.Admissible`, and with it
`FinalCountGate`. Hashes are at the top of `lg-spine/SPINE.md`. Consumers (S3, FLOWER-SPINE) re-pin before their
final exact-type checks.

## R8 — One canonical molecule universe, 2026-11-04 ~19:50 UTC

**Finding.** The scratch packets live in three incompatible molecule universes.

| universe | molecule base | packets |
|---|---|---|
| (1) legacy MOLE-era | `Molecule.DegreeBlock` blocks | CLCN (M3), TWIST/MOLECPL (M6), LFTWIST (M7), and M8's current build |
| (2) lg-spine | connected `IsBlock` (F57), but a pre-F72 `WaveB2Draft/Molecules.lean` (`986e96c8…`, no one-rung vine (II)) | lg-spine, S1, S2a, S3a/S3b, FLOWER-SPINE |
| (3) B2 final | `waveb2-snap-final/WaveB2-Molecules.lean` `5cc50611…`: connected `IsBlock` plus F72 | VINES M4 / VINEPARAM canonical, partly |

**Ruling.** The canonical universe is B1 snapshot 9 + the B2 final candidate (all of `waveb2-snap-final`, including
Molecules `5cc50611`) + the molecule library ported to it.
- The B2 molecule definitions are held out from the freeze (B2.3-only), but they are the audited B2-final text, and
  they will be frozen with B2.3.
- Every packet rebases onto this universe before its seal port.

**Packet UNIVERSE (new agent, scratch `universe`).** It builds the canonical base in dependency order:
1. B1 snapshot 9 and B2 final draft modules.
2. The Molecule* library: mole, plus lg-spine's connectivity repairs, adapted to F72.
3. CLCN (M3).
4. TWIST/MOLECPL (M6).
5. LFTWIST (M7).
6. VINES (M4).

Ports are proof-only where possible, via projection lemmas such as `degreeBlock_of_isBlock`; VINEPARAM's canonical
copy uses one already. A statement change is allowed only where a legacy definition differs from the canonical one,
and every such change is listed.

**Effect on other packets.**
- S1's congruence definition and GAP.congEquiv wait for UNIVERSE's LFTWIST port, together with the missing
  symmetry/composition/commutation lemmas for `FamilyOperation`.
- Packets continue in their current universe meanwhile and rebase when UNIVERSE publishes each layer.

## R9 — Leafwise `Stage1Piece.Represents`, and the S2a interface, 2026-11-04 ~20:20 UTC

**(a) `Represents` carries the leaf profiles.** It is stated for leaf-modified kernels (`kernelLeaves` with
`LeafProfiles` and `leafSizeProduct`), like gates 1 and 3. Reason: TARGET applies Props 5.1/6.1 leafwise at
L2065–L2067. The weights `jbrProd^{-4Λ}` and the k-derivatives of the nonregular couple sum need it.

**(b) `Represents` is LG-SPINE's reading of a loose source step (redvine → redvine2), not a literal TARGET
statement.** It stays a separately named spine input, provided by S2 together with the literal redvine2/3 text, and
it goes on the audit list as a reading. S2 must prove it for S2a's construction. It must not be weakened to fit.

**(c) `Stage1Data` / `Stage1Piece` is the S2a interface.** S2a instantiates it with its actual construction (R7)
once UNIVERSE L2 (CLCN) is available. LG-SPINE keeps the record's field list stable and documents it in SPINE.md.
Any change is announced at the top of SPINE.md with old and new hashes.

## R10 — Prop 6.1 at 30d is restored (F80 is fixed), 2026-11-04 ~20:40 UTC

**History.** The 2026-11-04 morning ruling restated the Prop 6.1 gates in order 0 (pl234 pin 0936). The reason was
ISSUE-XNORM: the snapshot-8 `XNorm` put a per-frequency `⊤` inside `∫⁻`. That made it a lower integral with no
triangle inequality, so TARGET's telescoping (prooflayer1-1/1-2, L1241–L1246) could not be done in `XNormRestr` at
30d.

**F80 (snapshot 9, now frozen)** replaced that with the a.e. `C^{Λ₁}` guard. The integrand is a.e. equal to a Borel
function, `∫⁻` is a genuine integral, and the triangle inequality is derivable. The reason for the order-0
restatement is gone.

**V5 needs the derivatives.** It needs TARGET's layerregest3, `𝔛^{η,30d,30d}` with k-derivatives, for coherent K* with
q ≠ q', to meet `sumint`'s `Admissible` (`SNorm 30d 30d`).

**Ruling.**
- The Prop 6.1 gate is TARGET's literal 30d form: the 0814 pin `CoherentApproximationGate`, with `XNormRestr η (30d)
  (30d)`, restated word for word on snapshot 9 (B2 final). The leafwise gate likewise.
- **New packet PL23-30D** proves it on snapshot 9 for q > q':
  - the triangle inequality for `XNormRestr` under the F80 guard;
  - the tensor and Leibniz bounds with derivatives;
  - REGREF's `TraceDeriv` for the lower-layer trace.
- LG-SPINE keeps consuming the order-0 consequence. It follows from the 30d gate by
  `XNorm00Restr_weight_le_XNormRestr`, so LG-SPINE does not change.

## R11 — FLOWER-SPINE inputs: owners, 2026-11-04 ~21:45 UTC

**Shared with LG-SPINE word for word.** `coarse` and `ladder`.

**Flower Stage 1 gates.** `gardens` (`FlowerStage1At`, L2292–L2300) and `couples` (`CoupleStage1At`, L2312) have the
same shape as LG-SPINE's `Stage1ReductionGate`.
- They are LG-SPINE's own readings of "repeat the arguments", so they go on the audit list as readings.
- Providers: the same Stage 1 packets, S2a (construction), S2 (`Represents`) and S4 (`subpro`), with TARGET's
  flowerest1 adjustments (1)–(7).
- If a Dirac factor `δ(t_{f^pr} − s)` cannot be absorbed into a plain `G_sb`, the provider stops and reports it. A gate
  is never weakened.

**`RegularCouplesAt`** (the regular-couple leg of clause (2), L2312 "using (taylorbound) and (estcouple2)").
- It is a conclusion-shaped sub-sum bound, so it may stay a spine input only because it gets proved.
- **New packet FLOWER-REG** derives it from the shared Props 6.1 (30d, R10) and 6.2, `taylorbound` (WKETAYLOR-GATE, done)
  and a fixed-root-time trace. It uses REGREF's `TraceDeriv` and the snapshot-9 port in b21-snap9.

**`FinalCountGate`** stays a separate hypothesis, as in `layergarden_of_spine` (γ-sensitive, F69b).

**Request to LG-SPINE.** Expose `Stage1PieceD.gbar` and `rbar` (`@[expose]`), or factor out the integral part of
`Represents`, so FLOWER-SPINE can drop its copies (`FStage1Data`, `FCounts`, `gbar'`, `rbar'`).
