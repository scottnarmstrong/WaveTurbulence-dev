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

## R12 — FLOWER-SPINE `regular` split (FLOWER-REG finding), 2026-11-04 ~22:00 UTC

**Finding.** `RegularCouplesAt` is stronger than TARGET L2312 derives.
- Its `dt = true` part (all of kind `tr`) consists of Dirac-root kernels `∂_t∂_s K*` at s = t. Prop 6.1/6.2,
  `taylorbound` and the trace do not control these.
- TARGET handles them "by the same arguments as flowerest1".

**Ruling: split the input in two.**
- **`RegularCouplesL0At`** (kind `L0`, `dt = false`): TARGET's "(taylorbound) and (estcouple2)" leg.
  - Provider: FLOWER-REG.
  - Inputs: the 30d gate, Prop 6.2, `taylorbound` and the trace, plus **B2.2 `incoherentDecay` (sealed on main)** for
    the incoherent regular couples. B2.2 is now an allowed input.
- **`RegularCouplesDtAt`** (`dt = true`, including kind `tr`): the Dirac-root regular couples.
  - Provider: the flower Stage 1 machinery, i.e. S2a / S2 / S4 with flowerest1's adjustments, in the same shape as the
    `gardens` and `couples` gates (R11).
  - The exponents must be TARGET's: `δ^{νN}`, `L^{100d}` from B1.12(2). Sharper ones are allowed only where proved.
- FLOWER-SPINE restates its `regular` input as the conjunction of the two and re-pins it.

## R13 — V5 Step 3 endpoint and the degenerate decorations (ε, F21), 2026-11-04 ~22:00 UTC

**Finding.** TARGET L1844–L1846 replaces ε by 1 "by trivial summation, gaining L^{−0.1γ₀}". For large M this does not
work: trivial summation over the restricted subspace costs L^{(M−1)d} against L^{M(d−γ)}.

The blueprint already lists this as a gap: GAP.degenerate.vine (F21), "the L^{−0.1γ₀} gain in vineest Step 3 for
degenerate decorations — the analytic half of F21", with DH23 `extradegen` as its input.

**Ruling.**
- V5 Step 3's endpoint is stated for the ε ≡ 1 kernel (`clockedExpr`), the main term.
- The degenerate decorations are a separate graph node, GAP.degenerate.vine. The new packet **DEGEN-VINE** proves it,
  from DH23 `extradegen` / DH23 §10.5 and the DEGEN packet (G0, done in scratch).
- The vineest assembly combines the two.
- TARGET L1844–L1846 goes into the findings ledger as a CANDIDATE erratum ("trivial summation" is insufficient for
  large M). It is confirmed or withdrawn once DEGEN-VINE's proof shows what is actually needed.

## R14 — PL23-30D obligations, 2026-11-04 ~22:00 UTC

**Accepted.** PL23-30D is READY: both Prop 6.1 gates are proved at 30d on snapshot 9. Its two obligations are B2.1
`RegularAsymptoticsGate` and **`LeafwiseRegularAsymptoticsGate`**.

**The leafwise gate is an open node, not proved anywhere.**
- REGREF's handoff says the leafwise analytic estimate is RA1 work: DH23 Prop 6.1 with individually modified leaf
  inputs, used at TARGET L2065–L2067.
- RA1 couples and RA1-TREES proved only the common-profile form.

**New packet RA1-LEAFWISE.**
- Prove RA1 (couples and trees) with per-leaf profiles, generalizing `regular_couple_asymptotics` and `ra1Tree`.
- Then derive `LeafwiseRegularAsymptoticsGate` with REGREF's leafwise kernels (`Leafwise.lean`).

## R15 — FLOWER-REG accepted; the leafwise B2.2 gate is an open node, 2026-11-04 ~22:45 UTC

**FLOWER-REG.** `regularCouplesL0 : RegularAsymptoticsGate → LeafwiseRegularAsymptoticsGate →
LeafwiseIncoherentDecayGate → WTPrefix RegularCouplesL0At`. It is accepted.

**Its extra obligation is allowed.** `LeafwiseIncoherentDecayGate` (Prop 5.1 applied leafwise, TARGET L2062–L2067) is
already LG-SPINE's `leafDecay` spine input. The weight `jbr k^{−4Λ_{p+1}}` (with 4Λ_{p+1} ≥ 160d) must be moved onto
the individual leaves, and the common-profile B2.2 cannot do that.

**The gate is proved nowhere.** INCOH-INST proved only the common-profile B2.2 `incoherentDecay`.

**New packet INCOH-LEAFWISE.** It generalizes INCOH-INST's proof to per-leaf profiles and proves
`LeafwiseIncoherentDecayGate` on snapshot 9. It runs alongside RA1-LEAFWISE (R14), which does the same for B2.1.

## R16 — Seal targets after D10, 2026-11-04 ~23:20 UTC

**Targets.** The five approved successors are the sealing targets for the end-to-end chain: `main_v2`,
`propansatz_v2`, `layergarden_v2`, `fixedpoint_v2` and `layergardenFlower_v2`. They are DRAFT_SORRY anchors on main
(D10).

**How the successors are proved.**
- `layergarden_v2` comes from `layergarden_of_spine` with `FinalCountGate` replaced by its 1/2 < γ form. This is the
  `finalCountGate_of_half` route: G2 Prop 9.4 plus G8 Prop 9.6 for γ > 1/2. The successor's `1 / 2 < P.γ →` hypothesis
  supplies the restriction inside the prefix.
- `layergardenFlower_v2` comes from `layergardenFlower_of_spine` the same way.
- `fixedpoint_v2`, `propansatz_v2` and `main_v2` use the existing X3 / INDUCT / MAIN-GLUE assemblies, re-run with the
  restriction threaded through.

**The originals stay open.** `main`, `propansatz`, `layergarden`, `fixedpoint` and `layergardenFlower` remain
DRAFT_SORRY. Their γ ≤ 1/2 range is the research track (repair route under independent review).

## R17 — `VineCountInput` (Prop 9.4, single vine) re-scoped; packet VINE-COUNT, 2026-11-05 ~00:30 UTC

**Finding.** The G2 agent found our internal `VineCountInput` mis-posed (an internal statement, not a source one):
- the ladder gain needs `Adm` to restrict each ladder's gap to about `P S`;
- the true count carries a dimension constant per interior atom, which needs `C₂^m` in `vineF` with `C₂ ≤ C₁`, as
  the source's "C₁ large" absorbs it;
- premises are missing: `K.C.shape = .vc h`, the lower gap bound (as `hlow`), SG / nonzero VC gap, and the ladder scales
  in `Adm`.

**Ruling.**
- Restate `VineCountInput` with these three fixes, matching DH23 L1799–L1801 and the `countA` definition, where the
  ladder-scale restriction is part of the admissible class. Adjust `vine_excess_single` accordingly.
- **New packet VINE-COUNT** proves it. Route: VINEPARAM's molecule-level charts for vines (I)–(VIII) with inserted
  ladders, plus two new link lemmas:
  - (a) the chart's rung slots are exactly the `maximalLadders` of `K.vc`;
  - (b) each ladder's gap is the VC gap r or 0.
- With these, the bilinear rung count gives 𝔛^{−z} per ladder, and the bounded core is counted by main's counting
  lemmas.
- Take `vineparam` as a named obligation, word for word (Contract.lean `cd16890b…`), while its catalogue compiles.
- Garden-decoration counts (LADDER-DECAY) are not bridged.

**L1794 (DH23, ΔF = 1 triangle).** Recorded as a CANDIDATE erratum with the analytic configuration: v₃ with
k_{ℓ₁} = k_{ℓ₂} free in the unit ball gives about L^d pairs, against δ⁻¹L^{d+1−2γ}. The final bound still holds.

## R18 — Prop 9.6 history properties (N1, N2) are conclusions of Prop 9.5 / the algorithm, 2026-11-05 ~00:45 UTC

**The properties.** G8's Prop 9.6 needs:
- (N1): every β-atom of 𝕄_fin has a nonzero gap;
- (N2): the ι/κ property of case (6), "κ_{v1}+κ_{v2} = 0 and the three gaps sum to 0 ⇒ |r_β| ≳ L^{−50η}R₂".

**Ruling.** Both are properties of the cutting history, so they are carried by the final molecule's labels (κ, R, ι).
- G3 states them as explicit conclusions of its Prop 9.5 / finalmol package, with DH23 line citations (algorithm
  L1773–L1801, Remark subcondition, ι at L1782), and proves them.
- They never appear as hypotheses of Prop 9.6.

**Also recorded.**
- MOLEPROP4-T internal-input defects: `OpCAt` lacked connectivity; `OpDAt` lacked |Y| ≤ 3, connectivity, `hopen` and
  the end-exemption. These join deviations 1 and 3 (internal statements, not source errata).
- G8 found an exposition gap at DH23 L1862–L1874: "operations (a), (b) only on ε-atoms" also needs degree-1 α/β atoms
  to be deleted for free. Recorded as a CANDIDATE exposition gap, not a false statement.

## R19 — Stage 1 interface amendments (S2a findings), 2026-11-05 ~02:30 UTC

**(1) Pieces are indexed by (class, σ).**
- TARGET L1950 splits one congruence class into up to 3^n terms by the SG/LG/ZG prescription σ, all over the same
  gardens. The σ-split is a partition of the DECORATION sum, not of the gardens.
- So `Represents` must carry the σ-restricted family. Each piece's value is Σ over the class's gardens of the
  decoration sum restricted to σ.
- The partition identity becomes "garden sum = Σ_class Σ_σ piece values". It holds because the σ-indicators partition
  the decorations.
- LG-SPINE amends `Stage1Partition` / `Represents` accordingly, after LG-SPINE-REBASE lands in lg-spine-u, and
  re-proves the assembly (`nonregular_prefix`, `stage1_core_bound`). FLOWER-SPINE's flower gates follow the same shape.

**(2) `center`.**
- The unit-ball centres are summed per term, inside the analytic reduction (redvine2), and are not part of the class
  count.
- LG-SPINE moves the centre sum into `Represents`, following TARGET L1950–L1976 exactly, and documents the reading.
- If TARGET instead counts centres in the class count, follow TARGET and say so.

**(3) `gsk`, `bsk`.** These are construction data. S2a computes them: the regular decomposition of the original
garden, and the bad-vine count among the ingredients of 𝒱_0.

**(4) The triple-bond clause of `Structural`.**
- It needs "the molecule of a prime couple has no triple bond" (TARGET L709 / DH21 Prop 4.14). The universe has only
  the forward direction (`miniA_triple`, `miniB_triple`).
- This is a stated source fact. S2a proves it, from SKELETON / COMB-CORE's mini-occurrence classification.
- Likewise S2a proves `isMolecule_eraseBond` for HVC groups.

## R20 — V5 Step 3 chart geometry (vineest-s3 session 5), 2026-11-05 ~05:00 UTC

**(1) The VINEPARAM contract (`FullVineChart`, Contract.lean) is NOT amended.**
- V4, VINE-COUNT and VINEPARAM all consume it, and VINEPARAM's catalogue build is in flight.
- V5 derives the numbering it needs inside its own packet:
  - prove a re-indexing lemma, `FullVineChart` → `FullVineChart` (reversing or permuting the rungs), giving a chart
    whose rung 0 is the end rung next to `b` for a type-(II-e) vine;
  - use only the contract's own fields: `rung_bonds`, a degree-4 count, and molecpl's `EndRungData`.
- If the re-indexed chart cannot be fed to V4's `vineChain_eq_sumintForm`, prove a chart-independence lemma for the
  sumint form instead, since the summand is a relabelling.
- If neither works, STOP with the exact reason. Only then is a contract amendment considered, and VINEPARAM must prove
  any new field.

**(2) The layer-failure time order (TARGET L1846–L1847) comes from layers, not parent pairs.**
- Prove the domain lemma: on the support of the layer indicators, t_{u4} ≤ q₄+1 ≤ q₂ < t_{u2} except on a null set.
  So adding the layer-order pair to the constraints leaves the integral unchanged.
- This is a proof step, not a premise. It is an exposition point, not an erratum.

**(3) The incoherency dictionary.** The link between `LayeredGarden.incoherency` of the native rows and `CohOn` is a
definitional bridge, so prove it.

**(4) `n_(3)`.**
- The inequality cohmol index ≤ D.M₀ + D.M₁ suffices, because L^{−η⁸·n} decreases in n.
- Prove it by relating the chart's groups (rung pairs, and the core triple) to the groups of a `VineRealization` built
  from the same chart, again from the contract's own fields.
- The same applies to (1): if this is genuinely not derivable, STOP with the reason.

**(5) (c), the q < q′ orientation.** Prove it, by swap + conjugation invariance of `XNorm`/`XNormRestr` and
conj-coherence of `IsCoherentCoupleAt`, then `couple_row_le_conj`.

**(6) Candidate erratum (V5).**
- TARGET Step 3 and `sumint` require t₀¹ > max(t′, t″). That is not the actual domain when u₂₁ or u₂₂ is a leaf.
- The order-0 trace route (`XNorm00Restr_trace`) handles it, at the cost of the constant `traceR η`.
- To be assessed for the errata file once V5 is READY.

## R21 — VINE-COUNT scope and the ladder-scale form (vine-count session 2), 2026-11-05 ~05:30 UTC

**(1) Chains of m ≥ 2 vines: the product count is false, and the source does not need it.**
- VINE-COUNT's configuration: a path of double bonds z′ = a = x = b = z, with gaps r = 1/L forced by conservation. It
  has about L^{2d+2−4γ} labels, against 𝔉 ≈ L^{2d−γ}.
- DH23 L1797 removes only a single vine or two double bonds in Step 1, by Prop `subsetvc` (L2128) and `subpro` (a), (e).
- So `prop94_vine_all` keeps the premise `SingleVineVC K ∨ Nonempty (DoubleShape K)`. This is NOT a free premise:
  G3's excessprop1 glue must derive it at each Step-1 application, from:
  - the universe's `subsetvc_classification` (proved in VINES, `VineSGOrdinaryRemovalSingle` and its neighbours);
  - the `subpro` (a), (e) obligations (S4).
- `Stage2Op.vine` being more permissive than the source is internal; it is not an erratum.

**(2) The ladder-scale form.**
- The canonical `Adm` ladder clause is lg-spine's source-audited `LadderGaps` / `sourceLadderGapScales`: an ∃ over
  realisations, with only 1 ≤ ‖r‖ at P = 1.
- VINE-COUNT proves its `LadderScaleAdm` (an ∀ over realisations, two-sided at P = 1) FROM that form. Two lemmas are
  needed:
  - (a) realisation independence of a sub-ladder's gap, a ladder-combinatorics lemma;
  - (b) ‖r‖ ≤ c₀ at P = 1, from the unit-ball labels.
- If (a) is false, give the configuration. The fix then goes in the consumer, not in the source form.

## R22 — V5 Step 3: the chart in V4, row alignment, and cohmol groups (vineest-s3 session 6 STOP), 2026-11-05 ~01:50 UTC

**(1) Normalized chart.**
- In V5's own copy of the V4 modules (vineest-s3/uni), wrap `chosenVineChart` and `chainPieceChart` in `normalizeChart`.
- Then rebuild. About 300 modules is compute time, not a reason to stop.
- V4's proofs use only contract fields, so they should go through unchanged. Repair any that do not.
- `Contract.lean` is not amended.

**(2) Clause (d) per vine (STOP reason A).**
- `Admissible` belongs to the sumint statement (B1.6), so it is not changed.
- In V5's V4 copy, implement vine-aligned enumerations:
  - a free bijection for pairs;
  - for branches, the key (vine index, −depth).
- Prove the structural fact this needs: a child of v lies in a vine of index ≤ vine(v), or choose the vine indexing so that it holds by construction.

**(3) cohmol groups (STOP reason B).**
- The cohmol groups of TARGET Def `cohmol` (L1489) are meant to be the parametrization's variable groups:
  - the core triangle or the IV triple;
  - the doubled pairs;
  - the leftover pair of VII.
- The contract STRUCTURE stays as it is. VINEPARAM instead delivers a strengthened existence theorem, `vineparam_grouped`: every vine admits a `FullVineChart` whose groups (rung pairs plus the core triple) equal VINES' `realizedGroups` as atom sets.
- **New packet VINEPARAM-GROUPS:**
  - check the base catalogue charts against the cohmol groups;
  - re-mine with the group constraint if needed;
  - show that rung insertion preserves the match.
- V5 then picks its chart from the grouped subtype.
- `normalizeChart` only permutes rungs, so it preserves the match.
- If no group-matching chart exists for some base template, VINEPARAM-GROUPS STOPS with that template. That would be a source finding about TARGET L1489 versus DH23 Prop 7.6.

## R23 — FLOWER-SPINE `RegularCouplesDtAt` exponent; Stage 1 packets S2 and S4 start, 2026-11-05 ~02:45 UTC

**(1) `RegularCouplesDtAt` uses δ^{2νN}, which corrects R12's "δ^{νN}".**
- TARGET's own flowerest bound (L2306) is ⟨k − ζk′⟩^{−4Λ_{p+1}P} L^{(100d)³P} δ^{2νn}.
- With exactly δ^{νN}, the clause cannot be closed to B1.12(2)'s constants. With δ^{2νN} it closes, since
  2δ^{2νN} ≤ δ^{νN}.

**(2) FLOWER-SPINE's remaining proof copies are accepted until the port.**
- The copies are `piece_bound_int`, `sum_bound_int` and `core_bound_int`.
- LG-SPINE will later add a `stage1_piece_bound` for the integral conjunct alone. That is a proof-level addition,
  with no spine-input text change. The copies are removed before landing, because duplicate code fails the commit
  gate.

**(3) S4 SUBPRO starts.** It proves TARGET Prop `subpro` (L2040–L2051) for S2a's construction (`stage1PieceOf`).
- It discharges redsplice's `SubproObligation`.
- It also instantiates G3's generic `SubproOblG` (contained, hingeSG, hingeJoint, crossing) and `subpro` (a), (e) for
  R21's Step-1 classification.

**(4) S2 REPRESENTS starts.** It proves `Represents` (R9, R19 shape: `sel`, `ctr`) for S2a's pieces, via TARGET
(redvine) L1954, (redvine2) L1962 and (redvine3) L1973.
- **V5 vineest** (Steps 3 and 4) is consumed. Until it is READY it is the single named input, with V5's exact
  statement.
- **S1 congruence** is consumed. Until it is READY it enters as the named `Equivalence` statement.
- **What S2 proves itself:**
  - that `sel` is exactly the σ-indicator;
  - the centre-sum mass bound with C₁, for LG pieces and later for flower pieces.
- **S2 audits S2a's reading at L1956:** one gap entry per group, none per ladder. S2 confirms it is what redvine2
  consumes, or reports otherwise.

## R24 — `Represents` interface amendments and the split of S2 (S2 REPRESENTS findings D1–D5), 2026-11-05 ~02:35 UTC

**D1. Pieces are (class, σ on groups, finer class τ).**
- TARGET L1950 splits each σ-term into at most 2^n finer classes, by twists at 𝒱₀ only. A σ-term of a coarse class is
  not one spliced integral, because LG/ZG vines stay unspliced and their twists change the time domain.
- `sel π LG κ := (κ has prescription σ) ∧ LG ∈ τ`.
- `Stage1Counts` becomes at most 6^N pieces per class (3^n · 2^n). The assembly absorbs 6·C₀. This is a
  constants-only amendment.

**D2. Restricted prescriptions.**
- The piece index uses prescriptions restricted to the groups (`maximalGroups`).
- LG-SPINE generalizes the per-class piece index to an arbitrary finite type, if its interface fixes `Prescription G`.

**D3. The centre loss.**
- The mass bound becomes (C₁√δ)^{n−n_sb} · C₁^{n_sb}.
- TARGET L1960 writes "a loss of at most C_0^n", then omits it in (redvine2). This is recorded as an exposition point.
- LG-SPINE re-proves the assembly. Per node, (δ/2L^{d−γ})^{n_sb} times the count leaves δ per node, so δ-smallness
  absorbs C₁^{n_sb}. If it cannot, LG-SPINE STOPS and reports.

**D4. New packet REGRED-LEAF.** A leafwise skeleton reduction: REGRED's chain re-run with `LeafProfiles` (R9a).
- Per S2's notes, only `nativeKernelValue`, `reducedStarProduct` and `kernelK_native_reduction` mention F.
- The attachment, fiber and phase lemmas are F-independent and are reused.

**D5. Accepted.**
- `Represents` omits redvine2's weight and phase, which only feed the mass bound.
- ζ(G_sb) is absorbed into w.
- S2a's DV entries are an extra 3-way split, which is harmless.

**D6.** The audit of S2a's L1956 reading is CONFIRMED (`RepAudit.lean`).

**The split of S2:**
- **LG-SPINE-AMEND2:** D1–D3 in lg-spine-u and flower-spine-u, plus R23(2) (`stage1_piece_bound` for the integral
  conjunct; drop FLOWER's proof copies).
- **REGRED-LEAF:** D4.
- **REP-ANALYTIC:** generic W5 (centre decomposition: unit-ball partition of unity, treelemma node centres) and W6
  (time-Fourier superposition with `XNormRestr` bounds, including the multi-time K̃^U).
- **S2 main (represents):** W1 (sel/partition), W2 (finer classes; S1 EQUIV named until READY), W3 (factorization over
  the U_j), then W7 (assembly), consuming the others.

## R25 — σ is indexed by the objects of 𝒞, with σ-independent gap pairs (S2 finding D7), 2026-11-05 ~03:00 UTC

**Source.** TARGET L1950: "for each vine-like object in 𝒞, we can specify whether it has SG, LG or ZG". The
prescription is per OBJECT of 𝒞, i.e. the specific objects from `vinechainlem`, with the canonical designation of R6.
It is not per group.

**Ruling.**
- **Designate the pair once, outside σ.** S2a amends `internalPair` and `hingePair` (RedSpliceGap, RedSpliceColl2).
  The gap pair of each group is taken from the group's designated object (S2's `groupObject`, i.e. the R6 canonical
  designation), and it is chosen BEFORE and independently of σ. The dart types must not depend on σ.
- **Then W1b follows.** For a fixed object, every internal pair gives the same gap kind (`object_hasGapKind_unique`),
  so `splicedGapIndicator` on G_sb equals the σ-restriction `selOf`.
- **The `VineHyperGapAmbiguity` example is consistent with this.** Two different adjoint designations of one hyper
  group are different objects; only the designated object enters 𝒞.
- **Re-check after the change.** S2a re-checks the `Sound` fields (`gapSpecification_hinge_kind`, `hingePair_spec`)
  under the new choice.

**R25 addendum (S2a-AMEND STOP), ~03:10 UTC.**

**(a) The designated object is the whole group object.** `groupObject` must not be a bare choice of any `O` with
`O.atoms ⊆ S`. It is:
- `vc ⟨S, a, b⟩` for a VC group;
- the group's own hyper object for HV and HVC (R6).

Sub-blocks are never designated.

**(b) The bridge is stated on gap kind, on the support, by cases.** For each group, on decorations with ε̃·Z ≠ 0, the
specified pair's gap kind equals the designated object's gap kind.
1. **Non-hinge joint.** The pair is inside the designated object (`objectJoint_pair`), so use
   `object_hasGapKind_unique`.
2. **Hinge with a residual object (skip VC, HVC).** The pair sits at a joint x or y of the residual object, and it lies
   inside the whole-group object.
3. **Whole-group hinge (a unit u = S).** The specified pair is the external out/in pair at the degree-4 joint a.
   - `vc_top_exists` gives 7 ≤ deg a + deg b, so such a joint exists.
   - Charge 0 at a degree-4 atom, plus conservation at a in the original molecule, gives: external gap = −(internal gap
     of the designated object at a).
   - Gap kind depends only on ‖r‖ (SG: 0 < ‖r‖ ≤ L^{−γ+η}; LG: ‖r‖ > L^{−γ+η}; ZG: r = 0), so the kinds agree.
   - Check that the decoration identification `Os_sb` (TARGET L2040) keeps the original conservation at a.

**(c) σ-independence of the choice still holds.**

## R26 — G8 case (4): the small-cell X-route goes through an X-terminal Theorem A (F6-2), 2026-11-05 ~03:40 UTC

**Research.** /home/scott/wt-scratch/research-g8-xroute/NOTES.txt.
- **The only small cell.** The only small-cell post is X = (a=b, c=d, ac, ad, bc, bd), proved by a degree count.
- **The bound holds.** Every case-(4) component whose M₁ reaches X satisfies 𝔄₀ ≲ L^{−η/10} (Theorem X, PROVED).
  - The proof: operation (c) on one chain, then (d) on the other. Carry ℓ through (Y) to X. Remove the (3,3) or (3,4)
    pair with Lemma A.3(4) (G8's `pairGainAt`). The leftover double bond c=d gains L^{−η/4}, using LG.
  - A mechanical check found 0 failures in 44,868 cases (|M₀| ≤ 16).
- **No gap and no erratum.** This is not a DH23 gap: DH23's Prop 10.4(2) proof (L1961–L1977) handles M′ = X under
  case (I), and A.3(4) (L2106) lists the needed system form.
- **Why the hypothesis appeared.** `¬YReachesSmallCell` is a formalization artifact: X's closed ladder cell has two
  parametrizations.
- **Exposition point.** DH23 L790 does not say which parametrization defines a closed cell's gap.

**Ruling: (R2).**
- **Theorem X.** Build `IsX`, `isX_of_smallCell`, `YRouteX`, `smallCell_route` (k ≤ 2), `xMinus_afree`,
  `route_bound_X`, `theorem_A_X` and `theorem_A_X_one`, per NOTES §5.1.
- **C4Main.** Branch on `YReachesSmallCell M₁`. Use `theorem_A_X` when it holds; otherwise use `prop104_two_proved`
  together with F6-1's decoration-level consumer.
- **Not needed.** (R1), dropping the small-cell hypothesis from Prop 10.4(2)′, is not needed.
- **Who does it.** The work goes to a parallel packet, G8-XROUTE, in its own scratch. G8 #7 continues F6-1, and the
  next G8 session glues the two together.

## R27 — TARGET remtame case (i): erase, do not cut; N1 and N2 stand (research-remtame-i), 2026-11-05 ~04:00 UTC

Research: /home/scott/wt-scratch/research-remtame-i/NOTES.txt. Checks: check_remtame.py, including a random test of
18,126 cases.

**Finding: an exposition gap at TARGET L2152 / L2218.** Case (i) says "cut at v and proceed normally", and L2218 says
"modified trivially". Neither is accurate.
- **(a) The premise "values fixed" is false.** Take a component of M − v that meets v only through an
  opposite-direction double bond to one atom; then the value is not pinned. This is harmless, because then c ≤ 2 and
  Δχ ≤ −2. CANDIDATE erratum.
- **(b) The pin is lost after the cut.** Pinned values are pinned by the charges of M_pre. After the cut, the zero-gap
  half can lie in a component whose own charges do not pin them.
- **(c) Prop 9.6 is false for a component with an unpinned zero-gap β-atom.** Counterexample: X = {a,b,c,v₁} with
  bonds c→a ×2, a→b, a→v₁, v₁→b, b→c ×2. Then 𝔄 ≥ c·C₁⁻⁴, against the required L^{−γ₀−3η²}.

(finalcount1) itself is unaffected.

**Ruling.**
1. **Erase, do not cut.** Model case (i) like case (ii) and like DH23 §10.5 (L1985: "we shall not make any cut at
   non-hinge degenerate atoms"). A zero-gap tame ε-atom of degree ≥ 3, met as Op 2's v₃ or Op 4's v, is ERASED: v and
   its bonds are removed, and no α- or β-atom is created.
   - In G3: generalize `HStep5` by dropping `ErasableAt`, and use `Good (R + (deg v − 2))`.
   - The imperfect-component bound becomes R + T, with T = Σ(deg v_e − 2).
2. **N1 and N2 (R18) stand as stated.** They remain conclusions of G3's Prop 9.5 package, and G8's `FinalDec` is
   unchanged. Weakening `betaGap` is NOT permitted: `Prop96At` is false without it (counterexample X).
3. **The erasure deviation.** Δχ = c − deg v.
   - If v is pinned (some component of M − v has nonzero net flux from v, which always holds at degree 3), then
     E_pre ≤ E_pos.
   - Otherwise E_pre ≤ (2L+1)^d · E_pos, and in that case deg v = 4 and c ≤ 2.
   - The required bound holds in every case for d ≥ 3. The case table is in NOTES L4.
4. **The case split at L2152** is read as "pinned, or not pinned (and then c ≤ 2)". This is DH23 10.5(4)'s "bridge, or
   Δχ ≤ −2".
5. **Two pre-existing case-(ii) items get their own ticket, DAMAGED** (research first):
   - (i) Final components that are imperfect with ε-degree < 4 ("damaged"), and surviving tame zero-gap ε-atoms. G8 has
     no case for them, and G3 delivers "ε-atoms LG or tame" where G8 needs strict LG.
   - (ii) TARGET's "ZG ⇒ tame by subpro (3)" when Op 2's v₃ is a hinge atom. G3's skip of such triangles must be shown
     to be sound, or replaced.

## R28 — S4 SUBPRO findings: hinge pair, atom-set containment, L ≠ 0, nonempty groups, 2026-11-05 ~04:30 UTC

**(1) `hingePair` is the lift of R25's `hingeOrigPair`.**
- S2a's `Cs.first`/`Cs.second` and the gap-specification entry pair then coincide, so hingeSG follows directly from
  the Z restriction (TARGET L2042–L2047; L2152 "SG with fixed (ℓ₁, ℓ₂)").
- The old `Classical.choose` over all `TripleAt` pairs goes. It could mix the two joints of a unit, which made (6)
  unprovable and Z differ from the source.

**(2) The changes are made in redsplice itself, not in S4's copies.** These are `GroupUnits.vl` (no VC/HVC group with
neither units nor a skipped vine), `ObjSpec.src` (skip-shape facts, `od R.added = e`), `ProperPair`, and (1).
- One tree is the single source of truth. Keep `amend-orig/` backups and add an R28 section to HANDOFF.md.
- Every new field must be PROVED by the construction (`exists_groupUnits`, `vc_top_exists`, `hvc_top_exists`).
- Then run a fresh rebuild and the `Sound` checks again. S4 then rebases subpro on that tree.

**(3) `contained` is atom-set containment.**
- TARGET L2040–L2051 says "subset", which is atom-set containment.
- The designation-level `Outside`/`IsContained` fails for hyper objects when the SG designation differs from the C₁ one.
- So lg-spine-u's `SubproSupport.contained` and G3's `SubproOblG.contained` are restated with atom-set containment
  (S4's `contained_atoms` form).
- Each consumer re-proves its use: lg-spine's counting cover, and G3's `vineLG_of_run`. If a consumer genuinely needs
  designation-level containment, it reports the configuration.

**(4) `hL : P.L ≠ 0` (typing: L ≥ 1).** It is added to `SubproObligation`'s discharge, and threaded from the gate's
L ≥ L₀.

## R30 — V5 Step 4c: the derivative loss at clause (b), and clause (c), 2026-11-05 ~05:30 UTC

**The finding (F1).** In replaceterm1, Q sits at k₁ and T at ℓ₁ = k₁ ± r. Shifting T by r gives the weight
M_Q · (T(k₁ + εr) − T(k₁))/|r|. That weight has 29d derivatives, but sumint (`propertyKj`, L1605) asks for 30d.

**Assessment.**
- This is a derivative-counting slack, not a mathematical failure. TARGET itself (L995) notes that the kernels have
  S^{40d,40d} inputs, of which only S^{10d,10d} is used.
- It is recorded as an exposition point at TARGET L1903.

**Ruling: option (ii).**
- Prove an internal variant of `sumint`, parametric in the weight-regularity exponent A, with A ≥ A₀ for some explicit
  threshold. The proof needs more than d decay for the unit-ball sums; give the exact threshold. The existing 30d
  theorem (B1.6 / V1 / V2) must be a special case.
- The bad-vine slot then consumes it at A = 29d.
- If sumint's Lean proof cannot be made parametric cheaply, fall back to option (i): derive 31d versions of the
  needed Prop 5.1/6.1 outputs as INTERNAL lemmas, using the 40d input slack exactly as in TARGET L995. Frozen
  statements stay untouched in both cases.

**F2, clause (c).** Prove the time-difference extraction lemma: Fourier-expand (J(s) − J(t))/|s − t|^{1−3η} in
(s₁, t₁) with an X^{1−η}-controlled bound. This is real analysis that TARGET (L1903) only asserts. Do the proof.

**F3.** The x*/y* reading of replaceterm1 for Vines II-a and II-b is recorded as a notation point.

## R31 — V5 Step 4: the representative of a twisted garden, invariants, slot labels (Step 4a findings), 2026-11-05 ~06:00 UTC

**(1) Representative independence.**
- TARGET's K^U_{(G′)} is built from G′'s skeleton G′_sk. That is the maximal collapse of the regular objects, which is
  unique by REG-STRUCT's structure theorem with uniqueness (C1).
- The statement must therefore use CANONICAL representatives: in each section, the skeleton of each representative is
  the REG-STRUCT canonical skeleton of its garden. Prove that every garden of the class has exactly one canonical
  representative (skeleton recoverability), and that LF twists map canonical representatives to canonical ones
  (`twistexplain`).
- `VineEstFull` then has the literal TARGET form.
- The current "∀ sections Z" form may stay only if the kernel's independence of the representative is PROVED.
  Otherwise it is stronger than TARGET and may be false.

**(2) Twist invariants.** The quantities in the bound are `RowSizes`, `RowCoherent`, `clLocalOrder1`, n_(2), n_(3)
and b. Prove that each is invariant under LF twists (TARGET `twistexplain`, L890–L902 / Remark), or prove the precise
relation that holds. Do not restate them per twisted garden.

**(3) Slot labels.** After a twist at the lower joint, check the four momentum slots of the twisted kernels against
TARGET's u₂₁/u₂₂ convention (tildeK2, tildeJ2), and record the result.

## R29 — DAMAGED: tame clusters are erased at the end (Op 5); eligible triangles; damaged components get their own bound. Revises R27 item 1. 2026-11-05 ~06:15 UTC

**Sources.**
- Research: /home/scott/wt-scratch/research-damaged/NOTES.txt (§7).
- Referee: /home/scott/wt-scratch/research-damaged-referee. Verdict: the core holds, and amendments A1–A5 are required.
  They are incorporated below.

**Findings.**
1. **TARGET L2152 is false for a hinge v₃.** It says "a ZG v₃ in Op 2 is tame by subpro (3)". Counterexample: an order-6
   couple whose only vine, (I-a), is merged into a hinge h. The triangle pair at h is a crossing pair with zero gap,
   and h is not tame. The referee re-derived this and found it in 300 of 300 random decorations.
   - The literal cut breaks N1.
   - DH23 L1777/L1985 has the same gap, under DH23's reading that the SG triple is fixed.
2. **Hinge cuts along a non-designated pair are not covered.** With 0 < |D−E| SG, Op 2 cuts h along a crossing pair,
   which DH23 L1815's vine-LG proof does not cover. This is a CANDIDATE exposition gap at DH23 L1815 / TARGET L2187.
3. **Single-atom tame erasure fails per component.** C1 gives A ~ L^γ, and C0 gives A = 1 against L^{−η⁵}. The bound
   (finalcount1) is unaffected.
4. **TARGET L2193/L2197 is false.** "imperfect = odd" for R = 1 contradicts L2189 ("exactly R if R=1") against L2218.
   CANDIDATE, harmless.

**Ruling.**
1. **Run model.**
   - Tame atoms are never cut in Ops 1–4.
   - A triangle is ELIGIBLE iff three things hold: its triples at v₁ and v₂ are SG; its pair at v₃ has nonzero gap; and
     at every hinge atom among v₁, v₂, v₃, the triangle pair is one of that hinge's two designated pairs (A1).
     Op 2 acts only on eligible triangles. The skipped v₁ and v₂ are cut in Op 3. Step 2 stops at
     `NoEligibleTriangle`, and DesRec becomes a theorem.
   - Op 4 makes only nonzero-gap β-cuts, and it stops at `NoBetaCut` (G8's `FinalDec.noBetaCut`).
   - A new Op 5 erases every tame ε-atom, one maximal connected tame cluster at a time, creating no α- or β-atom.
   - Requirement (d) also fixes the zero/nonzero status of every opposite pair. This costs at most 16^{n_sb}, which is
     absorbed like C_0^{n_sb}.
2. **N1 and N2 hold unconditionally** (R18 stands). All finalmol conclusions hold for M_fin, with one exception: the
   chains clause, and the vine clause pending O4, is claimed only for components WITHOUT tame atoms (A2; referee
   molecule F). Those are the only components Prop96At receives.
3. **G3.**
   - `NoEligibleTriangle` replaces `NoSGTriangle` (re-prove `cycles_of`, adding the hinge step of A1).
   - `DegenSGT` replaces `DegenSG`.
   - `NoBetaCut` is the Step-4 stop.
   - Add phase 5, with these conclusions: imperfect ≤ R + Σ_K(e_K + χ_K − 1 − s_K); strict epsLG; and perfect
     components are tame-free.
   - Retire StepE2/StepE4/`NoBetaCutAll` and the single-atom HStep5. The `G3EraseDev*` lemmas may be reused.
4. **`erase_cluster_deviation`.**
   - Pinned(K) means: some atom of K is unbalanced, OR some component of M − K receives nonzero flux, OR some atom of K
     has M_sb-degree < 4, whose value subpro (3) fixes to some k_j (A3).
   - If K is pinned, E_pre ≤ E_pos. Otherwise E_pre ≤ (2L+1)^d E_pos, and J ≥ |K| + 1.
   - Slack lemma: log_L I_K ≤ a(|K| − J) − η·e_K − C₀η⁵(|K| + e_K), with a = 2γ₀ + 5η², for d ≥ 3.
5. **G8.** Add a new theorem `Prop96DamagedAt` (the DCB, with Z counted for every R), proved from P101, rough96 and
   interpolation at θ = η³. It needs only FinalShape's isMolecule, classes, noLoop, noTriple, conn and nonempty, plus
   FinalDec's epsLG. Prop96At is unchanged.
6. **Assembly.** A_sb ≤ ∏_{Ops 1–5} I · ∏_components A. Each cluster contributes L^{−slack_K} with slack_K > 0, and
   the assembly is for 1/2 < γ < 1. Two glue obligations are named (A4): O3, the ladder polylog (log L)^{C(s+e)}, and
   O6.
7. **Ledger (A5).** All of these are CANDIDATES:
   - TARGET L2152, hinge v₃: erratum.
   - DH23 L1777/L1985: exposition gap, with the "as fixed" caveat.
   - DH23 L1815 / TARGET L2187, non-designated hinge cut: exposition gap.
   - TARGET L2193/L2197: erratum. The identification fails by L2189 against L2218; the Z = 0 failure is shown at
     graph level only.
   - TARGET L2152/L2218, single-atom erasure: exposition gap.

## R32 — S2 REPRESENTS: who produces the classes, VINEEST4, LEAFGATES (S2 session-3 questions), 2026-11-05 ~07:30 UTC

**(1) S2 owns the producer.**
- `Stage1Data` (members, `Cl`, `cls`, `sel`, the pieces) is construction data for `Stage1ReductionAt`, so S2 builds it. Never
  take it as a hypothesis.
- **Classes.** Use S1's congruence on `FamilyReconstruction` states (`congruent_equivalence_isVFamily`), restricted to
  canonical representatives (V5 Step 4b, R31(1)): the prime skeleton, with SKELETON's
  `existsUnique_prime_with_replacements`, so that each garden has exactly one state.
- **"Same G_sb across τ"** (TARGET Remark `twistexplain` (c)). Prove it as an EQUALITY where the construction allows it,
  making the relevant S2a data choice-free if necessary. If equality is blocked by `Classical.choose` inside
  `SpState.add`, prove instead that the piece value is invariant under the garden isomorphism, and use that. Choose the
  cheaper route and record why.
- **Order.** Do the vine-free case first (`represents_noVine`), then the general case.

**(2) VINEEST4.**
- It stays a single named input of S2 until V5 is READY. Transcribe V5's `VineEstCanon` statement verbatim; both worlds
  are built on the canonical universe types.
- The per-U_j application inside G_sk, and the decoration and time-splitting identity, are S2's to prove (W3/W4).
- The two scratch build worlds (vineest-s3/uni and represents/lg-spine-u) are unified in the final PORT phase.

**(3) LEAFGATES.**
- The leafwise gates at lower orders, `LeafwiseCoherentApproximationAt` and `LeafwiseIncoherentDecayAt`, are already
  proved (L3: RA1-LEAFWISE, INCOH-LEAFWISE, PL23-30D) and are fields of `SpineInputs`.
- S2 proves `stage1Reduction_of_leafGates : LeafGates(lower orders) → Stage1ReductionAt P`.
- LG-SPINE's assembly then composes it with its `SpineInputs` leaf fields: a glue step, recorded for the PORT phase.
  This changes how the spine input is discharged, not any frozen text.

**(4) Note for the PORT phase.** REGRED-LEAF copied 56 REGRED modules from vineest-s3/uni. Before landing, duplicate
module names across scratch trees must be resolved into one closure.

## R33 — Stage 1 interface defects F-TT and F-DERIV (S2 session-4 STOP), 2026-11-05 ~08:00 UTC

**F-TT: the root time.**
- **The defect.** `Stage1ReductionAt` allows `tt j ∈ Icc p (p+1)`. But (C2), the spliced integral, can match the class
  sum only if the root-adjacent constraint τ_b < tt_j is present.
- **The source and the frozen text differ.** TARGET `layergarden` (L761–763) states K_G(p+1, …), where that constraint
  is automatic. The frozen B1.2 (`Frozen/Theorems/Layergarden.lean`) quantifies `∀ t ∈ Ioc p (p+1)`, so the interface
  must handle t < p+1. Fixing tt = p+1 is not an option.
- **Ruling.** The spliced time domain in `Represents` carries the root constraints τ_b < tt_j for root-adjacent branches.
  Equivalently, layer-p boxes are truncated at tt_j. This is TARGET's own sumint domain clause (ii): "all variables are
  less than t".
- **Who does it.** LG-SPINE (AMEND3) amends `splicedTimeDomain` / `Represents`. It re-proves the consumers
  (`stage1_core_bound`, the spliced-bound inputs), using that the oscillatory time-integral bounds are uniform over
  boxes defined by order constraints with fixed endpoints.
- **Stop condition.** If a consumer genuinely needs untruncated boxes, LG-SPINE STOPS with the lemma.

**F-DERIV: the coherent-error norm.**
- **The defect.** The 2026-11-04 interface correction (lg-spine SPINE.md, "Prop 6.1 order-zero interface correction";
  pl234 ISSUE-XNORM) reduced the coherent-approximation error to `XNorm00Restr`, with no k-derivatives. It did so
  because higher-derivative Fourier guards were not known to be measurable.
- **Why it no longer holds.**
  - Snapshot 9's F80 a.e. guard (System.lean cc53aad3) addresses that measurability issue.
  - The spine does consume the derivatives after all: `SplicedAmplitudeBounds` needs SNorm 30d of the bond
    amplitudes, and the ladder bounds use them.
- **Ruling.** Restore TARGET's literal norm (layerregest3, `proplayer2`): the coherent error is bounded in
  X^{η,30d,30d} (couples) / X^{η,30d,0} (trees), i.e. `XNormRestr η 30d 30d` / `XNormRestr η 30d 0`. This supersedes
  the order-zero correction.
- **Owners.**
  - LG-SPINE (AMEND3) restates `CoherentApproximationGate` and `LeafwiseCoherentApproximationGate`.
  - The providers are PL23-30D (Prop 6.1 at the literal 30d norm) and RA1-LEAFWISE / REGREF. The provider check is
    part of AMEND3.
  - If a provider proves only the order-zero form, AMEND3 STOPS with the exact provider statement. Never weaken the
    consumer instead.
- **Flower.** FLOWER-SPINE follows both changes.

## R34 — FINALCOUNT-ASSEMBLY: quantifier order of the Prop 9.6/10.2 constants; atom renaming; the ρ change, 2026-11-05 ~09:00 UTC

**BLOCKER-1, the quantifier order.**
- `Prop96At`, `Prop96DamagedAt` and APPB's `dh23_prop_10_2` quantify `∃ Cstar, ∀ C1 ≥ Cstar` AFTER the size
  parameter m (|M₀| ≤ (1+log L)^m). But in `WTPrefix`, C₁ is chosen before ν, δ and D, and m ≥ 4(40d)^{2D+3} depends
  on D.
- The frozen order is fixed, so C₁ may NOT depend on D.
- **Ruling.** Restate these results so that m enters only through the large-L threshold R₀, as in DH23, where
  |M| ≤ (log L)^m only produces (log L)^{C(m)} factors that L^{η-power} absorbs for L ≥ L₀(m). The constant Cstar must
  depend only on d, γ and η.
- **New packet G8-QUANT** checks the APPB and G8 proofs for any genuine m-dependence of the multiplicative constant.
  If one exists, it STOPS with the exact lemma.

**M9, atom renaming.** G3's final conclusions need an infinite atom type, but `GBranch G.tree` is finite.
- **New packet ATOM-TRANSPORT** transports the molecule notions along `mapAtoms … Sum.inl` (V ⊕ ℕ) in both directions.
  The notions are `Object`, `IsBlock`, `IsVine`, `IsVC`, `HyperLikeRealization`, `IsDV`, `HasGapKind`, `IsTame`,
  `SubproOblG`, `UnselOK`, `DegenSGT` and `SourceLadderGaps`.
- It also proves that `countA` is invariant under the renaming.

**M1, the ρ change.** TARGET L2226 (ρ_fin ≥ ρ_sb − C₀ p_op) is proved by the assembly.

**Errata candidate.** At TARGET L2216, "p_sb ≤ p_op" should read ≤ 2 p_op, because Operation 2 cuts two critical SG
atoms. It is harmless, since η³/2 ≥ 8η⁶.

## R35 — TARGET L1913 (ii) fails for trivial couples and trees; the Bs″ argument is repaired (PL234-ENDPOINT STOP), 2026-11-05 ~09:40 UTC

**Finding.** TARGET L1913 (ii) says: "if q = L_r then J̃_Q(t,s) equals 0 if t = L_r".
- **Trivial couples and trees.** The claim is false there: J̃ ≡ 1 on [q, q+1], and `RegCpl.app … triv = F`. This was
  proved for the trivial couple (`pl234-endpoint/Triv.lean`).
- **Type 1 with q = q′.** It also fails for s < q.
- **Consequence.** The constant-in-t extension of a trivial approximant gives F where the true kernel F·1_{t>q} gives 0.

**Ruling: option 2.** In V5 Step 4c's Bs″ argument:
- **Trivial objects.** For trivial Q and T, use the exact kernel F·1_{t>q} in place of the approximant. It is exact, so
  there is no remainder.
- **Weakened hypotheses.** Weaken `hQ0`/`hT0` to nontrivial b and s ≥ L_q b. Prove them for the nontrivial approximants:
  type 2 with a nonempty positive chain, and the q < q′ branch with a nonempty chain, both vanish because their
  leading integral is ∫_q^q.
- **Re-check.** Confirm `replSum_decomp_ext` and the cancellation with the trivial pieces handled this way. Check also
  that layerregest10 (realness) holds for the mixed exact/approximant products.

**Ledger.** TARGET L1913 (ii) is a CANDIDATE erratum, harmless after the repair.

## R36 — FINALCOUNT-ASSEMBLY blockers: ghost triangles, vine ρ-loss, 2026-11-05 ~09:30 UTC

**(1) Ghost-triangle bookkeeping.**
- **The problem.** G3's `UStep2.excess` uses ΔF and ΔV_β = 3 − #α, which count ghost atoms. A ghost is an already-cut
  degree-2 atom of the triangle; DH23 L1777 cuts only atoms of degree ≥ 3.
- **What the bound actually needs.** The true Δ's are smaller by g, the number of ghosts. So the per-step bound must
  hold with the TRUE Δ's.
- **Why it should hold.** The ghost's two bonds have a fixed difference, its gap lying in a ball, so the triangle count
  gains.
- **New packet G2-GHOST** proves the ghost-aware triangle deviation: excesseqn2 with the true ΔF and ΔV_β for g ≥ 1
  ghosts. It uses G2's TriCount machinery and the sibling or relative-ball counts. G3's `UStep2.excess` is then
  restated with the true Δ's.
- **Stop condition.** If the bound fails for some ghost configuration, G2-GHOST STOPS with the configuration and the
  count. That would be a source finding at DH23 L1777–L1796 / TARGET Operation 2.

**(2) Vine ρ-loss.** The assembly needs `ladderLoss M (M.atoms \ S) ≤ C₀` for an IsVine S.
- **New packet VINE-RHO** proves it, from the direction facts for the inserted rung chains: each slot is a 2-cut, so
  `block_two_cut_opposite` applies per slot, across 14 slots in the 8 types, plus at most 15 template atoms.

**(3) Errata.** L2216 (p_sb ≤ 2 p_op) is already recorded as E19.

## R37 — Triple bonds at hinges (S4-NOTRIPLE STOP), 2026-11-05 ~10:30 UTC

**Finding.**
- TARGET Operation 1 (L2140) says the collected objects "also include any possible triple bonds in M_sb (see Prop
  subpro (2))". But subpro (2) only gives each triple bond a hinge endpoint. It does not put the triple bond in C₁ ∪ C₂.
- **Configuration.** Merge two whole-group SG VC units whose joints carry the bonds j1→b1, b2→j1 and b1→j2. This gives a
  hinge–hinge triple bond that lies in no collected object.
- It is not yet verified that this configuration occurs in a prime garden.
- DH23 L1775 has Step 1 cut triple bonds "in (c)" at a joint, along two of their bonds.
- Status: CANDIDATE exposition gap at TARGET L2140.

**Pigeonhole fact.** A triple bond between a hinge v and any atom w uses 3 of v's unit's 4 external bonds, two at each
joint. So two of the three are the full external pair of one joint. That pair is SG by subpro (5): at a degree-4 joint
of charge 0, its gap equals the vine gap.

**Ruling.**
- **(a) S2a, choice of designated pair.** When a hinge has a triple bond, `hingeOrigPair` chooses the joint whose
  external pair lies in the triple bond. It stays σ-independent (R25), since the choice depends only on the molecule.
  S4 re-checks subpro (5)/hingeSG and (6) crossing under this choice.
- **(b) G3, Step 1.** Add a `triple` constructor to `HStep1C`. It cuts the hinge endpoint of a triple bond along its
  designated pair, which now lies inside the triple bond. This is an α/β cut with the `UStep3` deviation. `NoTripleBond`
  after Step 1 is then PROVED, not assumed.
- **(c)** FINALCOUNT-ASSEMBLY consumes (b).
