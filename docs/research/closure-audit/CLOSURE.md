> **Note for readers.** This is the verbatim working report of an independent, read-only audit run on 2026-11-07, when development stopped. It uses the campaign's internal work-package names (FC23, C2-E-B, S2-ST, V5, …) and ruling numbers (R…). Paths under `<scratch>/`, `<repo>/` and `<worktrees>/` refer to working directories that are not included. The formalization report it was prepared for has not been published (decisions D14, D15).

# CLOSURE — what stands between origin/main and a proved `main_v2`

Auditor: O-CLOSURE-MAP (Opus), 2026-11-07 ~10:30–11:30 UTC, read-only. Main = origin/main `5c6d256c` (no
mathematical change since `b003e9b3`). Handoffs snapshotted with sha256 in `snap/` at 10:26 UTC; re-checked unchanged
after the stop order. TARGET = `WKE-Longer_times_Final_arXiv.tex` (sha256 `493eef6b…`).

The paper analysis (deliverable 4, now the priority) is in **PAPER-GAPS.md**. Machine-readable tree: **closure.json**.

## 0. Headline

- **Everything above the flower estimate is done or one landing away.**
  - VERIFIED here (Lean, against main's own build): the five frozen types equal the V2-chain gate types by `rfl`, and
    `main_v2` follows from `LayergardenFlowerV3Gate` and `LayergardenV2Gate` alone, using only sealed theorems and
    main's sorry-free assembly theorems; `#print axioms` = `[propext, Classical.choice, Quot.sound]` for
    `main_v2_of_propansatz`, `propansatz_v2_of_gates`, `fixedpoint_v2_of_closed_gates_v3`, `wkeTaylor`,
    `nlsAkBridge` (check file `check/AxChain.lean`; sanity: `main_v2` itself shows `sorryAx`).
  - VERIFIED here: **`layergarden_v2` is proved, unlanded.** `WaveTurbulence.VineEst.layergarden_v2_proof` in the
    batch-4b-3 port worktree (`<worktrees>/port-b4b3`, branch `w/port-b4b3` from main
    `bf597bcf`; targeted `lake build` of `VineEst.V5Proof` finished 10:05 UTC, exit 0, 19157 jobs) has exactly the
    frozen type (`rfl`) and standard axioms (check file `check/AxV5f.lean`; sanity: the frozen anchor shows `sorryAx`).
    The packet's own PROGRESS.md still says "build-3 running"; nobody recorded the success. Remaining for the seal:
    R143 kernel replay, land_check on main, seal audit.
- How the checks were run (reproducible, read-only, nothing built): plain `LEAN_PATH` runs fail on this machine at
  `vm.max_map_count = 65530` ("failed to read … .olean.private"). Instead `lean --setup check/*.setup.json` with lake's own
  per-module setup files (copied from `.lake/build/ir/**.setup.json` of the built worlds, project `.olean.private`
  added so proof bodies are visible), niced, one at a time, ~3 s each. Worlds: `WaveTurbulence-dev` (main; no import
  olean newer than the V2Chain oleans) and the port-b4b3 worktree.
- **The only open mathematics on the path is `layergardenFlower_v3`'s three owner inputs** (`hFam`, `hCut2`,
  `hCut2Zero`); the fourth (`hStage1`) is closed by the same 4b-3 port.
- **13 OPEN leaves**, of which **3 are route-uncertain** and one sub-item has **no owner and no route** (§2).
- **Critical path:** `V5TopClassBound` (SCOPED only; 4.7–7.6k lines; riskiest) → S2-ST vine piece
  `VineCaseRepresentsSTψTop` → producer of `Stage1ReductionAtSTBLDψTop` → FC23 E3–E5 (`FC23UniformCut1At`) and C2-E-B
  `ComponentClassBoundAtT` → flower-top's four-binder theorem ported to main → seal `layergardenFlower_v3`,
  `fixedpoint_v2`, `propansatz_v2`, `main_v2`. In parallel and not on the longest chain: `TopIncoherentDecayGate`
  (C2-B-TOP), the 4b-3 landing.
- **Live anchors sealed: 0 / 5.** The meter's 16 / 27 counts no live theorem (§4).

## 1. The tree

Status vocabulary: PROVED-ON-MAIN; PROVED-IN-SCRATCH (consistent world per R138: yes/no); STAGED (named input: owner,
current agent); MISSING (no one working on it); OPEN = STAGED or MISSING. "Current agent": all agents were stopped by
the owner during this audit, so "current" means the last session that held the item.

### 1.1 The five live anchors and the chain above the flower estimate

```
main_v2  (Frozen/Theorems/MainV2.lean, DRAFT_SORRY; TARGET L314–L320, proof L795–L823)
└─ MainGlue.main_v2_of_propansatz            PROVED-ON-MAIN (XChain/V2Chain/MainV2.lean)
   ├─ PropansatzV2Gate = type of propansatz_v2   (rfl, verified)
   └─ NlsAkBridgeGate  = type of nlsAkBridge     SEALED (TARGET L540–L566, L817–L819)

propansatz_v2  (Frozen/Theorems/PropansatzV2.lean, DRAFT_SORRY; TARGET L689–L707, proof L795–L823)
└─ V2Chain.propansatz_v2_of_gates             PROVED-ON-MAIN (XChain/V2Chain/PropansatzV2.lean)
   ├─ LayergardenV2Gate  → layergarden_v2
   ├─ FixedpointV2Gate   → fixedpoint_v2
   └─ WkeTaylorGate      = type of wkeTaylor   SEALED (TARGET L752–L758)

fixedpoint_v2  (Frozen/Theorems/FixedpointV2.lean, DRAFT_SORRY; TARGET L780–L794, proof L2306–L2338)
└─ V2Chain.fixedpoint_v2_of_closed_gates_v3   PROVED-ON-MAIN (XChain/V2Chain/FixedpointV2.lean)
   ├─ LayergardenFlowerV3Gate → layergardenFlower_v3
   ├─ LayergardenV2Gate       → layergarden_v2
   ├─ WkeTaylorGate           SEALED
   └─ (internal) X2E.oX2Exp, Cpl.oX3Cpl   PROVED-ON-MAIN (TARGET L2309–L2338 moment/Chebyshev steps)

layergarden_v2  (Frozen/Theorems/LayergardenV2.lean, DRAFT_SORRY; TARGET L761–L779, proof L1293–L2255)
└─ VineEst.layergarden_v2_proof   PROVED-IN-SCRATCH, port-b4b3 worktree (main-based; lake-trace consistent: YES;
   │                              R143 kernel replay: not run; not landed)            [verified here]
   └─ Spine.layergarden_v2_of_V5                         PROVED-ON-MAIN (Stage1/Producer.lean, batch 4b-2)
      ├─ Spine.stage1ReductionGate_of_V5'                 PROVED-ON-MAIN (Stage 1, TARGET L1927–L2053)
      │   ├─ Vine.Param.vineparam, Spine.leafwise_incoherent_decay, Spine.leafwise_coherent_approximation  ON MAIN
      │   └─ WTPrefix VineEstCanonLayerHalfMK
      │       └─ VineEst.vineEstCanonLayerHalfMK = KindFinal.vineEstCanonLayerHalfMK_of_gates (main gates)
      │          PROVED-IN-SCRATCH, port-b4b3 (TARGET vineest L1742–L1922; W2 + V5-KIND, two-key PASS R136/R144)
      ├─ Spine.layergarden_v2_of_stage1_finalCount        PROVED-ON-MAIN (batch 3)
      └─ FinalCountAsm.finalCount_half                    PROVED-ON-MAIN (batch 5; TARGET L2101–L2255, 1/2<γ)
```

**Answer to the brief's specific question:** `fixedpoint_v2`, `propansatz_v2` and `main_v2` need nothing beyond
`layergardenFlower_v3`, `layergarden_v2` and what is already on main. Checked by compiling the composition
`main_v2 ⇐ main_v2_of_propansatz (propansatz_v2_of_gates hL (fixedpoint_v2_of_closed_gates_v3 hG hL wkeTaylor)
wkeTaylor) nlsAkBridge` against `type_of% @main_v2` in main's built world (`check/AxChain.lean`, exit 0). Remaining
non-mathematical work: the proof-body edits in the four `Provider/*V2/V3.lean` files (all four are empty shells on
main) plus seal audits.

### 1.2 `layergardenFlower_v3` (Frozen/Theorems/LayergardenFlowerV3.lean, DRAFT_SORRY; TARGET L2279–L2305)

```
FlowerTop.layergardenFlower_v3_of_owners'   PROVED-IN-SCRATCH (flower-top, frozen world build-final8, 143 modules,
│   exact type vs frozen v3, standard axioms, second key PASS R104).  Consistent world per R138: NO — a symlink farm
│   over main's live oleans of ~02:00 UTC, no hash ledger; main has been rebuilt by four landings since. Must be
│   re-ported (120 FlowerTopPort copies) anyway.
├─ discharged inside: hcount (finalCount_half, main); plain clause (plain_of_family: M→∞ limit of hFam, DCT);
│  couple half (coupleHalf_of_spine / FlowerP7, TARGET L2312); P5 coarse/ladder witnesses; leafwise inputs (main)
├─ hStage1 : LGSpine.Stage1ReductionGate     PROVED (stage1ReductionGate_of_V5' + port-b4b3 HalfMK; land 4b-3)
├─ hFam : WTPrefixP (FC23UniformCut1Input C U)   STAGED — owner FC23 (Opus; last session 11, CHECKPOINT)   OPEN
│   (TARGET L2283, L2294; E33.  Note: tighter than the frozen plain clause by L^{(80d+2)Pm} δ^{6νN}; FC23 S3 shows
│    the tightness is load-bearing for the cut1 interpolation. Fine against the (100d)³P allowance.)
├─ hCut2 : Cut2EB.PositiveCut2FrozenInput     STAGED — owner C2-E-B (Opus; session 19 in progress at stop) OPEN
│   (TARGET L2285, L2299–L2300; E35)
└─ hCut2Zero : Cut2ZeroFrozenInput            STAGED — owner C2-E-B; not started                            OPEN
```

### 1.3 Below `hFam` (FC23UniformCut1At)

| Node | Lean | Status | Owner / last agent | TARGET |
|---|---|---|---|---|
| E1 cut1 family = component sums on C2-C's retained cut | `FC23Int.flowerWeighted_eq_components_retained` | PROVED-IN-SCRATCH (eb world; R138 no) | FC23 S8 | L2287–L2288 |
| Agreement, slot form | `FC23Bond.fc23Weight_eq_regionBondWeight_mul`, `slotProduct_coherent` | PROVED-IN-SCRATCH (bond world; no) | FC23 S11 | L1464, L899 (layerreg1) |
| C2-B-COH block gate | `FC23Coh.c2bCohBlockGateFin` | PROVED-IN-SCRATCH (coh world; no) from main's gates; two-key PASS (R137) | C2-B / FC23 | L1145–L1232 |
| **O6** row-form agreement | `RowTopAgreementCouple/Tree` (probe statements) | STAGED, small | FC23 | layerreg1 |
| **O7** E2 regroup of the cut1 family into twist-closed slices | `FC23OrbitRegroup` | STAGED (owner C2-E-B, shared OG; C2-E-B proved the marked-face version `pointedFace_sum_orbitsT'`) | FC23 + C2-E-B | — (E33/E35 architecture) |
| **O8** E3 slice premises + piece bound | — | MISSING as code (plan in FC23 S11 "Do 3") | FC23 | L2293–L2297 |
| **O9** E4/E5 count and budget into FC23's B | — | MISSING as code | FC23 | L2302–L2304 |
| weighted Stage-1 gate | `Stage1ReductionAtSTBLDψTop` | STAGED (→ §1.5) | S2-ST | L1927–L1960, L2293 |

### 1.4 Below `hCut2`, `hCut2Zero` (C2-E-B)

| Node | Lean | Status | Owner | TARGET |
|---|---|---|---|---|
| face regroup, glued faces, plain j₂≥1 norm chain | `pointedFace_sum_orbitsT'`, `gluedFaceGood`, `flowerSumP_plain_enorm_leT` | PROVED-IN-SCRATCH (world m2; R138 fresh hash rebuild not run) | C2-E-B S18 | L2299 |
| weight split pin · stem · top | `blockPhi_eq_split` | PROVED-IN-SCRATCH | C2-E-B S18 | L2283–L2285 |
| **O10** per-class bound | `ComponentClassBoundAtT bd` | STAGED (needs the widened gate O5, C2-B-COH for width-2 slices, world m3, compI → S2-ST bridge) | C2-E-B | L2299 |
| **O11** budget `perRepT bd ≤ T`, root-label (flux) sum | `FTFluxCode` (in progress) | OPEN; S19 found session 18's free block-label sums diverge at anchor labels, repair in progress | C2-E-B S19 | L2299 |
| **O12** nonplain patterns (cut2 factor 1) | — | MISSING as code | C2-E-B | L2299, L2331 |
| **O13** j₂ = 0 clause (`Cut2ZeroCore`; L^{−P/9} from the L budget, research-cut2 §5) | — | MISSING as code | C2-E-B | L2285 |

### 1.5 Below `Stage1ReductionAtSTBLDψTop` (the shared weighted Stage-1 gate; R142)

| Node | Lean | Status | Owner | TARGET |
|---|---|---|---|---|
| statement + assembly from pieces | `S2ST.stage1STBLDψTop_of_pieces` | PROVED-IN-SCRATCH, world `s2-st/mw` (R138-certified, R145) | S2-ST S17 | L1927–L1960 |
| **O3** vine pieces | `VineCaseRepresentsSTψTop` (T1–T6) | STAGED; S18 launched then stopped | S2-ST | L1942–L1960, L1742 |
| **O4** vine-free pieces (top weights) | `NoVineRepresentsSTψTop` | STAGED | S2-ST | L1942–L1960 |
| **O1** weighted V5 class bound + continuity export | `V5TopClassBound`, `twistedRecenteredModCXTop_continuousOn` | STAGED; SCOPED only, Phase 1 not started (lead + helper uni-top-bond) | V5-SPACE-EXT / v5top | L1742–L1922 |
| **O2** weighted incoherent decay | `TopIncoherentDecayGate` (+ general `StarIncoherentDecayGate`) | STAGED; root-rate pieces compiled, leafwise layer + gate open | C2-B-TOP | L953–L1058 (W at L991–L1012) |
| **O5** widened gate with branch-local stem weights ω (FINDING-STEMROW) | `S2ST/Top/SlotWeight` defs only; no statement | MISSING as a statement; sub-items: (a) centre-uniform moment version of C2-A `quadratic_resonance_fourier_measure` — **unowned**; (b) C2-B-COH accepting ρ-localized measures — unverified; (c) stem cutoffs at vine-region top branches — S2-ST routes them to V5Top, V5Top SCOPE §6.2 item 1 excludes ρ-localized weights — **no owner, no route** | S2-ST / C2-B / v5top | L2285, L2299–L2300 |
| leafwise gates, VINEPARAM | `Spine.leafwise_*`, `Vine.Param.vineparam` | PROVED-ON-MAIN | — | L953, L1145 |

## 2. The OPEN list

| # | Leaf | Owner | Last agent | Owner's size estimate | My assessment |
|---|---|---|---|---|---|
| O1 | `V5TopClassBound` + Top continuity export | V5-SPACE-EXT (v5top) | uni-top lead + uni-top-bond (Opus) | 4.7–7.6k (SCOPE); 3.3–7k (research-internal) | **route uncertain**: fork of 598+34 V5 modules; owner's "riskiest" step (collapsing selected exceptional rows via ZpSurj.coherent) unproved; does not cover O5(c) |
| O2 | `TopIncoherentDecayGate` (general star form) | C2-B-TOP | c2b-top (Opus) | 2–3.5k | route clear: TARGET proplayer1 already carries W; C2-B-REG's method with root jets; first layers compiled |
| O3 | `VineCaseRepresentsSTψTop` | S2-ST | S18 (Opus) | ≈4–4.7k for O3+O4 (≈2.4k pre-planned) | route clear given O1/O2 (templates FX/ContMX compiled); blocked on O1's final shape |
| O4 | `NoVineRepresentsSTψTop` (top weights) | S2-ST | — | (in O3's) | route clear |
| O5 | widened Stage-1 gate with stem weights ω (W1–W4) | S2-ST (+ C2-B, v5top, C2-A) | S17/S19 handshake | none | **route uncertain**; O5(c) **no route as scoped** (V5Top excludes ρ-localized resonance cutoffs at region tops) |
| O6 | `RowTopAgreementCouple/Tree` | FC23 | — | 0.2–0.5k | route clear (slot form proved) |
| O7 | FC23 E2: cut1 family into twist-closed slices with S2-ST's premises | FC23 + C2-E-B | FC23 S11 | none | route clear (C2-E-B's regroup proved for marked faces; adapt to empty marking) |
| O8 | FC23 E3 slice premises + piece bound | FC23 | — | none | route clear, laborious |
| O9 | FC23 E4/E5 budget into B (cψ^{12N} absorbed by δ^{2νN}) | FC23 | — | none | route clear (arithmetic) |
| O10 | `ComponentClassBoundAtT` | C2-E-B | S18/S19 | none | route clear given O5 |
| O11 | `perRepT ≤ T`, flux root-label sum | C2-E-B | S19 | none | **route uncertain**: a divergence in the session-18 budget was found at stop; repair (`FTFluxCode`) unfinished |
| O12 | nonplain patterns, j₂ ≥ 1 | C2-E-B | — | none | route presumably clear (cut2 factor 1); nothing written |
| O13 | j₂ = 0 clause | C2-E-B | — | none | route clear on paper (research-cut2 §5, inequality (5.1)) |

Not counted as OPEN (no new mathematics): land 4b-3 (`layergarden_v2_proof`, `vineEstCanonLayerHalfMK`); port flower-top
and the FC23/C2-E-B/S2-ST/C2-B-COH/C2-B-TOP/V5Top closures into one main world (resolving the R130 LS-spine clash and the
draft-world `chi0` clash); the four provider bodies; four seal audits.

**Circular staging (packet level, not logical):**
- FC23 ⇄ S2-ST: FC23 needs S2-ST's `Stage1ReductionAtSTBLDψTop`; S2-ST's T3 needs FC23's `RowTopAgreement*` (O6).
- S2-ST ⇄ C2-E-B: S2-ST would not widen the gate (O5) until C2-E-B confirmed W1–W4; C2-E-B could not prove O10 until the
  widened statement exists. C2-E-B S19 answered "yes, with two provisos", and both provisos land back on S2-ST/C2-A
  (moments) and on V5Top (class-commonness jointly with the top factors).
- S2-ST → V5Top → (refuses) → S2-ST: S2-ST routes region-top stem weights to V5Top; V5Top §6.2 says it cannot carry
  them. Nobody owns them (O5(c)).

**Same input staged in different forms:**
- The weighted Stage-1 gate: FC23's `Stage1ReductionAtSTBLDψTopN` and S2-ST's `Stage1ReductionAtSTBLDψTop` are
  identical up to namespace qualification (checked by normalized text diff). C2-E-B needs a *different, wider* form
  (branch-local ω), not yet stated.
- Weight presentation predicates: `GPresented` (probe/V5Top/S2-ST gate), `StarPresented` (C2-B-TOP general gate),
  `NodeWeightLocallyPresented` (S2-ST W2), global `SpatialMeasure` nodeWeight (V5Top §6.2). R145 ordered one predicate;
  not reconciled, and V5Top says the local one does not imply the global one for resonance cutoffs.
- V5 class input: `V5ClassInput` (FC23 S6) → `V5BondClassBound` (FC23 S10/S11 = VineSpaceB, landed as definitions in
  4b-1c) → `V5TopClassBound`. The first two are superseded.
- Binder alignment `0 ≤ B₀` vs `0 < B₀` in `UniformTermCertTargetK` (R141/R143), for any VineSpaceB port.

## 3. OFF-PATH (one paragraph)

On the path: S2-ST (O3–O5), V5Top lead and helper (O1), C2-B-TOP (O2), FC23 (O6–O9), C2-E-B (O10–O13), port-b4b3 (lands
`layergarden_v2` and `hStage1`). Off the path to `main_v2`: V5-SPACE-EXT's `V5BondClassBound`/VineSpaceB proof modules and
the batch-4b-1c statements (superseded by `V5TopClassBound`, R142; at most reused as machinery); S2-ST's session-16
bond-multiplier `Stage1ReductionAtSTBLDψ` and FC23's node-label `STBLDψInput` (superseded); flower-top's STB2 migration
and `Stage1BothBridge` (unused after R104); the phased STB/STB2/STBL producers except as the base of the ψTop gate; all
γ ≤ 1/2 research (needed only for the superseded v1 anchors); `layergardenFlower_v2` work of any kind. C2-B-COH is on
the path only for C2-E-B's width-2 regular-couple slices; FC23 does not need it (agreement makes its factors external).
Main's growth from 443k to 1.37M lines since 2026-11-05 21:23 is the ports of batches 3, 4a, 4b-1/1b/1c/2 and 5, which
are the `layergarden_v2` chain; much of the volume is duplicated copies rather than new mathematics, and none of it
moves the flower estimate.

## 4. Meter check

The README meter (`5c6d256c`): "estimated completion 91.0 %", "frozen theorems sealed: 16 / 27".
- The 11 unsealed: `main_v1`, `propansatz_v1`, `layergarden_v1`, `fixedpoint_v1`, `layergardenFlower_v1` (γ ∈ (0,1);
  superseded by the γ ∈ (1/2,1) successors, D9/D10), `layergardenFlower_v2` (max-form cutoffs; superseded by v3, D13),
  and the five live ones.
- **6 are superseded** and should leave the denominator: the five v1 anchors and `layergardenFlower_v2`. Strictly,
  they are not *provably* unsealable — the v1 anchors would need the γ ≤ 1/2 repair of DH23 Prop 9.6 (refereed route,
  not formalized, out of scope by D9), and v2 is a different (non-smooth) statement nobody consumes — but no campaign
  work targets them, so counting them is misleading. Honest denominator: 16 + 5 = 21 → **16 / 21 sealed, live 0 / 5**.
- **Proposed metric:** report (i) live anchors sealed **0 / 5** (→ 1 / 5 after 4b-3 lands and is sealed; the other four
  all wait on the flower estimate); (ii) **OPEN leaves on the path to `main_v2`: 13**, of which 3 route-uncertain and 1
  sub-item with no owner; (iii) per-leaf owner estimates where given (O1 4.7–7.6k, O2 2–3.5k, O3+O4 4–4.7k, O6
  0.2–0.5k; others none). Drop the lines-of-Lean ratio (501 % of the blueprint estimate) and the P4 packet percentage
  (94 %), which measure volume, not distance.
