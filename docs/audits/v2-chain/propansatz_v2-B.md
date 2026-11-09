# SEAL-AUDIT `propansatz_v2`, KEY-B (refute-first, independent)

Anchor `WaveTurbulence.propansatz_v2` (`WaveTurbulence/Frozen/Theorems/PropansatzV2.lean`). Seal commits on origin/main:
`a2216712` ("Seal propansatz_v2 with its proved assembly") and `7d98ae17dae8fc7cf902e852badd5ab0a494e1c8` ("manifest: ABI
hash of the sealed propansatz_v2"). Final main `1987105a` (= origin/main; the only later commits are main_v2's seal and
ABI, outside this closure). Freeze `8d7ccb4a` (D10). Binding rules: `seal-prep/audit-briefs/AUDIT-COMMON.md`; anchor brief
`AUDIT-propansatz_v2.md`. Work dir `/home/scott/wt-scratch/seal-audit-propansatz_v2-B/`. Clean export: `export/` =
`git archive 7d98ae17`. Nothing outside this directory was edited, and nothing was pushed. Every Lean process was run niced
(`nice -n 10`), one heavy process at a time.

Order kept: I reconstructed the source (h, step 1) before reading the Lean statement or docstring (`notes/h1-source-reconstruction.md`,
21:16 UTC). I wrote the binder table (`notes/h2-binder-table.md`, 21:24 UTC) and all my own results (`notes/own-results.md`)
before opening the brief's claim appendix or `seal-prep/logs/live-*` / HANDOFF.md.

## Verdict table

| Item | Verdict | One-line evidence |
|---|---|---|
| (a) Anchor bytes | **PASS** | Only change since 8d7ccb4a: body `by sorry` → `by exact WaveTurbulence.Provider.propansatz_v2`. Prefix `684d371b…`, suffix `9f481990…` recomputed = manifest. Manifest entry: only `state`, `abi_sha256` changed. 100/100 closure hashes match. Guard OK; module check PASS (13118 files) |
| (b) Provider | **PASS** | Does not import its anchor (source + Lake closure). Statement text byte-equal (434 B). Types `==` (alpha-equal); `Expr.equal` differs only by 2 hygienic instance-binder names; pp.all text equal; `rfl` OK. Body = brief's assembly exactly. Export used only by the anchor. Proof modules private `import`. Anchor-only probe sees 102 project modules (100 defs + provider + anchor) and no proof-closure constant |
| (c) Axioms | **PASS** | `[propext, Classical.choice, Quot.sound]` for the anchor, the provider, `propansatz_v2_of_gates`, `propansatzS_of_gates`, `propansatz_body_of_context`, `layergarden_v2`, `fixedpoint_v2`, `wkeTaylor`, `regularAsymptotics`, `layergardenFlower_v3` (+ provider), and the 5 glue lemmas |
| (d) Hidden hypotheses / vacuity | **PASS** | The assembly's 3 binders are discharged by exactly the 3 SEALED anchors (kernel-checked defeq). The witnesses are built by the layer induction. All glue inputs are reachable kernel-replayed theorems. No project axiom/opaque/sorry. Non-vacuity compiled (P6). `AnsatzAt` contains all of source (1)–(4), with §4.1 deviations only |
| (e) ABI | **PASS** | Pre-seal `3882921f…` reproduced in a freeze environment = manifest DRAFT ABI. Post-seal `cc09a048…` reproduced = manifest. `#print` differs only in the value line. pp.all type byte-identical (3213 B, sha256 `6c1f1a34…`) |
| (f) Kernel replay | **PASS** (quick) | 219,354 constants from 11,170 modules; REPLAY OK, no shim, nothing missing, no project axiom/opaque/unsafe/partial, no sorryAx/ofReduceBool/trustCompiler user. 8231 s replay, 2:17:59 wall, max RSS 5.89 GB. All 11,170 replayed modules' oleans trace back to the seal commit's sources. Quick mode: 40,618 VineParam certificate proofs statement-only |
| (g) Status fields | **PASS** | DRAFT_ANCHORS 7 (list below); UNREGISTERED_SORRIES 0; DRAFT_IMPORT_VIOLATIONS 0; SEALED_THIS_TURN `WaveTurbulence.propansatz_v2` |
| (h) Five-bin table | **PASS** | 25 expanded rows: SOURCE 0, STANDING 19, TYPING 6, RULED 1 (`1/2 < γ`, D9/D10/E1), **EXCESS 0**. Conclusion fidelity row by row; no weakening beyond D1–D7 |

## (a) Anchor bytes

- `git log` of the anchor path: only `8d7ccb4a` (freeze) and `a2216712` (seal). `git diff 8d7ccb4a 7d98ae17 -- <anchor>` is the
  one-line body change. My region hasher (`tools/hash_regions.py`) is an independent re-implementation of the guard's
  convention: the prefix runs through the newline ending the PROOF_BEGIN line, and the suffix starts at the PROOF_END line.

  | | file sha256 | prefix | suffix | body |
  |---|---|---|---|---|
  | freeze 8d7ccb4a | `edd71ce8df838648…` (= brief) | `684d371b5ff772d5b2edfc0e2eab874ec0bdcd9d0507a6a5a1ee39bea6eea75b` | `9f48199048606af986e4911abed0172f6e65c9c8c91f1c2874961ad85a7ea8d0` | `  by sorry` |
  | seal 7d98ae17 / main 1987105a | `86e23094be3a436eee2a5a3ec8607fe22ebd2ba91dc9da995aecdaae2cdd7626` | same | same | `  by exact WaveTurbulence.Provider.propansatz_v2` |

  Manifest prefix and suffix are equal to these values.
- Manifest entry (`tools/manifest_diff.py`), freeze → seal: CHANGED `abi_sha256` (`3882921f…` → `cc09a048…`) and `state`
  (`DRAFT_SORRY` → `SEALED`); nothing else. The pre-seal manifest (`a2216712^`) is identical to the freeze entry, and main
  1987105a's entry is identical to the seal entry. All 100 `definition_closure` hashes match the export files, and the
  closure list is unchanged since freeze.
- On the clean export: `check_frozen_anchors.py` → `FROZEN-ANCHOR GUARD OK`; `check_lean_modules.py` → `PASS (13118 Lean
  files)` (`evidence/guard-and-modules.out`). `check_index.sh` needs a git work tree (`git checkout-index`), so I ran its two
  scripts directly, as AUDIT-COMMON allows.

## (b) Provider (`WaveTurbulence/Provider/PropansatzV2.lean`, sha256 `f307a4b8…6702`)

- **No self-import.** The source imports are `public import` of Mathlib and the anchor's 5 `Frozen.Defs.*`, plus plain
  `import` of `Frozen.Theorems.{LayergardenV2, FixedpointV2, WkeTaylor}` and `Foundations.XChain.V2Chain.PropansatzV2`. Lake's
  resolved closure (`.lake/build/ir/WaveTurbulence/Provider/PropansatzV2.setup.json`, 19,588 modules) does not contain
  `WaveTurbulence.Frozen.Theorems.PropansatzV2`. The guard's reverse-import check is OK. The kernel replay's full
  olean-header closure contains the anchor only as the root.
- **Statement.** The statement text is byte-equal to the anchor's (434 bytes), with identical `open`/`universe`/public-import
  context.
  - Elaborated types: `prv.type == anc.type` is **true**. `Expr.equal` is **false**; the parallel Expr walk (probe A1) finds
    exactly 2 differences: the binder names of the anonymous instance binders `[MeasurableSpace Ω]` and
    `[IsProbabilityMeasure μ]`, `inst._@.WaveTurbulence.Frozen.Theorems.PropansatzV2…_hyg.17/22` vs
    `inst._@.WaveTurbulence.Provider.PropansatzV2…_hyg.17/22`. Hygiene puts the module name into these names; binder infos
    and every subterm are identical.
  - `pp.all` prints both as `inst✝` and the texts are equal; the seal log says "PROVIDER TYPE TEXT = ANCHOR TYPE TEXT".
  - `example : type_of% @WaveTurbulence.propansatz_v2.{u} = type_of% @WaveTurbulence.Provider.propansatz_v2.{u} := rfl`
    elaborates.
- **Body.** The replay prints the provider value as `WaveTurbulence.V2Chain.propansatz_v2_of_gates.{u} WaveTurbulence.layergarden_v2
  WaveTurbulence.fixedpoint_v2.{u} WaveTurbulence.wkeTaylor`, which is the brief's assembly exactly. The anchor value is
  `WaveTurbulence.Provider.propansatz_v2.{u}`.
- **Export use.** `Provider.propansatz_v2` / `Provider.PropansatzV2` occur, at seal and at final main, only in the anchor
  (import + body) and in the provider's own docstring. The anchor itself is imported only by the root `WaveTurbulence.lean`;
  it is later consumed by main_v2's chain.
- **Private proof imports; freeze environment.**
  - Probe A1 (my setup generator `tools/mksetup.py`: the anchor's Lake setup plus the anchor's `.olean`/`.olean.server`
    only, no private parts) imports only the anchor module.
  - It loads 11,077 modules, of which 102 are project modules: exactly the 100 manifest-closure `Frozen.Defs`, the provider
    and the anchor.
  - Not visible there: `V2Chain.propansatz_v2_of_gates`, `propansatzS_of_gates`, `PropansatzV2Gate`,
    `Induct.propansatz_body_of_context`, `Induct.InductContext`, `layergarden_v2`, `fixedpoint_v2`, `wkeTaylor`,
    `layergardenFlower_v3`, `Provider.layergarden_v2`. Visible: only `Provider.propansatz_v2` and `propansatz_v2`.
  - The anchor's own Lake closure has the same 101 project modules (100 closure defs + the provider), and the manifest
    closure equals it minus the provider, in both directions.
  - At freeze the provider stub had an empty public part, so the elaboration environment is unchanged; (e) confirms this.
- **Independent restatement.** In the anchor-only environment I wrote the statement with `WTPrefix`, `IsGaussianData` and
  `AnsatzAt` unfolded by hand (`probes/A1/KeyBProbeA1.lean`). It elaborates against `:= propansatz_v2`. The project-owned
  constants in the type are exactly `WTPrefix`, `WTParams` (+ `.γ .d .D`), `IsGaussianData`, `Mom`, `AnsatzAt`, all from
  closure modules.

## (c) Axioms

Probe P4 imports the provider's Lake closure plus the anchor and provider; P5 uses `layergardenFlower_v3`'s setup. Every
line below is `depends on axioms: [propext, Classical.choice, Quot.sound]`:

- the anchor, the provider, `propansatz_v2_of_gates`, `propansatzS_of_gates`, `Induct.propansatz_body_of_context`;
- `layergarden_v2`, `fixedpoint_v2`, `wkeTaylor`, `regularAsymptotics`, `layergardenFlower_v3`,
  `Provider.layergardenFlower_v3`;
- `SysAPI.IsASolution.tsum_normSq_eq`, `Induct.initialRapidEvent_ae`, `Induct.measure_initialRapidEvent`,
  `Induct.memLp_gaussian_mass`, `Induct.memLp_initial_l1`.

These lists are precomputed; (f) is the independent check. (In P4's exported view every one of these constants shows kind
"AXIOM", because the module system exports theorems without bodies; A1 likewise shows "anchor value visible: false". The
replay, which reads all olean parts, reports each as `theorem`.)

## (d) Hidden hypotheses and vacuity

- **Assembly.** `V2Chain.propansatz_v2_of_gates : LayergardenV2Gate → FixedpointV2Gate → WkeTaylorGate → PropansatzV2Gate`
  (P4 `#check`) has no other binders.
  - Its three hypotheses are discharged by exactly `layergarden_v2`, `fixedpoint_v2`, `wkeTaylor`, all SEALED at
    7d98ae17. The replay reports each as a `theorem` in its `Frozen.Theorems` module.
  - The gate abbrevs are definitionally the anchors' types; the kernel accepted the provider. They are not syntactically
    equal (P4 Expr walk). The differences are auxiliary `…Gate._proof_n` constants standing for the numeral-instance proofs
    `Nat.instAtLeastTwoHAddOfNat …`/`Nat.instNeZeroSucc …` (proof-irrelevant), hygienic instance-binder names, and one delta
    step (`WkeTaylorGate := Induct.WkeTaylorGate`).
  - `rfl` examples `Gate = type_of% @anchor` elaborate for all four.
- **Trace.** `propansatz_v2_of_gates` → `propansatzS_of_gates` (the `WTPrefixS` plumbing for `γ ∈ S`, threshold alignment
  `gatesS_common_prefix`) → `Induct.propansatz_body_of_context`.
  - The `InductContext` fields are all discharged in `propansatzS_of_gates`: parameter facts, `hφin`, `hsol`, the three gate
    bodies, `uniform_schwartz_bracket_bound`, the size threshold and the small-δ facts. None is a hypothesis.
  - Induction: p = 0 is `basePrefixData`, where `a = initialCoeff`, `Fev = initialRapidEvent`, `R = E = Et = 0`, and
    `ansatz_zero` proves it. Each step is `exists_prefix_extension` (from `fixedpoint`) followed by `extendPrefix`
    (`prefix_next_ansatz`, which uses the layergarden and Taylor bodies).
  - The final witnesses `⟨S.a, S.Fev, S.R, S.E, S.Et, S.ansatz⟩` come from the constructed prefix data, not from any
    hypothesis.
- **Glue inputs.** The reach pass (`replay/reach.out`) finds each of these reachable from the anchor and of kind `theorem`:
  - mass conservation (T L819): `SysAPI.IsASolution.tsum_normSq_eq`, `NLS.IsAkSolution.tsum_normSq_eq`;
  - a.s. rapid decay of `initialCoeff`: `Induct.initialRapidEvent_ae`, `Induct.measure_initialRapidEvent`;
  - Gaussian moments of the mass: `Induct.memLp_gaussian_mass`, `Induct.memLp_initial_l1`.

  `MainGlue.ansatz_norm_sq_le_initial_mass`, the main-only glue, is not in this closure. The replay finds 0 reachable project
  axioms or opaques and 0 sorry users.
- **Non-vacuity of the prefix.**
  - Each `∃` threshold is followed by a non-empty range: η = η₀, ν = ν₀, L = L₀, and (δ, 𝔇) = (1/⌈τ★/δ₀⌉, ⌈τ★/δ₀⌉).
  - Probe P6 compiles `KeyB.nonvacuous`, a sorry-free derivation of `∃ P μ a Fev R E Et, ∀ p ≤ P.D, AnsatzAt …` from the
    sealed anchor. It fixes d = 3, γ = 3/4, φin = 0, τ★ = 1 and φ ≡ 0 (`wke_zero`: 𝒦(0,0,0) = 0), and takes δ, 𝔇 from the
    returned δ₀.
  - The data are iid standard complex Gaussians on `((Fin 3 → ℤ) → ℂ, Measure.infinitePi stdComplexGaussian)`, with
    `IsGaussianData` proved from `iIndepFun_infinitePi` and `infinitePi_map_eval`.
- **Non-vacuity of the conclusion (`AnsatzAt` strength).** `AnsatzAt` (sealed, D7; closure file sha256 `73df9bf6…`) contains
  every clause of source (1)–(4), with the §4.1 deviations only (table §(h) C):
  - (1): the unique classed solution on [0,p] on `Fev p` with data √φin g, the nesting `Fev p ⊆ Fev (p−1)`,
    ℙ(Fev p) ≥ 1 − e^{−N_p}, and gauge + translation symmetry;
  - (ansatz1)/(ansatz2): the moment form (D2), ‖R_p‖ ≤ L^{−θ_p} (D1) and |E_p| ≤ ⟨k⟩^{−Λ_p}e^{−N_p};
  - (ansatz3)/(ansatz4): the cumulant = truncSum + Ẽ (D6), Ẽ's support and its bound;
  - (ansatz5): the order-N bound;
  - added conclusions: (2′) (D3) and the measurability/integrability conjuncts (D5).

  The integrability conjunct makes every Bochner integral in the items non-junk. ℙ(Fev p) ≥ 1 − e^{−N_p} with N_p ≥ 1 for
  large L excludes empty events.

## (e) ABI

- **Post-seal.** Probe P3a (`module / import all WaveTurbulence.Frozen.Theorems.PropansatzV2 / #print …`, my setup with
  `.olean.private` for the anchor and every project module, as the repository convention) gives stdout sha256
  `cc09a048f79055dfe5ead9615b921d861ccaa248d723ab29138848eec63fd6f1` = manifest = HANDOFF prediction = seal log.
- **Pre-seal.** Probe P2a is the freeze-commit anchor file verbatim, compiled as module
  `WaveTurbulence.Frozen.Theorems.PropansatzV2` against the anchor's Lake setup minus the provider. The freeze stub's public
  part was empty, and `lake-manifest.json`/`lean-toolchain` are unchanged since 8d7ccb4a. The file's `public section` is
  closed before `#print`, so that no `open` is active, as in the 2-line probe. After removing the single
  "declaration uses `sorry`" warning line, stdout sha256 is `3882921f640aa59a7ae763972a0f91a63b49109ff1b3916059882b02e20ebc6f`
  = manifest DRAFT ABI = seal log's pre-seal control.
- **#print diff.** The two 7-line outputs differ in line 6 only: `sorry` → `WaveTurbulence.Provider.propansatz_v2`.
- **pp.all.** The type part (3213 bytes, sha256 `6c1f1a345171c385b1d23bfa656c7eb22daa0697f2c574d132963c2da0505ebe`) is
  byte-identical before (P2b) and after (P3b). The values are `sorryAx.{0} (…)` and `WaveTurbulence.Provider.propansatz_v2.{u}`.
  The new imports cause no drift in instances, coercions or notation.

## (f) Kernel replay

- **Adaptation.** Adapted from `/home/scott/wt-scratch/seal-lg2/replay/Replay.lean` (sha256 `6c943568…`) and `replay.sh`
  (`b8298ed6…`). The diff is `replay/Replay.diff`: root module/constant `PropansatzV2`/`propansatz_v2`; this chain's
  `wanted` list; Expr checks (provider vs anchor; gates vs anchors); the dump of reachable modules. The driver runs index
  batches until the closure's project count is covered (the template hard-coded 6×2000; this closure has 12,126 project
  modules, so 7 batches). My `Replay.lean` sha256 is `2c147f40…`.
- **Replay.**
  - Closure: 23,102 modules (10,976 library, 12,126 project); base environment 661,703 library constants, trusted.
  - Reachable: 229,810 constants; MISSING 0; 11,170 project modules loaded. Same-name constants in two modules: 1,665, of
    which 0 differ in type/value.
  - No project AXIOM, OPAQUE or UNSAFE/PARTIAL is reachable, and there is no direct user of
    `sorryAx`/`ofReduceBool`/`trustCompiler`/`ofReduceNat`. Core axioms used directly: propext, Classical.choice, Quot.sound.
  - Reachable frozen theorems: `propansatz_v2`, `layergarden_v2`, `fixedpoint_v2`, `wkeTaylor`, `layergardenFlower_v3`,
    `regularAsymptotics`, all SEALED in the manifest.
  - Kinds: 195,683 theorems, 22,133 defs, 585 inductives, 802 ctors, 151 recs.
  - **REPLAY OK (8231 s): 219,354 constants, no shim.**
  - Wall 2:17:59, max RSS 5,893,112 KB. In quick mode, 40,618 `WaveTurbulenceVineParam` theorems whose proofs use only that
    library were checked by statement only; 92,875 cross-library VineParam theorems were replayed with proofs. Log:
    `replay/Replay-quick.out`.
- **Trace hashes (the replayed oleans are the seal commit's sources).**
  - For all 12,103 project modules of the closure that have constants, the Lake trace in main's `.lake` records a source
    hash equal to Lake's own `computeTextFileHash` of the seal export's file (`trace/Hashes.lean`, run with `import Lake`).
  - Each trace's output hashes for `.olean`/`.olean.server`/`.olean.private` equal `computeBinFileHash` of the files on disk.
    The `.hash` files agree, and all traces name Lean 4.35.0 eb6cafb.
  - 0 problems (`trace/trace-check.out`). 1,815 VineParam traces record their source under
    `/home/scott/WaveTurbulence-worktrees/port-vp/`, with hashes equal to the seal sources.
  - All 11,170 replayed modules are among the checked ones (0 unchecked).

## (g) Status fields (at seal commit 7d98ae17)

- **DRAFT_ANCHORS: 7.** `WaveTurbulence/Frozen/Theorems/{Main, Fixedpoint, Layergarden, LayergardenFlower, Propansatz,
  MainV2, LayergardenFlowerV2}.lean` (main_v1, fixedpoint_v1, layergarden_v1, layergardenFlower_v1, propansatz_v1,
  main_v2, layergardenFlower_v2). The manifest has 327 entries: 300 definitions SEALED, 20 theorems SEALED, 7 DRAFT_SORRY.
  Pre-seal there were 8 DRAFT; at main 1987105a there are 6, because main_v2 is sealed later.
- **UNREGISTERED_SORRIES: 0.** The guard is OK. My comment-, string- and nesting-aware scan (`tools/sorry_scan.py`) of all
  13,118 `.lean` files finds exactly 7 `sorry` tokens, the registered bodies of the 7 files above, and no `admit`.
- **DRAFT_IMPORT_VIOLATIONS: 0.** The guard's quarantine pass is OK. The lakefile `quarantinedModules` lists exactly the 7
  draft anchor/provider pairs; PropansatzV2 left the list in a2216712.
- **SEALED_THIS_TURN:** `WaveTurbulence.propansatz_v2` (seal a2216712, ABI 7d98ae17).

## (h) Five-bin binder table

Source reconstructed from the raw TeX (sha256 `493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb`, re-hashed
= pin): Prop `propansatz` L689–L707, (parameters)/(parameters2) L611–L612, setup L540–L615, (DAT) L292, (WKE) L299, the
p = 0 base case L708 and L819. Rulings: D2, D6, D7 (WAVE-B §4.1 (D1)–(D6), Q5), D9, D10, E1; D13/E34 do not touch this
type. The full table with citations is in `notes/h2-binder-table.md`; summary:

| # | Binder | Bin | Citation |
|---|---|---|---|
| 1–2 | `d : ℕ`, `3 ≤ d` | STANDING | T L314 |
| 3–4 | `γ : ℝ`, `γ ∈ Ioo 0 1` | STANDING | T L314; D2 |
| 5 | `η ∈ Ioc 0 η₀` | STANDING | T L604 |
| 6–7 | `φin : 𝓢(Mom d, ℝ)`, `∀ k, 0 ≤ φin k` | STANDING | T L292, L314 |
| 8 | `τstar`, `0 < τstar` | STANDING | T L314; D6 |
| 9–10 | `φ`, `IsWKESolution φin τstar φ` | STANDING | T L299–L312, L598–L604; D6 (closed-interval class) |
| 11–12 | `ν ∈ Ioc 0 ν₀`, `δ ∈ Ioc 0 δ₀` | STANDING | T L607 |
| 13 | `D : ℕ` | STANDING | T L608 (defD) |
| 14 | `1 ≤ D` | TYPING | implied by τ★ = 𝔇δ > 0 with δ > 0 |
| 15 | `τstar = D * δ` | STANDING | T L608 |
| 16 | `L₀ ≤ L` | STANDING | T L609 |
| 17 | `1 / 2 < P.γ` | RULED | D9, D10, E1 |
| 18–21 | `Ω`, `[MeasurableSpace Ω]`, `μ`, `[IsProbabilityMeasure μ]` | TYPING | probability space of (DAT) |
| 22 | `g : (Fin d → ℤ) → Ω → ℂ` | STANDING | T L292 (indexing by n, k = n/L; D6) |
| 23 | `IsGaussianData`.1 `∀ n, Measurable (g n)` | TYPING | "random variables" |
| 24 | `IsGaussianData`.2.1 `iIndepFun g μ` | STANDING | T L292 i.i.d. |
| 25 | `IsGaussianData`.2.2 `μ.map (g n) = stdComplexGaussian` | STANDING | T L292; D6 circular complex Gaussian |

Counts: SOURCE 0 · STANDING 19 · TYPING 6 · RULED 1 · **EXCESS 0**. The prover choices (`∃ η₀, C₁, ν₀, δ₀, C₂, L₀` and
`∃ a Fev R E Et`) and their non-empty ranges are in (d). Conclusion fidelity (`AnsatzAt` vs (1)–(4)) is row by row in
`notes/h2-binder-table.md` §C. Every clause is faithful or carries a named deviation: D1 (R_p real C^{Λ_p} on ℝ^d), D2
(moment), D3 ((2′) added), D4 (uniqueness in the class), D5 (measurability/integrability added), D6 (truncSum), D7/Q5
(symmetric events as preimages). Nothing is weakened outside these. θ_p, Λ_p, N_p, R_p (`Rdown`) match (parameters),
(parameters2) on 0 ≤ p ≤ 𝔇.

### Comparison with the claim appendix (opened after the table)

The appendix also finds EXCESS 0 and the same RULED row. The differences are granularity and bin names only, and change no
verdict:
1. The appendix keeps `WTPrefix` as one STANDING "bundle". AUDIT-COMMON (h) requires the recursive expansion, so I expanded
   it into 16 rows: 15 STANDING and 1 TYPING (`1 ≤ D`).
2. The appendix bins `g, IsGaussianData μ g` as SOURCE. I bin them STANDING (rows 22, 24, 25), with measurability as TYPING
   (row 23). (DAT) L292 is the paper's standing data assumption, which the proof of `propansatz` uses (L708) but which is
   not an explicit premise of the Proposition. Neither reading is EXCESS.
3. The appendix's counts (SOURCE 1, STANDING 1 bundle, TYPING 1, RULED 1) count bundles; mine count binders (0/19/6/1).

### Comparison with seal-prep logs and HANDOFF.md (opened after my results)

- `logs/live-20261108T193926Z/run.log` agrees with me on every check for this anchor:
  - pre-seal control `3882921f…`; post-seal `cc09a048…`;
  - `PRINT DIFF OK ['sorry'] -> ['WaveTurbulence.Provider.propansatz_v2']`;
  - pre/post pp.all `SAME TEXT OK (50 lines)`. The log uses `#check @…`; my `#print` type part is 47 lines, and both are
    unchanged.
  - `PROVIDER TYPE TEXT = ANCHOR TYPE TEXT (pp.all)`; std-3 axioms;
  - `RECHECK OK … body only; manifest fields ['abi_sha256','state']; DRAFT_SORRY anchors now 7`;
  - `SEALED propansatz_v2 at 7d98ae17`.
- HANDOFF item 9 says "the gate abbrevs are definitionally the anchor types". I agree (definitional, kernel-checked). They
  are not syntactically equal; see (d).
- **Disagreement / gap 1.** The live run ends `SEAL ABORT: full ABI check … probe failed for WaveTurbulence.Mom`. That
  probe's only stderr was the elan override notice: `scripts/abi_hash.py` treats any stderr as failure and does not set
  `ELAN_NO_OVERRIDE_NOTICE` (`abi_hash_setup.py` does). Then `main reset to LAST_GOOD 1987105a (local only)`.
  - The brief states "full 327-anchor ABI OK" on 1987105a. I found no log of that re-run in seal-prep/ or status/, and I did
    not re-run all 327 anchors.
  - This does not affect this anchor: its ABI is reproduced independently, and its closure is replayed.
  - wt-orch should file the full-ABI re-run log and set `ELAN_NO_OVERRIDE_NOTICE=1` in `abi_hash.py`.
- **Disagreement 2 (tooling claim, not a defect).** The replay template's `Expr.equal` check (reported as `Expr.equal` for
  `layergarden_v2` in `Seal-layergarden_v2.md`) is **false** for this anchor. The cause is the hygienic names of the
  anonymous instance binders, which embed the module name. The brief's alternative criterion, pp.all text equality (and
  `==`), holds, and so does `rfl`.

## Observations (non-blocking)

1. **Recording order.** The brief requires both keys of `fixedpoint_v2` (this chain's second seal) to PASS before
   propansatz_v2 is recorded. No `SEALAUDIT-*` status file existed while this audit ran. My verdict does not depend on
   fixedpoint_v2's statement fidelity, because the whole proof closure, including fixedpoint_v2's proof, was kernel-replayed
   here. wt-orch should still respect that order.
2. **Full mode not run.** Quick mode checked 40,618 VineParam certificate proofs by statement only, as in the layergarden_v2
   seal audit. Quick took 2h18m single-threaded on a shared machine. Full mode is `replay/replay.sh full`.
3. **Stale README.** The README status block at the seal commit still says "DRAFT_ANCHORS: 10 … propansatz v1/v2". The
   manifest gives 7.
4. **`check_index.sh` needs a git checkout.** It cannot run on a `git archive` export; I ran its two scripts directly.

## Evidence (paths relative to `/home/scott/wt-scratch/seal-audit-propansatz_v2-B/`; sha256 in `evidence/SHA256SUMS`)

| What | Path |
|---|---|
| Clean export of 7d98ae17 | `export/` |
| Freeze-time anchor and manifests | `evidence/PropansatzV2.freeze.lean`, `evidence/frozen.{freeze,preseal,main}.json` |
| Guard and module check | `evidence/guard-and-modules.out` |
| sorry scan | `evidence/sorry-scan.out` |
| Tools | `tools/hash_regions.py`, `manifest_diff.py`, `mksetup.py` (my setup generator), `sorry_scan.py`, `runprobe.sh` |
| Probes and outputs | `probes/A1` (anchor-only env, restatement, Expr diff), `P2` (pre-seal ABI and pp.all), `P3` (post-seal ABI and pp.all), `P4` (axioms, gates), `P5` (flower axioms), `P6` (non-vacuity); each `*.stdout`/`*.stderr` (time, RSS, rc) |
| Replay | `replay/exe/Replay.lean`, `replay/Replay.diff`, `replay/replay.sh`, `replay/Replay-quick.out`, `replay/reach-modules.txt`; reach pass `replay/exe2`, `replay/reach.out`, `replay/reach-names.txt` |
| Trace check | `trace/Hashes.lean`, `trace/hashes.txt`, `trace/trace-check.out` |
| Notes | `notes/h1-source-reconstruction.md`, `notes/h2-binder-table.md`, `notes/own-results.md` |

Key hashes:
- anchor at seal: `86e23094be3a436eee2a5a3ec8607fe22ebd2ba91dc9da995aecdaae2cdd7626`
- provider: `f307a4b8a3a61fe5b0c2d1fd80e1892ffbbe2212cb9b4de36555188cc6042702`
- TeX: `493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb`
- GAMMA-HALF-SUCCESSORS.md: `7366905da3067ae0efbf504be34b0030b4c3e5ffe2b15596646aebab34f4f614` (= brief `7366905d…`)
- P3a stdout: `cc09a048…`; P2a stripped: `3882921f…`

`propansatz_v2` may be recorded as PROVED (key B)
