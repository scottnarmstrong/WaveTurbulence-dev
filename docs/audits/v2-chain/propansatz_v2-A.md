# SEAL AUDIT — `propansatz_v2`, KEY-A (refute-first, independent)

Auditor: KEY-A (Opus 5.5), 2026-11-08/09. I had no access to KEY-B's work. I wrote none of the anchor, the provider, the
proof chain or the seal script. The binding rules are `flower-core/seal-prep/audit-briefs/AUDIT-COMMON.md`, the anchor brief
`AUDIT-propansatz_v2.md` and the skill `lean-statement-audit`. I opened the claim appendix and the seal logs only after
recording my own results; see `RESULTS-BEFORE-APPENDIX.md` (sha256 `c2175f2b…`) and the comparison section below. All
relative paths below are under `/home/scott/wt-scratch/seal-audit-propansatz_v2-A/`.

- Seal commits on origin/main: `a2216712` (seal) and `7d98ae17dae8fc7cf902e852badd5ab0a494e1c8` (ABI). The final pushed
  main is `1987105a`. Between 7d98ae17 and 1987105a only the MainV2 files, the root, the lakefile and the manifest
  change, and none of them is in this closure.
- Clean export: `git archive 7d98ae17 | tar -x -C export/`.
- Freeze commit: `8d7ccb4a` (D10). Raw TeX re-hashed: `493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb` (matches the pin).
- Lean v4.35.0 through the `wt-throttled` wrapper. Every Lean run used `nice -n 10`, with at most one heavy process at a time.

## Verdict table

| Item | Verdict | Evidence (short) |
|---|---|---|
| (a) Anchor bytes | **PASS** | Recomputed prefix `684d371b…` and suffix `9f481990…` equal the manifest. The only blobs since freeze are draft `6d8aa71b` (file sha256 `edd71ce8…`) and sealed `f8a5c033` (`86e23094…`). The body changed from `by sorry` to `by exact WaveTurbulence.Provider.propansatz_v2`. The manifest entry changed from freeze to seal in `state` and `abi_sha256` only. 100/100 `definition_closure` hashes match. The guard prints `FROZEN-ANCHOR GUARD OK`; `check_lean_modules` PASS (13118 files) on the clean export. |
| (b) Provider | **PASS** | The provider does not import its own anchor, either in source or in Lake's resolved closure. Statement text is identical (434 chars). Types are `==` and pp.all-identical, and the `rfl` example passes. The value is exactly `propansatz_v2_of_gates.{u} layergarden_v2 fixedpoint_v2.{u} wkeTaylor`. Only the anchor imports or names the provider. The proof modules are imported privately. A probe importing the anchor alone sees 102 WT modules (100 Defs, provider, anchor), and the proof-closure names are unknown. |
| (c) Axioms | **PASS** | `[propext, Classical.choice, Quot.sound]` for the anchor, provider, `propansatz_v2_of_gates`, `propansatzS_of_gates`, `propansatz_body_of_context`, `layergarden_v2`, `fixedpoint_v2` and `wkeTaylor`. |
| (d) Hidden hypotheses / vacuity | **PASS** | The 3 gate binders are discharged by exactly the 3 sealed exports. Every reachable chain constant is a `theorem` (or a `def` for data). The witnesses are built by induction from proved results. The glue lemmas are proved theorems and reachable. The replay finds no project axiom/opaque. A non-vacuity and consumption witness `KeyA.consume` compiles in the anchor's own environment with standard axioms. `AnsatzAt` contains (1)–(4) plus the D7 deviations. |
| (e) ABI | **PASS** | I reproduced pre-seal `3882921f…` from my own rebuild of the freeze environment (stub provider + DRAFT anchor) and post-seal `cc09a048…`. The `#print` outputs differ only in the value line (`sorry` → `WaveTurbulence.Provider.propansatz_v2`). The pp.all type (3213 chars) is byte-identical before and after. |
| (f) Kernel replay | **PASS (quick mode)** | REPLAY OK: 219,354 constants in 11,170 modules (closure 12,126 project / 23,102 total modules), 8211 s, wall 2:17:47, RSS 6,259,336 kB. MISSING 0. No project AXIOM/OPAQUE/UNSAFE/PARTIAL. No user of `sorryAx`, `ofReduceBool`, `trustCompiler` or `ofReduceNat`. Trace and olean hashes of all 12,103 indexed modules match the seal commit's sources. In quick mode, 40,618 VineParam-internal theorem proofs were checked by statement only. |
| (g) Status fields | **PASS** | DRAFT_ANCHORS 7 (paths below). UNREGISTERED_SORRIES 0. DRAFT_IMPORT_VIOLATIONS 0. SEALED_THIS_TURN = `propansatz_v2` only. The README status block is stale (documentation note). |
| (h) Five-bin table | **PASS** | `H-TABLE.md`: 36 premise/prefix rows (STANDING 25, TYPING 6, SOURCE 3, RULED 2) and 17 conclusion rows (SOURCE 14, RULED 3). **EXCESS 0.** |

**Recording precondition from the brief, not an item of this seal.** The brief requires both keys of `fixedpoint_v2` to
PASS before this anchor is recorded, and transitively the audit of `layergardenFlower_v3`, which `fixedpoint_v2` consumes.
When I finished, `flower-core/status/` contained no `SEALAUDIT-*` line for any seal. wt-orch must enforce this precondition.

## (a) Anchor bytes — details

- `tools/anchor_hash.py` is my own byte-level implementation of the guard convention. The prefix runs up to and
  including the PROOF_BEGIN line; the suffix starts at the PROOF_END line. Results:
  - DRAFT (8d7ccb4a): file `edd71ce8df83…`, prefix `684d371b5ff7…`, suffix `9f48199048…`, body `'  by sorry\n'`.
  - SEALED (7d98ae17): file `86e23094be3a…`, the same prefix and suffix, body `'  by exact WaveTurbulence.Provider.propansatz_v2\n'`.
- File history: `git log --full-history` shows 8d7ccb4a, the merge 50a9cfd7 (same blob) and a2216712. Over all 368
  commits in `8d7ccb4a..7d98ae17` the file has exactly two blob values.
- Manifest (`tools/manifest_diff.py`): from 8d7ccb4a to 7d98ae17 the entry differs in `abi_sha256` (`3882921f…` →
  `cc09a048…`) and `state` (`DRAFT_SORRY` → `SEALED`) only. Over f78bcabf → 7d98ae17, only this entry changed in the
  manifest. All 100 closure hashes match the export. The closure set equals the 100 `Frozen.Defs` modules in Lake's
  setup for the anchor. Since freeze, the only change under Frozen/Defs is 4 new D13 flower files, none of them in this closure.
- On the export, `check_frozen_anchors.py --root export` prints `FROZEN-ANCHOR GUARD OK`.
  `check_lean_modules.py` prints `PASS (13118 Lean files, 0 comparator configurations)` (`logs-check_lean_modules.txt`).

## (b) Provider — details

- Imports: Mathlib and the anchor's 5 `Frozen.Defs` (public); `Frozen.Theorems.{LayergardenV2,FixedpointV2,WkeTaylor}` and
  `Foundations.XChain.V2Chain.PropansatzV2` (private `import`). These are the sealed anchors, not their providers.
  Lake's `Provider/PropansatzV2.setup.json` (19,588 modules) contains neither `Frozen.Theorems.PropansatzV2` nor the v1
  anchor. The anchor's own setup contains Mathlib, the 100 Defs and the provider, and no proof module, so the statement
  elaborated in its freeze environment.
- Usage: only `Frozen/Theorems/PropansatzV2.lean` imports the provider module, and only the anchor and provider files
  contain `Provider.propansatz_v2`.
- `probes/Probe1.lean` (module probe, `import` of the anchor only; my setup generator `tools/gen_setup.py`; output
  `Probe1.out`):
  - `V2Chain.propansatz_v2_of_gates`, `layergarden_v2`, `fixedpoint_v2` and `wkeTaylor` are each *Unknown identifier*.
  - The environment has 102 WT modules; 273 WT constants, all from the Defs, the provider or the anchor.
  - The provider module contributes exactly `[WaveTurbulence.Provider.propansatz_v2]`.
  - `example : type_of% @…propansatz_v2.{u} = type_of% @…Provider.propansatz_v2.{u} := rfl` elaborates.
  - Types are BEq-equal with equal hashes, and the pp.all text is equal (3169 chars; `ppall-anchor-type.txt` / `ppall-provider-type.txt`).
  - `Expr.equal` is **false**. `Probe1b` locates exactly 2 differing binder sites: the anonymous instance binders
    `[MeasurableSpace Ω]` and `[IsProbabilityMeasure μ]`. Their hygienic names `inst._@.<module>.3596003496._hygCtx._hyg.17/.22`
    embed the module name (`Frozen.Theorems.PropansatzV2` vs `Provider.PropansatzV2`). Binder infos, structure and
    counters are identical. The rule accepts pp.all text equality, which holds.
- `Probe3` (module probe, `import all` of the 6 chain modules) gives the anchor value `== Provider.propansatz_v2.{u}` and the
  provider value `== propansatz_v2_of_gates.{u} layergarden_v2 fixedpoint_v2.{u} wkeTaylor`. The replay confirms both.

## (c) Axioms — details

`Probe2.out`: all eight constants listed in the table print `[propext, Classical.choice, Quot.sound]`. Item (f) is the
independent check of the same fact.

## (d) Hidden hypotheses and vacuity — details

Trace:

- `Provider.propansatz_v2 := propansatz_v2_of_gates layergarden_v2 fixedpoint_v2 wkeTaylor`.
- `propansatz_v2_of_gates` (`V2Chain/PropansatzV2.lean`) unfolds its gate abbrevs, then applies `WTPrefixS.ofR`/`ofFull`,
  `propansatzS_of_gates` and `.toR`.
- `propansatzS_of_gates` aligns the three prefixes (`gatesS_common_prefix`), shrinks δ₀ and enlarges L₀ by explicit
  formulas, and fills every field of `InductContext` with standing hypotheses or proved lemmas
  (`uniform_schwartz_bracket_bound`, `delta_half_power_le_of_threshold`, `assemblySizeThreshold`) and the 3 gate bodies.
- `Induct.propansatz_body_of_context` runs the induction on p ≤ 𝔇:
  - Base: `basePrefixData`, with a = initial coefficients, Fev = `initialRapidEvent`, R = E = Ẽ = 0, and `ansatz_zero`.
  - Step: `exists_prefix_extension` gets its event F and solution from the `FixedpointBody` gate (that is,
    `fixedpoint_v2`) applied to the previous prefix data. `prefix_next_ansatz` uses the layergarden and Taylor gates.
- The existential witnesses `a, Fev, R, E, Et` are therefore built by the induction from proved results, never taken
  from a hypothesis.

Inputs, from the kernel replay (`replay/Replay-quick.out`, CHAIN and REACHABLE lines). Each is a `theorem` (or `def` for
data), reachable from the root, and replayed:

- the sealed exports `layergarden_v2`, `fixedpoint_v2` and `wkeTaylor`, plus the sealed `regularAsymptotics` and
  `layergardenFlower_v3` reached through them;
- the glue lemmas:
  - mass conservation, a-system form: `Induct.solution_norm_sq_le_initial_mass`, used through `integrable_signed_prod_of_solutions`;
  - a.s. rapid decay: `Induct.initialRapidEvent_ae` → `Probability.ae_initialCoeff_isRapidDecay`;
  - Gaussian mass moments: `Induct.memLp_gaussian_mass`;
  - `Induct.memLp_initial_l1`;
- `ansatz_zero`, `basePrefixData` (def), `exists_prefix_extension` and `prefix_next_ansatz`.

The only `Frozen.Theorems` constants reachable from the root are the 6 listed (including the root). All 6 are `SEALED`
both in the manifest at 7d98ae17 and on main. The replay finds no project axiom, opaque, unsafe or partial constant.

Binders are discharged exactly (`Probe2`/`Probe3`). `propansatz_v2_of_gates` has 3 binders. Each is defeq to the type
of the sealed export that discharges it, and the kernel checked this in the replay. After unfolding the
V2Chain/Induct abbrevs, the only syntactic differences are auxiliary `_proof_n` constants that Lean abstracted for the
`Nat.AtLeastTwo` instance arguments, and `have` vs `let` in the fixedpoint gate. Both are proof-irrelevant or zeta.

Non-vacuity (`probes/Probe4.lean`, sha256 `151a8f53…`) runs in the anchor's own environment with no proof-closure import:

- Every prover choice of the prefix leaves a non-empty universal range (`eta_range`, `delta_range`, `L_range`). For
  example, any δ₀ > 0 and τ★ > 0 give 𝔇 = max 1 ⌈τ★/δ₀⌉ and δ = τ★/𝔇 ≤ δ₀.
- Premise witnesses:
  - d = 3 and γ = 3/4, which satisfy both 0 < γ < 1 and the D10 restriction 1/2 < γ;
  - φin = 0 ≥ 0, τ★ = 1, and φ ≡ 0 with `IsWKESolution` (`wke_zero`);
  - Ω = (Fin 3 → ℤ) → ℂ with μ = `Measure.infinitePi` of `stdComplexGaussian` and g n ω = ω n, a probability measure
    with `IsGaussianData` (`gaussian_data`).
- `KeyA.consume` applies `WaveTurbulence.propansatz_v2.{0}` to all of these and produces
  `∃ a Fev R E Et, ∀ p ≤ 𝔇, AnsatzAt ⟨3, 3/4, η₀, 0, 1, 0, C₁, ν₀, δ, 𝔇, C₂, L₀⟩ …`. Axioms are standard (`Probe4.out`).

Strength of the conclusion: I read the body of `AnsatzAt` (sealed, D7). It contains:

- (1) measurable symmetric event, nesting, `1 − e^{−N_p} ≤ ℙ(Fev p)`, classed solution on [0,p] with uniqueness, measurability and integrability;
- (2) moment = 1_{n=n'}(φ(δp,n/L) + R_p(n/L) + E_p(n)), with `SNormR Λ_p Λ_p R_p ≤ L^{−θ_p}` and `|E_p| ≤ ⟨n/L⟩^{−Λ_p}e^{−N_p}`;
- (2') intermediate times;
- (3) cumulant on `μ.restrict (Fev p)` = Σ_{N≤N_p} `truncSum` + Ẽ_p, with support and bound;
- (4) the order-N bound with L^{−(m−1)/6}δ^{νN}.

The only departures are the §4.1 deviations (D1)–(D7). `truncSum` is a `finsum` over a finite support
(`finite_layeredGardens`), and for N ≤ N_p it equals the untruncated sum (`truncSum_untruncated`, proved). A degenerate
Fev is excluded for large L, because N_p → ∞ forces ℙ(Fev p) → 1, and the statement holds for every L ≥ L₀.

## (e) ABI — details

- Primary method (`lake env lean` with a non-module `import M` probe): post-seal it fails with
  `failed to read file …J1VI031.olean.private`. That is the vm.max_map_count limit (65530), because a non-module importer
  maps the whole private closure. I therefore used the setup-file method with my own generator.
- I audited `scripts/abi_hash_setup.py` rather than reusing it. It builds a module probe `import all M` from M's
  `setup.json`, adds M's own arts and the `.olean.private` of every WT module, and hashes stdout. That is sound. The
  output has no path prefix, so it does not depend on the probe location.
- Post-seal: `abi/post-setup.out` sha256 = **`cc09a048f79055dfe5ead9615b921d861ccaa248d723ab29138848eec63fd6f1`**, which is manifest `abi_sha256`.
- Pre-seal: I rebuilt the freeze environment in `freeze-build/`:
  - The freeze stub provider (`git show 8d7ccb4a:…Provider/PropansatzV2.lean`, sha256 `b9d16c7c…`, no declarations) and
    the DRAFT anchor (`edd71ce8…`) were compiled with `lean --setup … -o`. Their setups were derived from the anchor's
    Lake setup, with the provider entry replaced by my stub. The one warning was the expected `declaration uses 'sorry'`.
  - `abi/pre-setup.out` sha256 = **`3882921f640aa59a7ae763972a0f91a63b49109ff1b3916059882b02e20ebc6f`**, which is the DRAFT abi in
    the freeze manifest. The rebuild is byte-exact.
- `diff pre-setup.out post-setup.out` gives only line 6, `sorry` → `WaveTurbulence.Provider.propansatz_v2`.
- pp.all: `pre-setup-ppall.out` (`a2ad7dac…`) and `post-setup-ppall.out` (`3fbc1746…`) have identical type parts, 3213
  chars, lines 1–47. They differ only in the value (`sorryAx.{0} …` → `WaveTurbulence.Provider.propansatz_v2.{u}`).
  Adding the provider theorem and its environment therefore caused no elaboration drift in instances, coercions or notation.

## (f) Kernel replay — details

- Kit: adapted from `/home/scott/wt-scratch/seal-lg2/replay/` (`Replay.lean` sha256 `6c943568…`, `replay.sh` `b8298ed6…`;
  I read both before use). My versions are `replay/Replay.lean` (`71f55926…`) and `replay/replay.sh` (`276ac01a…`); the
  diff is in `replay/Replay.diff` (`9a032009…`). Changes:
  - root module `Frozen.Theorems.PropansatzV2` and root constant `WaveTurbulence.propansatz_v2`;
  - the propansatz chain as the `wanted` list, with reachability-from-root reporting;
  - Expr-level exactness checks for the anchor and provider values;
  - dumps of reached modules and stubbed constants;
  - `nice -n 10`, my own directories, and index batches up to 16,000 modules with a coverage check.
- **Run 1 was invalid and aborted by me.** The inherited batch loop stopped at 12,000 modules, while this closure has 12,126.
  126 modules (for example `Flower/CompMK/Defs`) went unindexed, which showed up as `MISSING: 86`. Its output is kept as
  `replay/Replay-quick.aborted1-index-gap.out`.
- Run 2 indexed all modules: 12,103 modules carry constants and 23 are import-only.
- Result: base = 661,703 library constants (exported parts, trusted as in every seal audit). Project closure = 12,126
  modules, of which 11,170 hold reachable constants. Reachable = 229,810 (10,456 library refs), MISSING 0. 1,664
  same-name duplicates across loaded modules, of which 0 have a differing type or value.
- Kinds before stubbing: theorem 195,683; def 22,133; inductive 585; ctor 802; rec 151; no axiom or opaque. Project
  AXIOMS, OPAQUE and UNSAFE/PARTIAL reachable: none. Direct users of `sorryAx`, `ofReduceBool`, `trustCompiler` or
  `ofReduceNat`: none. This scan covers every reachable constant, the quick-mode stubs included.
- `REPLAY OK (8211s): 219354 constants`. One `Kernel.Environment.replay` call; no shim; no project constant forced to an
  axiom on failure.
- **Quick-mode caveat.** 40,618 theorems from `WaveTurbulenceVineParam` modules whose proofs use no constant outside
  that library (internal certificate lemmas, listed in `replay/stubbed-quick.txt`) were sent with their statement only.
  92,875 cross-library VineParam theorems were replayed with their proofs. The kit's closing phrase "no constant turned
  into an axiom" refers to failure handling; in quick mode these 40,618 were stubbed by design. Full mode was not run.
  The brief requires quick mode at least.
- Trace check (`tracecheck/`):
  - My `TextHash.lean` reproduces `Lake.computeTextFileHash`; on the anchor it gives `135a84d1982a943d`, equal to its trace.
  - For all 12,103 indexed modules, the trace-recorded source hash equals the Lake text hash of the clean export's file: 0 mismatches.
  - For all 36,309 olean parts, the on-disk bytes match the trace output hashes (`BinHash.lean`): 0 mismatches.
  - The 11,170 replayed modules are a subset of the checked set.
  - 1,791 VineParam traces record their source path under the sibling worktree `../WaveTurbulence-worktrees/port-vp/`.
    Their content hashes still equal the seal commit's files.

## (g) Status fields — details (independent: `tools/status_fields.py` on the export, own comment/string masking)

- DRAFT_ANCHORS: 7. `Frozen/Theorems/{Main, Fixedpoint, Layergarden, LayergardenFlower, Propansatz, MainV2,
  LayergardenFlowerV2}.lean`, that is `main_v1`, `fixedpoint_v1`, `layergarden_v1`, `layergardenFlower_v1`,
  `propansatz_v1`, `main_v2` and `layergardenFlower_v2`. The lakefile quarantine lists exactly these 7 anchors and their providers (14 modules).
- UNREGISTERED_SORRIES: 0. There are 7 `sorry` tokens, all of them in the 7 DRAFT anchor files.
- DRAFT_IMPORT_VIOLATIONS: 0.
- SEALED_THIS_TURN: `propansatz_v2`. The seal commit pair removes it from the quarantine, the root imports it, and the
  manifest flips it to SEALED. It is the only manifest change in f78bcabf → 7d98ae17. Totals: 20 sealed theorems and 300 sealed definitions.
- Note: the README AUTO status block at 7d98ae17 is stale. It says "DRAFT_ANCHORS: 10 … propansatz v1/v2 …" and
  "SEALED: 17 theorems". This is documentation only; the manifest and guard are authoritative.

## (h) Five-bin table

The full table is in `H-TABLE.md` (sha256 `ef6680cc…`). I reconstructed the source first in `SOURCE-RECON.md` (`998ec54e…`)
from the raw TeX (L314, L540–L612, L689–L707, L708, L752–L830) and the rulings D6, D7, D9, D10, D13, E1, E34 and the
ERRATA §C deviations. Every alias is expanded: `WTPrefix`, `IsWKESolution`, `IsGaussianData` and `AnsatzAt`.

- Premise and prefix rows: 36, with STANDING 25, TYPING 6, SOURCE 3 (the three `IsGaussianData` conjuncts) and RULED 2
  (`ContinuousOn φ (Icc 0 τ★)` per D6, and `1/2 < γ` per D9/D10). **EXCESS 0.**
- Conclusion rows: 17, with SOURCE 14 and RULED 3 (D7 (D4) uniqueness class, (D5) measurability/integrability, (D3) item 2'). (D1) R_p on ℝ^d also applies to C3.
- Quantifier order is exactly (Π) of D7 item 7, then the D10 restriction, then the probability data, then the witnesses, then ∀ p ≤ 𝔇.
- The source has C₁ depending only on (τ★, η, 𝔆) and C₂ only on (𝔇, δ, φin). Lean relaxes both to depend on all
  earlier binders, which D7 item 7 rules. C₁ and C₂ do not occur in `AnsatzAt`.

## Comparison with the claim appendix and the seal logs (opened after my results)

Claim appendix (`AUDIT-propansatz_v2.md` §Claim appendix). All of these differences are of granularity or citation;
neither side found an EXCESS.

1. The appendix classifies the whole `WTPrefix` bundle as one STANDING row. I expand it to 27 rows (H-TABLE rows 1–25, with 14a–c). One of them,
   `ContinuousOn φ (Icc 0 τ★)` inside `IsWKESolution`, is RULED (D6) rather than SOURCE-literal, and the constant
   dependences rest on D7 item 7. The appendix does not cite D6 or D7 item 7. AUDIT-COMMON requires every alias to be
   expanded, and the appendix does not do this.
2. The appendix bins `g` together with `IsGaussianData` as SOURCE. I bin `g` as TYPING and the three conjuncts as SOURCE;
   the circular complex Gaussian law also relies on D6.
3. The appendix's counts are SOURCE 1, STANDING 1 bundle, TYPING 1, RULED 1. Mine are 36 + 17 rows (above).
4. The appendix leaves the conclusion binders unclassified. I classify them; the rulings used are D7 (D1)–(D6) and Q5.
   Same verdict: EXCESS 0.

Seal-script logs (`seal-prep/logs/live-20261108T193926Z/`, `propansatz_v2.*` and `run.log`):

5. They agree with me on the pre-seal ABI `3882921f…`, the post-seal ABI `cc09a048…`, the print diff (`['sorry'] →
   ['WaveTurbulence.Provider.propansatz_v2']`), the axioms of the anchor and provider, the pp.all type equality, the
   guard, `check_lean_modules` and the RECHECK (frozen diff body-only; manifest fields `abi_sha256`, `state`; DRAFT
   anchors 7). My pre-seal value comes from an independent rebuild of the freeze environment.
6. **Disagreement with the brief.** The brief says "full 327-anchor ABI OK". The seal script's own run ends with
   `probe failed for WaveTurbulence.Mom … note: using toolchain 'wt-throttled' …` / `SEAL ABORT: full ABI check` /
   `RESULT: ABORTED` (`run.log`, `full_abi.log`). The cause shown is tooling: `abi_hash.py`'s primary path treats any
   stderr output as failure and does not set `ELAN_NO_OVERRIDE_NOTICE`, so the elan override notice tripped it. Main was
   left at 1987105a. I did not rerun the 327-anchor ABI, which is out of scope here. For `propansatz_v2` I reproduced
   the ABI independently. wt-orch should confirm that a clean full-ABI run exists, or rerun it with the notice suppressed.
7. The seal script checks Expr equality only through pp.all text. I additionally record the `Expr.equal` = false cause:
   hygienic instance-binder names, which are benign.

## Evidence index (sha256)

`probes/Probe1.out` 0ff83db7… · `Probe1b.out` ab7f1983… · `Probe2.out` 1c36d81a… (its `value!` lines panic under the module
system and are superseded by `Probe3`) · `Probe3.out` af089e1d… · `Probe4.lean` 151a8f53… / `Probe4.out` 978ea935… ·
`abi/pre-setup.out` 3882921f… · `abi/post-setup.out` cc09a048… · `replay/Replay-quick.out` fe908b13… ·
`replay/reached-modules-quick.txt` bf056627… · `replay/stubbed-quick.txt` ec9fcea3… · `tracecheck/indexed-modules.txt`
c6da2866… · `freeze-build/out/…/Frozen/Theorems/PropansatzV2.olean` a653abfc… · `tools/gen_setup.py` c6f7f07e… ·
`tools/anchor_hash.py` b7ef72a0… · `tools/status_fields.py` e4bf7cfe… · `tracecheck/check_modules.py` b453b51b….

Not done: the full-mode replay (quick mode is the required minimum) and the 327-anchor ABI rerun (out of scope; see
item 6). I made no edits outside this directory and pushed nothing.

`propansatz_v2` may be recorded as PROVED (key A)
