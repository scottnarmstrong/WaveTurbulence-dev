# KEY-A — two-key seal audit, key A, of the five full-range anchors (0 < γ < 1)

> **Reading note.** This is the key-A record of the two-key seal audit of the five full-range anchors. Paths under `<work>/` are the auditor's local working files (scripts, logs, probe outputs); they are not part of the repository. `<sources>/` is the pinned LaTeX source of the papers. All other paths are relative to the repository root. The audit is of main at `5c19b015`, and Lean names refer to the repository at that commit; for what has changed in Lean since then (unused code removed, proof-only rewrites of 29 files; no frozen statement changed), see the [README](README.md) of this directory.


Auditor: KEY-A (refute-first; I wrote none of the anchors, providers, glue, proof chain or seal tooling). Brief:
`<work>/seal/audit-briefs/KEY-A-ALL.md`, with `AUDIT-COMMON.md` and the five
`AUDIT-<id>-A.md` (binding, item by item; the kernel replay is done once, for the union). Dates: 2026-11-09 22:40 –
2026-11-10 (UTC). Work directory: `<work>/seal-audit-ALL-A/`. Relative paths below are in that directory.
Nothing outside it was edited and nothing was pushed (this report and the status line were then written where the brief
says).

## Verdict summary

| anchor | (a) bytes | (b) provider | (c) axioms | (d) hidden hyp./vacuity | (e) ABI | (f) replay | (g) status | (h) binders | verdict |
|---|---|---|---|---|---|---|---|---|---|
| layergardenFlower_v4 | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS (EXCESS 0) | **PASS** |
| layergarden_v1 | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS (EXCESS 0) | **PASS** |
| fixedpoint_v1 | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS (EXCESS 0) | **PASS** |
| propansatz_v1 | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS (EXCESS 0) | **PASS** |
| main_v1 | PASS | PASS | PASS | PASS | PASS | PASS | PASS | PASS (EXCESS 0) | **PASS** |

I found no configuration, byte or constant that makes any of the five claims false. The disclosed procedural deviation
(§0, D1: I saw the v4 claim appendix before my v4 table) does not change any item. The other deviations from the brief are
in the method, not the result: method 1 of the ABI hash had to run on overlays (§(e)), and the replay ran in quick mode,
which the brief allows (§1.2).

## 0. Subject, scope and disclosures

- This repository (used read-only). Final pushed main **`5c19b015`**
  (`5c19b015c635ea1c1ab8ec028e16952a1d6354f0`). It differs from the last ABI commit `a25673fd` in 5 docs files only, and
  the current origin/main `9aa303c2` differs from it in `docs/` only. Clean export: `export/` = `git archive 5c19b015`.
  I used main's build (`.lake/build`, land_check of the seal, 22:27–22:31 UTC) read-only: no `lake` command was run in
  the main checkout, and every Lean process reads the build through LEAN_PATH or my own setup files.
- The briefs' Subject `<…>` fields were not filled in. I took them from origin/main:

| anchor (export) | freeze | seal commit | ABI commit | provider body (exact; export `WaveTurbulence.Provider.<name>`) |
|---|---|---|---|---|
| layergardenFlower_v4 (`WaveTurbulence.layergardenFlower_v4`) | `eae9b6b3` (merge `8bbfb3b8`) | `4558dd65` | `88e4495a` | `WaveTurbulence.GammaLow.Glue.layergardenFlower_v4_of_low WaveTurbulence.GammaLow.Close.flower_low_closed` |
| layergarden_v1 (`WaveTurbulence.layergarden`) | `f2d1fb6b` | `2e2c16ef` | `a89b5012` | `…Glue.layergarden_of_low …Close.layergarden_low_closed` |
| fixedpoint_v1 (`WaveTurbulence.fixedpoint`) | `f2d1fb6b` | `008e27f9` | `e5c86a37` | `…Glue.fixedpoint_of_low …Close.flower_low_closed …Close.layergarden_low_closed` |
| propansatz_v1 (`WaveTurbulence.propansatz`) | `f2d1fb6b` | `6f4a03d2` | `09c867a6` | `…Glue.propansatz_of_low …Close.flower_low_closed …Close.layergarden_low_closed` |
| main_v1 (`WaveTurbulence.main`) | `8d1d2e3b` | `bfbb5546` | `a25673fd` | `…Glue.main_of_low …Close.flower_low_closed …Close.layergarden_low_closed d hd γ hγ` |

  Mode A. FL = `WaveTurbulence.GammaLow.Close.flower_low_closed` (`WaveTurbulence.Foundations.GammaLow.Close.Final`), LG =
  `WaveTurbulence.GammaLow.Close.layergarden_low_closed` (`…GammaLow.Close.Halves`). The γ ≤ 1/2 port is `a46344ef`
  (GH-PORT sync 6), merged by `304a871c`. The world copies of `Glue/*.lean` are byte-identical to main's.
- **Disclosures.**
  - D1: at the start I read `AUDIT-layergardenFlower_v4-A.md` in full, claim appendix included, before building my v4
    table. I read the other four briefs only up to "## Claim appendix" until my tables were on disk (`h/tables.md`). I
    still built the v4 table row by row from the TeX, the rulings and the Lean text; its differences to the appendix are
    in §(h).
  - D2: a `ps` check of my own replay showed the command line of KEY-B's concurrent replay process (a path under
    `seal-audit-ALL-B/`). I did not open that directory or any KEY-B output.
  - D3: before writing these results I did not read the seal script's `logs/live-*`, the seal `HANDOFF.md`, AUDIT-V4.md,
    or any prior audit of these five statements. Since the brief says only "compare and report every disagreement" with
    the logs, and I read none, there is nothing to compare against there.
  - D4: the transient Lean checks are kept as evidence in `probes/`. That is my audit directory, not a repository, and
    nothing there is tracked or importable by the project.

## 1. Shared evidence

### 1.1 Source reconstruction ((h) first)
`01-source-reconstruction.md`, written before any Lean statement was read. The raw TeX
(`<sources>/paper/source/WKE-Longer_times_Final_arXiv.tex`) re-hashes to sha256
`493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb` (= pin). What I read:
- the TeX: T L270–L330 (Thm 1.1, L314–L319), L596–L625 (parameters (Π), θ = η²⁰ at L612), L660–L800 (propansatz
  L689–L707, base case L708, layergarden L761–L779, fixedpoint L780–L794) and L2255–L2340 (flowerest1 L2279–L2286 and
  its uses L2306–L2338);
- the rulings: docs/DECISIONS.md (all of D1–D16), E1 and E34 (docs/ERRATA-AND-DEVIATIONS.md L268ff, L1926ff), and
  R190–R192 (`docs/campaign/orch/RULINGS.md` L4721–L4800);
- the design documents: WAVE-B v2 (`docs/blueprint/WAVE-B.md` §1.2, §4.1–§4.3, §4.15), `docs/review/WAVE-B-B1.md`
  §1–§2 and `WAVE-B-B1-B112.md`.

Full-range rulings: D2, R190, R192 and D16 make 0 < γ < 1 the target. E1 is an erratum of the **proof** (DH23 Prop 9.6 at
γ ≤ 1/2), not of the statements, and licenses no γ restriction.

### 1.2 Kernel replay of the union ((f); run once, cited by every anchor)
- **Tool.** `replay/Replay.lean` adapts `<work>/seal-lg2/replay/Replay.lean` (sha256 `6c943568…`); the
  diff is in `replay/Replay.diff`, 103 lines. Changes:
  - roots: the five sealed modules `WaveTurbulence.Frozen.Theorems.{LayergardenFlowerV4, Layergarden, Fixedpoint,
    Propansatz, Main}` and constants `WaveTurbulence.{layergardenFlower_v4, layergarden, fixedpoint, propansatz, main}`;
  - the chain list;
  - per-anchor Expr checks (anchor vs provider), plus FL/LG kind and type;
  - the reachable project modules are written to `replay/reach-mods.txt`.

  The replay logic itself is the reference's, unchanged. Its parts:
  - base environment: the exported parts of the library modules, inserted unchecked;
  - lazy loading of all three olean parts of every project module holding a reachable constant;
  - every reachable project constant (types, values, inductives with ctors/recursors) is sent to `Kernel.Environment.replay`
    once, with no shim and nothing turned into an axiom;
  - quick mode: the `WaveTurbulenceVineParam` certificate theorems whose proofs use no constant outside that library are
    checked by statement only (the brief's "quick mode at least"). Every cross-library VineParam proof is replayed with
    its proof.
- **Driver.** `replay/replay.sh` adapts the reference's `replay.sh` (sha256 `b8298ed6…`). It differs in three ways:
  - no `lake env`: LEAN_PATH is the exact path recorded in the build's traces, and LEAN_SYSROOT is elan's v4.35.0;
  - the index batches loop until the closure is covered;
  - the process runs at nice 10.

  The exe was built in `replay/exe/` with the same toolchain.
- **Result** (`replay/Replay-quick.out`):
  - closure: 24 793 modules (library 10 976, project 13 817); base env 661 703 library constants; 271 627 project
    constant names indexed;
  - reachable: 248 367 constants (10 782 library refs), **MISSING 0**; 12 691 project modules loaded;
  - same-name constants in two loaded modules: 1 835, of which **0** differ in type (or, for non-theorems, in value);
  - reachable project constants by kind: theorem 210 824, def 24 835, ctor 991, inductive 741, rec 194;
  - **project AXIOMS reachable: [] · OPAQUE: [] · UNSAFE/PARTIAL: [] · direct users of
    `sorryAx`/`ofReduceBool`/`trustCompiler`/`ofReduceNat`: []**; core axioms referenced directly by project terms:
    `propext`, `Classical.choice`, `Quot.sound`;
  - reachable `Frozen.Theorems` constants: the five anchors and the sealed `layergarden_v2`, `layergardenFlower_v3`,
    `wkeTaylor`, `nlsAkBridge` and `regularAsymptotics` (all `SEALED` in the manifest, under D10, D13, D7, D7 and D8);
  - **REPLAY OK: 237 585 constants, in 12 691 modules, no shim, no constant turned into an axiom.** VineParam proofs
    checked by statement only (quick mode): 40 618 theorems; VineParam theorems replayed with their proofs (cross-library):
    92 873;
  - replay phase 10 319 s; whole run 2:53:10 wall, user 10 012 s; **max RSS 12 404 120 kB (12.4 GB)**; rc = 0; one niced
    process.
- **Chain.** Every chain constant was found with its real kind: the five anchors, the five providers, the five glue
  theorems, `wtPrefix(P)_of_halves`, FL, LG, the gate definitions, the named-input theorems and the four sealed v2/B1
  anchors. All are `theorem`, except the gates, which are `def`.
  - FL = `flower_low_closed`: kind theorem, no universe levels, **type exactly the constant
    `WaveTurbulence.GammaLow.Flower.LayergardenFlowerLowGate`**.
  - LG = `layergarden_low_closed`: kind theorem, **type exactly `WaveTurbulence.GammaLow.LGLow.LayergardenLowGate`**.
  - Neither has binders, so no section `variable`/`include` leaked in.

### 1.3 The replayed oleans are the seal commit's sources ((f))
- **Tool.** `trace/exe/TraceCheck.lean`, my own. For each module it:
  - reads the module's Lake trace (`.lake/build/lib/lean/<M>.trace`);
  - compares the recorded source hash with Lake's text hash of the same relative path in the clean 5c19b015 export.
    The hash is `Hash.ofText` = `mixHash 1723 (hash (crlfToLf s))`, reimplemented from the toolchain's
    `lake/Lake/Build/Trace.lean`;
  - checks that every recorded output olean part (`.olean`, `.olean.server`, `.olean.private`) hashes
    (`Hash.ofByteArray`) to the value in the trace.
- **Result.** All **13 817** closure modules, and separately the **12 691** modules the replay loaded, report "OK; problems:
  0" (`trace/closure-src.out`). 1 815 of them (1 804 among the replayed ones) are `WaveTurbulenceVineParam` modules
  compiled in the worktree `<work>/…` and present in main's build. Their source
  hashes equal the 5c19b015 texts.
- **Compiler.** The build ran a Lean v4.35.0 toolchain wrapper (`<work>/sysroot/bin/lean`) → `lean-shared`. I read both in full: they only
  throttle (slots, memory guard) and then exec elan's genuine `leanprover/lean4:v4.35.0` `lean` with `--threads=5`. The
  sysroot `lake` is byte-identical to elan's.
- **Compile options.** All 13 014 main-library `.setup.json` files carry only `autoImplicit=false`,
  `relaxedAutoImplicit=false` and three linters: no `debug.skipKernelTC`, no heartbeat or recursion overrides.

### 1.4 Axioms ((c))
`probes/compose.lean` is a module probe over Lake setup files built by my own generator `probes/gen_setup.py` (the seal
tools and `scripts/abi_hash_setup.py` were read, not used). It runs `#print axioms` (which reads the precomputed per-module
lists; see the toolchain's `Lean/Util/CollectAxioms.lean`) for 32 constants:
- the five anchors and the five providers;
- the five glue theorems and `wtPrefix_of_halves`, `wtPrefixP_of_halves`;
- FL and LG;
- `layergardenFlower_v3`, `layergarden_v2`, `wkeTaylor`, `nlsAkBridge`;
- `MainGlue.main_of_propansatz_nlsAkBridge`, `Cpl.oX3Cpl`, `X2E.oX2Exp`;
- the named-input theorems `Fama.stage1ReductionGateLow`, `Flower.stage1MKGateLow`, `H2.finalCountAtMKLAt_holds`,
  `Ghost.chainCoverLowL'_holds`, `TVine.Struct.subObjects_holds` and `Famc.coarseSplicedGateLow`.

**Every one depends on exactly `[propext, Classical.choice, Quot.sound]`** (`probes/compose.out` L1–L34; one report wraps over three lines). The replay
(§1.2) is the independent check.

### 1.5 FL and LG are closed; named inputs; watch items ((d))
**FL chain** (terms in the 5c19b015 export; all theorems kernel-replayed in §1.2):
- `flower_low_closed := flower_low_of_marked one_le_C₀L one_le_cθL stage1MKGateLow`
  → `flower_low_of_stage1 hC₀ hcθ Fama.stage1ReductionGateLow hI`
  → `Flower.flowerest1_low_of_items5 hC₀ hcθ h5a hI H2.finalCountAtMKLAt_holds`
  → `flowerest1_low_of_items4 … finalCountGateLow_closed …`
  → `flowerest1_low_of_items3 … subObjectsInput …`
  → `items2 … (LGLow.CC.coupleClauseLow_of_three h5a h6 hSO)`
  → `items … (fineSplicedGateLowMK_of_count hSO (finalCountGateLowMK_of_L hH2))`
  → `flowerest1_low_of_parts (nonregLowTarget_of hC₀ hcθ hI selSumTargetTG hH) hD`.
- Named inputs and the closed theorems that discharge them:

| input | discharged by |
|---|---|
| L5a `Stage1ReductionGateLow` | `Fama.stage1ReductionGateLow` |
| L6 `FinalCountGateLow` | `finalCountGateLow_closed` = `finalCountGateLow_of_ghost Ghost.chainCoverLowL'_holds` (the low-range ghost chain cover, R194) |
| L3 `SubObjectsInput` | `TVine.Struct.subObjects_holds` |
| L8 item I `Stage1MKGateLow C₀L 452 cθL` | `stage1MKGateLow` |
| L8 item H2 | `H2.finalCountAtMKLAt_holds` (the bank re-cut) |
| item H | `fineSplicedGateLowMK_of_count` |
| item D / couple clause `CoupleClauseLowInput` | `LGLow.CC.coupleClauseLow_of_three` |

- Budget constants:
  - `C₀L := Classical.choose exists_stage1MKGateLow`, which is legitimate because `exists_stage1MKGateLow : ∃ C₀, 2 ≤ C₀
    ∧ Stage1MKGateLow C₀ 452 cθL` is a theorem; `one_le_C₀L` is proved from `two_le_C₀L`;
  - `cθL := max 1 cθGen`, with `one_le_cθL` proved;
  - `cP = 452` is a literal.

**LG chain:** `layergarden_low_closed := layergarden_low_of_stage1 Fama.stage1ReductionGateLow = LGLow.layergarden_low
h5a Famc.coarseSplicedGateLow finalCountGateLow_proved TVine.Struct.subObjects_holds.{0,0}`.
- `layergarden_low` = `layergarden_of_nonregular_on (· ≤ 1/2)` applied to main's spine gates
  `Spine.leafwise_coherent_approximation`, `Spine.coherent_taylor`, `Spine.leafwise_incoherent_decay` and
  `Spine.ladder_fourier`. Each is a closed theorem of a `WTPrefix` gate (`LGSpine.*Gate`) whose body uses γ only as a
  parameter (`coupleLeaves P.L P.γ P.δ …`, `splicedFrequencySpectrum … P.γ …`). These are **full-range statements, with no
  `1/2 < γ`**.
- L07 FINDINGS F1–F3 (read): `TypeGateAt` contains no γ, and `typeGateAt_of_main` derives it from main's own five gates,
  so the waist is not stronger than main's chain. `layergarden_of_nonregular_on` is main's `…_v2_of_nonregular_half`
  made generic in the γ-predicate.

**Every input of every glue theorem** is FL, LG, a sealed frozen export (`layergardenFlower_v3`, `layergarden_v2`,
`wkeTaylor`, `nlsAkBridge`) or a proved theorem. Since FL and LG are closed theorems whose types are exactly the gate
constants (§1.2), and the whole closure replays with no axiom, `sorryAx` or opaque, **no named input can survive as a
hypothesis**.

**Watch items at γ = 1/2 (AUDIT-V4 §7).** Main's `FinalMKStep` `hmarg : 2γ₀ + 4η² ≤ 1` (false at γ = 1/2) and the ghost
step's `h8 : 8η ≤ 2γ − 1` (false for every γ ≤ 1/2).
Checked at term level by my own exe (`watch/exe/Watch.lean`; olean reader built on the replay's loading code, no
elaboration). It walks every constant reachable from FL and from LG (types and values) and matches, structurally, every
binder domain of each reachable project constant's type, including those nested in hypotheses, against `8 * _ ≤ 2 * _ -
1` (h8), `2 * _ + 4 * _ ^ 2 ≤ 1` (hmarg) and `1 / 2 < _` (`watch/watch.out`; 1:00:30 wall, 8.0 GB RSS).
- FL reaches 231 531 constants in 11 064 project modules; LG reaches 217 059 in 9 778.
- **No constant with an h8- or hmarg-shaped premise is reachable from FL or from LG.** Main's `FinalMKStep`
  (`hmarg`) and the h8 ghost chain (`FinalCount/AsmPhase2*`, `LowChain*`, `FinalMKChain/*`, which a source grep finds
  in the closure because the high half imports them) are not in FL's or LG's dependency closure.
- Their replacements are proved and axiom-clean (§1.4): the bank re-cut `H2.finalCountAtMKLAt_holds` and the low-range
  chain cover `Ghost.chainCoverLowL'_holds`.
- The 52 `1/2 < _` hits (28 under FL, 24 under LG; the same SumintPar/CountLemmas lemmas) are all harmless:
  - a case-conditional premise `hhigh : 1/2 < γ → β/20 < min (2γ−1) (1−γ)`, true vacuously at γ ≤ 1/2
    (`SumintPar.exists_source_*`, `SumintSmallness.beta_high`, `Flower.V5WT.*Out`);
  - or the γ > 1/2 branch of an explicit γ-generic case split. `CountLemmas.coupledPair_bound` (`PairCount.lean`) uses
    `coupledPair_low_bound` when `γ ≤ 1/2` and `coupledPair_high_bound … (lt_of_not_ge hhalf)` otherwise;
    `exists_source_normal_block_bound` has `by_cases hg : 1/2 < γ`;
  - or not about γ at all (`twoExitKernelConstant_lt_top`'s exponent `1/2 < a`).

  None survives as a hypothesis of FL or LG, which are closed.

### 1.6 Full-range check (KEY-A)
- **Elaborated types** (`probes/info_<k>.lean`; a meta pass lists every `WTParams.γ` application or projection with the
  head of its enclosing application):
  - v4, layergarden, propansatz and main: **none**;
  - fixedpoint: exactly two, `WTParams.γ` under `WaveTurbulence.Lop` and under `WaveTurbulence.aTr`. Both are the
    a-system's scaling parameter (coupling δ/(2L^{d−γ}), phases L^{2γ}; T L712), not a restriction;
  - main: γ occurs only as the bound variable of `hγ : γ ∈ Ioo 0 1` and in `α = L ^ (−γ)` (T L314).
  - In every case the prefix's `γ ∈ Ioo 0 1` sits inside the constants `WTPrefix`/`WTPrefixP` (both bodies read).
- **Definition closures** (`h/gamma-grep.out`): grep, comments stripped, of the union of the five manifest definition
  closures plus the anchors (108 + 102 + 115 + 101 + 13 files) for `γ`, `gamma`, `1 / 2`, `1/2`, `α`, `2⁻¹` and `half`.
  Every hit is one of:
  - γ as a parameter: `coupling d L γ δ = δ/(2L^{d−γ})`; the phases `L^{2γ}` in `aNonlin`, `phaseProd`, `phaseProdOff`
    and `treeTerm`; `IsASolution`, `Lop`, `aTr`, `KG`, `KQ` and `kernelK(gen)` taking `P.γ`;
  - the prefix's `γ ∈ Ioo 0 1` (`WTPrefix`, `WTPrefixP`) and main's `hγ`;
  - α as the NLS coupling (`IsSmoothNLSSolution`, `solvableEvent`, `kineticTime α = 1/(2α²)`);
  - 1/2 as a normalisation: `stdComplexGaussian`'s variance 1/2 per component (𝔼|g|² = 1), `θ_p`'s `(2)⁻¹ ^ p`
    (T L611), fixedpoint's contraction constant `2⁻¹` (§4.3 (D1)).

  **No γ restriction beyond 0 < γ < 1** in any statement or closure.
- **Inner closed inputs used at S = univ:** `Cpl.oX3Cpl = WTPrefix OX3CplBody` and `X2E.oX2Exp = WTPrefixP OX2ExpBody`
  contain no γ token. `InductContext` (propansatz) holds only `P.γ ≤ P.d`, which is true for every γ < 1 ≤ 3 ≤ d.
  `MainGlue.main_of_propansatz_nlsAkBridge` uses `hγ` only to call propansatz at (d, γ).

### 1.7 Status fields ((g))
My own scan of the clean export (`g/status.out`; a comment- and string-aware tokenizer over 14 410 `.lean` files) and the
repository guards run on the export: `a/guard.out` `FROZEN-ANCHOR GUARD OK`, `a/modules.out` `check_lean_modules: PASS
(14410 Lean files)`, `a/pinned.out` `PINNED-TEXT GUARD OK`.
- **DRAFT_ANCHORS: 2** — `layergardenFlower_v1` (`WaveTurbulence/Frozen/Theorems/LayergardenFlower.lean`) and
  `layergardenFlower_v2` (`WaveTurbulence/Frozen/Theorems/LayergardenFlowerV2.lean`). Manifest: 326 SEALED, 2
  DRAFT_SORRY.
- **UNREGISTERED_SORRIES: 0.** The only `sorry` tokens are the two registered DRAFT bodies, L53 of each.
- **DRAFT_IMPORT_VIOLATIONS: 0.**
- **SEALED_THIS_TURN: 5** — layergardenFlower_v4, layergarden_v1, fixedpoint_v1, propansatz_v1, main_v1.
- Source scan for `axiom`, `opaque`, `unsafe` and `partial` declarations: 0. The replay (§1.2) is authoritative.

### 1.8 Common (b)/(e) evidence
- **Provider imports.** Each provider's public imports are exactly the anchor's `Frozen.Defs.*` plus Mathlib (pre-seal
  stub = post-seal, `probes/ovl/mk_ovl.py`). Its proof modules are private `import`s only:
  - v4: `Glue.Flower`, `Close.Final`;
  - layergarden: `Glue.Layergarden`, `Close.Halves`;
  - fixedpoint, propansatz, main: `Glue.<X>`, `Close.Final`, `Close.Halves`.
- **No self-import.** No provider imports its own anchor, either in source or in Lake's resolved closure (provider
  `.setup.json`, 21 660–22 805 entries; none of the five `Frozen.Theorems` modules is among them).
- **Export used only by the anchor.** Each provider module is imported only by its anchor, and each export name occurs
  only in the anchor and provider files.
- **Freeze environment.** The anchor's own Lake setup file has 13 (main) to 115 WaveTurbulence entries: the frozen defs
  plus the provider (exported parts). A module probe importing only the anchor sees none of the glue theorems,
  `wtPrefix_of_halves`, FL, LG, the two gates, the sealed v2/v3 anchors or `MainGlue` (all `VISIBLE … false`;
  `probes/info_<k>.out`). Its loaded WaveTurbulence modules are 109 / 103 / 116 / 102 / 14: the defs, the provider and
  the anchor.
- **ABI method 2** (my setup file on the real build, module probe `import all M` / `#print E`, `probes/abi2_<k>.*`)
  reproduces all five manifest hashes. **Method 1** (non-module `import M` / `#print E` on a scratch root) fails on the
  real build for every sealed anchor: "failed to read file `…J1VI029.olean.private`", the vm.max_map_count symptom on
  which the repository's own `abi_hash.py` falls back. I therefore ran method 1 on two overlays compiled in my directory
  (`probes/ovl/`, farm = main's built `Frozen/Defs` plus two overlay-compiled modules):
  - pre-seal: the `seal^` anchor (`by sorry`) and the `seal^` provider stub, i.e. the freeze environment; the defs are
    unchanged since freeze (§(a));
  - post-seal: the sealed anchor text and a stub provider with the same public imports and statement, body `sorry`.

  The post-seal overlay `#print` is **byte-identical** to method 2's output on the real build.

## 2. Per-anchor sections

### 2.1 layergardenFlower_v4 (D16; TARGET `flowerest1`, full range) — the chain's first seal

| item | verdict | evidence |
|---|---|---|
| (a) | PASS | prefix `4af98d833f5acd30…`, suffix `9f48199048606af9…` = manifest = freeze file; body `by sorry` → `by exact WaveTurbulence.Provider.layergardenFlower_v4`; commits touching the file since freeze: only `eae9b6b3`, `4558dd65`; manifest change exactly {state, abi_sha256}; 107 closure hashes match; seal commit 5 paths, ABI commit 1 path / 1 field |
| (b) | PASS | statement text byte-identical (incl. `open Classical in`); type `==` and **Expr.equal** (replay and probe); pp.all text identical (342 lines, sha256 `969eaea517646c45…` both); body exactly `Glue.layergardenFlower_v4_of_low Close.flower_low_closed`; exact-type and composition `example`s compile; Decidable instances below |
| (c) | PASS | anchor, provider, glue, FL, `layergardenFlower_v3`: `[propext, Classical.choice, Quot.sound]` |
| (d) | PASS | glue = `wtPrefixP_of_halves layergardenFlower_v3 hFL`, split exhaustive, γ = 1/2 in the low half; FL closed; watch items (§1.5); non-vacuity at γ = 1/2, 1/4 compiled |
| (e) | PASS | pre-seal `585a8d7c0aeb65d744a34f5565cb4e627b349a7705384c6c3c40c42e23fa0a7e` (= DRAFT abi); post-seal `e1a20b63605ff3c7637ad6010925f192254e2a620e7f3bb1295767ca925e7beb` by both methods (= manifest = seal-prep dry run); `#print` differs only in the value line `sorry` → `WaveTurbulence.Provider.layergardenFlower_v4`; pp.all type pre = post (29 837 characters) |
| (f) | PASS | §1.2 (union replay OK), §1.3 (traces) |
| (g) | PASS | §1.7 |
| (h) | PASS | 42 rows: SOURCE 12, STANDING 14, TYPING 9, RULED 7, **EXCESS 0**; no γ restriction |

**(b) details.**
- In the replay, `Provider.layergardenFlower_v4.type == anchor.type` and `Expr.equal` are both true. Its value is
  `GammaLow.Glue.layergardenFlower_v4_of_low GammaLow.Close.flower_low_closed`, and the anchor's value is
  `WaveTurbulence.Provider.layergardenFlower_v4`.
- `probes/compose.lean`: the glue conclusion (after its gate binder; no loose bvars) is `==` and `Expr.equal` to the
  anchor's type.
- **`open Classical in` / Decidable.** The two `if ∀ j, pat j = .plain` instances are
  `@Nat.decidableForallFin (2*Pm) (fun j => pat j = .plain) (fun a => instDecidableEqFixPat (pat a) .plain)` in the
  anchor, the provider, the glue conclusion and the gate `LayergardenFlowerLowGate`'s body (pp.all; equal to the anchor's
  modulo the de Bruijn shift from the gate's one extra binder `P.γ ≤ 1/2`). It is the frozen
  `instDecidableEqFixPat`, not `Classical.propDecidable`. The anchor was elaborated without the private imports and is
  `Expr.equal` to the glue conclusion, which was elaborated in the γ ≤ 1/2 world, so those imports add no instance that
  changes it.

**(d) details.**
- `Glue/Halves.lean` L44–L69 (`wtPrefixP_of_halves`; read in full):
  - `by_cases h : 1 / 2 < γ` is placed right after `γ ∈ Ioo 0 1`, and **all** witnesses (η₀, C₁, ν₀, P₀, δ₀, C₂, L₀)
    are taken from the one selected half, so nothing is combined across halves. Each witness keeps its half's
    positivity/≥ 1 proof, and each universal range is the prefix's own.
  - The `else` branch passes `le_of_not_gt h : γ ≤ 1/2`, so **γ = 1/2 goes to the low half**. The split is exhaustive.
  - Provenance: `Glue/Halves.lean` L14–L61 are verbatim the audited `<work>/gamma-half-scope/drafts/HalvesGlue.lean`
    L14–L61, whose sha256 `5c4f759a…` = L07 `COPIED-SHA256SUMS`.
- FL is closed (§1.2), with named inputs as in §1.5 and watch items as in §1.5.
- **Non-vacuity at γ ≤ 1/2** (`probes/vac.lean`, compiles, axioms standard; concrete `Pγ γ = ⟨d=3, γ, η=1/100, φin=0,
  τ★=1, φ=0, C₁=1, ν=1/100, δ=1, D=1, C₂=1, L=3⟩` at γ = 1/2 and γ = 1/4):
  - `(1/2), (1/4) ∈ Ioo 0 1`;
  - every prefix choice is followed by a non-empty range: `(Ioc 0 η₀).Nonempty`; `∃ L ≥ L₀`; `∃ Pm ≥ P₀`;
    `delta_range` gives δ ∈ (0, δ₀] and D ≥ 1 with τ★ = Dδ for every δ₀ > 0;
  - `IsWKESolution 0 τ 0`;
  - `RemainderBound (Pγ (1/2)) 0 p` and `RemainderBound (Pγ (1/4)) 0 p` (via `SNorm` of 0 = 0);
  - p = 0 < 𝔇;
  - t = 1/2 ∈ (0, 1) and s = 1/4 ∈ (0, t);
  - N = 0 ≤ N_{p+1}⁴;
  - a valid `cut2 = some 0`, `cut1 = some 0` configuration: n = (3¹¹, 3¹¹, 3¹¹) gives (2⁰·L)¹⁰ ≤ |n/L| at L = 3;
  - the universal variables `kind`, `pat`, `dagger` and the couple binders range over inhabited types; the couple
    premise `kind = .tr → dt = true` holds at `dt = true`.

  `ansatz_inhabited (1/2)` and `ansatz_inhabited (1/4)` produce, from the sealed `propansatz` at γ = 1/2 and 1/4 (with
  thresholds beyond its existentials), remainders R with `RemainderBound P R 0` that are actual ansatz remainders.

**(h)** Table: `h/tables.md`, Π1–Π19 + Π13a and V1–V22.
- The prefix is (Π_P), with `γ ∈ Ioo 0 1` STANDING and **no `1/2 < P.γ`**. This matches D16: v3 minus that hypothesis.
- Every body binder is SOURCE (T L2263, L2268, L2271–L2285, L2309–L2312), TYPING, or RULED under D7 (B1.12 (D2), (D3),
  (D8)–(D10), F68, F78) and D13 (product cutoffs, E34).
- **EXCESS 0.**
- Differences to the appendix (35 rows: SOURCE 13, STANDING 11, TYPING 4, RULED 7) are granularity and four bin labels,
  none involving EXCESS:
  - `∃ δ₀` STANDING (mine) vs SOURCE;
  - `n n'` TYPING vs SOURCE;
  - the couple clause's `t ∈ Ioo p (p+1)`: RULED (mine), because T's (trterm1) has t ∈ [p, p+1]; the endpoint exclusion
    weakens an added clause and is not a premise of flowerest1;
  - `kind : TreeKind` SOURCE (mine) vs RULED.

`layergardenFlower_v4` may be recorded as PROVED (key A)

### 2.2 layergarden_v1 (D7; TARGET `layergarden`, full range)

| item | verdict | evidence |
|---|---|---|
| (a) | PASS | prefix `150a9eb3807a7d3c…`, suffix `9f481990…` = manifest = freeze file; body → `by exact WaveTurbulence.Provider.layergarden`; commits since freeze: `f2d1fb6b`, `2e2c16ef` only; vs pre-seal manifest exactly {state, abi_sha256} (vs `f2d1fb6b` also `approved_at` "PENDING-D7" → "2026-11-04", the D7 recording, before the seal); 101 closure hashes match; seal 5 paths, ABI 1 path / 1 field |
| (b) | PASS | statement text byte-identical; type `==` and **Expr.equal**; pp.all identical (192 lines, `19b46b090aeb486d…`); body exactly `Glue.layergarden_of_low Close.layergarden_low_closed`; exact-type and composition examples compile |
| (c) | PASS | anchor, provider, glue, LG, `layergarden_v2`: standard three |
| (d) | PASS | glue = `wtPrefix_of_halves layergarden_v2 hLG` (`Glue/Halves.lean` L22–L42, same split, γ = 1/2 low); LG closed with the four inputs (§1.5); spine gates full-range; non-vacuity compiled |
| (e) | PASS | pre-seal `ae0ce36636b12aa0b8952e3c4dfd31eb79cd35af4754d7717a1a3c7eea180140` (= DRAFT abi); post-seal `92b0b3e853d27ce9620781008f2421fbbdbc727b8ca61b739843af1737873b42` by both methods (= manifest = dry run); value line only; pp.all pre = post (15 675 characters) |
| (f) | PASS | §1.2, §1.3 |
| (g) | PASS | §1.7 |
| (h) | PASS | 33 rows: SOURCE 7, STANDING 14, TYPING 10, RULED 2, **EXCESS 0** |

**(d) non-vacuity at γ ≤ 1/2** (`probes/vac.lean`):
- p = 0 < 𝔇;
- `RemainderBound (Pγ γ) 0 p` at γ = 1/2 and 1/4, and `RemainderBound P R 0` for the propansatz remainders
  (`ansatz_inhabited`);
- t = 1 ∈ Ioc 0 1;
- N = 0;
- the m-range: `2 ≤ 10 · R_{p+1}` at L = 3, where R_𝔇 = ⌊(log 3)^{120}⌋ ≥ 1 (log 3 ≥ 1);
- balanced ζ exist at every width 2m (`IsBalancedSig (j < m ? 1 : −1)`).

Unbalanced ζ would give an empty sum (`truncSum` filters `LG.garden.sig = ζ`), so `IsBalancedSig` hides nothing.

**(h)** Table G1–G14 plus Π. Every binder is SOURCE (T L761–L769, L708/L760) or TYPING, and RULED for `RemainderBound`
(§4.2 (D1)) and `t ∈ Ioc p (p+1)` (§4.2 (D2)). Clause (2b) is the merged (estcouple)/(estcouple2) (§4.2 (D3)). **EXCESS
0, no γ restriction.** Differences to the appendix are granularity only (it bundles the prefix as one STANDING row and
bins `n` SOURCE; I bin it TYPING).

`layergarden_v1` may be recorded as PROVED (key A)

### 2.3 fixedpoint_v1 (D7; TARGET `fixedpoint`, full range)

| item | verdict | evidence |
|---|---|---|
| (a) | PASS | prefix `9033444b16e6a484…`, suffix `9f481990…`; body → `by exact WaveTurbulence.Provider.fixedpoint`; commits `f2d1fb6b`, `008e27f9` only; manifest as layergarden; 114 closure hashes match; seal 5 paths, ABI 1 path / 1 field |
| (b) | PASS | text byte-identical; type `==`; Expr.equal false, **Expr.equal after erasing macro scopes: true** (`probes/binders_fp.out`: of 550 binder names exactly two differ, the anonymous instance binders `[MeasurableSpace Ω]`, `[IsProbabilityMeasure μ]`, `inst._@.WaveTurbulence.Frozen.Theorems.Fixedpoint…_hyg.9/.14` vs `…Provider.Fixedpoint…_hyg.9/.14`); pp.all identical (2 143 lines, `9577a4d07cc434a7…`, with `pp.maxSteps`/`pp.deepTerms` raised so no `⋯` elision); the four `let`s (`Ntr`, `Λ`, `ℒ`, `Zs`) are inside that identical pp.all text (no let/have or zeta difference); `example : type_of% @fixedpoint.{u} = type_of% @Provider.fixedpoint.{u} := rfl` compiles; levels [u]/[u]; body exactly `Glue.fixedpoint_of_low FL LG` |
| (c) | PASS | anchor, provider, glue, FL, LG, `wkeTaylor`, `layergardenFlower_v3`, `layergarden_v2`, `Cpl.oX3Cpl`, `X2E.oX2Exp`: standard three |
| (d) | PASS | S-generic route at S = univ; inner inputs full-range; FL, LG closed; IH satisfiable at γ = 1/2, 1/4 |
| (e) | PASS | pre-seal `4fafe6c0092a7ad991c1d32442cc62231e774edfb5e5d3aa48501f8de47fffaf` (= DRAFT abi); post-seal `bcfe4a35a9ef74f10abb380c4a9aab4e5417359cc693c9fa7a832fd6c4d16780` by both methods; value line only; pp.all pre = post (203 825 characters) |
| (f) | PASS | §1.2, §1.3 |
| (g) | PASS | §1.7 |
| (h) | PASS | 54 rows: SOURCE 15, STANDING 19, TYPING 14, RULED 6, **EXCESS 0** |

**(d) details.**
- The glue (`Glue/Fixedpoint.lean`) is exactly `toFull (V2Chain.fixedpointS_of_parts (S := Set.univ)
  (V2Chain.cplMomentsS_of_gates (ofFull hG) (ofFull hL) (ofFull hW) Cpl.oX3Cpl) (V2Chain.part2S_of_X2
  (V2Chain.flowerest1S_of_gates (ofFull hG) X2E.oX2Exp)))`, with `hG := layergardenFlower_v4_of_low hFL`, `hL :=
  layergarden_of_low hLG` and `hW := WaveTurbulence.wkeTaylor`.
- `V2Chain.WTPrefixS S Q` is `WTPrefix` with exactly one extra premise `γ ∈ S` after `γ ∈ Ioo 0 1`. `ofFull` drops it and
  `toFull` supplies `Set.mem_univ γ`, so the encoding threads `γ ∈ S` and cannot make `WTPrefix` vacuous.
- At S = univ every γ-assumption of `fixedpointS_of_parts`, `cplMomentsS_of_gates`, `part2S_of_X2` and
  `flowerest1S_of_gates` is `γ ∈ univ`. Their γ > 1/2 instance (`fixedpoint_v2_of_closed_gates_v3`) is not used. The
  type-check of the kernel-replayed glue at the full-range type is the proof of that.
- **Non-vacuity at γ ≤ 1/2** (`probes/vac.lean`):
  - `gaussian_exists d` builds Gaussian data from Mathlib's `exists_iid` with `stdComplexGaussian`: measurable,
    `iIndepFun`, law `stdComplexGaussian`, on a probability space;
  - `ansatz_inhabited (1/2)` and `ansatz_inhabited (1/4)`: for a parameter tuple with `P.γ = γ` (thresholds from the
    sealed `propansatz`'s own existentials) and such data, there are a, Fev, R, E, Et with `∀ q ≤ 0, AnsatzAt P μ g a Fev
    R E Et q`. So the induction hypothesis — the only non-trivial premise — is satisfiable at γ = 1/2 and 1/4. T L708's
    p = 0 base case is satisfiable as well;
  - `IsGaussianData` is inhabited.

**(h)** Table F1–F23 plus Π. `AnsatzAt` is expanded into its 13 conjuncts (AUDIT-COMMON (h) requires it):
- 9 are SOURCE: T L691 (symmetry, nesting, probability, the solution on [0,q]), L693, L695, L697–L705;
- 4 are RULED by D7: `MeasurableSet (Fev q)`, measurability of `a · t n`, integrability of finite products, and item (2′)
  (WAVE-B §4.1 (D3)/(D5), §5).

The data binders are STANDING (T L292–L294, D6). The conclusion's internal binders are SOURCE (T L782–L793), with
unique solvability and the ½ contraction RULED (§4.3 (D1)/(D4)). **EXCESS 0.** `WTParams.γ` occurs only under `Lop` and
`aTr` (§1.6). Difference to the appendix: it keeps the IH as one SOURCE row (unexpanded) and bins the data SOURCE and
`IsProbabilityMeasure` TYPING; the expansion finds no EXCESS conjunct.

`fixedpoint_v1` may be recorded as PROVED (key A)

### 2.4 propansatz_v1 (D7; TARGET `propansatz`, full range)

| item | verdict | evidence |
|---|---|---|
| (a) | PASS | prefix `f30b287326ee9824…`, suffix `9f481990…`; body → `by exact WaveTurbulence.Provider.propansatz`; commits `f2d1fb6b`, `6f4a03d2` only; manifest as layergarden; 100 closure hashes match; seal 5 paths, ABI 1 path / 1 field |
| (b) | PASS | text byte-identical; `==`; **Expr.equal after erasing macro scopes** (exactly the two anonymous instance binders differ, `probes/binders_pa.out`); pp.all identical (39 lines, `535114cea9158d3e…`); `example : type_of% @propansatz.{u} = type_of% @Provider.propansatz.{u} := rfl` compiles; levels [u]/[u]; body exactly `Glue.propansatz_of_low FL LG` |
| (c) | PASS | anchor, provider, glue, FL, LG, `wkeTaylor`: standard three |
| (d) | PASS | INDUCT at S = univ; witnesses constructed; unconditional inputs γ-generic |
| (e) | PASS | pre-seal `4db839d1ef1a3deef8566363da7a853aa3cd55ba45cc1d1660f13cca65fa6748` (= DRAFT abi); post-seal `1e9629b501a5d4517e0e1d56612367bf7328632ecc0f38b1bf9151dbab8b431e` by both methods; value line only; pp.all pre = post (2 527 characters) |
| (f) | PASS | §1.2, §1.3 |
| (g) | PASS | §1.7 |
| (h) | PASS | 30 rows: SOURCE 3, STANDING 19, TYPING 8, RULED 0, **EXCESS 0** |

**(d) details.** The glue is `toFull (V2Chain.propansatzS_of_gates (S := Set.univ) (ofFull hL) (ofFull hF) (ofFull hW))`,
with `hL := layergarden_of_low hLG`, `hF := fixedpoint_of_low hFL hLG` and `hW := wkeTaylor`.
- **Witnesses.** `propansatzS_of_gates` builds `InductContext P` and calls `propansatz_body_of_context`. That proves
  `∀ p ≤ 𝔇, Nonempty (AnsatzPrefixData P μ g p)` by induction: `basePrefixData` at p = 0 (T L708), then
  `extendPrefix … (exists_prefix_extension … H.fixedpoint …)`. It then returns `⟨S.a, S.Fev, S.R, S.E, S.Et,
  S.ansatz⟩`, so **the witnesses are built, not taken from a hypothesis**.
- **γ in `InductContext`.** The only γ field is `gamma_le_dimension : P.γ ≤ d`, discharged from `hγ.2 : γ < 1` and
  d ≥ 3, i.e. valid for every γ ∈ (0, 1).
- **Unconditional inputs** (the docstring's three stage-3 O8 lemmas): `solution_norm_sq_le_initial_mass` (mass
  conservation, T L819), `solution_norm_le_one_add_gaussian_mass` and `integrable_signed_prod_of_solutions`
  (`Foundations/XChain/SolutionMomentIntegrability.lean`). They are proved theorems, generic in `{L γ δ T}` with no γ
  premise, and kernel-replayed.
- **Non-vacuity.** The conclusion is existential. I read the body of `AnsatzAt` (sealed, D7), and it contains:
  - (1): measurable symmetric `Fev p`, nested, probability ≥ 1 − e^{−N_p}, a classed solution on [0, p] that is unique
    in the class;
  - (2): ‖R_p‖ ≤ L^{−θ_p}, |E_p| ≤ ⟨n/L⟩^{−Λ_p} e^{−N_p}, and the two-point identity with 1_{n=n'};
  - (3): the cumulant = Σ_{N ≤ N_p} truncSum + Ẽ, with the support condition and the Ẽ bound;
  - (4): the order-N bound with L^{−(m−1)/6} δ^{νN};
  - only the §4.1 deviations: (D1)–(D7), measurability/integrability, and (2′).

  So `AnsatzAt` is not weaker than T's (1)–(4).

**(h)** Prefix plus data (STANDING; T L292–L294, D6). The conclusion `∃ a Fev R E Et, ∀ p ≤ 𝔇, AnsatzAt … p` is SOURCE
(T L689). No premise beyond the prefix and the data. **EXCESS 0.**

`propansatz_v1` may be recorded as PROVED (key A)

### 2.5 main_v1 (D6; Theorem 1.1, full range 0 < γ < 1)

| item | verdict | evidence |
|---|---|---|
| (a) | PASS | prefix `fdb8acf38409984d…`, suffix `9f481990…`; body → `by exact WaveTurbulence.Provider.main`; commits `8d1d2e3b`, `bfbb5546` only; manifest change exactly {state, abi_sha256}; 12 closure hashes match; seal 5 paths, ABI 1 path / 1 field |
| (b) | PASS | the five checks of the brief all pass (below) |
| (c) | PASS | anchor, provider, glue, FL, LG, `nlsAkBridge`, `wkeTaylor`, `MainGlue.main_of_propansatz_nlsAkBridge`: standard three |
| (d) | PASS | γ-generic assembly; θ = η₀²⁰ before φin; solvable event non-empty at γ = 1/2, 1/4 |
| (e) | PASS | pre-seal `05d07e58bd43f9f500570d2d4993deec5442d73225ca0f6536ba2ba20c3e7f2c` (= DRAFT abi); post-seal `b83d1394ae7b902677b6fbd70ae839d0ef59cd5e71c395558b16be4169c729fc` by both methods; value line `fun d hd γ hγ => sorry` → `fun d hd γ hγ => WaveTurbulence.Provider.main hd hγ` only; pp.all pre = post (75 485 characters) |
| (f) | PASS | §1.2, §1.3 |
| (g) | PASS | §1.7 |
| (h) | PASS | 24 rows: SOURCE 17, TYPING 5, RULED 2 (D6 selection device), STANDING 0, **EXCESS 0** |

**(b) details** (the binder adaptation of the sealed `wkelwp` and `main_v2`):
- (1) The conclusion text is byte-identical to the anchor's.
- (2) Binder table (`probes/info_main.out`):
  - anchor `(d)`, `(hd)`, `(γ)`, `(hγ)`, all default;
  - provider `{d}` implicit, `(hd : … := by assumption)` default with `autoParam`, `{γ}` implicit,
    `(hγ : … := by assumption)` default with `autoParam`;
  - names and order identical; each type `Expr.equal` after unwrapping `autoParam`;
  - these are exactly the four adaptations. The pp.all diff is confined to those binder lines (lines 1–12).
- (3) The conclusions after the four binders are `==` (BEq), and `Expr.equal` after erasing macro scopes (the only differing binder names are the two
  anonymous instance binders `[MeasurableSpace Ω]`, `[IsProbabilityMeasure P]`, whose macro scopes name the module;
  `probes/binders_main.out`).
- (4) `example : type_of% @WaveTurbulence.main.{u} := fun d hd γ hγ => @WaveTurbulence.Provider.main.{u} d hd γ hγ`
  compiles.
- (5) The anchor's value (replay, all olean parts) is `fun d hd γ hγ => WaveTurbulence.Provider.main.{u} d hd γ hγ`, so
  the auto-params are the anchor's own `hd` and `hγ`.

**(d) details.**
- The glue is `MainGlue.main_of_propansatz_nlsAkBridge (propansatz_of_low hFL hLG) WaveTurbulence.nlsAkBridge d hd γ hγ`,
  with γ-generic hypotheses `(hγ : γ ∈ Ioo 0 1)`, and **no γ > 1/2 premise**.
- It obtains η₀ from propansatz at (d, γ) and sets **θ := η₀²⁰ before φin** (T L611/L612; quantifier order ∃ θ > 0 ∀ φin
  enforces θ = θ(d, γ)). It then:
  - picks η = η₀, ν = ν₀, and D = ⌈τ★/δ₀⌉ via `ceiling_subdivision`;
  - applies the sealed `nlsAkBridge`, which supplies the measurable selection.

  Every lemma it uses is either a proved theorem with no γ premise (kernel-replayed) or `NLS.kineticTime_rpow_neg_pos`
  applied at the given γ.
- **Meaning and non-vacuity at γ ≤ 1/2** (`probes/vac.lean`, `main_event_nonempty (1/2)` and `(1/4)`). With d = 3,
  φin = 0, τ★ = 1, φ = 0 (`IsWKESolution`), L ≥ max(L₀, 3), α = L^{−γ}, T = τ★·T_kin and Gaussian data:
  - main's own bound `1 − e^{−(log L)^{120}} > 0` shows the solvable event is non-empty;
  - a selection `U` (by choice on the event) satisfies the premise `∀ ω ∈ solvableEvent …, IsSmoothNLSSolution … (U ω)`,
    so that premise is not a vacuous universal.

  `IsWKESolution` is inhabited (`wke_zero`; `wkelwp` gives it for small τ★ and any Schwartz data).

**(h)** Table M1–M24:
- `hd : 3 ≤ d`, `hγ : γ ∈ Ioo 0 1` (the source's full range, D2), the data and (limit) are SOURCE (T L294, L314–L318);
- `IsWKESolution` is SOURCE + D6;
- the selection device `∀ U` and its premise are RULED (D6);
- **EXCESS 0**.

Differences to the appendix are bin labels only:
- the variables d and γ: TYPING (mine) vs SOURCE;
- `[IsProbabilityMeasure P]`: SOURCE (mine) vs TYPING;
- the selection device: RULED (mine, D6) vs SOURCE.

`main_v1` may be recorded as PROVED (key A)

## 3. Files (all under `<work>/seal-audit-ALL-A/`)

| file | content |
|---|---|
| `01-source-reconstruction.md` | TeX and rulings reconstruction, written first |
| `h/tables.md`, `h/gamma-grep.out` | five-bin tables; full-range grep |
| `a/item_a.py`, `a/item_a.out` | prefix/suffix/manifest/commit checks |
| `a/guard.out`, `a/modules.out`, `a/pinned.out` | repository guards on the clean export |
| `g/status.out` | status fields |
| `d/*.json`, `d/watch-grep.out` | source closures; source-level watch grep |
| `replay/Replay.lean`, `replay/Replay.diff`, `replay/replay.sh`, `replay/Replay-quick.out`, `replay/reach-mods.txt` | kernel replay |
| `trace/exe/TraceCheck.lean`, `trace/closure-src.out` | trace check |
| `watch/exe/Watch.lean`, `watch/watch.out` | FL/LG watch-item reachability |
| `probes/gen_setup.py`, `probes/gen_probes.py`, `probes/run_probe.sh` | probe infrastructure |
| `probes/info_*.lean`/`.out` | exact-type examples; pp.all; Expr checks; visibility; γ uses |
| `probes/compose.lean`/`.out` | composition witnesses; axioms; glue conclusions; Decidable |
| `probes/vac.lean`/`.out` | non-vacuity at γ = 1/2, 1/4 |
| `probes/abi2_*`, `probes/m1/*`, `probes/ovl/*` | ABI methods 1 and 2; pre- and post-seal overlays; pp.all pre/post |
