# KEY-B — seal audit (key B) of the five full-range anchors (0 < γ < 1)

> **Reading note.** This is the key-B record of the two-key seal audit of the five full-range anchors. Paths under `<work>/` are the auditor's local working files (scripts, logs, probe outputs); they are not part of the repository. `<sources>/` is the pinned LaTeX source of the papers. All other paths are relative to the repository root.


Auditor: KEY-B (independent; I wrote none of the anchors, providers, glue, proof chain or seal script). Brief:
`seal/audit-briefs/KEY-B-ALL.md`, binding together with `AUDIT-COMMON.md` and the five `AUDIT-<id>-B.md`. Primary
refutation target (KEY-B): the PROOF side — hidden hypotheses through the glue, FL and LG. Working directory (exports,
probes, replay, outputs, tools): `<work>/seal-audit-ALL-B/`. 2026-11-09 22:40 – 2026-11-10 UTC.

## Verdict

| anchor | (a) bytes | (b) provider | (c) axioms | (d) hidden hyps / vacuity | (e) ABI | (f) replay | (g) status | (h) binders | key B |
|---|---|---|---|---|---|---|---|---|---|
| `layergardenFlower_v4` | PASS | PASS | PASS | PASS | **PASS** | PASS | PASS | PASS (EXCESS 0) | **PASS** |
| `layergarden_v1` | PASS | PASS | PASS | PASS | **PASS** | PASS | PASS | PASS (EXCESS 0) | **PASS** |
| `fixedpoint_v1` | PASS | PASS | PASS | PASS | **PASS** | PASS | PASS | PASS (EXCESS 0) | **PASS** |
| `propansatz_v1` | PASS | PASS | PASS | PASS | **PASS** | PASS | PASS | PASS (EXCESS 0) | **PASS** |
| `main_v1` | PASS | PASS | PASS | PASS | **PASS** | PASS | PASS | PASS (EXCESS 0) | **PASS** |

Headline evidence. One kernel replay of the union of the five closures: **REPLAY OK, 237,585 constants in 12,691
modules, 10,071 s, wall 2:53:29, max RSS 12.4 GB**, no project axiom/opaque/unsafe/partial constant, no user of
`sorryAx`/`ofReduceBool`/`trustCompiler`/`ofReduceNat`, MISSING 0; the 13,817 closure modules' `.trace` source hashes and
5.26 GB of olean bytes match the seal commit's sources. FL and LG are binder-free `theorem`s whose types are
`Expr.equal` to the gate constants; their own closures contain no `h8 : 8η ≤ 2γ−1` or `hmarg` lemma at all. Each
provider statement is byte-identical to its anchor (main: the conclusion, plus exactly the four briefed binder
adaptations) and its type `==` the anchor type (main: the conclusions after the four binders); v4 and layergarden are
also `Expr.equal`, fixedpoint, propansatz and main differ only in two hygienic instance-binder names. Before and after
the seal the anchor type is `Expr.equal` and all ten ABI hashes reproduce. No GammaLow module or constant is visible
from any anchor's environment.

Findings (none blocking): N1 the D7 anchors' manifest `author_approval.approved_at` changed after the freeze commit
(`PENDING-D7` → `2026-11-04`, the D7 approval landing `cff26541`), so "changed in exactly state and abi_sha256" holds
from the landed freeze, not from `f2d1fb6b`; N2 `regularAsymptotics` (SEALED, D8) is a consumed sealed anchor of all
five closures but is not listed in the briefs; N3 the `open Classical in` Decidable instances of v4 are the
constructive `Nat.decidableForallFin … instDecidableEqFixPat` (identical in anchor, provider, glue and gate);
N4 README's status block is stale at `5c19b015`; N5 `AnsatzAt` (3)–(4) range over balanced signatures only (D7-approved;
noted for completeness). Details in §7.

## 0. Subject (pinned from git; the briefs' `<…>` fields were not filled)

This repository; audited state `origin/main` = **`5c19b015`** ("Merge HQ documentation
updates from origin/main"). `git diff --stat a25673fd 5c19b015` touches only `README.md`, `docs/campaign/*` (HQ progress
meter `0a082c5c`, `ff12fe34`, merged at `5c19b015`). During the audit origin/main moved on to `6b65391e` (local HEAD
`1b5e1f49`): `git diff --name-only 5c19b015 origin/main` lists only `docs/…` and `README.md` (no Lean file, manifest,
lakefile or toolchain change), and the newest artifact of the replayed closure is `Frozen/Theorems/Main.trace`,
2026-11-09 22:31:29 UTC (the main_v1 seal build), so the build the replay and probes read is the seal's.

| anchor (export) | freeze | seal commit | ABI commit | provider body |
|---|---|---|---|---|
| `layergardenFlower_v4` (`WaveTurbulence.layergardenFlower_v4`) | `eae9b6b3` (D16; landed `8bbfb3b8`) | `4558dd65` | `88e4495a` | `Glue.layergardenFlower_v4_of_low FL` |
| `layergarden_v1` (`WaveTurbulence.layergarden`) | `f2d1fb6b` (D7; landed `cff26541`) | `2e2c16ef` | `a89b5012` | `Glue.layergarden_of_low LG` |
| `fixedpoint_v1` (`WaveTurbulence.fixedpoint`) | `f2d1fb6b` (D7; landed `cff26541`) | `008e27f9` | `e5c86a37` | `Glue.fixedpoint_of_low FL LG` |
| `propansatz_v1` (`WaveTurbulence.propansatz`) | `f2d1fb6b` (D7; landed `cff26541`) | `6f4a03d2` | `09c867a6` | `Glue.propansatz_of_low FL LG` |
| `main_v1` (`WaveTurbulence.main`) | `8d1d2e3b` (D6) | `bfbb5546` | `a25673fd` | `Glue.main_of_low FL LG d hd γ hγ` |

The ten commits are consecutive (`d0961baf` → `4558dd65` → … → `a25673fd`, 22:26:49–22:32:00 UTC), in seal order.
γ ≤ 1/2 port: `304a871c` ("Merge w/gh-port @a46344ef"). Mode A: FL = `WaveTurbulence.GammaLow.Close.flower_low_closed`
(module `…Foundations.GammaLow.Close.Final`), LG = `WaveTurbulence.GammaLow.Close.layergarden_low_closed` (module
`…Foundations.GammaLow.Close.Halves`).

Read-order discipline. I did not open the seal logs (`seal/logs/live-*`) or `seal/HANDOFF.md` before writing my results
(compared in §7.4), and never opened the other key's directory `seal-audit-ALL-A/` (I saw only its replay process in
`ps` when checking machine load). Four claim appendices were opened after my (h) tables were written (`h-tables.md`,
sha256 `af3e385c…`). **Disclosure:** the v4 brief's claim appendix was displayed when I first read that brief (it is
printed inline); my v4 table was nevertheless reconstructed from the TeX and differs from it (§7.3). I read
`seal_full.sh`'s header only to locate the repository, as AUDIT-COMMON allows.

## 1. Shared evidence

### 1.1 Clean export, guard, module check, intermediate states
`git archive 5c19b015 | tar -x` → `export-main/` (14,709 paths). On it, `scripts/check_frozen_anchors.py --root export-main
--manifest export-main/manifest/frozen.json` → **`FROZEN-ANCHOR GUARD OK`** and `scripts/check_lean_modules.py` →
**`PASS (14410 Lean files, 0 comparator configurations)`** (`guard_final.out`; `check_index.sh` runs exactly these two on
an export of the index). The same two checks on my own exports of each of the ten seal/ABI commits: **GUARD OK and
modules PASS at all ten** (`guard_each.out`). I audited the guard's convention (`check_theorem_region`: prefix = bytes
through the newline after `FROZEN_ANCHOR_PROOF_BEGIN`, suffix = from the start of the `FROZEN_ANCHOR_PROOF_END` line;
a SEALED body must match `\s*by\s+(exact\s+|simpa\s+using\s+)<implementation.export>\s*` within 3 lines / 240 bytes)
and reimplemented it (`tools/item_a.py`).

### 1.2 Probe harness (mine)
`tools/probe.py`, `tools/abi.py`: a probe's setup JSON is generated from Lake's own `.lake/build/ir/<M>.setup.json` of
the imported modules (union of their `importArts` plus each imported module's own artifacts; private parts only where
stated; artifact overrides for the DRAFT rebuild). Every Lean run goes through the `wt-throttled` gate
(a Lean v4.35.0 toolchain wrapper, `<work>/sysroot/bin/lean`), `nice -n 10`, one at a time. I audited `scripts/abi_hash_setup.py` (same
union for one module, private parts of every project module, probe `module` / `import all M` / `#print E`) and
`scripts/abi_hash.py` (documented convention: non-module `import M` / `#print E`, sha256 of stdout; it falls back to the
setup form when a non-module import exceeds `vm.max_map_count`). I did not use `seal/tools/*`.

### 1.3 Kernel replay of the UNION — item (f) for all five anchors
Adapted from `<work>/seal-lg2/replay/` (`Replay.lean` sha256 `6c943568…`, `replay.sh` `b8298ed6…`; diff
`replay/Replay.diff`). Changes: roots = the five anchors and their five `Frozen.Theorems` modules; `wanted` = this batch's
chain; EXACT lines for anchor/provider/glue/FL/LG; a census per anchor (reachability from each root alone over the same
loaded data); a dump of every reachable project constant with its gate-like hypothesis heads; index batches that loop
over the whole closure and abort on an index gap. Unchanged: base = exported parts of the 10,976 library modules
(trusted, as in every seal audit), lazy loading of ALL olean parts of project modules holding reachable constants,
quick-mode stubs (`WaveTurbulenceVineParam` theorems whose proofs use no constant outside that library are checked by
statement only), and ONE `Kernel.Environment.replay` call with no shim. Run from this repository
(`main HEAD 5c19b015…`), exe built from `replay/Replay.replayed.lean` (sha256 `82f441b9…`), one niced process.

```
closure modules: 24793; lib: 10976; project: 13817      index: 13817 of 13817 project modules indexed; gaps: 0
base env: 661703 library constants (exported parts)
reachable (union): 248367; lib refs: 10782; MISSING: 0; project modules loaded: 12691
same-name constants in two loaded modules: 1835; of these with different type (or value): 0
project AXIOMS reachable: []   project OPAQUE reachable: []   project UNSAFE/PARTIAL reachable: []
direct users of sorryAx/ofReduceBool/trustCompiler/ofReduceNat: []
core axioms referenced directly by project terms: [Quot.sound, Classical.choice, propext]
reachable project constants by kind: inductive 741, ctor 991, def 24835, theorem 210824, rec 194
reachable project constants: 237585 in 12691 modules; VineParam theorem proofs checked by statement only: 40618;
  VineParam theorems replayed WITH proofs (cross-library): 92873
REPLAY OK (10071s): 237585 constants, no shim, no constant turned into an axiom (quick-mode stubs: 40618)
Elapsed (wall clock) 2:53:29; Maximum resident set size 12433216 kB; rc=0
```
Reachable `Frozen.Theorems` constants (union): the five anchors, `layergardenFlower_v3`, `layergarden_v2`, `wkeTaylor`,
`nlsAkBridge`, `regularAsymptotics` — all SEALED in the manifest. (The "library AXIOM" list my program also prints is
noise: body-less exported library constants appear as axioms in the trusted base; the line above restricted to the
core/critical axioms is the meaningful one.) Output: `replay/Replay-quick.out`.

### 1.4 Census per anchor (same run; reachability from each anchor alone)

| root | reachable (project, modules) | theorem / def / inductive / ctor / rec | project AXIOM / OPAQUE / UNSAFE-PARTIAL / sorry-users | critical axioms referenced | Frozen.Theorems reached |
|---|---|---|---|---|---|
| `layergardenFlower_v4` | 241,960 (231,905 in 11,948) | 206,135 / 23,897 / 720 / 966 / 187 | none | propext, Classical.choice, Quot.sound | v4, `layergardenFlower_v3`, `regularAsymptotics` |
| `layergarden` | 224,869 (215,273 in 10,520) | 192,643 / 21,052 / 596 / 810 / 172 | none | same | layergarden, `layergarden_v2`, `regularAsymptotics` |
| `fixedpoint` | 247,277 (236,682 in 12,531) | 210,015 / 24,747 / 738 / 988 / 194 | none | same | fixedpoint, `layergarden_v2`, `layergardenFlower_v3`, `wkeTaylor`, `regularAsymptotics` |
| `propansatz` | 247,953 (237,286 in 12,651) | 210,567 / 24,793 / 741 / 991 / 194 | none | same | propansatz, `layergarden_v2`, `layergardenFlower_v3`, `wkeTaylor`, `regularAsymptotics` |
| `main` | 248,359 (237,577 in 12,683) | 210,816 / 24,835 / 741 / 991 / 194 | none | same | main, `nlsAkBridge`, `layergarden_v2`, `layergardenFlower_v3`, `wkeTaylor`, `regularAsymptotics` |
| FL `flower_low_closed` | 231,531 (221,509 in 11,067) | 197,644 / 22,271 / 609 / 833 / 152 | none | same | `regularAsymptotics` only |
| LG `layergarden_low_closed` | 217,059 (207,495 in 9,779) | 186,259 / 19,855 / 521 / 719 / 141 | none | same | `regularAsymptotics` only |

The FL/LG rows come from a second run of the same program in a reach-only mode (no kernel step; `Reach-FL-LG.out`,
2 m 44 s, RSS 6.0 GB). `main` reaches none of the other four anchors: the glue does not chain through them.

### 1.5 Trace check: the replayed oleans are the seal commit's sources
`tools/TraceCheck.lean` (uses Lake's own `Hash.ofText` and `computeBinFileHash`): for each of the 13,817 closure modules,
the source-text input hash in its `.trace` equals `Hash.ofText` of the file in my export of `5c19b015` (whose Lean
sources equal the seal commits'), and each recorded output hash (`.olean`, `.olean.server`, `.olean.private`) equals the
hash of the file the replay read: **13,817 / 13,817 OK, 0 bad, 0 missing** (5.26 GB of oleans; `trace-check.tsv`).
Negative controls: an appended comment in one source, and one flipped byte in a copied `.olean.private`, are both
reported BAD. No closure artifact was modified after 22:31:29 UTC (before the replay started).

## 2. The shared proof DAG (item (d), KEY-B's primary target)

All five providers are the L07 glue applied to the same two closed theorems FL and LG.

### 2.1 Provider and glue layer

| theorem | hypothesis | discharged by | kind of discharger |
|---|---|---|---|
| `Glue.layergardenFlower_v4_of_low` | `hFL : Flower.LayergardenFlowerLowGate` | FL | `theorem`, no binders, levels `[]`, type `Expr.equal` to `const LayergardenFlowerLowGate` |
| (body `wtPrefixP_of_halves hi lo`) | `hi` | `WaveTurbulence.layergardenFlower_v3` | SEALED frozen export (D13; PROVED, docs/audits/v2-chain) |
| `Glue.layergarden_of_low` | `hLG : LGLow.LayergardenLowGate` | LG | `theorem`, no binders, levels `[]`, type `Expr.equal` to `const LayergardenLowGate` |
| (body `wtPrefix_of_halves hi lo`) | `hi` | `WaveTurbulence.layergarden_v2` | SEALED frozen export (D10; PROVED, R152) |
| `Glue.fixedpoint_of_low` | `hFL`, `hLG` | FL, LG | theorems |
| | `hG := layergardenFlower_v4_of_low hFL`, `hL := layergarden_of_low hLG` | the glue theorems above | theorem |
| | `hW := WaveTurbulence.wkeTaylor` | sealed `wkeTaylor_v1` | SEALED frozen export (D7; PROVED, audit-b2a) |
| `V2Chain.fixedpointS_of_parts (S := univ)` | `CplMomBody`, `Part2Body` prefixes | `cplMomentsS_of_gates (ofFull hG) (ofFull hL) (ofFull hW) Cpl.oX3Cpl`, `part2S_of_X2 (flowerest1S_of_gates (ofFull hG) X2E.oX2Exp)` | theorems |
| `cplMomentsS_of_gates` | `hC : OX3Cpl` (`= WTPrefix OX3CplBody`, no γ condition) | `Cpl.oX3Cpl` | theorem, no hypotheses |
| `flowerest1S_of_gates` | `hE : OX2Exp` (`= WTPrefixP OX2ExpBody`, no γ condition) | `X2E.oX2Exp` | theorem, no hypotheses |
| `toFull`, `WTPrefixS.ofFull`, `WTPrefixPS.ofFull` | the `γ ∈ S` slot | `Set.mem_univ γ` / discarded | theorems (read line by line) |
| `Glue.propansatz_of_low` → `V2Chain.propansatzS_of_gates (S := univ)` | `hL`, `hF := fixedpoint_of_low hFL hLG`, `hW := wkeTaylor` | glue theorems; sealed `wkeTaylor` | theorems / SEALED |
| `Glue.main_of_low` → `MainGlue.main_of_propansatz_nlsAkBridge` | `hpropansatz : PropansatzGate` | `propansatz_of_low hFL hLG` | theorem |
| | `hnlsAkBridge : NlsAkBridgeGate` | `WaveTurbulence.nlsAkBridge` | SEALED frozen export (D7; PROVED, SEAL-B1-second-key) |
| | `d hd γ hγ` | the anchor's own binders (its value is `fun d hd γ hγ => Provider.main d hd γ hγ`) | — |

`WTPrefixS S Q` (`XChain/V2Chain/PrefixS.lean`) is `WTPrefix Q` with one extra premise `γ ∈ S` after `γ ∈ Ioo 0 1` and
before every existential; `ofFull` discards it and `toFull` supplies `Set.mem_univ γ`, so at `S = univ` nothing can
become vacuous, and a γ > 1/2 use inside the S-generic theorems would have to come from `γ ∈ univ`, which the kernel
would reject. Their signatures carry only `S`. Main's assembly (`XChain/MainAssembly.lean`) has `hγ : γ ∈ Ioo 0 1`
only; θ := η₀²⁰ with η₀ from `hpropansatz d hd γ hγ`, before φin (T L611); the probability bound is
`1 − e^{−(log L)^{40d}} ≤ 1 − e^{−N_𝔇}` via `eventually_final_exponent` (N_𝔇 ≥ (log L)^{40d}). Its lemmas
(`ceiling_subdivision`, `schwartz_lattice_sum_le`, `eventually_final_exponent`, `induction_error_absorption`,
`gate_solvable_measurability`, `ansatz_solvable_probability`, `exists_ansatz_step`, `ansatz_observable_error`,
`hasLaw_stdComplexGaussian`, `NLS.kineticTime_rpow_neg_pos`) take γ only as a parameter (`α = L^(−γ)` or `P.γ`); none
has a γ condition (signatures read). The "three unfrozen glue lemmas" of propansatz's docstring are proved theorems in
the closure: `Induct.solution_norm_sq_le_initial_mass` (mass conservation, T L819), `Induct.initialRapidEvent_ae` /
`measure_initialRapidEvent` (a.s. rapid decay of `initialCoeff`), `Induct.solution_norm_le_one_add_gaussian_mass`
(Gaussian moments of the mass); the base case is `Induct.isASolution_zero_of_rapidDecay`. The witnesses `a, Fev, R, E,
Et` are built inside `propansatzS_of_gates`'s induction over p ≤ 𝔇; no hypothesis supplies them.

### 2.2 FL (`flower_low_closed : Flower.LayergardenFlowerLowGate`)

| theorem | hypothesis | discharged by | kind |
|---|---|---|---|
| `Close.flower_low_closed` | — | `flower_low_of_marked one_le_C₀L one_le_cθL stage1MKGateLow` | `theorem`, no binders |
| `Close.flower_low_of_marked` | `hC₀ : 1 ≤ C₀`, `hcθ : 1 ≤ cθ`, `hI : Stage1MKGateLow C₀ 452 cθ` | `one_le_C₀L`, `one_le_cθL`, `Flower.stage1MKGateLow` (C₀ := `C₀L`, cθ := `cθL`) | theorems |
| `Close.flower_low_of_stage1` | `h5a : Fama.Stage1ReductionGateLow` | `Fama.stage1ReductionGateLow` (L5a) | theorem |
| `Flower.flowerest1_low_of_items5` | `hH2 : WTPrefix fun P => P.γ ≤ 1/2 → FinalCountAtMKLAt P` | `Flower.H2.finalCountAtMKLAt_holds` = `finalCountAtMKLAt_low [MKLowInputs]`, instance `mkLowInputs := ⟨Ghost.chainCoverLowLE'_holds⟩` | theorem; the class input is discharged by a proved instance |
| `flowerest1_low_of_items4` | `h6 : FinalCount.FinalCountGateLow` | `finalCountGateLow_closed` = `finalCountGateLow_of_ghost Ghost.chainCoverLowL'_holds` (inside: `haveI : Src.LowInputs := ⟨hL⟩`) | theorem |
| `flowerest1_low_of_items3` | `hSO : Famc.SubObjectsInput` | `Flower.subObjectsInput` = `TVine.Struct.subObjects_holds` (L3, N2 Thm 1.15) | theorem |
| `flowerest1_low_of_items2` | `hD : CoupleClauseLowInput` | `LGLow.CC.coupleClauseLow_of_three h5a h6 hSO` | theorem |
| `flowerest1_low_of_items` | `hH : FineSplicedGateLowMK` | `fineSplicedGateLowMK_of_count hSO (finalCountGateLowMK_of_L hH2)` | theorem |
| `flowerest1_low_of_parts` | `hN : NonregLowTarget`, `hCouple` | `nonregLowTarget_of hC₀ hcθ hI selSumTargetTG hH`, `hD` | theorems (`selSumTargetTG` closed) |
| budget `C₀L` | `2 ≤ C₀L` | `C₀L := Classical.choose exists_stage1MKGateLow`; `exists_stage1MKGateLow : ∃ C₀, 2 ≤ C₀ ∧ Stage1MKGateLow C₀ 452 cθL := stage1B4Low 452 cθL (markedClassRepresentsMK_prefixLow (le_max_right _ _))` | choice from a PROVED existential (`two_le_C₀L`, `one_le_C₀L`) |
| budget `cθL` | `1 ≤ cθL` | `cθL := max 1 MkSlotsG.cθGen`; `one_le_cθL := le_max_left _ _` | definition + proof |
| budget `cP = 452` | (literal) | consumed by the proved `stage1B4Low 452 cθL` | — |

### 2.3 LG (`layergarden_low_closed : LGLow.LayergardenLowGate`)

| theorem | hypothesis | discharged by | kind |
|---|---|---|---|
| `Close.layergarden_low_closed` | — | `layergarden_low_of_stage1 Fama.stage1ReductionGateLow` | `theorem`, no binders |
| `LGLow.layergarden_low` | `h5a`, `h5c : Famc.CoarseSplicedGateLow`, `h6`, `hSO` | `Fama.stage1ReductionGateLow`, `Famc.coarseSplicedGateLow` (L5c), `Close.finalCountGateLow_proved` (= `finalCountGateLow_of_ghost Ghost.chainCoverLowL'_holds`), `TVine.Struct.subObjects_holds.{0,0}` | theorems |
| `LGLow.layergarden_of_nonregular_on (H := (· ≤ 1/2))` | `hLeaf`, `hTaylor`, `hDecay` | `Spine.leafwise_coherent_approximation`, `Spine.coherent_taylor` (= `PL234.coherentTaylorGate regularAsymptotics leafwise_regular_asymptotics`, SEALED `regularAsymptotics`, D8), `Spine.leafwise_incoherent_decay` | theorems; the gates are `WTPrefix` statements without γ condition |
| `LGLow.nonregular_prefix_low` | `hladder : LadderFourierGate`, `hfine : FineSplicedGammaInput` | `Spine.ladder_fourier`; `fineSplicedGammaInput_of_subObjects hSO` (L07 F1; L5c's `Famc.fineSplicedChoicesGamma`, all 0 < γ < 1) | theorems |
| | budget `C₀ : ℕ → ℝ → ℕ`, `hC₀` | destructured from the proved `Stage1ReductionGateLow`; `6 * C₀ d γ`, side condition by `omega` | from a proved existential |

L07's FINDINGS F1–F3 (`world/src/…/GammaLow/Glue/FINDINGS.md`) read: F1 the fourth LG input `FineSplicedGammaInput`
(now discharged as above), F2 `layergarden_of_nonregular_on` = main's γ-restricted `layergarden_v2_of_nonregular_half`
made generic in `H`, F3 the family-free waist `TypeGateAt` (`LGLow/COPIED-SHA256SUMS` lists each copied declaration of
main with its sha256 and fail-closed replacements "gate bundle → `TypeGateAt`"). Whatever the copies say, their proofs
are in the replayed closure.

### 2.4 Mechanical cross-checks (`replay/reach-dump.tsv` → `dag-spine.txt`, `dag-gates.txt`)
- Every theorem in §§2.1–2.3 is a reachable `theorem`; every gate-like hypothesis on the spine (`Stage1MKGateLow`,
  `Stage1ReductionGateLow`, `FinalCountGateLow`, `SubObjectsInput`, `CoupleClauseLowInput`, `FineSplicedGateLowMK`,
  `NonregLowTarget`, `SelSumTargetTG`, `ChainCoverLowL'`, `FineSplicedGammaInput`, the four spine gates) has a reachable
  discharger whose conclusion head is that gate and which has no gate-like hypothesis itself.
- Over the whole union (210,824 reachable theorems), 159 distinct gate-like hypothesis heads occur; 48 are the
  conclusion head of no reachable theorem. I inspected them: parameterised structures/predicates carried as data
  (`HyperLikeRealization`, `GateEnv`, `PieceHyp`, `LFHyps`, …) or named inputs supplied at their use sites by proved
  terms (`chartSupply_of_input tvineChartInput`, `… TVine.Chart.tvineChart_holds`; the classes `Src.LowInputs`,
  `MKLowInputs` by `⟨chainCoverLowL'_holds⟩`, `⟨chainCoverLowLE'_holds⟩`; `RegularAsymptoticsGate` by the sealed
  `regularAsymptotics`).
- Conclusive: FL and LG are closed (`theorem`, levels `[]`, type `Expr.equal` to the gate constant, so no binder and no
  `variable`/`include` hypothesis), and their closures contain no axiom other than the standard three and no `sorryAx`
  (§1.4); the kernel accepted their whole proof terms (§1.3). So no hypothesis of any conditional theorem in their
  chains is left open and none is discharged by an axiom, opaque constant or local hypothesis.

### 2.5 The halves (`Glue/Halves.lean`, read line by line)
`wtPrefix_of_halves {Q} (hi : WTPrefix fun P => 1/2 < P.γ → Q P) (lo : WTPrefix fun P => P.γ ≤ 1/2 → Q P) : WTPrefix Q`:
`intro d hd γ hγ; by_cases h : 1 / 2 < γ`. The split is on the already-fixed γ (third quantifier), BEFORE every
existential, so no witnesses are combined: in each branch η₀, C₁, ν₀, δ₀, C₂, L₀ (and P₀ in `wtPrefixP_of_halves`) are
exactly the chosen half's, with that half's proofs of `0 < η₀`, `1 ≤ C₁`, `0 < ν₀`, `0 < δ₀`, `1 ≤ C₂`, `2 ≤ L₀`; the
universal ranges are the prefix's own, unchanged (non-empty, §(h)). The last step feeds the half's body `h` (`1/2 < γ`)
or `le_of_not_gt h : γ ≤ 1/2`. Exhaustive; **γ = 1/2 falls in the low branch** (`¬ (1/2 < 1/2)`), and the low half's
premise is the non-strict `P.γ ≤ 1/2` in both gates (each gate value is `isDefEq` to "the anchor body with exactly
`P.γ ≤ 1/2 →` inserted"; the only syntactic difference is the gate's abstracted `_proof_n` auxiliaries, proof terms;
`exact2` probe). Neither half assumes γ < 1/2 strictly: FL and LG prove the gates as stated. (Copy record
`Glue/COPIED-SHA256SUMS`: lines 14–61 of the audited `gamma-half-scope/drafts/HalvesGlue.lean`, sha256 `5c4f759a…`,
namespace renamed, `toFull`/`toFullP` added.)

### 2.6 AUDIT-V4 §7 watch items at γ = 1/2
The tree has 28 declarations with `h8 : 8η ≤ 2γ − 1` (false for γ ≤ 1/2) or `hmarg : 2·min γ (1−γ) + 4η² ≤ 1` (false at
γ = 1/2) (`h8-decls.txt`: main's `FinalCountAsm.chain_cover`, `node2_facts`, `phase2_cover`, …, `Flower.FinalMKStep.hW_RCp`,
`hW_RC'p`, `hmarg_of_h8`, …, and eight `GammaLow.FinalCount.H.*` copies). Reach-only run from FL and from LG alone:
**`WATCH flower_low_closed: of 28 watch-list names, reached: []`; `WATCH layergarden_low_closed: … reached: []`.** In
the union, 17 of them are reachable, all through the sealed γ > 1/2 halves (`layergardenFlower_v3`, `layergarden_v2`),
where `h8`/`hmarg` hold; the eight `GammaLow.FinalCount.H.*` copies are not reachable at all. Their γ ≤ 1/2
replacements are proved: the root-only chain covers `Ghost.chainCoverLowL'_holds`, `Ghost.chainCoverLowLE'_holds`
(R194), through `finalCountGateLow_of_ghost` and `mkLowInputs`.

### 2.7 Non-vacuity, including γ ≤ 1/2 and γ = 1/2
Prefix: every prover choice is followed by a non-empty range (§(h) shared rows); γ ∈ {1/4, 1/2} are admissible and go to
the low half. `IsWKESolution φin τ★ φ` is inhabited for every Schwartz φin and every τ★ ∈ (0, τmax) by the sealed
`wkelwp` (`∃ τmax > 0, ∀ τ★ > 0, (τ★ < τmax ↔ ∃ φ, IsWKESolution φin τ★ φ) ∧ …`); `IsGaussianData μ g` is inhabited by
the product of `stdComplexGaussian` over `Fin d → ℤ` with g the coordinates. `RemainderBound P R p` is satisfiable: its
body `∀ q ≤ p, SNormR Λ_q Λ_q (R q) ≤ L^{−θ_q}` is verbatim the first conjunct of `AnsatzAt` (2) at each q, which the
sealed `propansatz` (this batch, full range) provides for all q ≤ 𝔇. The per-anchor premises are treated in §§3–6.

## 3. `layergardenFlower_v4` (export `WaveTurbulence.layergardenFlower_v4`)

| item | verdict | evidence |
|---|---|---|
| (a) | **PASS** | Since the freeze `eae9b6b3` the file changed only in `4558dd65` (`git log --follow`); pre-seal file sha256 `f29eed81f6b7472d…` (= brief's DRAFT); body `  by sorry` → `  by exact WaveTurbulence.Provider.layergardenFlower_v4` (1 line, 56 B); my prefix `4af98d83…` / suffix `9f481990…` = manifest; manifest entry freeze → final differs in exactly `state` (DRAFT_SORRY → SEALED, `4558dd65`) and `abi_sha256` (`585a8d7c…` → `e1a20b63…`, `88e4495a`, its only diff line); `definition_closure` 107/107 hashes match; seal commit = 5 paths (anchor, provider, lakefile: the v4 pair leaves the quarantine, root `+public import …LayergardenFlowerV4`, manifest state); guard OK. |
| (b) | **PASS** | No self-import: provider source imports are 16 public (the anchor's 15 Defs + Mathlib, equal sets) and 2 private (`GammaLow.Glue.Flower`, `GammaLow.Close.Final`); Lake's resolved closure of the provider (22,805 modules) does not contain the anchor module. Statement text byte-identical (1,426 B, `open Classical in` on both). Body exactly `GammaLow.Glue.layergardenFlower_v4_of_low GammaLow.Close.flower_low_closed`. Used only by the anchor (only importer; export name only in anchor and provider). Private imports: Lake's anchor closure = 9,139 modules, 108 WaveTurbulence, 0 Foundations/GammaLow; module probe importing only the anchor: 109 WaveTurbulence modules, 0 Foundations, 0 `GammaLow` constants; glue, FL, LG, gates, `WTPrefixS`, main's assembly invisible; provider export visible. Provider type `==` and `Expr.equal` to the anchor type, pp.all text equal (29,837 chars); `inferType` of the provider body `==`, `Expr.equal`, `isDefEq` and pp.all-equal to the anchor type; exact-type check `example : <frozen text> := WaveTurbulence.layergardenFlower_v4` and composition witness `example : <same> := Glue.layergardenFlower_v4_of_low FL` elaborate. Decidable instances of `if ∀ j, pat j = .plain`: 2, identical in anchor, provider, glue conclusion and gate body (`@Nat.decidableForallFin (2*Pm) (fun j => pat j = plain) (fun a => instDecidableEqFixPat …)`; N3). |
| (c) | **PASS** | `#print axioms` = `[propext, Classical.choice, Quot.sound]` for the anchor, the provider, the glue, FL, `layergardenFlower_v3` (and for the other 17 declarations of the batch). Independent: §1.3–1.4. |
| (d) | **PASS** | §2: glue = `wtPrefixP_of_halves layergardenFlower_v3 hFL`; FL closed and every named input discharged (§2.2, §2.4); halves exhaustive, γ = 1/2 low (§2.5); watch items absent from FL's closure (§2.6). Non-vacuity at γ ≤ 1/2 and γ = 1/2: p = 0 < 𝔇 (𝔇 ≥ 1); R with `RemainderBound P R 0` (§2.7); t = 1/2 ∈ (0,1), s = 1/4 ∈ (0,t); N = 0; every `FlowerKind`, every pattern vector, `dagger = none`/`some`, `cut1 = cut2 = none` (cut premise vacuous), and `cut1 = some j₁, cut2 = some j₂` with n chosen so that ‖n/L‖ ≥ (2^{j₁}L)^{10} (ℤ^d is unbounded); couples: t = 1/2, any k, N = 0, kind ℒ₀ with dt either value, kind a^tr with dt = true. |
| (e) | **PASS** | Pre-seal `585a8d7c0aeb65d744a34f5565cb4e627b349a7705384c6c3c40c42e23fa0a7e` reproduced from my own rebuild of the pre-seal provider stub and DRAFT anchor (`git show <seal>^:…`), = manifest DRAFT ABI; for this anchor the non-module `import M` form gives byte-identical output; post-seal `e1a20b63605ff3c7637ad6010925f192254e2a620e7f3bb1295767ca925e7beb` from main's build, = manifest = the brief's dry-run value. The two `#print` outputs differ only in line 34: `sorry` → `WaveTurbulence.Provider.layergardenFlower_v4`. The anchor's type in my DRAFT olean and in main's sealed olean is `Expr.equal` (all binder names included), so the private imports caused no elaboration drift (§7.1). |
| (f) | **PASS** | §1.3 (union replay; this anchor's closure is 231,905 project constants, §1.4); trace check §1.5. |
| (g) | **PASS** | §8. |
| (h) | **PASS** | Table in §9 (SOURCE 9, STANDING 13, TYPING 6, RULED 8, **EXCESS 0**); no γ restriction beyond `γ ∈ Ioo 0 1`; v3's `1 / 2 < P.γ` absent (Expr-level: glue conclusion = anchor type). |

## 4. `layergarden_v1` (export `WaveTurbulence.layergarden`)

| item | verdict | evidence |
|---|---|---|
| (a) | **PASS** (N1) | File history: `f2d1fb6b` (freeze), `2e2c16ef` (seal) only; pre-seal sha256 `f4d379a9338e688f…` (= brief); body → `by exact WaveTurbulence.Provider.layergarden` (1 line, 47 B); prefix `150a9eb3…`, suffix `9f481990…` = manifest; manifest: `author_approval.approved_at` `PENDING-D7` → `2026-11-04` at the D7 approval landing `cff26541` (N1), then exactly `state` (`2e2c16ef`) and `abi_sha256` `ae0ce366…` → `92b0b3e8…` (`a89b5012`, one line); closure 101/101; seal commit 5 paths (pair leaves quarantine; one root import); guard OK. |
| (b) | **PASS** | No self-import (source; Lake closure 21,660 modules without the anchor); public imports = the anchor's 14 Defs + Mathlib; private only `Glue.Layergarden`, `Close.Halves` (LG only). Statement byte-identical (863 B). Body exactly `Glue.layergarden_of_low GammaLow.Close.layergarden_low_closed`. Only importer: the anchor. Lake's anchor closure: 9,133 modules, 102 WaveTurbulence, 0 Foundations/GammaLow; union module probe: 0 GammaLow constants. Provider type `==`/`Expr.equal`/pp.all-equal (15,675 chars); body type `==`, `Expr.equal`, `isDefEq`; exact-type check and composition witness elaborate. |
| (c) | **PASS** | anchor, provider, glue, LG, `layergarden_v2`: standard three. |
| (d) | **PASS** | §2: glue = `wtPrefix_of_halves layergarden_v2 hLG`; LG closed, inputs discharged (§2.3–2.4); main's four spine gates proved, all γ; halves §2.5; watch items absent from LG's closure. Non-vacuity at γ ≤ 1/2: p = 0; `RemainderBound P R 0` (§2.7); t = 1 ∈ (0, 1]; N = 0; the m-range 2 ≤ m ≤ 10R₁ is non-empty for large L (R_𝔇 = ⌊(log L)^{40d}⌋ ≥ 1 for L ≥ e, R_{p−1} = N_p^{40d} ≥ 1); balanced ζ = (1,…,1,−1,…,−1); (2)(a) with n 0 ≠ n 1. |
| (e) | **PASS** | Pre-seal `ae0ce36636b12aa0b8952e3c4dfd31eb79cd35af4754d7717a1a3c7eea180140` reproduced from my own rebuild of the pre-seal provider stub and DRAFT anchor (`git show <seal>^:…`), = manifest DRAFT ABI; post-seal `92b0b3e853d27ce9620781008f2421fbbdbc727b8ca61b739843af1737873b42` from main's build, = manifest = the brief's dry-run value. The two `#print` outputs differ only in line 21: `sorry` → `WaveTurbulence.Provider.layergarden`. The anchor's type in my DRAFT olean and in main's sealed olean is `Expr.equal` (all binder names included), so the private imports caused no elaboration drift (§7.1). |
| (f) | **PASS** | §1.3–1.5 (215,273 project constants). |
| (g) | **PASS** | §8. |
| (h) | **PASS** | §9: SOURCE 5, STANDING 13, TYPING 5, RULED 3, **EXCESS 0**. |

## 5. `fixedpoint_v1` (export `WaveTurbulence.fixedpoint`)

| item | verdict | evidence |
|---|---|---|
| (a) | **PASS** (N1) | History `f2d1fb6b`, `008e27f9` only; pre-seal sha256 `05f2f20885e5b1b0…` (= brief); body → `by exact WaveTurbulence.Provider.fixedpoint` (46 B); prefix `9033444b…`, suffix `9f481990…` = manifest; manifest: approval fill (N1), `state` (`008e27f9`), `abi_sha256` `4fafe6c0…` → `bcfe4a35…` (`e5c86a37`, one line); closure 114/114; seal commit 5 paths; guard OK. |
| (b) | **PASS** | No self-import; public imports = 14 Defs + Mathlib; private `Glue.Fixedpoint`, `Close.Final`, `Close.Halves`. Statement byte-identical (2,412 B, including the four `let`s). Body exactly `Glue.fixedpoint_of_low FL LG`. Only importer: the anchor. Lake's anchor closure 9,146 modules, 115 WaveTurbulence, 0 GammaLow. Provider type `==` anchor type (so the four `let`s are `letE` nodes in both, no `let`/`have` or zeta difference), pp.all equal (146,304 chars), `isDefEq`; `Expr.equal` false only on two binder NAMES: the hygienic names of the anonymous instance binders `[MeasurableSpace Ω]`, `[IsProbabilityMeasure μ]` (`inst._@.WaveTurbulence.Provider.Fixedpoint…_hyg.9/.14` vs `inst._@.WaveTurbulence.Frozen.Theorems.Fixedpoint…_hyg.9/.14`; binder info `instImplicit` on both); same for the body type (`…Glue.Fixedpoint…_hyg.11/.16`). Levels `[u]`/`[u]`; `example : type_of% @WaveTurbulence.fixedpoint.{u} = type_of% @WaveTurbulence.Provider.fixedpoint.{u} := rfl` elaborates; exact-type check and composition witness elaborate. |
| (c) | **PASS** | anchor, provider, glue, FL, LG, `wkeTaylor`, `layergardenFlower_v3`, `layergarden_v2`: standard three. |
| (d) | **PASS** | §2.1: `toFull (fixedpointS_of_parts (S := univ) …)` with `hG`, `hL` from FL/LG and `hW := wkeTaylor`; `Cpl.oX3Cpl`, `X2E.oX2Exp` closed, their statements `WTPrefix`/`WTPrefixP` without γ condition; at S = univ, `WTPrefixS`/`ofFull`/`toFull` only thread `γ ∈ univ`. Non-vacuity: `IsGaussianData` inhabited (§2.7); for p < 𝔇 the hypothesis `∀ q ≤ p, AnsatzAt … q` is satisfied by the data the sealed `propansatz` produces (for every γ ∈ (0,1), including γ ≤ 1/2 and 1/2), at parameters admissible for both prefixes (take the smaller thresholds); T L708's p = 0 case is the trivial base (ℛ₀ = ℰ₀ = 0). |
| (e) | **PASS** | Pre-seal `4fafe6c0092a7ad991c1d32442cc62231e774edfb5e5d3aa48501f8de47fffaf` reproduced from my own rebuild of the pre-seal provider stub and DRAFT anchor (`git show <seal>^:…`), = manifest DRAFT ABI; post-seal `bcfe4a35a9ef74f10abb380c4a9aab4e5417359cc693c9fa7a832fd6c4d16780` from main's build, = manifest = the brief's dry-run value. The two `#print` outputs differ only in line 50: `sorry` → `WaveTurbulence.Provider.fixedpoint`. The anchor's type in my DRAFT olean and in main's sealed olean is `Expr.equal` (all binder names included), so the private imports caused no elaboration drift (§7.1). |
| (f) | **PASS** | §1.3–1.5 (236,682 project constants). |
| (g) | **PASS** | §8. |
| (h) | **PASS** | §9: hypothesis side SOURCE 3, STANDING 13, TYPING 9, RULED 0; conclusion SOURCE with D7 deviations; **EXCESS 0**. |

## 6. `propansatz_v1` and `main_v1`

### 6.1 `propansatz_v1` (export `WaveTurbulence.propansatz`)

| item | verdict | evidence |
|---|---|---|
| (a) | **PASS** (N1) | History `f2d1fb6b`, `6f4a03d2` only; pre-seal sha256 `e5a1975da30db2ba…` (= brief); body → `by exact WaveTurbulence.Provider.propansatz` (46 B); prefix `f30b2873…`, suffix `9f481990…` = manifest; manifest: approval fill (N1), `state` (`6f4a03d2`), `abi_sha256` `4db839d1…` → `1e9629b5…` (`09c867a6`, one line); closure 100/100; seal commit 5 paths; guard OK. |
| (b) | **PASS** | No self-import; public = 5 Defs + Mathlib; private `Glue.Propansatz`, `Close.Final`, `Close.Halves`. Statement byte-identical (512 B). Body exactly `Glue.propansatz_of_low FL LG`. Only importer: the anchor. Lake's anchor closure 9,132 modules, 101 WaveTurbulence, 0 GammaLow. Types `==`, pp.all equal (2,507 chars), `isDefEq`; `Expr.equal` false only on the two hygienic instance-binder names (as for fixedpoint). Universe rfl check elaborates (levels `[u]`/`[u]`); exact-type check and composition witness elaborate. |
| (c) | **PASS** | standard three for anchor, provider, glue, FL, LG, `wkeTaylor`. |
| (d) | **PASS** | §2.1: `toFull (propansatzS_of_gates (S := univ) (ofFull hL) (ofFull hF) (ofFull hW))`; its unconditional inputs (mass conservation, a.s. decay of `initialCoeff`, Gaussian moments, base case) are proved theorems taking γ as a parameter; witnesses built, not assumed. Non-vacuity: the conclusion is existential; `AnsatzAt` (sealed, read in full, §9) contains (1)–(4) of T L690–L706 with the §4.1 deviations (D1)–(D7) and the observation N5. |
| (e) | **PASS** | Pre-seal `4db839d1ef1a3deef8566363da7a853aa3cd55ba45cc1d1660f13cca65fa6748` reproduced from my own rebuild of the pre-seal provider stub and DRAFT anchor (`git show <seal>^:…`), = manifest DRAFT ABI; post-seal `1e9629b501a5d4517e0e1d56612367bf7328632ecc0f38b1bf9151dbab8b431e` from main's build, = manifest = the brief's dry-run value. The two `#print` outputs differ only in line 5: `sorry` → `WaveTurbulence.Provider.propansatz`. The anchor's type in my DRAFT olean and in main's sealed olean is `Expr.equal` (all binder names included), so the private imports caused no elaboration drift (§7.1). |
| (f) | **PASS** | §1.3–1.5 (237,286 project constants). |
| (g) | **PASS** | §8. |
| (h) | **PASS** | §9: SOURCE 4, STANDING 13, TYPING 8, RULED (inside `AnsatzAt`), **EXCESS 0**. |

### 6.2 `main_v1` (export `WaveTurbulence.main`)

| item | verdict | evidence |
|---|---|---|
| (a) | **PASS** | History `8d1d2e3b` (freeze), `bfbb5546` only; pre-seal sha256 `4a200b77adfaf861…` (= brief); body → `by exact WaveTurbulence.Provider.main` (40 B); prefix `fdb8acf3…`, suffix `9f481990…` = manifest; manifest freeze → final: exactly `state` (`bfbb5546`) and `abi_sha256` `05d07e58…` → `b83d1394…` (`a25673fd`, one line); closure 12/12; seal commit 5 paths; guard OK. |
| (b) | **PASS** | (1) conclusion text byte-identical (1,119 B). (2) binder table: `d` default → implicit; `hd : 3 ≤ d` → `autoParam (3 ≤ d) Provider.main._auto_1`, binder info default, unwrapped type `==`; `γ` default → implicit; `hγ : γ ∈ Ioo 0 1` → `autoParam (…) Provider.main._auto_3`, unwrapped `==` — exactly the four adaptations, names and order equal. (3) conclusions after the four binders: `==`, pp.all equal, `isDefEq`; `Expr.equal` false only on the two hygienic instance-binder names (`…Provider.Main…_hyg.219/.224` vs `…Frozen.Theorems.Main…_hyg.213/.218`). (4) `example : type_of% @WaveTurbulence.main.{u} := fun d hd γ hγ => @WaveTurbulence.Provider.main.{u} d hd γ hγ` elaborates, as do `example (d) (hd) (γ) (hγ) : <frozen conclusion> := WaveTurbulence.Provider.main` (auto-params from context) and the composition witness `… := Glue.main_of_low FL LG d hd γ hγ`. (5) The anchor's value (kernel data, replay EXACT line) is `fun d hd γ hγ => WaveTurbulence.Provider.main.{u} d hd γ hγ`: the auto-params are the anchor's own `hd`, `hγ`. Glue conclusion after `hFL`, `hLG` `==` the anchor type. No self-import; public = 12 Defs + Mathlib; private `Glue.Main`, `Close.Final`, `Close.Halves`; only importer the anchor; Lake's anchor closure 9,044 modules, 13 WaveTurbulence, 0 GammaLow. |
| (c) | **PASS** | standard three for anchor, provider, glue, FL, LG, `main_of_propansatz_nlsAkBridge`, `nlsAkBridge`. |
| (d) | **PASS** | §2.1: `MainGlue.main_of_propansatz_nlsAkBridge (propansatz_of_low hFL hLG) nlsAkBridge d hd γ hγ`, γ-generic, θ = η₀²⁰ before φin, probability via N_𝔇 ≥ (log L)^{40d}; its ten lemmas proved, γ as parameter only. Meaning/non-vacuity (D6), for γ ≤ 1/2 too: 1 − e^{−(log L)^{40d}} > 0 for L > 1, so the solvable event is non-null; the U-premise is satisfiable (choose a solution on the event, which `solvableEvent` defines by existence; `nlsAkBridge` (4) also gives a measurable selection); `IsWKESolution` inhabited by `wkelwp` for every Schwartz φin and small τ★; α = L^{−γ}, T = τ★·kineticTime α are definitional. |
| (e) | **PASS** | Pre-seal `05d07e58bd43f9f500570d2d4993deec5442d73225ca0f6536ba2ba20c3e7f2c` reproduced from my own rebuild of the pre-seal provider stub and DRAFT anchor (`git show <seal>^:…`), = manifest DRAFT ABI; post-seal `b83d1394ae7b902677b6fbd70ae839d0ef59cd5e71c395558b16be4169c729fc` from main's build, = manifest = the brief's dry-run value. The two `#print` outputs differ only in line 37: `fun d hd γ hγ => sorry` → `fun d hd γ hγ => WaveTurbulence.Provider.main hd hγ`. The anchor's type in my DRAFT olean and in main's sealed olean is `Expr.equal` (all binder names included), so the private imports caused no elaboration drift (§7.1). |
| (f) | **PASS** | §1.3–1.5 (237,577 project constants). |
| (g) | **PASS** | §8. |
| (h) | **PASS** | §9: SOURCE 11, STANDING 0, TYPING 5, RULED 3, **EXCESS 0**; the only γ condition is `γ ∈ Ioo 0 1` (main_v2's `Ioo (1/2) 1` is gone). |

## 7. Item (e) details, notes and disagreements

### 7.1 Item (e) — ABI before and after the seal
Method (`tools/abi.py`, `tools/run_abi.sh`; outputs `probes/run_abi.out`, `probes/abi_*`, `probes/cmp.out`):
- **Post-seal**: the probe `module` / `import all <anchor module>` / `#print <export>` (the setup form of
  `scripts/abi_hash_setup.py`), with Lake's own `.setup.json` of the anchor plus the anchor's artifacts and the private
  parts of every project module; sha256 of stdout.
- **Pre-seal**: in `draft/<id>/` I wrote the pre-seal provider stub and the pre-seal anchor (`git show <seal>^:<path>`;
  sha256 prefixes `18401a93…`/`f29eed81…`, `06746762…`/`f4d379a9…`, `7982203b…`/`05f2f208…`, `391626b6…`/`e5a1975d…`,
  `3415a630…`/`4a200b77…` — the anchors equal the briefs' DRAFT hashes), compiled the stub against the anchor's own Lake
  import data minus the provider (the stub's public imports equal the sealed provider's, (b)), then the anchor
  (`warning: declaration uses 'sorry'` only), and ran the same probe against those artifacts. For v4 I also ran the
  non-module form (`import M` / `#print E`, the documented convention of `scripts/abi_hash.py`): byte-identical output,
  so the two conventions agree. (On the sealed anchors the non-module form cannot run: a non-module import follows the
  provider's private imports, ≈ 23.6k modules × 3 parts, beyond `vm.max_map_count` — the fallback condition of
  `abi_hash.py`.)
- **Type identity before/after**: my replay executable's `cmp` mode reads both oleans (all three parts) and compares
  the anchor constant: for all five, kinds theorem/theorem, levels equal, type `==` **and `Expr.equal`**; pre value
  `sorryAx …` (main: `fun d hd γ hγ => sorryAx …`), post value the provider constant (main: `fun d hd γ hγ =>
  Provider.main d hd γ hγ`). This is stronger than pp.all text equality.

| anchor | pre-seal (rebuilt) | = manifest DRAFT | post-seal | = manifest | `#print` diff | type pre vs post |
|---|---|---|---|---|---|---|
| `layergardenFlower_v4` | `585a8d7c0aeb65d7…` | yes | `e1a20b63605ff3c7…` | yes | line 34 only (value) | `Expr.equal` |
| `layergarden_v1` | `ae0ce36636b12aa0…` | yes | `92b0b3e853d27ce9…` | yes | line 21 only | `Expr.equal` |
| `fixedpoint_v1` | `4fafe6c0092a7ad9…` | yes | `bcfe4a35a9ef74f1…` | yes | line 50 only | `Expr.equal` |
| `propansatz_v1` | `4db839d1ef1a3dee…` | yes | `1e9629b501a5d451…` | yes | line 5 only | `Expr.equal` |
| `main_v1` | `05d07e58bd43f9f5…` | yes | `b83d1394ae7b9026…` | yes | line 37 only | `Expr.equal` |

### 7.2 Notes N1–N5 (none blocking)
- **N1 (a), D7 anchors.** At the freeze commit `f2d1fb6b` the manifest had `approved_at: "PENDING-D7"`; the landing
  `cff26541` ("Land w/freeze-b1 …; approved_at filled; D7 recorded") set `2026-11-04`. So, measured from `f2d1fb6b`, the
  entries of `layergarden_v1`, `fixedpoint_v1`, `propansatz_v1` differ in `author_approval` as well as `state`,
  `abi_sha256`; measured from the landed freeze (and from the seal's parent), exactly `state` and `abi_sha256`. The
  frozen bytes, prefix/suffix hashes and closures never changed. Not a seal change.
- **N2 (c)/(d).** `regularAsymptotics` (SEALED, D8) is reached by all five anchors and by FL and LG
  (`Spine.coherent_taylor`); the briefs' "consumed sealed anchors" omit it. Its proof is inside the replayed closure.
- **N3 (b), v4.** Despite `open Classical in`, the elaborated Decidable instance of `if ∀ j, pat j = .plain` is the
  constructive `Nat.decidableForallFin … (fun a => instDecidableEqFixPat (pat a) .plain)` (the frozen
  `Defs.InstDecidableEqFixPat` is imported), identical in anchor, provider, glue conclusion and gate body; the private
  imports add no instance that changes it (Expr equality, and §7.1: the anchor type is `Expr.equal` before and after the seal).
- **N4 (g).** README's status block at `5c19b015` is stale ("DRAFT_ANCHORS: 7", "SEALED: 21 theorems", "frozen
  theorems sealed: 21 / 28", "Theorem 1.1 is formally proved for 1/2 < γ < 1"); the manifest has 2 DRAFT and 26 SEALED
  theorems. Documentation only (PROVED is recorded after the audits).
- **N5 (h), `AnsatzAt`.** Items (3)–(4) quantify over signatures with Σζ = 0 only; for other signatures the source's
  cumulant vanishes by the gauge symmetry of 𝔉_p (T L798), which (1) keeps. The definition is sealed and D7-approved;
  not EXCESS (it is in a conclusion of propansatz and a hypothesis of fixedpoint).

### 7.3 Differences with the briefs and claim appendices
- Brief main (b)(3) expects the conclusions to be `Expr`-equal "hygienic instance-binder names aside": confirmed in
  exactly that form (two names). The same two-name difference holds for fixedpoint and propansatz, whose briefs do not
  mention it (AUDIT-COMMON (b) allows "up to hygienic binder names").
- Brief fixedpoint/propansatz (b) expect `Expr`-equality up to binder names and `rfl` at `.{u}`: confirmed.
- Claim appendices (h): no EXCESS on either side; the differences are granularity and bins: v4 — I bin `∃ δ₀` STANDING
  (appendix SOURCE), `n n'` and the couple `k` TYPING (appendix SOURCE), the couple `t ∈ Ioo` RULED (D10; appendix SOURCE);
  my rows split `RemainderBound` from `R`; counts 9/13/6/8 vs 13/11/4/7. layergarden — appendix bins `IsBalancedSig ζ`
  SOURCE (I: RULED, D7 balanced-signature convention) and `n` SOURCE (I: TYPING); fixedpoint/propansatz — appendix uses
  one STANDING bundle, I expand `WTPrefix` into 16 rows; main — appendix bins `IsWKESolution` and the ∀U selection SOURCE
  (I: RULED D6), `d`, `γ` SOURCE (I: TYPING, with `hd`, `hγ` SOURCE).
- Briefs' (d) FL chain "at prep time `flowerest1_low_of_items4 … h6 …`": the landed route is `items5` with `h6`
  discharged inside by `finalCountGateLow_closed` (same theorem as `Close.finalCountGateLow_proved`).

### 7.4 Comparison with the seal logs and seal-prep HANDOFF (read after my results)
Read only after §§1–9 were written: `seal/logs/live-20261109T221649Z/run.log` (155 lines) and `seal/HANDOFF.md`.
- Agreement: START `d0961baf`; inputs `--fl …flower_low_closed@…Close.Final --lg …layergarden_low_closed@…Close.Halves`;
  per anchor "SEAL-PROBE INPUT OK … closed theorem, no binders", "SEAL-PROBE EXACT OK … (Expr ==, defeq)", axioms
  `[propext, Classical.choice, Quot.sound]`, pre-seal ABI controls and post-seal ABIs equal to mine (all ten hashes),
  "PRINT DIFF OK" with the same value lines, guard/land check OK, `abi_all: 328/328 OK`; push of the local commits was
  rejected as non-fast-forward (HQ auto-updates on origin) and `5c19b015` (merge) was pushed — matches §0.
- Measurement difference (not substantive): the log's pp.all lengths are 29,837 / 15,675 / 146,326 / 2,527 chars for
  v4 / layergarden / fixedpoint / propansatz; mine are 29,837 / 15,675 / 146,304 / 2,507. The two differing anchors are
  exactly those with the two hygienic instance binders, whose rendering depends on printer options; both runs find the
  provider and anchor texts equal.
- Disagreement (wording): the log's RECHECK says, for the D7 anchors, "frozen diff vs freeze f2d1fb6b = body only;
  manifest fields ['abi_sha256', 'state']". Against the manifest of `f2d1fb6b` the entries also differ in
  `author_approval.approved_at` (N1); the RECHECK evidently compares with the manifest at START. No consequence.
- HANDOFF §2 lists `RegularAsymptotics` among the sealed anchors the glue reaches (consistent with N2); §6.1 describes
  the then-open input route (`items4`, items I/H2 open), superseded by the closed `flower_low_closed` (§2.2).

### 7.5 Deviations from the procedure
- Directory: one directory `seal-audit-ALL-B/` for the five anchors (KEY-B-ALL is one session for all five); the report
  is this file (KEY-B-ALL replaces the per-anchor `SEAL-AUDIT.md`), and the status line goes to `status/KEY-B.txt`.
- Replay: quick mode (40,618 VineParam-internal theorem proofs checked by statement only, as in the v2-chain keys). My
  replay ran at the same time as the other key's replay (independent sessions); my own heavy processes ran one at a time.
- After the replay I added a reach-only mode to `Replay.lean` (no kernel step) for the FL/LG census; the replay itself
  used the build of `Replay.replayed.lean` (sha256 `82f441b9…`).
- Visibility probes are `module` files (the frozen statement elaborates as a module): a non-module import of an anchor
  follows the provider's private imports beyond Lake's anchor closure, so it does not model the freeze environment. I
  ran one module probe per the v4 anchor and one for the union of the five, plus Lake's per-anchor setup data.
- Post-seal ABI: only the setup form (`module` / `import all M`) can run on the sealed anchors (a non-module import
  of a sealed anchor pulls the provider's private closure, ≈ 23.6k modules × 3 parts, beyond `vm.max_map_count` — the
  documented fallback condition of `scripts/abi_hash.py`); on the DRAFT build I ran both forms for v4 (§7.1).
- Transient probe sources were deleted after recording (generators `tools/gen_probes.py`, `tools/abi.py` kept;
  outputs in `probes/out_*`, `probes/abi_*`).

## 8. Item (g) — status fields (all five; `tools/item_g.py` on `export-main`, independent of the guard)
- **DRAFT_ANCHORS: 2** — `layergardenFlower_v1` (`WaveTurbulence/Frozen/Theorems/LayergardenFlower.lean`, provider
  `WaveTurbulence.Provider.LayergardenFlower`), `layergardenFlower_v2` (`…/LayergardenFlowerV2.lean`,
  `WaveTurbulence.Provider.LayergardenFlowerV2`); max-form, E34; open by D13/D16.
- **UNREGISTERED_SORRIES: 0** (own lexer: comments and strings masked; `sorry`/`admit`/`sorryAx` tokens outside the two
  DRAFT bodies: none; control: the two DRAFT bodies' `sorry` are detected). No `axiom`/`opaque`/`unsafe` declaration in
  the tree.
- **DRAFT_IMPORT_VIOLATIONS: 0** (no module other than its anchor imports a DRAFT anchor or its provider). The lakefile
  quarantine is exactly the two DRAFT anchors and their providers; none of the five sealed modules is quarantined; the
  root imports the five anchors and no provider.
- **SEALED_THIS_TURN:** `layergardenFlower_v4`, `layergarden_v1`, `fixedpoint_v1`, `propansatz_v1`, `main_v1` (manifest
  state SEALED; 26 theorem anchors SEALED, 300 definitions SEALED). README stale (N4).

## 9. Item (h) — five-bin binder tables (verbatim from `h-tables.md`, written before the claim appendices)

Written 2026-11-09 ~23:10 UTC. TeX: `<sources>/paper/source/WKE-Longer_times_Final_arXiv.tex`,
re-hashed `493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb` (= pinned). Rulings read: D6, D7, D10,
D11, D13, D16 (docs/DECISIONS.md), E1, E34 (docs/ERRATA-AND-DEVIATIONS.md), R190, R192 (orchestrator RULINGS.md),
WAVE-B §1.2, §4.1–§4.3, §4.15 (docs/blueprint/WAVE-B.md) and WAVE-B-B1 §2 (docs/review/WAVE-B-B1.md).
Disclosure: the v4 brief's claim appendix was displayed to me when I first read that brief (it is not separated from
the brief text); I read the other four appendices only after this file was written.

### Source statements reconstructed (raw TeX)

- **Theorem 1.1 (`main`, T L314–L320).** Fix d ≥ 3, γ ∈ (0,1), Schwartz φin ≥ 0, τ* ∈ (0, τmax). Consider (NLS) (L278)
  with data (DAT) (L292: û_in(k) = √φin(k)·g_k, g_k i.i.d. standard (normalized complex) Gaussians), α = L^{−γ},
  T_kin = L^{2γ}/2. Then for L large, (NLS) has a smooth solution up to T = τ*·T_kin with probability
  ≥ 1 − e^{−(log L)^{40d}}, and sup_{t∈[0,T]} sup_{k∈ℤ_L^d} |E|û(t,k)|² − φ(t/T_kin, k)| ≤ L^{−θ}, θ > 0 depending only on
  (d,γ) (θ = η^{20}, L611), E taken on the solvable event. Quantifier order: d, γ → θ → data, τ* → L large.
- **Parameter prefix (Π) (T L606–L611).** τ* fixed, φ the WKE solution, C₀(d,γ), η small (C₀), 𝔆 (defC), C₁(τ*,η,𝔆),
  ν small (C₁), δ small (ν) with 𝔇 = τ*/δ ∈ ℤ, C₂(𝔇,δ,φin), L large (C₂). Encoded (WAVE-B §1.2, D7 F5) as the eventual
  quantifier string of `WTPrefix`; `WTPrefixP` inserts the moment order P after ν ("P large depending on C₁",
  "δ small depending on P", T L2279).
- **Prop `propansatz` (T L689–L707), base case L708.** For 0 ≤ p ≤ 𝔇 there are events 𝔉_p, real ℛ_p, ℰ_p, ℰ̃_p with
  (1) unique solution on [0,p] on 𝔉_p, 𝔉_p ⊃ 𝔉_{p+1}, ℙ(𝔉_p) ≥ 1 − e^{−N_p}, gauge/translation symmetric;
  (2) (ansatz1)–(ansatz2); (3) (ansatz3)–(ansatz4) for 2 ≤ R ≤ R_p; (4) (ansatz5) for n ≤ N_p.
- **Prop `layergarden` (T L761–L779).** In the inductive step (0 ≤ p ≤ 𝔇 − 1, T L708), for 1 ≤ R ≤ 10R_{p+1},
  n ≤ N_{p+1}^4: (1) R ≥ 2: (estgarden); (2) R = 1: off-diagonal vanishing, (estcouple), (estcouple2).
- **Prop `fixedpoint` (T L780–L794).** In the inductive step: an event 𝔉_{p+1} ⊂ 𝔉_p, symmetric,
  ℙ(𝔉_p ∖ 𝔉_{p+1}) ≤ e^{−4N_{p+1}}, on which (fixedest1)–(fixedest3) and the contraction (fixedest4) on the ball of
  radius e^{−10N_{p+1}} of Z = Z^{(5/4)Λ_{p+1}}([p,p+1]).
- **Prop `flowerest1` (T L2279–L2286; uses L2306–L2338).** P large (C₁), δ small (P); for (t,s,k,k′) with
  p+1 > t > s > p (L2263): (flowerest2) for 𝒳, and for 𝒴, 𝒲 with e^{−100N_{p+1}}; M₁, M₂ ≥ L dyadic cutoffs with gains
  M₁^{−80dP}, and (|k| ≥ M₁^{10}) M₂^{−P/9}; the couple/∂_t uses at L2310–L2312, (newnormn)/(sobolev2) at L2320–L2331.
- **Full range.** T L314 claims 0 < γ < 1. R190/R192/D16: the v1 anchors are the full-range targets as printed (each =
  its sealed v2 minus exactly `1 / 2 < P.γ`); v4 = v3 minus `1 / 2 < P.γ →`. E1 (DH23 Prop 9.6 case (4) false for
  γ ≤ 1/2) is a defect of the printed PROOF, not a restriction of any statement. No γ restriction beyond (0,1) is ruled.

### Shared prefix rows (`WTPrefix`, expanded; `WTPrefixP` adds row P12a)

| # | Binder | Bin | Citation |
|---|---|---|---|
| P1 | `d : ℕ` | TYPING | T L314 |
| P2 | `3 ≤ d` | STANDING | T L314 ("Fix d ≥ 3"), standing throughout (T L606) |
| P3 | `γ : ℝ` | TYPING | T L314 |
| P4 | `γ ∈ Ioo 0 1` | STANDING | T L314 (γ ∈ (0,1)); R190, R192, D16 (full range; nothing narrows it) |
| P5 | `∃ η₀, 0 < η₀ ∧ ∀ η ∈ Ioc 0 η₀` | STANDING | T L606 (η small depending on C₀(d,γ)); WAVE-B §1.2 |
| P6 | `φin : SchwartzMap (Mom d) ℝ` | STANDING | T L314 (Schwartz data); carrier `Mom d` = ℝ^d (D6) |
| P7 | `∀ k, 0 ≤ φin k` | STANDING | T L314 (φin ≥ 0) |
| P8 | `τstar : ℝ`, `0 < τstar` | STANDING | T L314, L606 (τ* ∈ (0, τmax)) |
| P9 | `φ : ℝ → SchwartzMap (Mom d) ℝ` | TYPING | T L606 (fix the solution φ(τ,k)) |
| P10 | `IsWKESolution φin τstar φ` | STANDING | T L606, Prop wkelwp L598; D6 (closed-interval Schwartz solution class encodes τ* < τmax) |
| P11 | `∃ C₁, 1 ≤ C₁` | STANDING | T L608 (C₁ depends on τ*, η, 𝔆) |
| P12 | `∃ ν₀, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀` | STANDING | T L608 (ν small depending on C₁) |
| P12a | (`WTPrefixP` only) `∃ P₀, ∀ Pm ≥ P₀` | SOURCE | T L2279 (P large depending on C₁; order after ν, before δ) |
| P13 | `∃ δ₀, 0 < δ₀ ∧ ∀ δ ∈ Ioc 0 δ₀` | STANDING | T L608 (δ small depending on ν); for `WTPrefixP` also T L2279 (δ small depending on P) |
| P14 | `∀ D : ℕ, 1 ≤ D → τstar = D * δ` | STANDING | T L609 (defD) 𝔇 = τ*/δ ∈ ℤ (1 ≤ D is implied by τ* > 0) |
| P15 | `∃ C₂, 1 ≤ C₂` | STANDING | T L610 |
| P16 | `∃ L₀, 2 ≤ L₀ ∧ ∀ L ≥ L₀` | STANDING | T L610 (L large depending on C₂) |
| — | `P := ⟨d, γ, η, φin, τstar, φ, C₁, ν, δ, D, C₂, L⟩` | TYPING | record of the chosen parameters (`WTParams`, no content) |

Non-vacuity of the prefix (every prover choice is followed by a non-empty range): (0, η₀], (0, ν₀], [P₀, ∞), (0, δ₀],
[L₀, ∞) are non-empty for every admissible witness; for every τ* > 0 and δ₀ > 0 the pair D = ⌈τ*/δ₀⌉ ≥ 1, δ = τ*/D ∈
(0, δ₀] satisfies P14; P4 admits γ = 1/4 and γ = 1/2 (low half) as well as γ > 1/2. The prefix restricts γ only by P4.

### layergardenFlower_v4 (`WTPrefixP fun Pm P => …`)

| # | Binder | Bin | Citation |
|---|---|---|---|
| P1–P16, P12a | prefix | as above | as above |
| V1 | `p : ℕ`, `p < P.D` | SOURCE | T L708 (inductive step 0 ≤ p ≤ 𝔇−1); 𝔼_p of flowerest1 (L2279) |
| V2 | `R : ℕ → Mom P.d → ℝ` | TYPING | inputs F_q = φ(δq) + ℛ_q (T L698) |
| V3 | `RemainderBound P R p` | RULED | D7 (WAVE-B §4.15 "remainders as in B1.2", §4.2 (D1)); T (ansatz2) L695 |
| V4 | `t ∈ Ioo p (p+1)` | SOURCE | T L2263 (p+1 > t > s > p) |
| V5 | `s ∈ Ioo p t` | SOURCE | T L2263 |
| V6 | `n n' : Fin P.d → ℤ` | TYPING | k, k′ ∈ ℤ_L^d as n/L (D6 lattice convention) |
| V7 | `ζ : ℤˣ` | SOURCE | ζ ∈ {±} (T L2268, L2280) |
| V8 | `N ≤ P.N (p+1) ^ 4` | RULED | D7 (B1.12 (D2), (D3)); T L2290 |
| V9 | `kind : FlowerKind` | SOURCE | 𝒳, 𝒴, 𝒲 (T L2271–L2281) |
| V10 | `pat : Fin (2*Pm) → FixPat` | RULED | D7 (B1.12 (D8), (D9), (D11)); T L2331 (∂_{t,s} terms) |
| V11 | `dagger : Option (Fin (2*Pm) → Fin 3 → Mom P.d)` | RULED | D7 (B1.12 (D8), R8); T L2327 (𝒥†) |
| V12 | `cut1 cut2 : Option ℕ` | SOURCE | T L2283, L2285 (M₁, M₂ dyadic cutoffs); D13 product form, E34 |
| V13 | `∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, (2^{j₁}L)^{10} ≤ ‖k‖` | SOURCE | T L2285 (M₂ cutoff only under |k| ≥ M₁^{10}) |
| V14 | couples: `t ∈ Ioo p (p+1)` | RULED | D7 (B1.12 (D10)); T L2309–L2312 (t ∈ [p,p+1]; the gate covers the open interval) |
| V15 | couples: `k : Mom P.d` | TYPING | ℝ^d frequency (T L680) |
| V16 | couples: `N ≤ P.N (p+1) ^ 4` | RULED | D7 (B1.12 (D2), (D3)) |
| V17 | couples: `kind : TreeKind` | RULED | D7 (B1.12 (D10): ℒ₀ and a^tr) |
| V18 | couples: `dt : Bool` | SOURCE | T L2312 (∂_t) |
| V19 | couples: `kind = .tr → dt = true` | RULED | D7 (B1.12 (D10)); T L2312 |

Counts (my granularity): SOURCE 9 (P12a, V1, V4, V5, V7, V9, V12, V13, V18), STANDING 13 (P2, P4–P8, P10–P16),
TYPING 6 (P1, P3, P9, V2, V6, V15), RULED 8 (V3, V8, V10, V11, V14, V16, V17, V19), **EXCESS 0**. No γ restriction
beyond P4 (the hypothesis `1 / 2 < P.γ` of v3 is absent; checked at the Expr level in (b)).

### layergarden_v1 (`WTPrefix fun P => …`)

| # | Binder | Bin | Citation |
|---|---|---|---|
| P1–P16 | prefix | as above | as above |
| L1 | `p : ℕ`, `p < P.D` | SOURCE | T L708, L761 (inductive step) |
| L2 | `R : ℕ → Mom P.d → ℝ` | TYPING | T L698 |
| L3 | `RemainderBound P R p` | RULED | D7 (WAVE-B §4.2 (D1)); T (ansatz2) L695, L949–L951 |
| L4 | `t ∈ Ioc p (p+1)` | RULED | D7 (§4.2 (D2)); source t = p+1 (T L761) |
| L5 | `N ≤ P.N (p+1) ^ 4` | SOURCE | T L761 (n ≤ N_{p+1}^4) |
| L6 | `m : ℕ`, `2 ≤ m`, `m ≤ 10 * P.R (p+1)` | SOURCE | T L761, L766 (R ≥ 2, R ≤ 10R_{p+1}) |
| L7 | `ζ : Fin (2*m) → ℤˣ` | SOURCE | T L764, L766 (signature, "any choices of ζ") |
| L8 | `IsBalancedSig ζ` | RULED | D7 (WAVE-B §4 conventions: balanced ζ⃗); for unbalanced ζ the garden sum of that signature is empty (gardens are completely paired, Def defgarden), so the source's bound is trivial there |
| L9 | `n : Fin (2*m) → (Fin P.d → ℤ)` | TYPING | k_j ∈ ℤ_L^d |
| L10 | `n : Fin 2 → (Fin P.d → ℤ)`, `n 0 ≠ n 1` | SOURCE | T L769 (nonzero only when k₁ = k₂) |
| — | (2b) `SNorm … (coupleRemainder P R p N t) ≤ …` (no binder) | RULED | D7 (§4.2 (D3)): (estcouple)+(estcouple2) merged, T L770–L776 |

Counts: SOURCE 5 (L1, L5, L6, L7, L10), STANDING 13, TYPING 5 (P1, P3, P9, L2, L9), RULED 3 (L3, L4, L8),
**EXCESS 0**. No γ restriction beyond P4.

### fixedpoint_v1 (`WTPrefix fun P => …`)

| # | Binder | Bin | Citation |
|---|---|---|---|
| P1–P16 | prefix | as above | as above |
| F1 | `Ω : Type u` | TYPING | probability space of the data (D6, D7) |
| F2 | `[MeasurableSpace Ω]` | TYPING | idem |
| F3 | `μ : Measure Ω` | TYPING | idem |
| F4 | `[IsProbabilityMeasure μ]` | TYPING | idem |
| F5 | `g : (Fin P.d → ℤ) → Ω → ℂ` | TYPING | the g_k of (DAT) (T L292) |
| F6 | `IsGaussianData μ g` | SOURCE | T L292 (DAT): g_k i.i.d. standard Gaussians (measurable, independent, law `stdComplexGaussian`; D6 reading) |
| F7 | `p : ℕ`, `p < P.D` | SOURCE | T L708 |
| F8 | `a Fev R E Et` | TYPING | the objects of Prop propansatz (T L689) |
| F9 | `∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q` | SOURCE | T L708 (induction hypothesis: (1)–(4) for 0 ≤ q ≤ p); body `AnsatzAt` RULED D7 (§4.1 (D1)–(D7)) |
| F10 | concl. `∃ F'`, `F' ⊆ Fev p`, `IsSymmetricEvent`, `μ.real (Fev p \ F') ≤ e^{−4N}` | SOURCE | T L780 |
| F11 | concl. `MeasurableSet F'` | RULED | D7 (§4.1 (D5)-type measurability; needed for the probabilities) |
| F12 | concl. `∀ ω ∈ F'` and `let`s `Ntr, Λ, ℒ, Zs` | SOURCE / TYPING | T L780 ("assuming 𝔉_{p+1}"); the lets are abbreviations |
| F13 | (1) `∀ t ∈ Icc p (p+1), ∀ n` | SOURCE | T L782 (fixedest1) |
| F14 | (2) `∀ b t n` (ℒ₀ does not depend on b) | SOURCE | T L784 (fixedest2) |
| F15 | (3) `∀ b ∈ Zs`, `∀ c ∈ Zs, ∃! b`, norm inequality | SOURCE + RULED | T L786–L788; D7 (§4.3 (D2) Z continuity, (D4) unique solvability) |
| F16 | (4) `∀ b ∈ Zs`, ball radius `e^{−10N}`, `∃ c ∈ Zs`; `∀ b b' c c'` + equations | SOURCE + RULED | T L790–L793; D7 (§4.3 (D1) constant ½, (D4)) |

Counts (hypothesis-side binders F1–F9 and the prefix): SOURCE 3 (F6, F7, F9), STANDING 13, TYPING 9 (P1, P3, P9,
F1–F5, F8), RULED 0 on the hypothesis side; conclusion-side binders F10–F16 SOURCE with the ruled deviations
noted. **EXCESS 0**. No γ restriction beyond P4.

### propansatz_v1 (`WTPrefix fun P => …`)

| # | Binder | Bin | Citation |
|---|---|---|---|
| P1–P16 | prefix | as above | as above |
| A1–A5 | `Ω`, `[MeasurableSpace Ω]`, `μ`, `[IsProbabilityMeasure μ]`, `g` | TYPING | D6, D7 |
| A6 | `IsGaussianData μ g` | SOURCE | T L292 (DAT) |
| A7 | concl. `∃ a Fev R E Et` | SOURCE | T L689 ("we can define an event 𝔉_p, functions ℛ_p, ℰ_p, ℰ̃_p") |
| A8 | concl. `∀ p ≤ P.D` | SOURCE | T L689 ("for each 0 ≤ p ≤ 𝔇") |
| A9 | concl. `AnsatzAt P μ g a Fev R E Et p` | SOURCE + RULED | (1)–(4) T L690–L706; deviations D7 §4.1 (D1)–(D7) |

`AnsatzAt` (sealed definition, read in full): (1) `MeasurableSet (Fev p)`, `IsSymmetricEvent` (D7 Q5), nesting
`1 ≤ p → Fev p ⊆ Fev (p−1)`, `1 − e^{−N_p} ≤ μ(Fev p)`, existence and uniqueness in the classed solution notion on
[0,p] (D4), measurability and integrability of products (D5) — T (1) L691; (2) `‖R p‖_{𝔖^{Λ_p,Λ_p}} ≤ L^{−θ_p}`
(D1), `|E p n| ≤ ⟨n/L⟩^{−Λ_p} e^{−N_p}`, the two-point moment identity (D2) — (ansatz1), (ansatz2) L693–L695;
(2′) intermediate times (D3, new); (3) for 2 ≤ m ≤ R_p, Σζ = 0, all n: cumulant = Σ_{N ≤ N_p} truncSum + Ẽ (D6), Ẽ = 0
off Σζ n = 0, |Ẽ| bound — (ansatz3), (ansatz4) L697–L700; (4) N ≤ N_p: |truncSum| ≤ … L^{−(m−1)/6} δ^{νN} — (ansatz5)
L702–L704. Observation (not EXCESS): (3)–(4) quantify over balanced ζ only (Σζ = 0); for unbalanced ζ the source's
cumulant vanishes by the gauge symmetry of 𝔉_p (T L798), which (1) retains. The definition is D7-approved and sealed.

Counts: SOURCE 4 (A6–A9), STANDING 13, TYPING 8 (P1, P3, P9, A1–A5), RULED: inside `AnsatzAt` (D1–D7),
**EXCESS 0**. No γ restriction beyond P4.

### main_v1

| # | Binder | Bin | Citation |
|---|---|---|---|
| M1 | `d : ℕ` | TYPING | T L314 |
| M2 | `hd : 3 ≤ d` | SOURCE | T L314 |
| M3 | `γ : ℝ` | TYPING | T L314 |
| M4 | `hγ : γ ∈ Ioo 0 1` | SOURCE | T L314; R190, R192, D16 (full range, no E1 restriction) |
| M5 | `∃ θ > 0` (after d, γ; before φin) | SOURCE | T L318 (θ depends only on (d,γ)), L611 (θ = η^{20}) |
| M6 | `φin : 𝓢(Mom d, ℝ)` | SOURCE | T L314 (Schwartz data); carrier D6 |
| M7 | `∀ k, 0 ≤ φin k` | SOURCE | T L314 |
| M8 | `τstar > 0` | SOURCE | T L314 (τ* ∈ (0, τmax)) |
| M9 | `φ : ℝ → 𝓢(Mom d, ℝ)` | TYPING | T L314 ("φ(τ,k) is the solution to (WKE)") |
| M10 | `IsWKESolution φin τstar φ` | RULED | D6 (closed-interval WKE solution class; τ* < τmax as existence on [0, τ*]); T L314, L598 |
| M11 | `∃ L₀, ∀ L ≥ L₀` | SOURCE | T L316 ("for sufficiently large L") |
| M12 | `α T : ℝ`, `α = L ^ (-γ)`, `T = τstar * kineticTime α` | SOURCE | T L314, L316 (α = L^{−γ}, T = τ* T_kin, T_kin = 1/(2α²)) |
| M13 | `Ω`, `[MeasurableSpace Ω]`, `P`, `[IsProbabilityMeasure P]` | TYPING | D6 (expectations are integrals against P) |
| M14 | `g : (Fin d → ℤ) → Ω → ℂ` | TYPING | T L292 (g_k) |
| M15 | `∀ n, Measurable (g n)`, `iIndepFun g P`, `∀ n, P.map (g n) = stdComplexGaussian` | SOURCE | T L292 (i.i.d. standard Gaussians); D6 (circular complex Gaussian) |
| M16 | concl. `MeasurableSet (solvableEvent …)` | RULED | D6 (`MeasurableSet F` asserted) |
| M17 | concl. probability `≥ 1 − e^{−(log L)^{40d}}` | SOURCE | T L316 |
| M18 | concl. `∀ U`, `(∀ ω ∈ solvableEvent, IsSmoothNLSSolution … (U ω))` | RULED | D6 (selection device ∀ U; statement about smooth NLS solutions) |
| M19 | concl. `∀ t ∈ Icc 0 T, ∀ n` and the bound with `E = ∫ 1_F ·` | SOURCE + RULED | T L317 (limit); D6 (E = E[1_F ·]) |

Counts: SOURCE 11 (M2, M4–M8, M11, M12, M15, M17, M19), STANDING 0, TYPING 5 (M1, M3, M9, M13, M14), RULED 3 (M10,
M16, M18), **EXCESS 0**. The only γ condition is M4 (γ ∈ (0,1)); main_v2's `Ioo (1/2) 1` is gone.

## 10. Reproduction (commands; all outputs under `<work>/seal-audit-ALL-B/`)
- (a) `python3 -I tools/item_a.py` → `item_a.out`; `python3 -I tools/item_b_text.py export-main` → `item_b_text.out`;
  guard/module check → `guard_final.out`, `tools/guard_each.sh` → `guard_each.out`.
- (f) `replay/replay.sh quick` → `replay/Replay-quick.out`, `replay/reach-dump.tsv`, `replay/modules.txt`;
  `lake env replay/exe/.lake/build/bin/replay reach replay/index replay/watch.txt <FL> <LG>` → `replay/Reach-FL-LG.out`;
  `lean --run tools/TraceCheck.lean replay/modules.txt export-main <main lib> trace-check.tsv`.
- (b)/(c) `python3 -I tools/gen_probes.py`; `tools/probe.py` runs → `probes/out_vis_layergardenFlower_v4.*`,
  `probes/out_vis_union.*`, `probes/out_exact.*` (sha256 of `exact.lean` `5a396e5c…`), `probes/out_exact2.*`
  (`fa3a0b17…`).
- (e) `tools/run_abi.sh` → `probes/run_abi.out`, `probes/abi_*`, `draft/<id>/`.
- (g) `python3 -I tools/item_g.py export-main` → `item_g.out`. (d) tables: `dag-spine.txt`, `dag-gates.txt`,
  `h8-decls.txt`.

## Final lines

- `layergardenFlower_v4` may be recorded as PROVED (key B)
- `layergarden_v1` may be recorded as PROVED (key B)
- `fixedpoint_v1` may be recorded as PROVED (key B)
- `propansatz_v1` may be recorded as PROVED (key B)
- `main_v1` may be recorded as PROVED (key B)
