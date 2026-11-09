# SEAL AUDIT — `fixedpoint_v2`, KEY-B (refute-first, independent)

- Anchor: `WaveTurbulence.fixedpoint_v2`, `WaveTurbulence/Frozen/Theorems/FixedpointV2.lean`, kind theorem, state SEALED.
- Seal commits: `793a7363` "Seal fixedpoint_v2 with its proved assembly (SEAL-PREP chain)", `f78bcabf4e3813a5baccd9243dadb1194760f8e4`
  "manifest: ABI hash of the sealed fixedpoint_v2". Freeze: `8d7ccb4a` (D10). Final pushed main `1987105a` (main checkout clean
  at that commit; its build was used for all probes and the replay).
- Clean export: `git archive f78bcabf | tar -x` → `/home/scott/wt-scratch/seal-audit-fixedpoint_v2-B/export`.
- All work in `/home/scott/wt-scratch/seal-audit-fixedpoint_v2-B/`; nothing outside it was written. Lean processes were niced (10),
  one heavy process at a time, run through the throttled `wt-throttled` wrapper (real binary Lean 4.35.0 eb6cafb7).
- Rules: `seal-prep/audit-briefs/AUDIT-COMMON.md`; item specifics `AUDIT-fixedpoint_v2.md`; skill `lean-statement-audit`.

## Verdict table

| Item | Verdict | Evidence (summary) |
|---|---|---|
| (a) Anchor bytes | **PASS** | prefix `9bde1193…b289` / suffix `9f481990…a8d0` recomputed at freeze and seal = manifest; the only byte change since `8d7ccb4a` is the body `by sorry` → `by exact WaveTurbulence.Provider.fixedpoint_v2`; manifest entry changed in exactly `state`, `abi_sha256`; 114/114 closure hashes match; guard OK, module check PASS on the export |
| (b) Provider | **PASS** | statement bytes = anchor's (2090 B), same `open`/`universe` context; `pp.all` type (216 KB, unelided) identical to the anchor's and to the freeze build's; `Expr` alpha-equal (`==` true; `Expr.equal` false only for 2 hygienic instance-binder names); body exactly the briefed assembly (checked on the olean `Expr`); no self-import (Lake closure and full source closure); export used only by the anchor; proof modules private: from an anchor-only importer all 9 proof-closure names are unknown, and the anchor's Lake setup = Mathlib + its 114 `Frozen.Defs` + the provider |
| (c) Axioms | **PASS** | `[propext, Classical.choice, Quot.sound]` for the anchor, provider, `V2Chain.fixedpoint_v2_of_closed_gates_v3`, `layergardenFlower_v3`, `layergarden_v2`, `wkeTaylor` (and their providers), `regularAsymptotics` (and its provider; reached through `layergarden_v2`), `X2E.oX2Exp`, `Cpl.oX3Cpl` |
| (d) Hidden hypotheses / vacuity | **PASS** | every chain constant is a `theorem` (replay); the three gates are discharged by the three sealed anchors; gates match the anchors' types (token-equal; `Expr` differences only abstracted `Nat.AtLeastTwo`/`NeZero` instance proofs); `toR`/`ofR` thread only `γ ∈ (1/2,1)`; thresholds explicit; Lean witnesses (compiled, standard axioms): non-empty δ-range, `IsGaussianData` inhabited (product Gaussian), zero solution of WKE, `AnsatzAt … 0` for zero data, and all premises jointly at a point inside the prefix |
| (e) ABI | **PASS** | pre-seal `3000d181…5031` reproduced from my own rebuild of the freeze sources; post-seal `5bf36503…3900` reproduced; `#print` outputs differ only in the value line (`sorry` → `WaveTurbulence.Provider.fixedpoint_v2`); `pp.all` type of the freeze build = seal build (sha256 `aa967638…6e22`, both) |
| (f) Kernel replay | **PASS** (quick mode) | `REPLAY OK (8339s): 218747 constants`, 11048 project modules, wall 2:19:45, max RSS 6.24 GB; MISSING 0; no reachable project axiom / opaque / unsafe / partial; no direct user of `sorryAx`/`ofReduceBool`/`trustCompiler`/`ofReduceNat`; quick policy: 40618 `WaveTurbulenceVineParam`-internal certificate theorems checked by statement only, 92875 VineParam theorems replayed with proofs; replayed oleans are the seal commit's sources (12022/12022 trace source hashes = export; 36066/36066 olean parts = recorded hashes) |
| (g) Status fields | **PASS** | at `f78bcabf`: DRAFT_ANCHORS 8 (listed below), UNREGISTERED_SORRIES 0, DRAFT_IMPORT_VIOLATIONS 0, SEALED_THIS_TURN `fixedpoint_v2` (`793a7363` + `f78bcabf`). Note: the README status block at `f78bcabf` is stale (says 10 drafts / 17 sealed theorems) |
| (h) Five-bin table | **PASS** | 50 expanded rows: STANDING 19, SOURCE 20, TYPING 6, RULED 5, **EXCESS 0** |

Dependency (brief): `layergardenFlower_v3` keys A and B must be PASS — see "Dependency" at the end.

## (a) Anchor bytes

- Convention (guard `check_theorem_region`): prefix = all bytes through the newline after `-- FROZEN_ANCHOR_PROOF_BEGIN`; suffix =
  all bytes from the start of the `-- FROZEN_ANCHOR_PROOF_END` line. Script `notes/hash.py` (my own).
- Freeze file (`git show 8d7ccb4a:…`): sha256 `820c05c32cbdbe7c0cb7a1cb9d06917729895a2770bf84967eb6cb5840ab50b2` (= brief's `820c05c3…`).
  Seal file: sha256 `6bbd2af2bd90945006eb85f52f8a7bfc95b84c785fdea5432f86f65c05c13453`.
- prefix `9bde11939dfa4f7b8f4de1c19d8f46dfc6d027ade6b01523d8e3219faa41b289` and suffix
  `9f48199048606af986e4911abed0172f6e65c9c8c91f1c2874961ad85a7ea8d0`, identical at freeze and seal, equal to the manifest.
  Body: `  by sorry\n` → `  by exact WaveTurbulence.Provider.fixedpoint_v2\n` (the full `diff` is that one line).
- `git log 8d7ccb4a^..f78bcabf -- WaveTurbulence/Frozen/Theorems/FixedpointV2.lean`: only `8d7ccb4a` and `793a7363`.
- Manifest entry: freeze (`8d7ccb4a`) vs seal (`f78bcabf`) and pre-seal parent (`793a7363^`) vs seal both differ in exactly
  `state` (DRAFT_SORRY → SEALED) and `abi_sha256` (`3000d181…` → `5bf36503…`). No other field (prefix, suffix, closure,
  implementation, approval, source, split policy) changed.
- `definition_closure`: 114 entries, 0 sha256 mismatches on the export; every path is owned by a SEALED definition anchor; no commit
  touched any of the 114 files in `8d7ccb4a..f78bcabf`. Lake's setup for the anchor lists exactly these 114 modules + the provider.
- Guard on the clean export (`check_index.sh` needs a git index, so I ran its two commands on the `git archive` tree):
  `python3 -I scripts/check_frozen_anchors.py --root . --manifest manifest/frozen.json` → `FROZEN-ANCHOR GUARD OK` (rc 0);
  `python3 -I scripts/check_lean_modules.py` → `check_lean_modules: PASS (13118 Lean files, 0 comparator configurations)` (rc 0).

## (b) Provider

- Text: the substring `theorem fixedpoint_v2 : … :=` of the provider equals the anchor's byte for byte (2090 bytes). Context lines
  `public section`, `open MeasureTheory ProbabilityTheory Finset Set`, `open scoped ENNReal`, `universe u` equal; only the namespace
  (`WaveTurbulence.Provider`) and the docstring differ.
- Elaborated (probe `probe/ProbeA.lean`, module, plain `import WaveTurbulence.Frozen.Theorems.FixedpointV2`, setup generated by my
  own `probe/gen_setup.py` from Lake's `.lake/build/ir/<M>.setup.json`): the frozen statement text re-elaborates there and is proved
  by `WaveTurbulence.fixedpoint_v2`; `example : type_of% @WaveTurbulence.fixedpoint_v2.{u} = type_of% @WaveTurbulence.Provider.fixedpoint_v2.{u} := rfl`
  elaborates (no error).
- `pp.all` (with `pp.deepTerms true`, `pp.maxSteps 10^8`, `pp.proofs true`; 215 984 bytes, **0 elisions**): anchor (seal build) =
  anchor (my freeze build) = provider after renaming the constant (`probe/pp_*.out`; sha256 anchor `aa96763853206e25d17bec4374b5d0bb12c5019d951f66e96d83e5c982be6e22`).
  The four `let`s (`Ntr`, `Λ`, `ℒ`, `Zs`) elaborate in all three as non-dependent `letE` (`pp.all` prints `have`) at the same four
  positions: no `let`/`have`/zeta difference.
- `Expr` level (olean `Expr`s, `replay/exe` EXACT section and `bindiff/`): provider type `==` anchor type: **true**; `Expr.equal`:
  false, and the only differences are the names of the two anonymous instance binders,
  `inst._@.WaveTurbulence.Frozen.Theorems.FixedpointV2.…_hyg.17/22` vs `inst._@.WaveTurbulence.Provider.FixedpointV2.…_hyg.17/22`
  (`[MeasurableSpace Ω]`, `[IsProbabilityMeasure μ]`; the macro scope contains the module name). Binder names carry no logical content.
- Body (olean `Expr`): anchor value `WaveTurbulence.Provider.fixedpoint_v2.{u}`; provider value
  `WaveTurbulence.V2Chain.fixedpoint_v2_of_closed_gates_v3.{u} WaveTurbulence.layergardenFlower_v3 WaveTurbulence.layergarden_v2 WaveTurbulence.wkeTaylor` — exactly the briefed assembly.
- No self-import: the provider's Lake setup (19590 modules) and its full source-level import closure (12021 project modules, all
  import kinds) do not contain `WaveTurbulence.Frozen.Theorems.FixedpointV2`.
- Export used only by the anchor: the only importer of `WaveTurbulence.Provider.FixedpointV2` in the export is the anchor file; the
  only file mentioning `Provider.fixedpoint_v2` is the anchor file.
- Private proof imports: the provider has `public import` of Mathlib and the anchor's 14 `Frozen.Defs`, and plain `import` of
  `Frozen.Theorems.LayergardenFlowerV3`, `Frozen.Theorems.LayergardenV2`, `Frozen.Theorems.WkeTaylor`,
  `Foundations.XChain.V2Chain.FixedpointV2`. The anchor's own Lake setup (its compile environment) contains Mathlib, the 114
  `Frozen.Defs` modules and the provider, and no proof-closure module. From the anchor-only importer, `#check` of
  `V2Chain.fixedpoint_v2_of_closed_gates_v3`, `V2Chain.FixedpointV2Gate`, `V2Chain.WTPrefixS`, `layergardenFlower_v3`, `layergarden_v2`,
  `wkeTaylor`, `X2E.oX2Exp`, `Cpl.oX3Cpl`, `V2Chain.fixedpointS_of_parts` all give `Unknown identifier` (`probe/ProbeA.out`).
  So the frozen statement elaborates in its freeze environment (Mathlib + the anchor's `Frozen.Defs` + the provider's theorem), and the
  freeze-build `pp.all` identity above confirms it.

## (c) Axioms

`#print axioms` (`probe/ProbeA.out`, `probe/ProbeB.out`, `probe/ProbeC.out`): `WaveTurbulence.fixedpoint_v2`,
`WaveTurbulence.Provider.fixedpoint_v2`, `WaveTurbulence.V2Chain.fixedpoint_v2_of_closed_gates_v3`, `WaveTurbulence.layergardenFlower_v3`,
`WaveTurbulence.layergarden_v2`, `WaveTurbulence.wkeTaylor`, `WaveTurbulence.Provider.{layergardenFlower_v3, layergarden_v2, wkeTaylor}`,
`WaveTurbulence.X2E.oX2Exp`, `WaveTurbulence.Cpl.oX3Cpl`, `WaveTurbulence.regularAsymptotics`, `WaveTurbulence.Provider.regularAsymptotics`:
each `depends on axioms: [propext, Classical.choice, Quot.sound]`. (These read precomputed per-module lists; (f) is the independent check.)
The reachable sealed `Frozen.Theorems` constants (replay) are exactly `layergarden_v2`, `fixedpoint_v2`, `regularAsymptotics`,
`layergardenFlower_v3`, `wkeTaylor`. `regularAsymptotics` (SEALED `regularAsymptotics_v1`) enters only through the proofs of the
sealed anchors (`Foundations/Spine/SourceProviders.lean`); the assembly module's own closure (744 modules) contains no `Frozen.Theorems`.

## (d) Hidden hypotheses and vacuity

Trace (source `Foundations/XChain/V2Chain/FixedpointV2.lean`, constant kinds from the replay's CHAIN lines, all `theorem`/`def`, none
unsafe): `fixedpoint_v2_of_closed_gates_v3 (hG : LayergardenFlowerV3Gate) (hL : LayergardenV2Gate) (hW : WkeTaylorGate) :
FixedpointV2Gate` :=
`(fixedpointS_of_parts (cplMomentsS_of_gates (ofR hG') (ofR hL') (ofFull hW') Cpl.oX3Cpl) (part2S_of_X2 (flowerest1S_of_gates (ofR hG') X2E.oX2Exp))).toR`.
- Inputs: the three gate binders and the closed theorems `X2E.oX2Exp : OX2Exp` and `Cpl.oX3Cpl : OX3Cpl` (theorems, no binders,
  standard axioms). All combinators (`fixedpointS_of_parts`, `cplMomentsS_of_gates`, `part2S_of_X2`, `flowerest1S_of_gates`,
  `WTPrefixS.ofR/toR/ofFull`, `WTPrefixPS.ofR`) are theorems. The replay found no reachable project axiom, opaque, unsafe or partial
  constant and no `sorryAx` user in the whole closure.
- Binders discharged exactly: the provider value applies the assembly to `layergardenFlower_v3`, `layergarden_v2`, `wkeTaylor`
  (the sealed exports themselves). `example`s in `probe/ProbeB.lean` type each sealed anchor at its gate and re-run the assembly.
- Gates "token for token" (verified, not trusted): the source text of `FixedpointV2Gate`, `LayergardenFlowerV3Gate`, `LayergardenV2Gate`
  equals the anchors' statement text (whitespace-normalized); the `open` contexts agree (`open Classical in` on both flower texts).
  At the `Expr` level (`bindiff/bindiff.out`; binder names ignored) the gate values differ from the anchor types only at numeric-literal
  instance proofs: the anchors carry `Nat.instAtLeastTwoHAddOfNat …` / `Nat.instNeZeroSucc …` inline, the abbreviations carry the
  auxiliary theorems `…Gate._proof_n` / `Induct.WkeTaylorBody._proof_1` that Lean abstracts from definition bodies (16, 12, 9, 3
  occurrences for the four gates; every one of this kind). These are proofs of `Prop`s, so the types are definitionally equal by
  proof irrelevance; the kernel replay re-checked the application. `WkeTaylorGate` is `Induct.WkeTaylorGate = WTPrefix
  Induct.WkeTaylorBody`, equal to `wkeTaylor`'s type after unfolding `WkeTaylorBody`, up to the same instance proofs.
- `WTPrefixS`/`ofR`/`toR` (`V2Chain/PrefixS.lean`) only thread `γ ∈ S`. `toR` cannot produce a vacuous `WTPrefix`: the anchor's type
  is the frozen `WTPrefix fun P => 1/2 < P.γ → …`, whose every existential threshold comes with `0 < η₀`, `0 < ν₀`, `0 < δ₀`, `2 ≤ L₀`;
  for `γ ≤ 1/2` `toR` uses the thresholds `1, 1, 1, 2` and the body is discharged by the false `1/2 < γ` (the D10 restriction itself).
  Thresholds are explicit: `WTPrefixS.large … gFix` with `gFix d D = max (exp (100d+11)) (max (16·2^{d+1}·latConst d) (18·3^{(5/4)(40d)^D+1}·4^{d+1}·latConst d²))`
  (`FixedptDraft/X3Assembly.lean:83`), `.small` with `exp (−25/ν) > 0`.
- Non-vacuity (`probe/NonVacuity.lean`, compiled in the anchor-only environment, rc 0, every theorem `[propext, Classical.choice, Quot.sound]`):
  1. prefix ranges: η ∈ (0, η₀], ν ∈ (0, ν₀], L ∈ [L₀, ∞) are non-empty because the thresholds are positive/finite;
     `delta_range_nonempty`: for every τ★ > 0, δ₀ > 0 there are δ ∈ (0, δ₀] and 𝔇 ≥ 1 with τ★ = 𝔇δ; `d ≥ 3`, `γ ∈ (1/2, 1)` non-empty;
  2. `isGaussianData_infinitePi`: `IsGaussianData (Measure.infinitePi fun _ => stdComplexGaussian) (fun n ω => ω n)` for every d
     (independence by `iIndepFun_infinitePi`, laws by `infinitePi_map_eval`);
  3. `isWKESolution_zero`: `IsWKESolution 0 τ (fun _ => 0)` (φin = 0 ≥ 0 is admissible Schwartz data);
  4. `ansatzAt_zero`: for every `P` with φin = 0, φ = 0, L ≥ 2, δ > 0 and every probability data,
     `AnsatzAt P μ g 0 (fun _ => univ) 0 0 0 0` (the trivial event, R₀ = E₀ = Ẽ₀ = 0, as T L708 says), using that
     `truncSum` at layer 0 is 0 (`IsCanonGC 0 _ = False`) and that the joint cumulant of zero variables is 0;
  5. `premises_satisfiable` and a closing `example`: at the concrete point `P₀ = ⟨3, 3/4, 1, 0, 1, 0, 1, 1, 1, 1, 1, 2⟩` (inside the
     prefix ranges, `τ★ = 𝔇δ`, `1/2 < γ < 1`) all premises after the prefix — probability space, `IsGaussianData`, `p = 0 < 𝔇`,
     `∀ q ≤ 0, AnsatzAt … q` — hold simultaneously. So the frozen statement is not vacuously true.
  For general φin the p = 0 ansatz is T L708 (Gaussian data: second moments give (ansatz1); cumulants of order ≥ 4 vanish, matching
  `truncSum` = 0 at layer 0; the class bound holds a.s., so 𝔉₀ = the a.s. event of finite class norm); I did not formalize that case.
  Corroborating only: the sealed `propansatz_v2` (`a2216712`, after this seal; not audited here) concludes `∀ p ≤ 𝔇, AnsatzAt … p` for
  every Gaussian data.

## (e) ABI

- Method: my own probes (`abi/mk.py`, `abi/AbiProbe.lean` = `module` / `import all WaveTurbulence.Frozen.Theorems.FixedpointV2` /
  `#print WaveTurbulence.fixedpoint_v2`), stdout sha256, run against setup files built from Lake's setup (the convention of
  `scripts/abi_hash_setup.py`, which I read; `.olean.private` for the module itself, and separately for all project modules — same
  result).
- Post-seal (main build): `5bf365035359eb4f6a93ed13841c83e8a1c4e359585cab017ad8868bc5603900` = manifest.
- Pre-seal: I rebuilt the freeze state myself (`freeze/`): compiled the freeze provider stub (`git show 8d7ccb4a:WaveTurbulence/Provider/FixedpointV2.lean`,
  sha256 `62a5e5aa…e78c`, imports only) and the freeze anchor (sha256 `820c05c3…50b2`, warning "declaration uses `sorry`" only)
  against main's Mathlib and `Frozen.Defs` oleans (toolchain, `lake-manifest.json` and all 114 Defs files unchanged since `8d7ccb4a`; the
  lakefile changed only in the quarantine list and a new `lean_lib`). The probe hash is
  `3000d181f909240df0eecaaac50bfe83cc2e57cab73cd29888a17e475e405031` = the manifest's DRAFT value.
- `diff freeze-self.out seal-self.out`: line 51 `sorry` → `WaveTurbulence.Provider.fixedpoint_v2` and nothing else (51 lines).
- `pp.all` type identical before and after (see (b)): no elaboration drift from the new imports.

## (f) Kernel replay

- Adapted `/home/scott/wt-scratch/seal-lg2/replay/` (template `Replay.lean` sha256 `6c943568…e98e`, read in full). Diffs:
  `replay/Replay.diff` (root module `WaveTurbulence.Frozen.Theorems.FixedpointV2`, root constant `WaveTurbulence.fixedpoint_v2`; new
  `wanted` list; new EXACT section: anchor/provider values and types, gate abbreviations vs anchor types) and `replay/replay.sh.diff`
  (own exe; `nice -n 10`; `LEAN_PATH` set explicitly from the anchor's Lake trace instead of `lake env` in the main checkout; index
  batches extended to 0..13999 because the closure has 12022 > 12000 project modules — the template's six batches would have left 22
  modules unindexed). Exe built from `replay/exe/Replay.lean` (sha256 `5411367438fc…2a8c`); no shim; one replay, no forcing.
- Result (`replay/replay-quick.out`, sha256 `b44b4413…ee69`): closure 22998 modules (10976 library, 12022 project); 248686 project
  constant names indexed; reachable 229131 (lib refs 10384), **MISSING 0**; same-name constants in two loaded modules 1647, of these
  with different type/value **0**; project AXIOMS / OPAQUE / UNSAFE-PARTIAL reachable: **none**; direct users of
  `sorryAx`/`ofReduceBool`/`trustCompiler`/`ofReduceNat`: **none**; reachable project constants by kind: theorem 195129, def 22086,
  inductive 582, ctor 799, rec 151; `REPLAY OK (8339s): 218747 constants` in 11048 modules; wall 2:19:45, user 8263 s, max RSS
  6 238 136 kB; rc 0.
- Quick-mode policy (as authorized by AUDIT-COMMON "quick mode at least"): 40618 theorems of the `WaveTurbulenceVineParam` certificate
  library whose proofs use no constant outside that library were sent to the kernel as statements only (an `axiomInfo` with the
  same type in the replay environment); 92875 VineParam theorems that use outside constants were replayed with their proofs. The
  template's final message "no constant turned into an axiom" refers to failure handling; the statement-only certificates are
  disclosed here. No `full` replay was run.
- Provenance: for all 12022 project modules of the closure, the source hash recorded in the Lake `.trace` (Lake `Hash.ofText`,
  recomputed by `trace/LakeHash.lean`) equals the hash of the export's (seal commit's) file — 0 mismatches; the 1815 VineParam traces
  record the source path of the worktree `port-vp` that built them, with the same content hash. All 36066 olean parts of the closure
  hash (Lake `Hash.ofByteArray`, `trace/OleanHash.lean`) to their `.hash` files, which equal the traces' recorded outputs. The files
  changed in `f78bcabf..1987105a` (MainV2, PropansatzV2 anchors and providers, root, lakefile, manifest) are not in the closure.

## (g) Status fields (at `f78bcabf`)

- DRAFT_ANCHORS: **8** theorem anchors in state DRAFT_SORRY: `main_v1` (`Frozen/Theorems/Main.lean`), `fixedpoint_v1` (`Fixedpoint.lean`),
  `layergarden_v1` (`Layergarden.lean`), `layergardenFlower_v1` (`LayergardenFlower.lean`), `propansatz_v1` (`Propansatz.lean`),
  `main_v2` (`MainV2.lean`), `propansatz_v2` (`PropansatzV2.lean`), `layergardenFlower_v2` (`LayergardenFlowerV2.lean`); the lakefile
  quarantine lists exactly these 8 anchor/provider pairs. Manifest: 327 anchors (300 definitions, 27 theorems: 19 SEALED, 8 DRAFT_SORRY).
- UNREGISTERED_SORRIES: **0** — guard OK; my own scan (comments and strings stripped) finds `sorry` only in the 8 draft anchors' bodies.
- DRAFT_IMPORT_VIOLATIONS: **0** — guard quarantine OK; my own scan: each draft provider is imported only by its anchor and no module
  imports a draft anchor.
- SEALED_THIS_TURN: `fixedpoint_v2` (`793a7363`, ABI `f78bcabf`).
- Documentation note (not a seal defect): the README status block at `f78bcabf` still reads "DRAFT_ANCHORS: 10 … layergardenFlower
  v1/v2/v3 …; SEALED: 17 theorems + 300 definitions" (last README auto-update 17:53 UTC, before the seals).

## (h) Five-bin binder table

The source statement was reconstructed from the raw TeX (sha256 re-hashed: `493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb`)
and the rulings D6, D7, D9, D10, D13, E1, E34 (+ deviation table §C) before reading the Lean statement or its docstring:
`notes/h-source-reconstruction.md` (written 21:15:27 UTC, before the anchor file was opened). Every project alias in the type was
expanded (list in `notes/h-binder-table.md`).

Quantifier order of the prefix: d, γ → ∃η₀ → η → φin, τ★, φ → ∃C₁ → ∃ν₀ → ν → ∃δ₀ → δ, 𝔇 → ∃C₂ → ∃L₀ → L (T L605–L611);
then 1/2 < γ, the data, p, the induction data, the IH, and the conclusion. Thresholds precede p and all random/induction data, so
they are uniform in them, as in the source.

| # | Binder (expanded) | Bin | Citation |
|---|---|---|---|
| 1 | `d : ℕ` | STANDING | T L314 "Fix d ≥ 3" |
| 2 | `3 ≤ d` | STANDING | L314 |
| 3 | `γ : ℝ` | STANDING | L314 |
| 4 | `γ ∈ Ioo 0 1` | STANDING | L314 |
| 5 | `η`, `η ∈ Ioc 0 η₀` | STANDING | L605 |
| 6 | `φin : SchwartzMap (Mom d) ℝ` | STANDING | L292, L314; D6 |
| 7 | `∀ k, 0 ≤ φin k` | STANDING | L292, L314 |
| 8 | `τstar : ℝ` | STANDING | L314 |
| 9 | `0 < τstar` | STANDING | L314; D6 reading |
| 10 | `φ : ℝ → SchwartzMap (Mom d) ℝ` | STANDING | L314, L605 |
| 11 | `IsWKESolution φin τstar φ` | STANDING | (WKE) L299–L307; D6 |
| 12 | `ν`, `ν ∈ Ioc 0 ν₀` | STANDING | L608 |
| 13 | `δ`, `δ ∈ Ioc 0 δ₀` | STANDING | L608 |
| 14 | `D : ℕ` | STANDING | (defD) L609 |
| 15 | `1 ≤ D` | TYPING | forced by τ★ > 0, δ > 0, 𝔇 = τ★/δ ∈ ℤ |
| 16 | `τstar = D * δ` | STANDING | (defD) L609 |
| 17 | `L`, `L₀ ≤ L` | STANDING | L610; L314 |
| 18 | `1 / 2 < P.γ` | RULED | D9, D10; E1 |
| 19 | `Ω : Type u` | TYPING | probability space of (DAT) |
| 20 | `[MeasurableSpace Ω]` | TYPING | idem |
| 21 | `μ : Measure Ω` | TYPING | ℙ |
| 22 | `[IsProbabilityMeasure μ]` | TYPING | ℙ |
| 23 | `g : (Fin d → ℤ) → Ω → ℂ` | STANDING | (DAT) L292; k = n/L |
| 24 | `∀ n, Measurable (g n)` | TYPING | random variables |
| 25 | `iIndepFun g μ` | STANDING | L292 "i.i.d." |
| 26 | `∀ n, μ.map (g n) = stdComplexGaussian` | STANDING | L292; D6 (circular) |
| 27 | `p : ℕ` | SOURCE | L708 |
| 28 | `p < P.D` | SOURCE | L708 |
| 29 | `a` | SOURCE | (akeqn) L545, L691 |
| 30 | `Fev` | SOURCE | 𝔉_q, L689, L691 |
| 31 | `R : ℕ → Mom d → ℝ` | SOURCE | L689 (real); D7 (on ℝ^d) |
| 32 | `E : ℕ → (Fin d → ℤ) → ℝ` | SOURCE | L689 |
| 33 | `Et` | SOURCE | L689 |
| 34 | `∀ q ≤ p, AnsatzAt … q` | SOURCE | L708 (IH: propansatz (1)–(4) for 0 ≤ q ≤ p) |
| 35 | `MeasurableSet (Fev q)` | RULED | D6, D7 |
| 36 | `IsSymmetricEvent L φin g (Fev q)` | SOURCE | L691, L567–L569; D7 (preimage form) |
| 37 | `1 ≤ q → Fev q ⊆ Fev (q-1)` | SOURCE | L691 |
| 38 | `1 - e^{-N_q} ≤ μ.real (Fev q)` | SOURCE | L691 |
| 39 | `∀ ω ∈ Fev q, IsASolution L γ δ q (initialCoeff …) (a ω)` | SOURCE | L691, (akeqn) L545–L547; class: D7 |
| 40 | uniqueness in the class on [0,q] | SOURCE | L691; D7 |
| 41 | `∀ t ∈ [0,q], ∀ n, Measurable (a · t n)` | RULED | D7 |
| 42 | integrability of products on `Fev q` | RULED | D7 |
| 43 | `SNormR Λ_q Λ_q (R q) ≤ L^{-θ_q}` | SOURCE | (ansatz2) L695 |
| 44 | `\|E q n\| ≤ ⟨n/L⟩^{-Λ_q} e^{-N_q}` | SOURCE | (ansatz2) L695 |
| 45 | `∫_{Fev q} a_n(q) ā_{n'}(q) = 1_{n=n'}(φ(δq) + R_q + E_q)` | SOURCE | (ansatz1) L693; D6, D7 |
| 46 | (2') `1 ≤ q → ∀ t ∈ [q-1,q], \|𝔼_q\|a_n(t)\|² − φ(δt)\| ≤ 2L^{-θ_q}` | RULED | D7 (E2f (a)) |
| 47 | (3) cumulant = Σ_{N≤N_q} truncSum + Ẽ (2 ≤ m ≤ R_q, Σζ = 0) | SOURCE | (ansatz3) L697–L698; D7 |
| 48 | (3) Ẽ = 0 unless Σζⱼnⱼ = 0 | SOURCE | L699 |
| 49 | (3) `‖Ẽ‖ ≤ (∏⟨nⱼ/L⟩)^{-Λ_q} e^{-N_q}` | SOURCE | (ansatz4) L700 |
| 50 | (4) `‖truncSum‖ ≤ (∏⟨nⱼ/L⟩)^{-Λ_q} L^{-(m-1)/6} δ^{νN}`, N ≤ N_q | SOURCE | (ansatz5) L702–L704 |

Counts: **STANDING 19, SOURCE 20, TYPING 6, RULED 5, EXCESS 0** (50 rows). The existentials ∃η₀, C₁, ν₀, δ₀, C₂, L₀ are prover
choices (outputs), not inputs; C₁, C₂ do not occur in the body.

Conclusion vs L780–L794 (all match; full notes in `notes/h-binder-table.md`): ∃ F' ⊆ Fev p, measurable (added conclusion, D6/D7),
symmetric, μ(Fev p ∖ F') ≤ e^{−4N_{p+1}}; on F', with Ntr = N_{p+1}, Λ = (5/4)Λ_{p+1}, ℒ_j = `Lop … (a ω p) j` ((eqnbk1.5); conjugate
middle slot = D3; j = 0 restricted to n₁+n₂+n₃ ≥ N_{p+1}), Z = continuous-in-t arrays with finite Z^Λ norm (D2):
(fixedest1) for all t ∈ [p,p+1], n; (fixedest2) e^{−20N}; (fixedest3) as "1−ℒ₁ maps Z into Z, is a bijection of Z, and
‖b‖_Z ≤ e^{3N}‖(1−ℒ₁)b‖_Z" (D4); (fixedest4) the solution map sends the e^{−10N} ball into itself with Lipschitz constant ½ (D1).
v2 = the D7-approved v1 text (= `docs/review/WAVE-B-B1.md`, checked) plus `1 / 2 < P.γ →` (D10; review page
`docs/review/GAMMA-HALF-SUCCESSORS.md` sha256 `7366905da3067ae0efbf504be34b0030b4c3e5ffe2b15596646aebab34f4f614`).

## Comparison with the claim appendix and the seal script's logs (read only after the results above; `notes/own-results-before-appendix.md`, 23:50 UTC)

Claim appendix (`AUDIT-fixedpoint_v2.md` §"Claim appendix"):
1. **Agreement:** EXCESS 0; `1/2 < P.γ` RULED (D9, D10, E1); the probability space TYPING; `p < P.D` and the IH SOURCE; the conclusion description.
2. **Disagreement (method):** the appendix lists the `WTPrefix` bundle as one row and `AnsatzAt` as one row. AUDIT-COMMON (h) requires
   recursive expansion of `WTPrefix` and `AnsatzAt`. Expanded, the IH contains four RULED fields (#35, #41, #42, #46: measurability,
   integrability and item (2') from D7) that the appendix does not show. None is EXCESS.
3. **Disagreement (bin):** the appendix bins `g, IsGaussianData` as SOURCE; I bin `g`, independence and law as STANDING (they are
   the data assumption of Thm 1.1, not premises of Prop `fixedpoint`) and measurability as TYPING. No effect on the verdict.
4. **Minor:** the appendix's bundle includes `C₁ ≥ 1` and `C₂ ≥ 1` among binders; they are existential prover choices. It cites
   L606–L610; I cite L605–L611.
5. Count lines differ accordingly (appendix: SOURCE 3 / STANDING 1 / TYPING 1 / RULED 1 rows; mine: 20 / 19 / 6 / 5 expanded rows).

Seal script logs (`seal-prep/logs/live-20261108T193926Z/`):
6. **Agreement:** pre-seal ABI `3000d181…`, post-seal `5bf36503…`, `PRINT DIFF OK ['sorry'] -> ['WaveTurbulence.Provider.fixedpoint_v2']`,
   "frozen diff vs freeze 8d7ccb4a = body only; manifest fields ['abi_sha256','state']", DRAFT_SORRY anchors 8, axioms. Its
   `fixedpoint_v2.{pre,post}.print.out` equal my outputs apart from a trailing `exit 0` line.
7. **Weakness in the script's check:** its `pp.all` comparisons (`fixedpoint_v2.{pre,post}.typeall.out`, `exact.out`) are elided
   (42 `⋯` each; `pp.deepTerms` off), so "pre = post" there compared a partial print. My unelided comparison (0 elisions) confirms
   the identity.
8. The script's run ended with `SEAL ABORT: full ABI check` (a probe for `WaveTurbulence.Mom` failed on elan override notes in its
   output) and "main reset to LAST_GOOD 1987105a (local only)". The brief states that the full ABI check was later OK at `1987105a`.
   For this anchor I reproduced `5bf36503…` against that build.

## Dependency

The brief requires both keys of `layergardenFlower_v3` (this chain's first seal) to be PASS before this key can PASS.
`/home/scott/wt-scratch/flower-core/status/SEALAUDIT-layergardenFlower_v3-A.txt` (2026-11-09 00:05:48 UTC): `PASS layergardenFlower_v3 A`;
`…/SEALAUDIT-layergardenFlower_v3-B.txt` (00:14:56 UTC): `PASS layergardenFlower_v3 B`. I read only these status lines, not those
audits. Recorded PROVED evidence for the other consumed sealed anchors, per the brief: `layergarden_v2` (audits/Seal-layergarden_v2.md,
R152), `wkeTaylor` (/home/scott/wt-scratch/audit-b2a). Their axioms and proofs are re-checked in (c) and (f) here.

`fixedpoint_v2` may be recorded as PROVED (key B)
