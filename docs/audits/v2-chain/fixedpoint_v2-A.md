# SEAL AUDIT — `fixedpoint_v2`, KEY-A

Auditor: KEY-A (Opus 5.5), independent; did not see KEY-B's work. Did not write the anchor, provider, chain or seal script.
Seal commit: `f78bcabf4e3813a5baccd9243dadb1194760f8e4` (seal 793a7363 + ABI f78bcabf); final main `1987105a` (no change
to the anchor, provider or their closures after f78bcabf: `git diff f78bcabf 1987105a` touches only PropansatzV2/MainV2
anchors+providers, lakefile, root, manifest). Clean export: `git archive f78bcabf` → `export/` (13,399 files).
Binding rules: AUDIT-COMMON.md, AUDIT-fixedpoint_v2.md; skill `lean-statement-audit`.
All Lean work: stock `leanprover/lean4:v4.35.0`, `nice -n 10`, one heavy process at a time, against main's build through
my own Lake-setup generator (`probes/gen_setup.py`).

## Verdict table

| Item | Verdict | One-line evidence |
|---|---|---|
| (a) anchor bytes | **PASS** | only change since freeze 8d7ccb4a is the body `by sorry` → `by exact WaveTurbulence.Provider.fixedpoint_v2`; prefix `9bde1193…`, suffix `9f481990…` = manifest; guard OK and module check PASS on the clean export; manifest delta = {state, abi_sha256}; 114/114 closure hashes match |
| (b) provider | **PASS** | no anchor import (source and Lake closures); statement byte-identical; elaborated type `rfl`/`==`/untruncated pp.all equal (Expr.equal differs only in 2 hygienic binder names); body exactly the brief's assembly; export used only by the anchor; private imports invisible from the anchor (116 project modules, 1 provider constant) |
| (c) axioms | **PASS** | anchor, provider, assembly, layergardenFlower_v3, layergarden_v2, wkeTaylor, oX2Exp, oX3Cpl, regularAsymptotics: `[propext, Classical.choice, Quot.sound]` |
| (d) hidden hypotheses / vacuity | **PASS** | every input is a `theorem` (real kinds from all olean parts); the 3 assembly binders are discharged exactly by the 3 SEALED anchors; gates = anchor types up to abstracted aux proofs; `toR` sound; Lean non-vacuity witness `kA_prefix` (standard axioms) |
| (e) ABI | **PASS** | pre-seal `3000d181…` reproduced from a local DRAFT build; post-seal `5bf36503…` reproduced; `#print` differs only in the value line; raw `Expr` of the type byte-identical pre/post (sha256 `c186c5b8…`) |
| (f) kernel replay | **PASS (quick mode)** | `REPLAY OK (8363s)`: 218,747 constants / 11,048 modules; no project axiom/opaque/unsafe/partial; no sorryAx/ofReduceBool/trustCompiler user; oleans bound to seal-commit sources via Lake trace hashes (12,022 modules, 0 mismatches); 40,618 VineParam certificate theorems statement-only (quick mode) |
| (g) status fields | **PASS** | DRAFT_ANCHORS 8; UNREGISTERED_SORRIES 0; DRAFT_IMPORT_VIOLATIONS 0; SEALED_THIS_TURN fixedpoint_v2 |
| (h) five-bin table | **PASS** | 45 expanded binders: SOURCE 22, STANDING 8, TYPING 5, RULED 10, **EXCESS 0** |

Dependency named in the brief: `layergardenFlower_v3`'s two keys must PASS before this key can PASS — see "Dependency" at
the end.

---

## (a) Anchor bytes
- History: `git log f78bcabf -- WaveTurbulence/Frozen/Theorems/FixedpointV2.lean` = 8d7ccb4a (freeze, D10), 793a7363
  (seal). `git diff 8d7ccb4a f78bcabf` of the file: exactly one line, `  by sorry` → `  by exact WaveTurbulence.Provider.fixedpoint_v2`.
- DRAFT file sha256 `820c05c32cbdbe7c0cb7a1cb9d06917729895a2770bf84967eb6cb5840ab50b2` (= brief `820c05c3…`); sealed
  file `6bbd2af2bd90945006eb85f52f8a7bfc95b84c785fdea5432f86f65c05c13453`.
- Own recomputation (`hash_anchor.py`, the guard's convention: prefix = bytes up to and including the PROOF_BEGIN line,
  suffix = from the PROOF_END line), identical for the DRAFT and sealed files:
  prefix `9bde11939dfa4f7b8f4de1c19d8f46dfc6d027ade6b01523d8e3219faa41b289`,
  suffix `9f48199048606af986e4911abed0172f6e65c9c8c91f1c2874961ad85a7ea8d0` = manifest. Body bytes
  `'  by exact WaveTurbulence.Provider.fixedpoint_v2\n'` (within the seal limits 3 lines / 240 bytes).
- `python3 -I scripts/check_frozen_anchors.py --root export --manifest export/manifest/frozen.json` → `FROZEN-ANCHOR GUARD
  OK` (check_frozen_anchors.out); `check_lean_modules.py` → `PASS (13118 Lean files, 0 comparator configurations)`.
- Manifest entry, freeze 8d7ccb4a vs seal f78bcabf: differs in exactly `state` (DRAFT_SORRY → SEALED) and `abi_sha256`
  (`3000d181…` → `5bf36503…`); `definition_closure` unchanged; all 114 entries' sha256 match the export. The 114 files are
  unchanged since the D6/D7 freezes (git log: 8d1d2e3b, f2d1fb6b only) and each has a SEALED manifest owner.

## (b) Provider
- `WaveTurbulence/Provider/FixedpointV2.lean` sha256 `884ab221…af1b`. Imports: public Mathlib + the anchor's 14
  `Frozen.Defs.*` (identical list); private `import` of `Frozen.Theorems.{LayergardenFlowerV3, LayergardenV2, WkeTaylor}`
  and `Foundations.XChain.V2Chain.FixedpointV2`. Not the anchor: source closure (12,021 modules incl. the provider) and
  Lake's provider `setup.json` (19,590 modules, 10,559 project) do not contain `Frozen.Theorems.FixedpointV2`.
- Text: the provider's `theorem fixedpoint_v2 : … :=` is byte-identical to the anchor's (2,433 bytes, sha256
  `cd61f432…`); same context lines; no `set_option`/notation/instance/attribute lines in either.
- Elaborated (probe B, provider environment): `example : type_of% @WaveTurbulence.fixedpoint_v2.{u} = type_of%
  @WaveTurbulence.Provider.fixedpoint_v2.{u} := rfl` compiles; `==` true; untruncated `pp.all` text equal (214,891 chars,
  no `⋯`). `Expr.equal` is false, and probe B2 locates the cause: the two types are structurally identical except for 2
  binder names, the hygienic auto-names of the instance binders `[MeasurableSpace Ω]`, `[IsProbabilityMeasure μ]`, which
  embed the module name (`inst._@.WaveTurbulence.Frozen.Theorems.FixedpointV2.…_hyg.17/22` vs
  `inst._@.WaveTurbulence.Provider.FixedpointV2.…_hyg.17/22`). Binder infos equal. Semantically irrelevant.
- The four `let`s (`Ntr`, `Λ`, `ℒ`, `Zs`) elaborate as `letE` with `nonDep = true` (printed `have`) in the anchor, the
  provider, and the pre-seal DRAFT anchor; no let/have or zeta difference.
- Body: the provider's value is exactly `WaveTurbulence.V2Chain.fixedpoint_v2_of_closed_gates_v3.{u}
  WaveTurbulence.layergardenFlower_v3 WaveTurbulence.layergarden_v2 WaveTurbulence.wkeTaylor` (`==` and `Expr.equal` with
  the constructed term; confirmed again in the replay from all olean parts).
- Export used only by the anchor: `Provider.fixedpoint_v2` occurs in Lean code only in the anchor's body; the provider
  module is imported only by the anchor (import graph of 13,117 modules).
- Private imports (probe A1: Lake's anchor `setup.json` + the anchor, module probe importing only the anchor): 116 project
  modules loaded = the 114 `Frozen.Defs` + `Provider.FixedpointV2` + the anchor; the provider module contributes exactly
  `[WaveTurbulence.Provider.fixedpoint_v2]`; `V2Chain.*`, `X2E.*`, `Fixedpt.*`, `Induct.*`, `Flower.*`, `VineEst.*`,
  layergardenFlower_v3, layergarden_v2, wkeTaylor, oX2Exp, oX3Cpl are all absent. Lake's anchor closure (project part) =
  definition_closure ∪ {provider} exactly. So the frozen statement elaborates in its freeze environment; (e) confirms the
  elaborated type did not drift.

## (c) Axioms
`#print axioms` → `[propext, Classical.choice, Quot.sound]` for `WaveTurbulence.fixedpoint_v2`,
`WaveTurbulence.Provider.fixedpoint_v2`, `WaveTurbulence.V2Chain.fixedpoint_v2_of_closed_gates_v3`,
`WaveTurbulence.layergardenFlower_v3`, `WaveTurbulence.layergarden_v2`, `WaveTurbulence.wkeTaylor`,
`WaveTurbulence.X2E.oX2Exp`, `WaveTurbulence.Cpl.oX3Cpl` (probes/out/B.out), `WaveTurbulence.regularAsymptotics` (reached
in the replay; probes/out/C.out); the anchor also in the anchor-only environment (A1.out). The independent check is (f).

## (d) Hidden hypotheses and vacuity
- Proof term: anchor := `Provider.fixedpoint_v2.{u}` := `fixedpoint_v2_of_closed_gates_v3 layergardenFlower_v3
  layergarden_v2 wkeTaylor`. Assembly type `LayergardenFlowerV3Gate → LayergardenV2Gate → WkeTaylorGate →
  FixedpointV2Gate.{u}`. Body: `(fixedpointS_of_parts (cplMomentsS_of_gates (ofR hG') (ofR hL') (ofFull hW') Cpl.oX3Cpl)
  (part2S_of_X2 (flowerest1S_of_gates (ofR hG') X2E.oX2Exp))).toR`, with `hG'`, `hL'`, `hW'` the gates re-typed by
  definitional unfolding (kernel-checked in (f)). Its 3 binders are discharged exactly by the 3 sealed anchors and by
  nothing else. `oX2Exp`, `oX3Cpl` are closed theorems.
- Constant kinds, from all olean parts in the replay: all chain constants listed in (f) are `theorem`, unsafe=false; the
  4 gates are `def`. (Under a plain module import, theorems of other modules appear as `axiomInfo` because their bodies
  are not exported; that is why kinds are taken from the replay, not from probe B.) Reachable `Frozen.Theorems`
  constants: layergarden_v2 (SEALED, D10), fixedpoint_v2 (D10), regularAsymptotics (SEALED, D8), layergardenFlower_v3
  (SEALED, D13), wkeTaylor (SEALED, D7). No DRAFT anchor or DRAFT provider is reachable.
- Gates (`V2Chain/GateTypes.lean`). Text: `FixedpointV2Gate`, `LayergardenV2Gate`, `LayergardenFlowerV3Gate` equal the
  anchors' type text token for token (whitespace-normalised). `WkeTaylorGate := Induct.WkeTaylorGate := WTPrefix
  WkeTaylorBody`. Elaborated (probes B, B2, B3): none is `==` to its anchor's type, but after unfolding the abbrev chain
  (and `WkeTaylorBody`, beta-normalised) EVERY leaf mismatch is a nested instance proof that Lean abstracted into an
  auxiliary theorem `…Gate._proof_N` / `WkeTaylorBody._proof_N` (definition bodies abstract nested proofs, theorem
  types do not) vs the inline proof of the same Prop: 12 / 9 / 3 / 16 mismatches, all of this kind (isProp, isDefEq of
  types), 0 others; `isDefEq` true. Proof-irrelevant, and the kernel accepts the composition anyway (f).
- `WTPrefixS`/`ofR`/`toR` (V2Chain/PrefixS.lean): `ofR`/`ofFull` only thread `γ ∈ S`. `toR` with `1/2 < γ` returns the
  hypothesis's own thresholds; with `γ ≤ 1/2` it returns thresholds 1, 1, 1, 1, 1, 2 and closes the body with
  `absurd hg hr`, where the frozen body is vacuous by design (`1/2 < P.γ →`, D10). No empty universal range is created.
- **Non-vacuity, Lean witness** (probes/ProbeNV.lean → out/NV.out, rc 0; all four theorems `[propext, Classical.choice,
  Quot.sound]`):
  - `kA_gaussian`: Gaussian data exists, `IsGaussianData (Measure.infinitePi fun _ => stdComplexGaussian) (fun n ω => ω n)`.
  - `kA_premises`: for every `P` with `1/2 < γ`, `0 < L`, `0 ≤ δ`, `φin ≥ 0`, `φ 0 = φin`, `1 ≤ 𝔇`, the premises after
    the prefix hold: Gaussian data, `p = 0 < 𝔇`, and `∀ q ≤ 0, AnsatzAt …` with a = initial coefficients,
    Fev = `Induct.initialRapidEvent` (full measure), R = E = Et = 0. This uses the repo's proved `Induct.ansatz_zero`,
    the literal `AnsatzAt … 0` (T L708: (1)–(4) are trivially true at p = 0).
  - `kA_prefix`: for every d ≥ 3, γ ∈ (1/2,1) and every prover choice η₀ > 0, C₁ ≥ 1, ν₀ > 0, δ₀ > 0, C₂ ≥ 1, L₀ ≥ 2,
    the next universal range is non-empty and the premises hold there: η = η₀; φin = 0, τ_* = 1, φ = 0
    (`kA_wke_zero`: `IsWKESolution 0 1 0`); ν = ν₀; D = ⌈δ₀⁻¹⌉₊+1, δ = 1/D ≤ δ₀, τ_* = Dδ; L = L₀.
  So the conclusion is asserted for satisfiable premises at every admissible prover choice. The witness uses zero data;
  for non-zero Schwartz data the sealed `wkelwp` supplies φ, which this audit does not need.

## (e) ABI
- Pre-seal: I rebuilt the DRAFT anchor (8d7ccb4a text, sha256 820c05c3…) and the freeze-time provider stub (sha256
  62a5e5aa…) with `lean --setup` (Lake's anchor setup with the stub substituted; only the registered `sorry` warning).
  `#print` probe (module, `import all`, private oleans: the `abi_hash_setup.py` convention): sha256
  `3000d181f909240df0eecaaac50bfe83cc2e57cab73cd29888a17e475e405031` = manifest DRAFT abi.
- Post-seal (main's build): `5bf365035359eb4f6a93ed13841c83e8a1c4e359585cab017ad8868bc5603900` = manifest (and = the
  dry-run prediction in seal-prep/HANDOFF.md).
- `diff` of the two `#print` outputs: only line 51, `sorry` → `WaveTurbulence.Provider.fixedpoint_v2`.
- Fully explicit type, pre vs post: raw `repr` of the elaborated type `Expr` byte-identical (2,844,881 bytes, sha256
  `c186c5b834a70e8e3a0def69564207f4d6a4d2fc34899c3f51f2f3411ded5dad`); untruncated `pp.all` (pp.maxSteps 10⁹,
  0 `⋯`) identical (214,935 chars); Expr.hash 3573528241 both; letE flags identical. No drift from new imports
  (instances, coercions, notations).
- A non-module `import` probe variant fails under a setup file ("missing data file for module Mathlib"). That variant is
  not needed, since both manifest hashes reproduce by the module method.

## (f) Kernel replay
- Adapted from `<scratch>/seal-lg2/replay/` (Replay.lean sha256 `6c943568…`, read in full). My file
  `replay/exe/Replay.lean` sha256 `0f41db649e3f92d5d0e48c2ca1c1417772ba1dafd45f709a92614373dd747e74`; diff recorded in
  `replay/Replay.diff` (sha256 `88e0b287…`). Changes: root module/constant; `wanted` list and exactness checks for this
  chain; a new `trace` mode; listing of reachable Frozen/Provider constants with real kinds. The replay core
  (closure, base environment, name index, lazy loading, reachability, stub policy, single `Kernel.Environment.replay`, no
  forcing) is unchanged. Driver `replay/replay.sh` (explicit LEAN_PATH = main's Lake path, stock v4.35.0 sysroot,
  `nice -n 10`, 7 index batches).
- **Sources bound** (`replay trace`): closure from olean headers = 22,998 modules (10,976 library, 12,022 project). For
  every one of the 12,022 project modules, Lake's own `computeTextFileHash` of the seal-commit export source equals the
  source hash in the module's `.trace`. All 36,066 olean parts have `computeBinFileHash` among the trace's recorded
  outputs. 0 mismatches (replay/trace.txt).
- **Replay** (replay/Replay-quick.out): base env 661,703 library constants (exported parts, trusted as by
  `importModules`); 248,686 project names indexed; reachable 229,131, MISSING 0; same-name constants in two loaded
  modules 1,647, 0 with a different type/value. `REPLAY OK (8363s): 218747 constants, no shim, no constant turned into
  an axiom`, from 11,048 project modules. Wall 2:20:22; max RSS 6,239,500 KB; rc 0.
- Project AXIOMS reachable `[]`; OPAQUE `[]`; UNSAFE/PARTIAL `[]`; direct users of
  sorryAx/ofReduceBool/trustCompiler/ofReduceNat `[]` (scanned on the original constants); core axioms referenced:
  propext, Classical.choice, Quot.sound. Kinds (before stubbing): 195,129 theorem, 22,086 def, 582 inductive, 799 ctor,
  151 rec.
- EXACT checks inside the replay: anchor value = `Provider.fixedpoint_v2.{u}` (true); provider value = the assembly
  (true); provider type `==` anchor type (true; `Expr.equal` false only for the hygienic binder names, see (b)).
- **Quick-mode caveat:** 40,618 `WaveTurbulenceVineParam` certificate theorems, whose proofs use no project constant
  outside that library, were checked by statement only (inserted as axioms in the replay environment). 92,875 VineParam
  theorems with cross-library proofs were replayed with their proofs. The stubbed proofs were still traversed for
  reachability and scanned for sorryAx/ofReduceBool/trustCompiler (none). The replay script's message "no constant turned
  into an axiom" means that no constant was converted after a kernel failure; the quick-mode statement-only policy is
  separate and declared in advance. AUDIT-COMMON requires "quick mode at least". A full-mode replay was not run.

## (g) Status fields (at the seal commit f78bcabf)
- **DRAFT_ANCHORS: 8.** All under `WaveTurbulence/Frozen/Theorems/`: `main_v1` Main.lean, `fixedpoint_v1`
  Fixedpoint.lean, `layergarden_v1` Layergarden.lean, `layergardenFlower_v1` LayergardenFlower.lean, `propansatz_v1`
  Propansatz.lean, `main_v2` MainV2.lean, `propansatz_v2` PropansatzV2.lean, `layergardenFlower_v2`
  LayergardenFlowerV2.lean. There were 9 before this seal (1e51bebf) and are 6 at final main 1987105a.
- **UNREGISTERED_SORRIES: 0.** The guard is OK. My own comment- and string-stripped scan finds exactly 8 `sorry`, each the
  registered body of one of the 8 DRAFT anchors. It also finds 0 `axiom` declarations and 0
  unsafe/implemented_by/extern/native_decide/ofReduceBool tokens.
- **DRAFT_IMPORT_VIOLATIONS: 0.** In my own import graph, no module imports a DRAFT anchor, and each DRAFT provider is
  imported only by its anchor. `FixedpointV2` left the lakefile quarantine and is imported by the root.
- **SEALED_THIS_TURN: fixedpoint_v2** (793a7363 + f78bcabf), the second seal of the chain: layergardenFlower_v3
  (e8019624/1e51bebf), fixedpoint_v2, propansatz_v2 (a2216712/7d98ae17), main_v2 (b9711f35/1987105a). At f78bcabf:
  19 sealed theorems, 319 SEALED entries among 327.

## (h) Five-bin binder table
Source reconstruction written first (`01-source-reconstruction.md`, sha256 `eb67331c…`); the TeX re-hashed to
`493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb`. Rulings: D6, D7 (WAVE-B §4.1/§4.3 deviations), D9,
D10, D13, E1, E34. The full table (45 rows, one per expanded binder of `WTPrefix`, `IsWKESolution`, `IsGaussianData`,
`AnsatzAt`) is in `02-binder-table.md` (sha256 `ef77494b…`), summarised here:

| Rows | Binders | Bin |
|---|---|---|
| 1, 3, 21, 22, 24 | `d`, `γ`, `Ω`+σ-algebra, `μ`+probability, `g n` measurable | TYPING (5) |
| 2, 4, 6, 7, 11, 12 | `3 ≤ d`, `γ ∈ (0,1)`, `φin` Schwartz, `φin ≥ 0`, `φ 0 = φin`, WKE equation | SOURCE (L277, L292, L299–L307, L314) |
| 5, 13–19 | η (after η₀), C₁, ν (after ν₀), δ (after δ₀), `D ≥ 1`, `τ_* = Dδ`, C₂, L (after L₀ ≥ 2) | STANDING (L604–L611, L687; (Π) D7) |
| 8, 9, 10 | `τ_* > 0`, `φ`, `ContinuousOn φ [0,τ_*]` | RULED D6 |
| 20 | `1 / 2 < P.γ` | RULED D9, D10, E1 |
| 23, 25, 26 | `g`, `iIndepFun g μ`, law = `stdComplexGaussian` | SOURCE, SOURCE (L292), RULED D6 |
| 27–32 | `p < 𝔇`, `a`, `Fev`, `R` (on ℝ^d: RULED D7 §4.1 (D1)), `E`, `Et` | SOURCE (L689, L708) ×5, RULED ×1 |
| 33–45 | `AnsatzAt q` for q ≤ p: Fev measurable (RULED); symmetric, decreasing, ℙ ≥ 1−e^{−N_q}, classed unique solution, 𝔖-bound on R, bound on E, two-point identity, cumulant expansion (3), order-N bound (4) (SOURCE, L689–L705, L708); a measurable, products integrable, (2') intermediate times (RULED, D7 §4.1 (D3)/(D5), ERRATA §C) | SOURCE 9, RULED 4 |

**Counts: SOURCE 22 · STANDING 8 · TYPING 5 · RULED 10 · EXCESS 0.** Quantifier order matches (Π); no threshold can depend
on p, the data, the events or the ansatz objects. The conclusion matches (fixedest1)–(fixedest4) and the event clause of
T L780–L794 with the D7 §4.3 deviations (D1) ½-contraction, (D2) continuity in Z, (D3) explicit middle conjugate (F9),
(D4) unique solvability. Exponents, windows, the lattice carrier and ⟨k⟩ all match. The v2 anchor is the D7-approved
`fixedpoint` verbatim except for the name, `1 / 2 < P.γ →`, one docstring paragraph and the provider import (diff
checked; D10).

### Comparison with the brief's claim appendix (opened after the table)
Agreement: EXCESS 0; `1/2 < γ` RULED (D9, D10, E1); `p < 𝔇` SOURCE; Ω/μ TYPING; the conclusion's seven conjuncts.
Differences (none changes the verdict):
1. The appendix does not expand `WTPrefix`, `IsGaussianData` or `AnsatzAt` (one "bundle" row each), although
   AUDIT-COMMON (h) requires recursive expansion. My table has 45 rows against its 6.
2. `WTPrefix` bundle: the appendix bins all of it STANDING. I bin `d ≥ 3`, `γ ∈ (0,1)`, `φin` Schwartz/`≥ 0` and the WKE
   initial condition and equation SOURCE (explicit in Theorem 1.1, L314), `τ_* > 0`, `φ` and `ContinuousOn` RULED (D6),
   and only the constant/threshold choices STANDING.
3. `IsGaussianData`: the appendix bins it SOURCE. I split it: measurability TYPING, i.i.d. SOURCE, the circular complex
   Gaussian law RULED (D6).
4. Induction hypothesis: the appendix bins all of `AnsatzAt` SOURCE and cites "WAVE-B v2 §4.3". `AnsatzAt`'s deviations
   are those of `propansatz`, i.e. WAVE-B §4.1, not §4.3 (fixedpoint's own). Four conjuncts are not in T's (1)–(4) and
   are D7-ruled additions: measurability of `Fev q` and of `a`, integrability of products, and item (2') (intermediate
   times, constant 2). I bin these RULED, along with `R` on ℝ^d. They are not EXCESS: they are part of the
   author-approved `propansatz` (D7), and the same induction (`propansatz_v2`) produces them.

### Comparison with the seal script's logs (seal-prep/logs/live-20261108T193926Z, read after my results)
Agreement: pre-seal ABI control `3000d181…`, post-seal `5bf36503…`, print diff `sorry` → `…Provider.fixedpoint_v2`,
axioms, guard/module checks, recheck "frozen diff vs freeze 8d7ccb4a = body only; manifest fields ['abi_sha256',
'state']; DRAFT_SORRY anchors now 8". Disagreements and observations:
1. The script's "SAME TEXT OK (1626 lines)" (pre vs post `pp.all`) and "PROVIDER TYPE TEXT = ANCHOR TYPE TEXT (pp.all)"
   compared **truncated** renderings: `fixedpoint_v2.{pre,post}.typeall.out` and `exact.out` each contain 30 `⋯`
   (default `pp.maxSteps`). That check is weaker than stated. My untruncated `pp.all` and raw-`Expr` comparisons show
   identity, so there is no consequence for this seal.
2. The run log ends with `SEAL ABORT: full ABI check` — `probe failed for WaveTurbulence.Mom`, caused by the elan
   override notice on stderr, which `abi_hash.py` treats as failure — and `RESULT: ABORTED`. The brief states "full
   327-anchor ABI OK" at 1987105a, but I found no log of a successful full run. The full 327-anchor check is not one of
   this key's items; this anchor's own ABI is reproduced in (e). wt-orch should confirm where the full check ran.

## Dependency: `layergardenFlower_v3` keys
The brief makes this key's PASS conditional on both keys of `layergardenFlower_v3`, this chain's first seal. Status files
(read 2026-11-09 00:15 UTC): `SEALAUDIT-layergardenFlower_v3-A.txt` = `PASS layergardenFlower_v3 A` (00:05:48 UTC),
`SEALAUDIT-layergardenFlower_v3-B.txt` = `PASS layergardenFlower_v3 B` (00:14:56 UTC). The other consumed sealed anchors
have recorded PROVED evidence: `layergarden_v2` (docs/campaign/orch/audits/Seal-layergarden_v2.md: "may be recorded as
PROVED"); `wkeTaylor` (<scratch>/audit-b2a, cited by the brief); `regularAsymptotics` is SEALED (D8). My
replay re-checked all of their proof closures in the kernel ((f), quick mode).

## Evidence files (all under <scratch>/seal-audit-fixedpoint_v2-A/; sha256)
- 01-source-reconstruction.md `eb67331c…`; 02-binder-table.md `ef77494b…`; 03-results-a-e-g.md `386bd7c7…`;
  04-results-d-f.md `f935dac8…` (written before the claim appendix and the logs were opened).
- hash_anchor.py `6e71bd6e…`; scan_sorry.py `083e1ce8…`; imports.py `2fb31838…`; check_frozen_anchors.out `1cf180b6…`;
  check_lean_modules.out `2fc9dd2a…`; draft-FixedpointV2.lean (= 820c05c3…); manifest-freeze.json.
- probes/gen_setup.py `bec2ea0d…`; ProbeA1 `f1ffd892…` → out/A1.out `511144ad…`; ProbeB `cc12f787…` → out/B.out
  `ea0b1e3d…`; ProbeB2 `222f53bc…` → out/B2.out `4f0dd565…`; ProbeB3 `f4a9a94e…` → out/B3.out `1e255531…`;
  ProbeNV `783f30a9…` → out/NV.out `1b81164…`; ProbeC `a6f80f1f…` → out/C.out `9cfd8890…`; AbiMod.lean `20af3bbd…` →
  out/abi-pre-mod.out (sha256 = 3000d181…), out/abi-post-mod.out (sha256 = 5bf36503…); PPFull-{pre,post}.lean →
  out/type-repr-{pre,post}.txt (both `c186c5b8…`), out/ppfull-{pre,post}.out; draft/src/{FixedpointV2 `820c05c3…`,
  ProviderFixedpointV2 `62a5e5aa…`}.lean and their local oleans in draft/lib.
- replay/exe/Replay.lean `0f41db64…`; replay/Replay.seal-lg2.lean `6c943568…`; replay/Replay.diff `88e0b287…`;
  replay/replay.sh `f49945d0…`; replay/Replay-quick.out `ba62138f…`; replay/trace.txt `bab18780…`.

`fixedpoint_v2` may be recorded as PROVED (key A)
