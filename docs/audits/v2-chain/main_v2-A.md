# SEAL AUDIT — `main_v2`, KEY-A (refute-first, independent)

- Auditor: KEY-A (Claude Opus 5.5), 2026-11-08. I wrote none of the anchor, the provider, the proof chain or the seal script.
- Subject: frozen anchor `WaveTurbulence.main_v2` (`WaveTurbulence/Frozen/Theorems/MainV2.lean`), Deng–Hani Theorem 1.1
  restricted to 1/2 < γ < 1 (D9, D10, E1).
- Commits (origin/main = HEAD of <repo>, clean): seal `b9711f351cebf8346c030fe5aaf122c95c92b57a`
  ("Seal main_v2 with its proved assembly"), ABI `1987105ac00b88c879ffebf4a56e30aa02b4f92f` ("manifest: ABI hash of the
  sealed main_v2"). Freeze `8d7ccb4a` (D10).
- Clean export: `git archive 1987105a` → `<scratch>/seal-audit-main_v2-A/export/`.
- Work dir: `<scratch>/seal-audit-main_v2-A/` (all probes, tools and logs referenced below are there).
- Machine discipline: one Lean process at a time, `nice -n 10`; no Lake invocation and no write in the main checkout.

## Verdict table

| Item | Verdict | One-line evidence |
|---|---|---|
| (a) Anchor bytes | PASS | Only the proof body changed since 8d7ccb4a (`by sorry` → `by exact WaveTurbulence.Provider.main_v2`); prefix `67762ca2…` and suffix `9f481990…` recomputed = manifest at freeze and seal; manifest entry changed in exactly `state`, `abi_sha256`; 12/12 closure hashes OK; guard OK, module check PASS on the clean export |
| (b) Provider | PASS | No import of the anchor (source, and Lake's resolved closure of 308 project modules); conclusion bytes identical (sha256 `cdb500ff…`); exactly the four binder adaptations; conclusions `Expr.equal` after erasing macro scopes and pp.all-identical; type_of% example compiles; anchor value `Expr.equal` to `fun d hd γ hγ => @Provider.main_v2.{u} d hd γ hγ`; body = registered assembly; export used only by the anchor; proof modules private and invisible from an anchor-only module import |
| (c) Axioms | PASS | `#print axioms` of anchor, provider, assembly, `propansatz_v2`, `nlsAkBridge` and the 10 named inputs: `[propext, Classical.choice, Quot.sound]` each |
| (d) Hidden hypotheses / vacuity | PASS | Provider = assembly applied to the sealed `propansatz_v2`, `nlsAkBridge` and the anchor's own d, hd, γ, hγ; all 40 direct inputs of the assembly are theorem/def/inductive/ctor by real kind (14 theorems incl. the 10 named); whole closure kernel-replayed with no axiom/opaque/sorry; θ = η₀^20 fixed before φin (T L612); probability bound via N_D ≥ (log L)^{40d}; every premise after the prefix has a compiled witness (`witness/Witness.lean`) |
| (e) ABI | PASS | pre-seal `36fb4c1d…` and post-seal `21103400…` reproduced (two probe methods each); `#print` outputs differ only in the value line; elaborated type identical as raw `Expr` (repr sha256 `431987c5…`) and pp.all (`cb5fdac3…`) between my freeze rebuild and the sealed build |
| (f) Kernel replay | PASS | `REPLAY OK (8544s): 219644 constants, no shim, no constant turned into an axiom` (quick mode; 40618 VineParam-internal certificate proofs checked by statement only); 11207 project modules; 0 project axioms/opaque/unsafe/partial; 0 direct users of sorryAx/ofReduceBool/trustCompiler/ofReduceNat; wall 2:23:10, max RSS 6.27 GB; all 11207 modules: seal-commit source = trace source hash and olean bytes = trace outputs |
| (g) Status fields | PASS | DRAFT_ANCHORS 6 (paths below); UNREGISTERED_SORRIES 0; DRAFT_IMPORT_VIOLATIONS 0; SEALED_THIS_TURN = [main_v2] (README's status block is stale; note N2) |
| (h) Five-bin table | PASS | 24 SOURCE / 0 STANDING / 8 TYPING / 4 RULED / **0 EXCESS** |

## (a) Anchor bytes — PASS

- History: `git log -- WaveTurbulence/Frozen/Theorems/MainV2.lean` = 8d7ccb4a (freeze, D10), b9711f35 (seal). Nothing else.
- `git diff 8d7ccb4a 1987105a -- WaveTurbulence/Frozen/Theorems/MainV2.lean` changes exactly one line, between the
  `FROZEN_ANCHOR_PROOF_BEGIN/END` markers: `  by sorry` → `  by exact WaveTurbulence.Provider.main_v2`.
- My own re-implementation of the guard's region convention (`tools/region_hash.py`: prefix = bytes up to and including
  the newline ending the PROOF_BEGIN line; suffix = bytes from the start of the PROOF_END line):

  | | file sha256 | prefix sha256 | suffix sha256 |
  |---|---|---|---|
  | freeze 8d7ccb4a | `af132464…cac600` (= brief's DRAFT `af132464…`) | `67762ca2a9dd62d2a5c50525c7b761f6c26a71a27519ff41a6f6032aa76b55f3` | `9f48199048606af986e4911abed0172f6e65c9c8c91f1c2874961ad85a7ea8d0` |
  | seal 1987105a | `000671e0…0ab3` | identical | identical |
  | manifest | — | `67762ca2…55f3` | `9f481990…a8d0` |
- Manifest entry `main_v2`, 8d7ccb4a → 1987105a (`tools/manifest_diff.py`): changed keys exactly `state`
  (DRAFT_SORRY → SEALED, in b9711f35) and `abi_sha256` (`36fb4c1d…` → `21103400…`, in 1987105a). All other keys
  (path, export, implementation, source, contract, split_policy, prefix/suffix, draft_allowlist, closure) unchanged.
- `definition_closure`: 12/12 files re-hashed in the export = manifest (Mom, LatticePoint, CollisionOp, IsWKESolution,
  PartialDeriv, NormLaplacian, TorusFourierCoeff, IsSmoothNLSSolution, StdComplexGaussian, InitialCoeff,
  SolvableEvent, KineticTime); each file's only commit is the D6 freeze 8d1d2e3b. The closure is complete: these are
  exactly the project definitions in the anchor's type (checked against the elaborated type).
- `check_index.sh` needs a git index; on the clean export I ran its two steps directly:
  `python3 -I scripts/check_frozen_anchors.py --root . --manifest manifest/frozen.json` → `FROZEN-ANCHOR GUARD OK`
  (rc 0); `python3 -I scripts/check_lean_modules.py` → `check_lean_modules: PASS (13118 Lean files, 0 comparator
  configurations)` (rc 0). Log: `logs/guard-and-modules.out`.
- The seal commit b9711f35 touches exactly 5 files: the anchor (1 line), the provider, `WaveTurbulence.lean` (+1 root
  import of the sealed anchor), `lakefile.lean` (−1 quarantine line: `Frozen.Theorems.MainV2`, `Provider.MainV2`),
  `manifest/frozen.json` (state). 1987105a touches only the manifest (`abi_sha256`).

## (b) Provider — PASS

Provider `WaveTurbulence/Provider/MainV2.lean` (sha256 `6fd8687c…36c0`), export `WaveTurbulence.Provider.main_v2`.

1. **No import of its own anchor.** Source imports: `public import` Mathlib + the anchor's 12 `Frozen.Defs.*`;
   `import` (private) `Frozen.Theorems.PropansatzV2`, `Frozen.Theorems.NlsAkBridge`, `Foundations.XChain.V2Chain.MainV2`.
   Lake's resolved closure (`.lake/build/ir/WaveTurbulence/Provider/MainV2.setup.json`, 9339 modules, 308 project
   modules) does not contain `WaveTurbulence.Frozen.Theorems.MainV2`.
2. **Statement = anchor's.** Conclusion text after the binder header is byte-identical (1119 bytes, sha256
   `cdb500ff74664480c217fcf9a6103897a2b9a9b21a8be83b5156765e31ae931f`, `tools/concl_cmp.py`). Elaborated (probe
   `exprs/Post.lean`, log `exprs/Post.out`): binder table

   | # | anchor | provider | after unwrapping `autoParam` |
   |---|---|---|---|
   | 0 | `(d : ℕ)` default | `{d : ℕ}` implicit | types `Expr.equal` |
   | 1 | `(hd : 3 ≤ d)` default | `(hd : autoParam (3 ≤ d) Provider.main_v2._auto_1)` default | `Expr.equal` |
   | 2 | `(γ : ℝ)` default | `{γ : ℝ}` implicit | `Expr.equal` |
   | 3 | `(hγ : γ ∈ Ioo (1/2) 1)` default | `(hγ : autoParam (γ ∈ Ioo (1/2) 1) Provider.main_v2._auto_3)` default | `Expr.equal` |

   Exactly the four adaptations of the brief, nothing else; names, order and level params (`[u]`) identical.
   Conclusions instantiated with the same four fvars: strict `Expr.equal` = false **only** because Lean's hygienic
   names of the anonymous instance binders `[MeasurableSpace Ω]`, `[IsProbabilityMeasure P]` embed the module name
   (`inst._@.WaveTurbulence.Frozen.Theorems.MainV2._hyg.217` vs `inst._@.WaveTurbulence.Provider.MainV2._hyg.217`);
   after erasing macro scopes from binder names, `Expr.equal` = true; pp.all text identical (72466 chars). (The
   same hygiene effect made a re-elaboration of the anchor text under a probe module name differ only in these two
   names, probe P1b, `Expr.eqv` true; under the true module name the elaboration is byte-identical, see (e).)
3. `example : type_of% @WaveTurbulence.main_v2.{u} := fun d hd γ hγ => @WaveTurbulence.Provider.main_v2.{u} d hd γ hγ`
   compiles (in `exprs/Post.lean`).
4. **Anchor value** (`import all` of the anchor): `fun d hd γ hγ => WaveTurbulence.Provider.main_v2 hd hγ`, and it is
   `Expr.equal` (binder names, binder info and types included) to
   `fun (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (1/2) 1) => @Provider.main_v2.{u} #3 #2 #1 #0`: the auto-params are
   filled by the anchor's own `hd`, `hγ` (bound variables of the value; nothing else in scope). Constants used by the
   value: only `Provider.main_v2` plus the core/Mathlib constants of the binder types.
5. **Body = registered assembly.** Source body is exactly
   `WaveTurbulence.MainGlue.main_v2_of_propansatz WaveTurbulence.propansatz_v2 WaveTurbulence.nlsAkBridge d hd γ hγ`;
   elaborated value `fun {d} hd {γ} hγ => MainGlue.main_v2_of_propansatz propansatz_v2 (fun {d} => nlsAkBridge) d hd γ hγ`
   (the `fun {d} =>` is the elaborator's eta-expansion of the implicit binder of `NlsAkBridgeGate`).
6. **Export used only by the anchor.** `grep -rn 'Provider\.main_v2\|Provider.MainV2' --include=*.lean` over the whole export (all libraries, root, lakefile):
   only `Frozen/Theorems/MainV2.lean` (import + body) and the provider's own docstring.
7. **Private proof modules; anchor-only view.** Lake's resolved closure of the anchor
   (`.lake/build/ir/WaveTurbulence/Frozen/Theorems/MainV2.setup.json`) has exactly 13 project modules: the 12
   `Frozen.Defs.*` and `Provider.MainV2`. Module probe P1 (`probes/P1_anchor_env.lean`, my own setup generator
   `tools/mksetup.py`, log `logs/P1.out`) importing only the anchor: loaded project modules = those 13 + the anchor;
   `MainGlue.main_v2_of_propansatz`, `propansatz_v2`, `nlsAkBridge`, `V2Chain.PropansatzV2Gate`,
   `V2Chain.NlsAkBridgeGate`, `MainGlue.ceiling_subdivision` all **absent**; `Provider.main_v2`, `main_v2` present.
   The anchor's freeze environment differs from the seal environment only by the provider's single public theorem
   (the freeze stub had no declaration); (e) shows the elaborated statement is byte-identical.
   Note: a *non-module* importer does load the whole private closure (that is what exceeds vm.max_map_count, as the
   brief says); this does not affect the anchor's own elaboration, which Lake performs with the 13-module closure.

## (c) Axioms — PASS

Module probe `ax/Ax.lean` (setup: provider's Lake closure + anchor; `import all` for the anchor, provider and assembly
modules), log `ax/Ax.out`: each of `WaveTurbulence.main_v2`, `Provider.main_v2`, `MainGlue.main_v2_of_propansatz`,
`propansatz_v2`, `nlsAkBridge`, `MainGlue.{ceiling_subdivision, schwartz_lattice_sum_le, eventually_final_exponent,
induction_error_absorption, gate_solvable_measurability, ansatz_solvable_probability, exists_ansatz_step,
ansatz_observable_error, hasLaw_stdComplexGaussian}`, `NLS.kineticTime_rpow_neg_pos` "depends on axioms: [propext,
Classical.choice, Quot.sound]". As COMMON notes, this reads precomputed per-module data; (f) is the independent check.
Observation: in a module import without `all`, imported theorems are presented as `axiomInfo` (module-system public
view); real kinds must be read from all olean parts, which (f) does.

## (e) ABI — PASS

- **Pre-seal (freeze build) reproduced.** I rebuilt the freeze state under its true module names in my directory
  (`fz/`): the freeze provider stub (8d7ccb4a, sha256 `0d0e01ee…ee85`, no declarations) and the DRAFT anchor
  (sha256 `af132464…`), compiled with `lean --setup` against main's Mathlib + 12 Defs (toolchain and
  lake-manifest unchanged between 8d7ccb4a and 1987105a; only lakefile quarantine lines differ). Canonical method of
  `scripts/abi_hash.py` (non-module probe `import M` / `#print export`, LEAN_PATH resolution) →
  `36fb4c1dd04ff1330839fb9cb4d465fee163bf52dcc6efb3471d8f5c577a8da4` = manifest DRAFT value (`abi/pre-seal.print`).
  Module-probe method (`import all`, own setup) on the same build → same hash (`abi/preM.print`).
- **Post-seal reproduced.** The non-module probe on main's build fails (`failed to read file …J1VI031.olean.private`:
  the full private closure exceeds vm.max_map_count). Module probe with my own setup (anchor + its Lake closure;
  private part of the anchor only, variant A; or of all 14 project modules, variant B, the `abi_hash_setup.py`
  convention) → `2110340043ade661f13a79379c82904919645a1d2cc59f3650fe539e27b75272` both = manifest.
- `diff abi/pre-seal.print abi/postA.print`: one line (37): `fun d hd γ hγ => sorry` →
  `fun d hd γ hγ => WaveTurbulence.Provider.main_v2 hd hγ`.
- Elaborated type, freeze build vs sealed build (`exprs/Pre.lean`, `exprs/Post.lean`): `repr` of the type
  byte-identical (706664 bytes, sha256 `431987c506529062d369527cfb7b4f2247c07b679113fb00d834542fbc334b57`, including
  hygienic binder names); pp.all identical (sha256 `cb5fdac339081ee7dd28502d07b5912b61d5a99af9b1962c5d304891f17bbe8b`).
  No drift (instances, coercions, notations) from the seal's imports.
- `scripts/abi_hash_setup.py` audited: it adds `.olean.private` for every project module of the anchor's Lake
  closure and uses `import all <anchor>`; my variant A (private part of the anchor only) gives the same hash, so the
  extra private parts do not affect the output here.

## (g) Status fields — PASS

Computed independently from the manifest and sources at 1987105a (`tools/status_fields.py`, `logs/status-fields.out`):
- **DRAFT_ANCHORS: 6** — `main_v1` (`Frozen/Theorems/Main.lean`), `fixedpoint_v1` (`Fixedpoint.lean`),
  `layergarden_v1` (`Layergarden.lean`), `layergardenFlower_v1` (`LayergardenFlower.lean`), `propansatz_v1`
  (`Propansatz.lean`), `layergardenFlower_v2` (`LayergardenFlowerV2.lean`). Manifest: 327 anchors = 27 theorems + 300
  definitions; 321 SEALED (21 theorems incl. `main_v2`), 6 DRAFT_SORRY.
- **UNREGISTERED_SORRIES: 0** — guard OK, and my own comment/string-masked token scan finds 6 `sorry`/`admit` tokens,
  exactly one in each DRAFT anchor file, none elsewhere.
- **DRAFT_IMPORT_VIOLATIONS: 0** — no module imports a DRAFT anchor module; no module other than its own anchor imports
  a DRAFT anchor's provider; all 6 DRAFT anchors remain in the lakefile quarantine and are not imported by the root.
- **SEALED_THIS_TURN: [`main_v2`]** — the only state change between 7d98ae17 (parent of the seal) and 1987105a.

## (d) Hidden hypotheses and vacuity — PASS

**Proof term.** `main_v2 = fun d hd γ hγ => Provider.main_v2 hd hγ` (b4);
`Provider.main_v2 = fun {d} hd {γ} hγ => MainGlue.main_v2_of_propansatz propansatz_v2 (fun {d} => nlsAkBridge) d hd γ hγ`.
`main_v2_of_propansatz` (`Foundations/XChain/V2Chain/MainV2.lean`, sha256 `70a777e8…756a`) has exactly the binders
`(hpropansatz : V2Chain.PropansatzV2Gate) (hnlsAkBridge : V2Chain.NlsAkBridgeGate) (d) (hd) (γ) (hγ)`; the provider
discharges them with the two SEALED anchors and the anchor's own four binders — nothing else. The gate abbreviations
are definitionally equal to the anchors' types (`isDefEq` true, probe `gatediff/GateDiff2.lean`); they are not
syntactically equal because the anchors carry the inline `AtLeastTwo` instance proof `Nat.instAtLeastTwoHAddOfNat 1 …`
where `GateTypes` has Lean's abstracted auxiliary theorem `V2Chain.LayergardenV2Gate._proof_1` (proof-irrelevant;
a `theorem` in the closure).

**Inputs of the assembly, by real kind** (replay, all olean parts; `ASSEMBLY-INPUT` lines of `replay/Replay-quick.out`):
14 theorems — the 10 named in the brief (`MainGlue.ceiling_subdivision`, `schwartz_lattice_sum_le`,
`eventually_final_exponent`, `induction_error_absorption`, `gate_solvable_measurability`,
`ansatz_solvable_probability`, `exists_ansatz_step`, `ansatz_observable_error`, `hasLaw_stdComplexGaussian`,
`NLS.kineticTime_rpow_neg_pos`) plus the compiler-generated `WTPrefix._proof_1`, `V2Chain.LayergardenV2Gate._proof_1`,
`main_v2_of_propansatz._proof_1_1` (private) and the equation lemma `WTParams.Rdown.eq_1` — and 24 defs (the two gates,
frozen definitions and `WTParams` projections), 1 inductive (`WTParams`), 1 constructor. No axiom, opaque, variable or
hypothesis. `propansatz_v2`, `nlsAkBridge`, `Provider.propansatz_v2`, `Provider.nlsAkBridge` are theorems (CHAIN lines).
Frozen theorem anchors reachable from `main_v2` (replay): `nlsAkBridge`, `layergarden_v2`, `propansatz_v2`,
`fixedpoint_v2`, `regularAsymptotics`, `layergardenFlower_v3`, `wkeTaylor`, `main_v2` — all SEALED in the manifest;
no DRAFT_SORRY anchor is reachable.

**Parameters against the source.**
- `θ := η₀ ^ 20`, with `η₀` from `hpropansatz d hd γ ⟨…⟩` (`WTPrefix`: `∀ d, 3 ≤ d → ∀ γ ∈ Ioo 0 1 → ∃ η₀ > 0, ∀ η ∈ Ioc 0 η₀,
  ∀ φin …`). The term `η₀ ^ 20` is formed before `intro φin hφ τstar hτ φ hsol`, so it depends only on (d, γ), as
  the statement's `∃ θ` position also enforces. Source: T L612 "We choose the θ in Theorem main as θ = η^{20}" (the
  brief cites L611, which is the line defining θ_p = η^{20}(1+2^{-p}); the sentence is on L612). The frozen
  `WTParams.theta p = η^20 (1 + 2⁻¹^p)` matches T L611; θ = η^20 < θ_p for all p.
- Probability: `hN : (log L)^{40d} ≤ N_D` (from `eventually_final_exponent`; frozen `Rdown 0 = ⌊(log L)^{40d}⌋₊`,
  `R p = Rdown (D − p)`, `N p = R p ^ (40d)`, so N_D = ⌊(log L)^{40d}⌋^{40d}: T L612 (parameters2)) and
  `hpr : 1 − e^{−N_D} ≤ P(F)` (`ansatz_solvable_probability`); hence `1 − e^{−(log L)^{40d}} ≤ 1 − e^{−N_D} ≤ P(F)`
  (`sub_le_sub_left (exp_le_exp.mpr (neg_le_neg hN))`), matching T L316.
- L₀ = max(L_base, L_prob, L_abs) is chosen after φin, τ★, φ, D, δ (T L316 "sufficiently large L").

**Meaning (D6 readings).** `solvableEvent` = {ω | ∃ u, IsSmoothNLSSolution L α T (initialCoeff L φin g ω) u};
`IsSmoothNLSSolution` = C^∞ (checked: `IsSmoothNLSSolution … ↔ ContDiffOn ℝ ∞ … ∧ …` holds by `Iff.rfl` with
`open scoped ContDiff`, so the order is `∞`, not analytic `ω`), L-periodic, initial Fourier coefficients = data, NLS
pointwise; `initialCoeff L φin g ω n = √(φin(n/L))·g n ω` (DAT); selection `∀ U, (∀ ω ∈ F, IsSmoothNLSSolution … (U ω)) → …`;
expectation `∫ F.indicator (‖û‖²) dP` (D6: 𝔼[1_F ·]). `nlsAkBridge` (3) gives uniqueness of smooth solutions, so the
integrand on F does not depend on the selection; (4) gives its measurability.

**Non-vacuity — every premise after each prover choice is satisfiable** (all compiled in `witness/Witness.lean`,
sha256 `6984580b…e027`, rc 0, no `sorry`; log `witness/Witness.out`):
- d = 3, γ = 3/4: `3 ≤ 3 ∧ 3/4 ∈ Ioo (1/2) 1`.
- After `∃ θ`: φin = 0 (nonneg) with τ★ = 1 and φ ≡ 0: `IsWKESolution 0 τ (fun _ => 0)` (`w_wke_zero`). For an
  arbitrary Schwartz φin (e.g. the nonzero nonnegative bump `w_nonzero_datum`, φin(0) = 1) some τ★ > 0 and a solution
  exist (`w_wke_exists`, from the sealed `wkelwp`: 0 < τmax and τ★ < τmax ↔ ∃ φ, IsWKESolution φin τ★ φ).
- After `∃ L₀`: `∀ L ≥ L₀` is nonempty (L = max L₀ 2); α, T are determined by their equations.
- Probability premises: Ω = (Fin d → ℤ) → ℂ, P = `Measure.infinitePi (fun _ => stdComplexGaussian)`, g n ω = ω n:
  probability measure, measurable coordinates, `iIndepFun`, each law `stdComplexGaussian` (`w_gauss`).
- Selection premise: a U exists for every (L, α, T, φin, g) (`w_select`, by choice on F).
- Time premise: 0 ∈ Icc 0 (τ★·kineticTime α) (`w_time`).
- The conclusion is not trivial: for L > 1, `0 < 1 − exp(−(log L)^{40d})` (`w_prob_pos`), so F has positive
  probability and the expectation bound constrains genuine smooth solutions.

## (f) Kernel replay — PASS

Adapted from `<scratch>/seal-lg2/replay/` (`Replay.lean` sha256 `6c943568…e98e`, `replay.sh`
`b8298ed6…5caa`, both read first). My versions: `replay/exe/Replay.lean` (sha256 `389ab36f…9c1f`) and
`replay/replay.sh` (`f8d4854d…aa3c`); diffs recorded in `replay/replay-diff-vs-lg2.patch` and
`replay/replaysh-diff-vs-lg2.patch`. Changes: root module `WaveTurbulence.Frozen.Theorems.MainV2`, root
`WaveTurbulence.main_v2`; `wanted` list = the main_v2 chain; exactness block for main_v2 (anchor/provider values,
gate equalities); real kinds of every direct input of the assembly; reachable modules written out for the hash check;
LEAN_PATH set explicitly (no `lake env`, no Lake in the main checkout); real v4.35.0 toolchain first on PATH;
`nice -n 10`. Replay logic unchanged: library constants (exported parts) inserted unchecked as the trusted base;
every reachable project constant (types + values, inductives with ctors/recursors) sent once to
`Kernel.Environment.replay`; quick mode stubs only WaveTurbulenceVineParam theorems whose proofs use no constant
outside that library.

Result (`replay/Replay-quick.out`, sha256 `c0349c2c…a2d2`):
- closure: 23129 modules (10976 library, 12153 project); reachable project modules 11207; reachable constants 230216
  (219644 project constants replayed: 585 inductive, 802 ctor, 22173 def, 195933 theorem, 151 rec before stubbing);
  MISSING 0; same-name constants in two loaded modules 1673, of which with a different type/value 0.
- project AXIOMS reachable: [] · OPAQUE: [] · UNSAFE/PARTIAL: [] · direct users of sorryAx/ofReduceBool/
  trustCompiler/ofReduceNat: [] · core axioms referenced directly: Quot.sound, Classical.choice, propext.
- quick-mode stubs: 40618 VineParam-internal certificate theorems checked by statement only; 92875 VineParam theorems
  replayed with proofs (cross-library).
- **`REPLAY OK (8544s): 219644 constants, no shim, no constant turned into an axiom`**; wall 2:23:10, max RSS
  6268300 kB, rc 0.
- **Replayed oleans = seal commit's sources** (`tools/tracecheck.py`, `tools/lakehash.c`, my C re-implementation of
  Lake's hashes — MurmurHash64A seed 11, `mixHash` with nil = 1723 — validated against the anchor's trace for source,
  olean, olean.server, olean.private, ir, ilean, ir.sig): for all 11207 reachable modules, the Lake text hash of the
  source file in the clean `git archive 1987105a` equals the source hash recorded in main's `.trace`, and the
  `.olean`/`.olean.server`/`.olean.private` byte hashes equal the trace's recorded outputs (`logs/tracecheck-reach.tsv`,
  sha256 `a2ac32bf…4a4c`): **11207 OK, 0 BAD**. 1804 of them (WaveTurbulenceVineParam) record their source path in the
  worktree `<worktrees>/port-vp/`; their sources are byte-identical to the seal commit's.
  (Over all 13162 traced modules of main's build, 47 stale artifacts of modules absent from the seal commit exist;
  none is in main_v2's closure.)

## (h) Five-bin binder table — PASS (0 EXCESS)

Source reconstructed from the raw TeX and the rulings before reading the Lean statement, its docstring or any audit
(`h-source-reconstruction.md`; TeX re-hashed: `493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb`).
Every project-owned name in the type expanded (12 sealed D6 definitions; `IsWKESolution` and `IsSmoothNLSSolution`
expanded field by field). Quantifier order matches: θ after (d, γ) only; L₀ after φin, τ★, φ.

| # | Binder | Bin | Citation |
|---|---|---|---|
| 1 | `d : ℕ` | SOURCE | T L314 |
| 2 | `hd : 3 ≤ d` | SOURCE | T L314 |
| 3 | `γ : ℝ` | SOURCE | T L314, L297 |
| 4 | `hγ : γ ∈ Ioo (1/2) 1` | RULED | E1, D9, D10 (source: γ ∈ (0,1); D2 square torus) |
| – | `∃ θ`, `θ > 0` (witness, conclusion) | SOURCE | T L318 |
| 5 | `φin : 𝓢(Mom d, ℝ)` (`Mom d = EuclideanSpace ℝ (Fin d)`) | SOURCE | T L314, L294 |
| 6 | `∀ k, 0 ≤ φin k` | SOURCE | T L314, L294 |
| 7 | `τstar : ℝ` | SOURCE | T L314 |
| 8 | `τstar > 0` | SOURCE | T L314 |
| 9 | `φ : ℝ → 𝓢(Mom d, ℝ)` | SOURCE | T L318, L598 |
| 10a | `ContinuousOn φ (Icc 0 τstar)` (into 𝓢) | RULED | D6 closed-interval WKE class (with 10b, 10c it encodes "τ★ < τ_max, φ the solution", by sealed `wkelwp`) |
| 10b | `φ 0 = φin` | SOURCE | T L302 |
| 10c | `∀ τ ∈ Icc 0 τstar, ∀ k, HasDerivWithinAt (φ · k) (collisionOp (φ τ) (φ τ) (φ τ) k) (Icc 0 τstar) τ` | SOURCE | T L299–L301 (WKE), L306–L307 (COL) with the D6 Dirac reading (change of variables re-derived) |
| – | `∃ L₀` (witness) | SOURCE | T L316 |
| 11 | `L : ℝ` | SOURCE | T L316, L285 |
| 12 | `L ≥ L₀` | SOURCE | T L316 |
| 13 | `α : ℝ` | TYPING | name for the coupling of T L278 |
| 14 | `T : ℝ` | TYPING | name for the final time |
| 15 | `α = L ^ (-γ)` | SOURCE | T L314, L297 |
| 16 | `T = τstar * kineticTime α` (`kineticTime α = 1/(2α²)`) | SOURCE | T L316, L297 |
| 17 | `Ω : Type u` | TYPING | sample space of the data, T L294 |
| 18 | `[MeasurableSpace Ω]` | TYPING | idem |
| 19 | `P : Measure Ω` | TYPING | idem (ℙ, 𝔼 of T L316–L318) |
| 20 | `[IsProbabilityMeasure P]` | TYPING | idem |
| 21 | `g : (Fin d → ℤ) → Ω → ℂ` (k = n/L) | SOURCE | T L292, L294; indexing ℤ^d ≅ ℤ_L^d, T L285 |
| 22 | `∀ n, Measurable (g n)` | TYPING | "random variables", T L294 |
| 23 | `iIndepFun g P` | SOURCE | T L294 "i.i.d." |
| 24 | `∀ n, P.map (g n) = stdComplexGaussian` (Re, Im iid N(0,1/2)) | SOURCE | T L294 "standard normalized Gaussian"; circular reading D6 |
| 25 | `U : Ω → ℝ → (Fin d → ℝ) → ℂ` | RULED | D6 selection device; T L318 |
| 26 | `∀ ω ∈ F, IsSmoothNLSSolution L α T (initialCoeff L φin g ω) (U ω)` — as a device | RULED | D6 |
| 26a | `ω ∈ solvableEvent …` = `∃ u, IsSmoothNLSSolution …` | SOURCE | T L316, L318 |
| 26b | `ContDiffOn ℝ ∞ (fun p => u p.1 p.2) (Icc 0 T ×ˢ univ)` | SOURCE | T L316 "smooth solution" |
| 26c | L-periodicity in each coordinate | TYPING | T L278, L285 (functions on 𝕋_L^d) |
| 26d | `torusFourierCoeff L (u 0) n = √(φin(n/L))·g n ω` | SOURCE | T L278 u(0)=u_in, L292 (DAT), L286 (fourier, L^{−d/2}); D6 |
| 26e | `I·∂_t u − Δu + α‖u‖²u = 0` on [0,T] × ℝ^d, Δ = (2π)⁻¹Σ∂²_j | SOURCE | T L278–L279, L285 |
| 27 | `t : ℝ` | SOURCE | T L317 |
| 28 | `t ∈ Icc 0 T` | SOURCE | T L317 |
| 29 | `n : Fin d → ℤ` (k = latticePoint L n = n/L) | SOURCE | T L317, L285 |

Conclusion: `MeasurableSet F` — RULED D6; `1 − exp(−(log L)^{40d}) ≤ P.real F` — SOURCE T L316 (natural log,
ℕ exponent 40·d); `|∫ 1_F ‖û(U ω t)(n)‖² dP − φ(t/T_kin)(n/L)| ≤ L^{−θ}` — SOURCE T L317 with RULED D6 (𝔼 = 𝔼[1_F ·]),
û per T L286.

**Counts (each expanded leaf once): SOURCE 24 · STANDING 0 · TYPING 8 · RULED 4 (4, 10a, 25, 26-device) · EXCESS 0.**
Watch items checked: no extra regularity/decay/size premise on φin, no a-priori bound on φ, no condition on L beyond
L ≥ L₀, no restriction of the probability space beyond i.i.d. N_ℂ(0,1) and measurability, no gate/estimate/witness
premise; θ before φin; L₀ after φ.

## Comparison with the brief's claim appendix and the seal script's logs (opened only after all items above were written)

**Claim appendix (AUDIT-main_v2.md L58–L75) vs my (h) table — every difference:**
1. *Verdict agrees:* 0 EXCESS in both.
2. *Granularity / expansion.* The appendix has 11 grouped rows and does not expand `IsWKESolution` or
   `IsSmoothNLSSolution`/`solvableEvent`. COMMON (h) requires one row per binder with every project-owned Prop alias
   expanded. My table expands both (10a–10c, 26a–26e); the expansion adds no EXCESS. Counts therefore differ:
   appendix SOURCE 10 / TYPING 1 / RULED 1, mine SOURCE 24 / TYPING 8 / RULED 4.
3. *Bin labels (none involves EXCESS):*
   - Appendix row 5 puts `IsWKESolution` in SOURCE. I put its closed-interval continuity clause in RULED (D6, the
     "closed-interval WKE solution class" reading), and its initial condition and equation in SOURCE.
   - Appendix row 7 puts `α`, `T` in SOURCE. I put the names in TYPING and their equations in SOURCE.
   - Appendix row 9 puts `∀ n, Measurable (g n)` in SOURCE. I put it in TYPING (a random variable is a measurable map).
   - Appendix row 10 puts `U` and its premise in SOURCE. I put the selection device in RULED (D6); the appendix
     itself cites D6. I put the content of the premise (event, C^∞, data, equation) in SOURCE.
4. *Citations:*
   - Appendix row 9 cites T L292 for "i.i.d." and the Gaussian law; those words are on T L294 (L292 is (DAT)).
   - Appendix row 4 cites only L314; "φin : ℝ^d → [0,∞) Schwartz" is on L294.
   - The brief's (d) item cites T L611 for "θ = η^{20}". L611 defines θ_p = η^{20}(1+2^{−p}); the sentence "We choose
     the θ in Theorem main as θ = η^{20}" is on L612.

**Seal script logs** (`seal-prep/logs/live-20261108T193926Z/`, `live-run-2.out`):
- Agreement:
  - `main_v2.pre.print.out` and `main_v2.post.print.out` are byte-identical to my `abi/pre-seal.print` and
    `abi/postA.print` (apart from the script's appended `exit 0` lines). Pre/post ABI `36fb4c1d…` / `21103400…` agree.
  - The seal script's pre/post pp.all type outputs are identical, as are mine.
  - `AXIOMS OK` agrees with (c). `RECHECK OK … body only; manifest fields ['abi_sha256', 'state']; DRAFT_SORRY
    anchors now 6` agrees with (a) and (g).
  - "MAIN_V2 CONCLUSION = ANCHOR CONCLUSION (pp.all, 32224 chars)" agrees with (b2). My 72466-char figure uses a
    different `format.width`.
- **Disagreement with the brief's subject line:** the run ends `SEAL ABORT: full ABI check … RESULT: ABORTED`
  (`full_abi.log`: `probe failed for WaveTurbulence.Mom`).
  - The probe's stdout was the correct `#print`. The failure came from the elan override notice
    (`note: using toolchain 'wt-throttled' from override set on '<repo>'`) on stderr, which
    `abi_hash.py` treats as a probe failure.
  - The script then reset local main to 1987105a without pushing. origin/main is nevertheless 1987105a, so it was
    pushed later, outside the script.
  - No log in seal-prep shows a successful 327-anchor ABI check, though the brief says "full 327-anchor ABI OK". I
    therefore ran the full check myself (below).

**My full 327-anchor ABI check** (`tools/fullabi.py`, `fullabi/results.tsv` sha256 `2865505c…977e`):
- Method: for each manifest anchor, a module probe `import all <M>` / `#print <export>`. Each probe used my own setup
  (M's Lake closure, M's artifacts and M's private part), the real v4.35.0 lean, `nice -n 10`, sequential.
- Result: **327 anchors, 327 OK, 0 not OK** (10 min 44 s).
- So the brief's "full 327-anchor ABI OK" holds at 1987105a, although the seal script's own final check aborted for
  the stderr reason above.

## Notes for wt-orch (none blocks this key's verdict)

- **N1 — consumed anchor `propansatz_v2`.** When I wrote this, `flower-core/status/` held no `SEALAUDIT-*` file, so its
  two-key PASS could not be confirmed. Its keys were still running.
  - The brief orders recording: `main_v2` after both keys PASS on `propansatz_v2`. That precondition is wt-orch's to
    check before recording PROVED.
  - main_v2's proof does not rest on that audit. The whole closure, `propansatz_v2`'s proof included, was
    kernel-replayed here with no axiom or sorry.
- **N2 — stale documentation at 1987105a.**
  - README's status block says `DRAFT_ANCHORS: 10 …` and `SEALED: 17 theorems + 300 definitions`; it also lists 8 names
    for a count of 10. The actual figures are 6 DRAFT and 21 sealed theorems + 300 definitions.
  - `docs/ERRATA-AND-DEVIATIONS.md` §A still calls `main_v2` "frozen and unproved".
  - HANDOFF item 11 already plans the README update.
- **N3 — seal script abort.** `scripts/abi_hash.py` runs `lake env lean` without `ELAN_NO_OVERRIDE_NOTICE=1`, unlike
  `abi_hash_setup.py`. The elan override on the main checkout therefore turns every probe into a "failure".
- **N4 — build provenance.**
  - 1804 VineParam oleans in main's build were compiled in `<worktrees>/port-vp/`. Their
    sources are byte-identical to the seal commit's.
  - Main's `.lake` holds 47 stale artifacts of modules absent from the seal commit. None is in main_v2's closure.
- **N5 — replay mode.** The replay ran in quick mode, the minimum COMMON allows. 40618 VineParam-internal certificate
  theorems (proofs using no constant outside that library) were checked by statement only; 92875 VineParam theorems
  were replayed with proofs. A full-mode replay would remove this caveat.
- **N6 — gate abbreviations.** `V2Chain.PropansatzV2Gate` and `V2Chain.NlsAkBridgeGate` are definitionally, not
  syntactically, equal to the sealed anchors' types (see (d)). The difference is proof-irrelevant.

## Evidence index (all under `<scratch>/seal-audit-main_v2-A/`)

**Source and binder table**
- `h-source-reconstruction.md`: source reconstruction, written first.
- `h-binder-table.md`: first draft of the (h) table.

**Export and hash tools**
- `export/`: clean `git archive 1987105a`.
- `freeze-MainV2.lean`: the DRAFT file.
- `tools/region_hash.py`, `tools/manifest_diff.py`, `tools/concl_cmp.py`, `tools/status_fields.py`.

**Probe tooling**
- `tools/mksetup.py`: my setup generator.
- `tools/runprobe.sh`: real lean, niced, with time and RSS.

**Probes**
- `probes/P1*`: anchor-only environment, visibility.
- `fz/`: freeze rebuild of the stub provider and the DRAFT anchor.
- `abi/`: ABI prints and hashes.
- `exprs/`: Expr and pp.all dumps, the binder table, value checks.
- `ax/`: `#print axioms` and the assembly's direct uses.
- `gatediff/`: gate vs anchor comparison.
- `witness/`: non-vacuity witnesses.
- `fullabi/`: 327-anchor ABI check.

**Replay**
- `replay/`: adapted replay (source, script, diffs vs lg2, output, reachable modules).
- `tools/lakehash.c`, `tools/tracecheck.py`, `logs/tracecheck-*.tsv`: source/trace/olean provenance.

**Guard and module check**
- `logs/guard-and-modules.out`.

`main_v2` may be recorded as PROVED (key A)
