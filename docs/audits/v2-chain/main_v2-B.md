# SEAL-AUDIT `main_v2` — KEY-B (refute-first, independent)

Auditor: KEY-B (Opus 5.5), 2026-11-08. Binding rules: `flower-core/seal-prep/audit-briefs/AUDIT-COMMON.md`; brief
`AUDIT-main_v2.md` (sha256 `16e7aaf6…`); launch brief `flower-core/briefs/audit/SEAL-AUDIT-main_v2-B.md`.
Subject: frozen anchor `WaveTurbulence.main_v2` (`WaveTurbulence/Frozen/Theorems/MainV2.lean`), sealed by
`b9711f35` "Seal main_v2 with its proved assembly (SEAL-PREP chain)" + `1987105a` "manifest: ABI hash of the sealed
main_v2" (= origin/main at launch). Clean export: `git archive 1987105ac00b88c879ffebf4a56e30aa02b4f92f` →
`/home/scott/wt-scratch/seal-audit-main_v2-B/export/`. Main's checkout moved during the audit to `7c955833`, then
`e1449ba4` (HQ auto-updates: README.md and docs/campaign only; no Lean source, manifest, lakefile or toolchain change).

## Verdict table

| Item | Verdict | One-line evidence |
|---|---|---|
| (a) Anchor bytes | **PASS** | only change since freeze `8d7ccb4a` is the body `by sorry` → `by exact WaveTurbulence.Provider.main_v2`; own prefix/suffix hashes = manifest; manifest entry changed in exactly {state, abi_sha256}; 12/12 closure hashes; guard OK + module check PASS on the clean export |
| (b) Provider | **PASS** (one wording disagreement, see F1) | no self-import (source + Lake closure); conclusion byte-equal; exactly the four binder adaptations; conclusions `==`/pp.all/isDefEq equal, `Expr.equal` false only on two hygienic instance-binder names; anchor value `fun d hd γ hγ => Provider.main_v2 hd hγ` on its own bvars; body = the brief's assembly; export used only by the anchor; private imports; anchor-only probe sees 14 project modules, no proof-closure name |
| (c) Axioms | **PASS** | 20 declarations (anchor, provider, assembly, 7 consumed sealed anchors, 10 helpers): `[propext, Classical.choice, Quot.sound]` |
| (d) Hidden hypotheses / vacuity | **PASS** | assembly inputs = 2 sealed exports + 10 theorems (kernel kinds via (f)); binders discharged exactly; θ = η₀²⁰ chosen before φin (T L611); P ≥ 1 − e^{−(log L)^{40d}} via N_𝔇 ≥ (log L)^{40d}; non-vacuity: term-level composition through the sealed export with explicit witnesses (P4), solvable event nonempty |
| (e) ABI | **PASS** | pre-seal `36fb4c1d…` (own overlay build of the freeze sources) and post-seal `21103400…` reproduced; `#print` differs only in the value line; pp.all type and raw Expr `repr` byte-identical before/after |
| (f) Kernel replay | **PASS** (quick mode) | `REPLAY OK (8486 s)`: 219,644 project constants / 11,207 modules reachable from `main_v2`; no project axiom/opaque/unsafe/partial, no `sorryAx`/`ofReduceBool`/`trustCompiler` user, MISSING 0; all 12,153 closure modules' trace source hashes = seal-commit sources and all 36,459 olean parts = trace outputs; wall 2:22:17, max RSS 6.27 GB; 40,618 VineParam certificate proofs checked by statement only (quick mode, disclosed) |
| (g) Status fields | **PASS** (README stale, F3) | DRAFT_ANCHORS 6; UNREGISTERED_SORRIES 0; DRAFT_IMPORT_VIOLATIONS 0; SEALED_THIS_TURN `main_v2` |
| (h) Five-bin table | **PASS** | SOURCE 10, STANDING 0, TYPING 8, RULED 4, **EXCESS 0** (table below; claim-appendix differences listed) |


## Findings (none blocking)

- **F1 (b), disagreement with the brief's item (b)3.** The brief says the conclusions after the four binders are
  `Expr.equal`. They are not: instantiated with the same fvars, `Expr.equal` is **false**; `==` (alpha-equivalence) is
  true, `isDefEq` true, pp.all text equal (72,466 chars). A structural walk (probe P2b) finds exactly **two**
  differences, both binder *names* of the anonymous instance binders `[MeasurableSpace Ω]` and
  `[IsProbabilityMeasure P]`: `inst._@.WaveTurbulence.Frozen.Theorems.MainV2._hygCtx._hyg.217/222` (anchor) vs
  `inst._@.WaveTurbulence.Provider.MainV2._hygCtx._hyg.223/228` (provider). Hygienic names carry the declaring module,
  so two modules can never produce `Expr.equal` binders here; binder info (`instImplicit`) and every other node are
  identical. Binder names are irrelevant to the kernel; AUDIT-COMMON accepts pp.all text equality. Not a defect. The
  seal script and HANDOFF claim only pp.all equality (32,224 normalized chars), consistent with this.
- **F2 (h), bin-label differences with the claim appendix** (no EXCESS on either side): see the comparison under (h).
- **F3 (g), stale README status block.** At 1987105a (and still at HEAD e1449ba4) README.md says `DRAFT_ANCHORS: 10 …
  (main, fixedpoint, propansatz v1/v2; layergarden v1; layergardenFlower v1/v2/v3)` and `SEALED: 17 theorems + 300
  definitions`. The manifest says 6 DRAFT (no v2/v3 among them) and 21 SEALED theorems + 300 definitions. Documentation
  only; the seal script's own count ("DRAFT_SORRY anchors now 6") is right.
- **F4 (context), full 327-anchor ABI check.** The launch brief says "full 327-anchor ABI OK". The only logged run of
  that check (`seal-prep/logs/live-20261108T193926Z/full_abi.log`, `live-run-2.out`) **aborted at its first anchor**
  (`Mom`): `scripts/abi_hash.py` runs `lake env lean` without `ELAN_NO_OVERRIDE_NOTICE=1`, elan printed its
  `wt-throttled` override note on stderr, and the script treats any stderr as failure. No later successful run is
  logged in seal-prep. **Independent re-run (`tools/fullabi.py`, own setup generator, abi_hash_setup convention,
  `ELAN_NO_OVERRIDE_NOTICE=1`, stock compiler, sequential, niced): `TOTAL 327: OK 327, DIFF 0`** (no stderr, every
  rc = 0; `fullabi/fullabi.log` sha256 `62a53bf9…c7ee`; 10 min 18 s). The claim holds for the seal commit's manifest and
  build; only its logged evidence was missing.
- **F5 (method notes).** (i) In a module-system environment without `.olean.private` parts, imported theorems are not
  `thmInfo` (e.g. `Provider.main_v2` and every `_proof_N` of the Defs show as non-theorems in the anchor-only probe);
  constant kinds must be read from all olean parts, as the replay does. (ii) `scripts/abi_hash_setup.py` (audited, not
  used): resolves through Lake's setup file for the frozen module, adds the module's three olean parts and the
  `.olean.private` of every `WaveTurbulence*` module (including `WaveTurbulenceVineParam`), probes `import all`, and
  hashes stdout; it fails on any stderr or on the substring `error` in stdout (spurious-failure risk only, not
  soundness); it runs `lake env lean` in the repository root (through the `wt-throttled` override = the throttle
  wrapper around the stock v4.35.0 binary). My own generator (`tools/mksetup.py`) reproduces both main_v2 hashes
  with the same convention.
- **F6 (sequencing, not a defect of this seal).** The provider consumes the sealed export `propansatz_v2`; the
  campaign rule (HANDOFF item 7) records `main_v2` PROVED only after both keys PASS on `propansatz_v2` (and upstream).
  No SEALAUDIT status file existed when I checked. Mathematically, `main_v2`'s soundness does not depend on the
  statement fidelity of the intermediate anchors (any kernel-checked theorem may be consumed) and (f) replays their
  proofs; only the bookkeeping order is at stake.

## Details and evidence

All paths below are relative to `/home/scott/wt-scratch/seal-audit-main_v2-B/` unless absolute. Lean probes: stock
v4.35.0 (`~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, githash `eb6cafb7…`, the compiler recorded in the
build traces), `nice -n 10`, one at a time, through my own Lake-setup generator `tools/mksetup.py` (from Lake's
`.lake/build/ir/<M>.setup.json` in main; no `lake env`, nothing written in any checkout). Each probe: ~2–3 s wall,
≤ 4.4 GB RSS.

### Order of work (protocol)
1. Source reconstruction from raw TeX + rulings **before** reading the Lean statement: `notes/01-source-reconstruction.md`.
2. Five-bin table (h): `notes/02-five-bin-table.md`.
3. Own results for (a)–(e), (g), (h): `notes/03-own-results-before-appendix.md`. **Only then** the claim appendix of
   the brief, HANDOFF.md, and the seal logs (`seal-prep/logs/live-*`, `live-run-2.out`) were read; (f) was compared
   after the replay finished.

### (a) Anchor bytes — PASS
- `git log -- WaveTurbulence/Frozen/Theorems/MainV2.lean`: only `8d7ccb4a` (freeze, D10) and `b9711f35` (seal).
  `git diff 8d7ccb4a 1987105a` of the file: one line, `-  by sorry` / `+  by exact WaveTurbulence.Provider.main_v2`.
- File sha256: freeze `af13246404639caf5c6028d76f3daba3883c80cbe751b8854f8c011575cac600` (= brief `af132464…`), sealed
  `000671e0a142da4797932bdf07fa87bb94a5519a3ceed684628a103811b40ab3`.
- Own recomputation with the guard's convention (`tools/prefix_suffix.py`: prefix = bytes up to the line after
  `FROZEN_ANCHOR_PROOF_BEGIN`, suffix = bytes from the line of `FROZEN_ANCHOR_PROOF_END`), identical at freeze and seal:
  prefix `67762ca2a9dd62d2a5c50525c7b761f6c26a71a27519ff41a6f6032aa76b55f3`, suffix
  `9f48199048606af986e4911abed0172f6e65c9c8c91f1c2874961ad85a7ea8d0` = manifest. Sealed body
  `  by exact WaveTurbulence.Provider.main_v2\n` (43 bytes, 1 line; limits 3 lines / 240 bytes).
- Manifest entry `main_v2`, freeze `8d7ccb4a` vs `b9711f35` vs `1987105a` (`tools/manifest_diff.py`): changed keys exactly
  `state` (DRAFT_SORRY → SEALED) and `abi_sha256` (`36fb4c1d…8da4` → `21103400…5272`). `definition_closure`: 12/12
  sha256 match the export (Mom, LatticePoint, CollisionOp, IsWKESolution, PartialDeriv, NormLaplacian,
  TorusFourierCoeff, IsSmoothNLSSolution, StdComplexGaussian, InitialCoeff, SolvableEvent, KineticTime).
- On the clean export: `python3 -I scripts/check_frozen_anchors.py --root . --manifest manifest/frozen.json` →
  `FROZEN-ANCHOR GUARD OK`; `python3 -I scripts/check_lean_modules.py` → `PASS (13118 Lean files)`.
- Toolchain, `lake-manifest.json` unchanged since the freeze; `lakefile.lean` changed only in the quarantine array and
  by the VineParam `lean_lib` (D12).

### (b) Provider — PASS (F1)
- Provider `WaveTurbulence/Provider/MainV2.lean` sha256 `6fd8687c…c136c0` (= seal-prep's `providers/MainV2.lean`).
  Imports: `public import` Mathlib + the anchor's 12 `Frozen.Defs`; `import` (private) `Frozen.Theorems.PropansatzV2`,
  `Frozen.Theorems.NlsAkBridge`, `Foundations.XChain.V2Chain.MainV2`. At the freeze it was a stub (sha256 `0d0e01ee…`,
  Mathlib + 12 Defs, no declaration).
- No self-import: the anchor module is absent from Lake's resolved closure of the provider
  (`.lake/build/ir/WaveTurbulence/Provider/MainV2.setup.json`, 9339 modules) and from the full source closure
  (public + private, `tools/closure.py`, 12152 project modules).
- Body (byte-compared): `WaveTurbulence.MainGlue.main_v2_of_propansatz WaveTurbulence.propansatz_v2
  WaveTurbulence.nlsAkBridge d hd γ hγ` = the brief. The assembly has no section variables.
- Export used only by the anchor: the only importer of `WaveTurbulence.Provider.MainV2` in the export is the anchor;
  the only textual use of `Provider.main_v2` is the anchor body.
- Statement (probe P2, `probes/P2Exact.lean`, `probes/P2.out`): conclusion text byte-equal (957 chars,
  `tools/concl.py`). Binder table:

  | # | anchor | provider | name | type after `autoParam` stripping | binder info |
  |---|---|---|---|---|---|
  | 0 | `(d : ℕ)` | `{d : ℕ}` | equal | `Expr.equal` | default → implicit |
  | 1 | `(hd : 3 ≤ d)` | `(hd : 3 ≤ d := by assumption)` | equal | `Expr.equal` (wrapped in `autoParam … _auto_1`) | default = default |
  | 2 | `(γ : ℝ)` | `{γ : ℝ}` | equal | `Expr.equal` | default → implicit |
  | 3 | `(hγ : γ ∈ Ioo (1/2) 1)` | `(hγ : … := by assumption)` | equal | `Expr.equal` (wrapped, `_auto_3`) | default = default |

  Exactly the four adaptations; level params `[u]` both. Conclusions after the four binders, instantiated with the
  same fvars: `==` **true**, `isDefEq` true, pp.all text equal (72,466 chars), `Expr.equal` **false**: two binder-name
  differences only (F1, probe P2b).
- `example : type_of% @WaveTurbulence.main_v2.{u} := fun d hd γ hγ => @WaveTurbulence.Provider.main_v2.{u} d hd γ hγ`
  compiles (P2).
- Anchor value (with the anchor's `.olean.private`): `fun d hd γ hγ => WaveTurbulence.Provider.main_v2 hd hγ`;
  structurally `λλλλ. @Provider.main_v2.{u} #3 #2 #1 #0`, so the auto-params are the anchor's own `hd`, `hγ`.
- Freeze environment (probe P1, `probes/P1.out`): a module importing only the anchor (Lake's set for the anchor + the
  anchor's olean/server) contains exactly 14 project modules: the 12 Defs, `Provider.MainV2` (3 constants:
  `main_v2`, `_auto_1`, `_auto_3`), and the anchor. `MainGlue.main_v2_of_propansatz`, `propansatz_v2`, `nlsAkBridge`,
  `Provider.propansatz_v2/nlsAkBridge`, `layergarden_v2`, the gates, `WTParams`, `AnsatzAt`, `WTPrefix`, and three
  helpers are all unknown. Lake's setup file for the anchor lists the same 13 imported project modules, so the
  frozen statement elaborated in Mathlib + its Defs + the provider's theorem; (e) shows no drift.

### (c) Axioms — PASS
Probe P3 (`probes/P3Axioms.lean`, `probes/P3.out`; env = Lake's provider set merged with the sets of the 7 consumed
anchors, all project `.olean.private` parts, `import all`): `[propext, Classical.choice, Quot.sound]` for
`main_v2`, `Provider.main_v2`, `MainGlue.main_v2_of_propansatz`, `propansatz_v2`, `nlsAkBridge`, `layergarden_v2`,
`fixedpoint_v2`, `layergardenFlower_v3`, `regularAsymptotics`, `wkeTaylor`, and the 10 helpers
(`ceiling_subdivision`, `schwartz_lattice_sum_le`, `eventually_final_exponent`, `induction_error_absorption`,
`gate_solvable_measurability`, `ansatz_solvable_probability`, `exists_ansatz_step`, `ansatz_observable_error`,
`hasLaw_stdComplexGaussian`, `NLS.kineticTime_rpow_neg_pos`). Independent check: (f).

### (d) Hidden hypotheses and vacuity — PASS
- Trace: `Provider.main_v2 := main_v2_of_propansatz propansatz_v2 nlsAkBridge d hd γ hγ`. The assembly's six binders are
  `hpropansatz : V2Chain.PropansatzV2Gate.{u}` := the SEALED export `propansatz_v2` (the kernel checks its type against
  the `abbrev`, so the gate is exactly what that anchor proves), `hnlsAkBridge : V2Chain.NlsAkBridgeGate.{u}` := the
  SEALED export `nlsAkBridge` (gate text = frozen type, compared), and `d hd γ hγ` from the provider's own binders.
  Nothing else enters: the assembly's body uses only these, its intro'd variables, and the 10 helpers, each a
  `theorem` with standard axioms (kinds from all olean parts in (f)).
- θ: `obtain ⟨η₀, …⟩ := hpropansatz d hd γ ⟨…⟩; refine ⟨η₀ ^ 20, …⟩` happens before `intro φin`, so θ = η₀²⁰ depends
  only on (d, γ) (T L611: "We choose the θ in Theorem 1.1 as θ = η^{20}"). The frozen ∃θ-before-∀φin enforces it anyway.
- Probability: `hN : (log L)^{40d} ≤ N_𝔇` (`eventually_final_exponent`, matching R_𝔇 = ⌊(log L)^{40d}⌋, N_𝔇 = R_𝔇^{40d},
  T L611–L612), `hpr : 1 − e^{−N_𝔇} ≤ P(F)` (`ansatz_solvable_probability`), so 1 − e^{−(log L)^{40d}} ≤ P(F) (T L316).
- Meaning (D6): E = ∫ 1_F ·; `MeasurableSet F` asserted; "smooth" = `IsSmoothNLSSolution`; selection device ∀U with
  no measurability or integrability premise on U. The integrand is integrable for every admissible U (mass
  conservation Σ_n|û(t,n)|² = Σ_n|c_n|², E Σ|c_n|² = Σ φin(n/L) < ∞), so the Bochner integral is the true expectation;
  `P.map (g n)` comes with `Measurable (g n)` (Mathlib's `map` junk value is not reachable).
- **Non-vacuity, term level** (probe P4, `probes/P4NonVacuity.lean`, `probes/P4.out`, axioms standard). The sealed
  export `main_v2.{0}` is applied through its whole prefix: after the prover's θ, the witnesses are φin = 0 (with
  `∀ k, 0 ≤ φin k`), τ★ = 1, φ ≡ 0 (`IsWKESolution 0 1 0` proved: `collisionOp 0 0 0 = 0`). After the prover's L₀,
  L = max L₀ 2, α = L^{−γ}, T = 1·kineticTime α (rfl, rfl), and Ω = ℂ^{ℤ^d} with
  `Measure.infinitePi (fun _ => stdComplexGaussian)` and g n ω = ω n (measurable; `iIndepFun_infinitePi`;
  `infinitePi_map_eval`). In that model P(F) ≥ 1 − e^{−(log L)^{40d}} > 0 (L ≥ 2), so **F is nonempty**; U is defined
  by choice on F (premise proved), and the conclusion is reached at t = 0 ∈ [0,T], n = 0. Every universal range is
  nonempty and every premise is satisfiable. Nontrivial data: `wkelwp_v1` is SEALED (Schwartz solutions for small τ★).

### (e) ABI — PASS
- Convention (abi_hash_setup.py, audited, F5): module probe `module / import all WaveTurbulence.Frozen.Theorems.MainV2 /
  #print WaveTurbulence.main_v2`, Lake's set + the module's 3 parts + every project `.olean.private`; sha256(stdout).
- Post-seal (main's build, `abi/post.setup.json`, `abi/post.out`): `2110340043ade661f13a79379c82904919645a1d2cc59f3650fe539e27b75272`
  = manifest.
- Pre-seal: own overlay (`preseal/compile.sh`): the freeze provider stub (`git show 8d7ccb4a:…Provider/MainV2.lean`) and
  the freeze anchor (`by sorry`) compiled with the stock compiler against main's Mathlib + Defs build (unchanged since
  the freeze: same toolchain, lake-manifest, Def hashes), module names as in Lake. `abi/pre.out` sha256
  `36fb4c1dd04ff1330839fb9cb4d465fee163bf52dcc6efb3471d8f5c577a8da4` = the manifest's freeze value.
- `diff abi/pre.out abi/post.out`: one line, `fun d hd γ hγ => sorry` → `fun d hd γ hγ => WaveTurbulence.Provider.main_v2 hd hγ`.
- Fully explicit type before/after: `pp.all` + `pp.sanitizeNames false` + `pp.proofs` (`abi/PpAll.lean`): byte-identical,
  75,959 bytes, sha256 `361e00c9…dd1f`, same `Expr.hash`; raw `repr` of the type Expr including hygienic names
  (`abi/Repr.lean`): byte-identical, 706,665 bytes, sha256 `bb678b2b…d7af`. No drift from the provider's new
  imports.

### (f) Kernel replay
**PASS (quick mode).** Kit adapted from `/home/scott/wt-scratch/seal-lg2/replay/` (read first; copies
`replay/Replay.lg2.lean` sha256 `6c943568…`, `replay/replay.lg2.sh` `b8298ed6…`). My versions: `replay/exe/Replay.lean`
(`8dd676e8…`), `replay/replay.sh` (`72cda253…`); diffs recorded in `replay/replay-diff-vs-lg2.diff` (88 lines) and
`replay/replay-sh-diff-vs-lg2.diff` (27 lines). Changes: root module `WaveTurbulence.Frozen.Theorems.MainV2`, root
constant `WaveTurbulence.main_v2`; a `wanted` list for the main_v2 chain (30 constants), with real kinds from all olean
parts and a check that none is stubbed; exactness lines for the anchor, provider and assembly; LEAN_PATH set explicitly
(no `lake env` in main's checkout); 7 index batches (12,153 project modules); `nice -n 10`. Replay logic (closure from
olean headers, library base from exported parts, project constants from all three parts, one
`Kernel.Environment.replay`, no failure handling that forces anything) is unchanged.

Run: `replay/replay.sh quick` → `replay/Replay-quick.out` (sha256 `92821652…5e096`).
- Closure: 23,129 modules = 10,976 library + **12,153 project** (= my source closure; every one has all three olean
  parts). The olean bytes are the seal commit's: all 12,153 trace source hashes equal Lake's `Hash.ofText` of the
  export sources (`tools/tracecheck.py`, `evidence-tracecheck.out`; 10,338 built in `/home/scott/WaveTurbulence-dev`,
  1,815 VineParam modules built in `…/WaveTurbulence-worktrees/port-vp`, same content hashes), and all 36,459
  `.olean/.olean.server/.olean.private` files equal their trace output hashes (`tools/oleancheck.py`,
  `evidence-oleancheck.out`). Build compiler: `/home/scott/wt-tools/sysroot/bin/lean` (the `wt-throttled` elan
  override), a throttle script that `exec`s the stock v4.35.0 binary (githash `eb6cafb7…`); `lake` is a hardlink to the
  stock one.
- Reachable from `main_v2`: 230,216 names; **219,644 project constants in 11,207 modules** (inductive 585, ctor 802,
  def 22,173, theorem 195,933, rec 151); MISSING 0; same-name constants in two loaded modules 1,673, with a different
  type (or, for non-theorems, value) **0**.
- **Project axioms reachable: none. Opaque: none. Unsafe/partial: none. Direct users of `sorryAx`/`ofReduceBool`/
  `trustCompiler`/`ofReduceNat`: none.** Core axioms referenced directly: `Quot.sound`, `Classical.choice`, `propext`.
- Reachable `Frozen.Theorems` constants: `nlsAkBridge`, `layergarden_v2`, `propansatz_v2`, `fixedpoint_v2`,
  `regularAsymptotics`, `layergardenFlower_v3`, `wkeTaylor` (all SEALED), plus the root.
- Chain kinds (all olean parts): the anchor, the provider, the assembly, the 7 sealed anchors and their providers, and
  the 10 helpers are `theorem`; the two gates are `def` (`abbrev`); none unsafe; all 30 `wanted` constants replayed
  (none stubbed).
- Exact values: anchor `fun d hd γ hγ => @WaveTurbulence.Provider.main_v2.{u} d hd γ hγ`; provider
  `fun {d} hd {γ} hγ => WaveTurbulence.MainGlue.main_v2_of_propansatz.{u} WaveTurbulence.propansatz_v2.{u}
  (fun {d'} => WaveTurbulence.nlsAkBridge.{u} d') d hd γ hγ`, which is the brief's assembly; `nlsAkBridge` is
  eta-expanded over its implicit `{d}`.
- **`REPLAY OK (8486 s): 219,644 constants`**, one `Kernel.Environment.replay` call. Wall 2:22:17, user 8,417 s,
  **max RSS 6.27 GB**, exit 0.
- **Quick-mode disclosure.** As in every quick-mode seal replay, **40,618 `WaveTurbulenceVineParam` certificate theorems**
  whose proofs use no project constant outside that library were sent to the kernel **by statement only**: they are
  inserted as axioms *in the replay set*. Their types are checked; their decide-heavy proofs are not re-checked here.
  So the script's closing phrase "no constant turned into an axiom" refers to failure handling only. The other
  92,875 VineParam theorems (every cross-library one) were replayed with their proofs. The "project AXIOMS reachable:
  []" line is computed from the real olean constants before stubbing. AUDIT-COMMON requires quick mode at least; a full-mode
  replay (no stubs) was not run.

### (g) Status fields — PASS (F3)
- DRAFT_ANCHORS: **6** — `WaveTurbulence/Frozen/Theorems/Main.lean` (main_v1), `Fixedpoint.lean`, `Layergarden.lean`,
  `LayergardenFlower.lean`, `Propansatz.lean`, `LayergardenFlowerV2.lean`; each has exactly one `by sorry` (raw scan:
  the only `sorry` tokens in code are these six). Manifest: 300 SEALED definitions, 21 SEALED theorems, 6 DRAFT.
- UNREGISTERED_SORRIES: **0** (guard `check_all_sorries` + own scan; no `axiom`/`opaque`/`unsafe`/`partial`/
  `implemented_by`/`extern`/`native_decide`/`ofReduceBool`/`skipKernelTC` in the 12,153-module closure).
- DRAFT_IMPORT_VIOLATIONS: **0** (guard quarantine + own scan: no importer of any DRAFT anchor; each DRAFT provider
  imported only by its anchor; no DRAFT anchor/provider module in main_v2's closure).
- SEALED_THIS_TURN: **`main_v2`** (`b9711f35` + `1987105a`).

### (h) Five-bin binder table — PASS
Reconstructed from T L276–L320, L596–L612 (raw TeX re-hashed: `493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb`)
and D6, D7, D9, D10, D13, E1, E34 before the docstring was read. Project-owned constants in the type, found
mechanically (P2): `Mom`, `IsWKESolution` (→ `collisionOp`), `kineticTime`, `stdComplexGaussian`, `solvableEvent`
(→ `IsSmoothNLSSolution` → `torusFourierCoeff`, `normLaplacian` → `partialDeriv`; `initialCoeff`), `latticePoint`;
23 constants including their `_proof_N`. No `WTPrefix`/`WTPrefixP`/`RemainderBound`/`AnsatzAt`/`IsGaussianData` in
this type.

| # | binder (Lean) | kind | bin | citation |
|---|---|---|---|---|
| 1 | `d : ℕ` | explicit | TYPING | T L314 |
| 2 | `hd : 3 ≤ d` | explicit | SOURCE | T L314 |
| 3 | `γ : ℝ` | explicit | TYPING | T L314, L294 |
| 4 | `hγ : γ ∈ Ioo (1/2) 1` | explicit | RULED | D9, D10, E1 (source γ ∈ (0,1)) |
| – | `∃ θ > 0` | conclusion witness | — | T L318, L611; scope (d, γ) ✓ |
| 5 | `φin : 𝓢(Mom d, ℝ)` | ∀ | SOURCE | T L314 "Schwartz initial data", L292 |
| 6 | `∀ k, 0 ≤ φin k` | premise | SOURCE | T L314, L292 |
| 7 | `τstar > 0` | ∀ + premise | SOURCE | T L314 |
| 8 | `φ : ℝ → 𝓢(Mom d, ℝ)` | ∀ | TYPING | T L314, L318, L598 |
| 9 | `IsWKESolution φin τstar φ` | premise | RULED | D6 (closed-interval Schwartz solution ⇔ τ★ < τ_max, Prop 3.2) |
| 9a | ↳ `ContinuousOn φ (Icc 0 τstar)` | conjunct | RULED | D6 |
| 9b | ↳ `φ 0 = φin` | conjunct | SOURCE | (WKE) L300–L301 |
| 9c | ↳ `∂τ φ(τ,k) = 𝒦(φ,φ,φ)(k)` on [0,τ★] | conjunct | SOURCE (+ D6 Dirac reading) | (WKE), (COL) L300–L306 |
| – | `∃ L₀, ∀ L ≥ L₀` | conclusion witness | — | T L316; L₀ after φin, τ★, φ (L605–L610) ✓ |
| 10 | `α T : ℝ` | ∀ | TYPING | T L294, L316 |
| 11 | `α = L ^ (-γ)` | premise | SOURCE | T L314 |
| 12 | `T = τstar * kineticTime α` | premise | SOURCE | T L316, L293 (T_kin = 1/(2α²)) |
| 13 | `Ω`, `[MeasurableSpace Ω]` | ∀, inst | TYPING | T L292 |
| 14 | `P`, `[IsProbabilityMeasure P]` | ∀, inst | TYPING | T L292, L316 |
| 15 | `g : (Fin d → ℤ) → Ω → ℂ` | ∀ | TYPING | T L292 (k = n/L ∈ ℤ_L^d) |
| 16 | `∀ n, Measurable (g n)` | premise | TYPING | "random variables" L292 |
| 17 | `iIndepFun g P` | premise | SOURCE | T L292 "i.i.d." |
| 18 | `∀ n, P.map (g n) = stdComplexGaussian` | premise | SOURCE | T L292; D6 circular complex Gaussian |
| 19 | `U : Ω → ℝ → (Fin d → ℝ) → ℂ` | ∀ | RULED | D6 selection device |
| 20 | `∀ ω ∈ F, IsSmoothNLSSolution L α T (initialCoeff L φin g ω) (U ω)` | premise | RULED | D6; T L316, L318 |
| 20a | ↳ `IsSmoothNLSSolution`: C^∞ on [0,T]×ℝ^d, L-periodic, û(0,n/L) = c n, (NLS) pointwise | def | SOURCE + RULED | (NLS) L278–L282, (fourier) L286–L289; "smooth" D6 |
| 20b | ↳ `initialCoeff`: c n = √φin(n/L)·g_n(ω) | def | SOURCE | (DAT) L292 |
| 20c | ↳ `solvableEvent`: {ω \| ∃ u, IsSmoothNLSSolution … u} | def | SOURCE | T L316, L318 |
| 21 | `t ∈ Icc 0 T` | ∀ + premise | SOURCE | T L317 |
| 22 | `n : Fin d → ℤ` | ∀ | SOURCE | T L317 |

Counts (top-level rows 1–22): **SOURCE 10, STANDING 0, TYPING 8, RULED 4, EXCESS 0**. Expansion rows 9a–9c,
20a–20c: SOURCE/RULED only. Other dimensions: quantifier order ∀d γ ∃θ ∀φin τ★ φ ∃L₀ ∀L ≥ L₀ … (θ = θ(d,γ) ✓);
(log L)^{40d} as printed (ℕ power) ✓; sup over closed [0,T] and all n ✓; φ evaluated at (t/T_kin, n/L) ✓; bound L^{−θ} ✓.

**Comparison with the claim appendix (opened after the table).** Same conclusion (EXCESS 0). Differences, all
labelling or granularity:
1. The appendix groups binders (11 rows: d with hd, γ with hγ, g with its three premises, U with its premise); my
   table has one row per binder, with recursive expansion of `IsWKESolution`, `IsSmoothNLSSolution`, `initialCoeff`,
   `solvableEvent` (AUDIT-COMMON (h) requires the expansion; the appendix does not expand them).
2. `IsWKESolution` (row 5 there): appendix SOURCE (equivalence via sealed `wkelwp`); mine RULED (D6, the
   docs/ERRATA-AND-DEVIATIONS.md §A table lists it as a D6 reading). `wkelwp_v1` is SEALED in the manifest.
3. U and its premise (row 10 there): appendix SOURCE; mine RULED (D6 selection device, §A table).
4. `Measurable (g n)` (row 9 there): appendix SOURCE; mine TYPING.
5. `d`, `γ`, `φ`, `α`, `T`: appendix folds them into SOURCE rows; mine TYPING.
6. `∃ θ`, `∃ L₀`: appendix rows 3, 6 as SOURCE; mine conclusion witnesses (not binders of the premise side).
7. Counts: appendix SOURCE 10 rows / TYPING 1 / RULED 1 (grouped rows) vs mine SOURCE 10 / TYPING 8 / RULED 4
   (per binder). Not comparable row-for-row; neither has EXCESS.

### Comparison with the seal script's logs and HANDOFF (read after my results)
`live-20261108T193926Z/run.log`, `live-run-2.out`, HANDOFF.md agree with every main_v2 number above: pre-seal ABI
`36fb4c1d…`, post-seal `21103400…`, `#print` diff value line only, pp.all type before = after, conclusion pp.all equal,
binders explicit vs implicit/autoParam, anchor and provider axioms standard, recheck "frozen diff = body only;
manifest fields ['abi_sha256','state']; DRAFT_SORRY anchors now 6". Disagreements: F1 (the brief's `Expr.equal`
wording; the script itself claims only pp.all), F4 (the logged full ABI check aborted). The seal script checked
axioms of the anchor and provider only; I also checked the assembly, helpers and consumed anchors (all standard).

### Files
Report and evidence: `/home/scott/wt-scratch/seal-audit-main_v2-B/` — `export/` (clean archive), `freeze-MainV2.lean`,
`notes/` (01 source reconstruction, 02 five-bin table, 03 own results before the appendix), `probes/` (P1–P4 sources and
outputs, setup files), `abi/` (pre/post `#print`, pp.all, repr), `preseal/` (overlay build of the freeze sources),
`replay/` (kit, diffs, `Replay-quick.out`), `fullabi/`, `tools/` (own scripts: setup generator, prefix/suffix, manifest
diff, closure, Lake text/binary hashes, trace and olean checks, full ABI), `evidence-tracecheck.out`,
`evidence-oleancheck.out`. Nothing outside this directory was written; no repository checkout was modified; nothing pushed.

`main_v2` may be recorded as PROVED (key B)
