# Seal audit: `WaveTurbulence.layergarden_v2` (B1.2 `layergarden`, γ ∈ (1/2, 1) successor), tag seal-lg2

Auditor: independent Opus (O-SEAL-LG2; brief `/home/scott/wt-scratch/sonnet-briefs/O-SEAL-LG2.md`, sha256 `902015ad…`,
pinned copy `brief.pinned.md`). Refute-first, following the lean-statement-audit seal checks. Date: 2026-11-07.
I did not write any of the anchor, the provider or the proof chain.

**Subject.**
- Seal commits on origin/main:
  - `0567017f` "Seal layergarden_v2 with batch 4b-3's VineEst.layergarden_v2_proof";
  - `cd80ff86` "manifest: ABI hash of the sealed layergarden_v2 (scripts/abi_hash_setup.py)".
- Proof landing: batch 4b-3, `6b8a1414` (merge of w/port-b4b3) and `68820285` (root import of `VineEst.V5Proof`).
- Statement freeze: `8d7ccb4a` "Freeze the gamma in (1/2,1) versioned successors (ruling D10)".
- `origin/main` = `cd80ff86` = HEAD of `/home/scott/WaveTurbulence-dev`, with a clean working tree.

**Manifest entry `layergarden_v2`.**
- export `WaveTurbulence.layergarden_v2`, path `WaveTurbulence/Frozen/Theorems/LayergardenV2.lean`, kind theorem, state
  `SEALED`;
- implementation `WaveTurbulence.Provider.LayergardenV2` / `WaveTurbulence.Provider.layergarden_v2`;
- source T Prop `layergarden`, L761–L779 (TeX sha256 `493eef6b…`, re-hashed: matches), restricted to 1/2 < γ < 1 (D9, D10,
  erratum E1); approval `docs/DECISIONS.md#D10`, split policy NOT_SPLIT;
- prefix `7e743631…`, suffix `9f481990…`, abi `bdc21757…`, definition closure of 101 files.

**Evidence base.** All evidence is my own, from:
- a clean `git archive cd80ff86` under `export/`;
- niced, one-at-a-time Lean processes against the dev checkout's land_check build;
- my own compile of the freeze-commit anchor and stub in a scratch root.

No log of the seal commit is relied on. Lake's own source hashes confirm that the build is of the sealed sources:
`Hash.ofText` of the anchor, provider and `V5Proof` sources equals the hash in each `.trace`
(`31fec510…`, `f44519a0…`, `7a45b323…`).

## Verdict

| Item | Verdict |
|---|---|
| (a) anchor bytes: only the registered proof body changed; prefix/suffix = manifest; guard on a clean export | **PASS** |
| (b) provider: no anchor import; statement verbatim (text and elaborated `Expr`); proved by `VineEst.layergarden_v2_proof` | **PASS** |
| (c) `#print axioms WaveTurbulence.layergarden_v2` | **PASS**: `[propext, Classical.choice, Quot.sound]` |
| (d) no hidden hypothesis in the chain; no vacuous gate | **PASS** |
| (e) `abi_sha256` change is only the proof term; both hashes reproduced; `abi_hash_setup.py` = `abi_hash.py` quantity | **PASS** |
| (f) kernel replay of the full closure, no shim, nothing forced to an axiom | **PASS (quick mode)**: `REPLAY OK`, 199,707 constants, 5,861 s |
| (g) status fields | DRAFT_ANCHORS 10; UNREGISTERED_SORRIES 0; DRAFT_IMPORT_VIOLATIONS 0; SEALED_THIS_TURN `layergarden_v2` |

**`layergarden_v2` may be recorded as PROVED.**

The status is restricted to 1/2 < γ < 1, per the frozen statement and D9/D10. The original `layergarden_v1` stays
DRAFT_SORRY.

Caveat on (f): quick mode checks 40,618 theorems of the `WaveTurbulenceVineParam` certificate library by statement only.
These are the theorems whose proofs use no project constant outside that library. Full mode was not run (see (f)).

## (a) Anchor bytes

- `git diff 8d7ccb4a cd80ff86 -- WaveTurbulence/Frozen/Theorems/LayergardenV2.lean` is one line in the proof region:
  `  by sorry` → `  by exact WaveTurbulence.Provider.layergarden_v2`. This is the file's only change since the freeze;
  `git log` lists only `8d7ccb4a` and `0567017f` for this file.
- I recomputed the region hashes with the guard's convention (`evidence/regionhash.py`): the prefix runs through the
  `FROZEN_ANCHOR_PROOF_BEGIN` line, and the suffix starts at the `FROZEN_ANCHOR_PROOF_END` line.

  | File | prefix | suffix | body |
  |---|---|---|---|
  | freeze `8d7ccb4a` | `7e743631…` = manifest | `9f481990…` = manifest | `  by sorry` |
  | sealed `cd80ff86` | `7e743631…` = manifest | `9f481990…` = manifest | `  by exact WaveTurbulence.Provider.layergarden_v2` |

  There are no CR bytes. The body matches the guard's SEALED rule (`by exact <implementation.export>`).
- The manifest entry changed between `8d7ccb4a` and `cd80ff86` in exactly two fields: `state` (DRAFT_SORRY → SEALED) and
  `abi_sha256` (`1d50de53…` → `bdc21757…`). All 101 `definition_closure` file hashes match the export.
- On a clean `git archive cd80ff86` export:
  - `python3 -I scripts/check_frozen_anchors.py --root . --manifest manifest/frozen.json` prints
    **`FROZEN-ANCHOR GUARD OK`**;
  - `scripts/check_lean_modules.py` prints `PASS (11657 Lean files)` (`evidence/guard.out`).
- The other changes in the seal commit are consistent:
  - the anchor and provider left the lakefile quarantine list, and the other 10 draft pairs remain;
  - the root `WaveTurbulence.lean` imports the anchor;
  - `scripts/abi_hash_setup.py` was added;
  - the provider gained `import VineEst.V5Proof` and the theorem;
  - the provider export is used only by the anchor (`grep`), and the provider module is imported only by the anchor.
- Lean-side confirmation:
  - The sealed anchor's olean stores the value `WaveTurbulence.Provider.layergarden_v2` (`probes/DumpType.lean`).
  - Its **elaborated type** (raw `Expr` dump, all olean parts) is byte-identical to the type I elaborated from the
    freeze-commit files in the freeze environment: Mathlib + frozen defs + the stub provider, compiled in
    `preseal/`. Both dumps have sha256 `11750e25…`.
  - So importing `V5Proof` through the provider did not change the elaboration of the frozen statement: no new
    instance or coercion was picked up.

## (b) Provider

- **No anchor import.**
  - Source imports: Mathlib, the same 14 `Frozen.Defs.*` as the anchor, and `Foundations.VineEst.V5Proof`.
  - In Lake's resolved closure (`.lake/build/ir/.../Provider/LayergardenV2.setup.json`, 19,114 modules), the anchor
    module is absent. The only `Frozen.Theorems.*` and `Provider.*` modules present are `RegularAsymptotics`, which is
    SEALED. No DRAFT anchor or DRAFT provider is in the closure.
  - The guard's reverse-import check passes.
- **Statement verbatim.**
  - Text: the 883 bytes from `theorem layergarden_v2 :` through `:=` are byte-identical in the two files. The only
    contextual differences are the namespace (`WaveTurbulence.Provider` vs `WaveTurbulence`) and a cosmetic duplicated
    `public section` line in the provider.
  - Elaborated (probe P1): the provider's type and the anchor's type are `Expr.==` **true** and `Expr.equal`
    **true**; their raw dumps are identical. Neither has universe parameters.
  - `example : type_of% @layergarden_v2 = type_of% @Provider.layergarden_v2 := rfl` checks.
  - Exact-type check: an `example` whose type is the frozen statement text, pasted, and whose body is the term
    `WaveTurbulence.layergarden_v2` elaborates. P1 produced no errors.
- **Proof.**
  - The provider body is the term `WaveTurbulence.VineEst.layergarden_v2_proof`, whose type is
    `LGSpine.LayergardenV2Gate`, an abbrev of `V2Chain.LayergardenV2Gate`.
  - `rfl` checks hold for anchor type = `V2Chain.LayergardenV2Gate` and anchor type = `LGSpine.LayergardenV2Gate`.
  - Structural difference between the anchor type and the gate body: the inline `Nat.AtLeastTwo` / `NeZero` instance
    *proofs* of numeric literals, which the `abbrev` elaborator abstracted as `V2Chain.LayergardenV2Gate._proof_1..4`.
    These are only `Prop`-valued instance arguments, defeq by proof irrelevance (`evidence/P1-anchor-vs-gate.diff`). The
    gate body is byte-identical to the dump of the earlier port-b4b3 audit.

## (c) Axioms

Probe P1 (module mode via a Lake setup file; see the method note) gives `[propext, Classical.choice, Quot.sound]` for:
- `WaveTurbulence.layergarden_v2`, `Provider.layergarden_v2` and `VineEst.layergarden_v2_proof`;
- `vineEstCanonLayerHalfMK`, `Spine.layergarden_v2_of_V5`, `stage1ReductionGate_of_V5'` and
  `layergarden_v2_of_stage1_finalCount`;
- `FinalCountAsm.finalCount_half` and `Vine.Param.vineparam`;
- the five `Spine` source providers;
- the calibration `Real.exp_pos`.

**Method note.** In Lean 4.35, `#print axioms` (`Lean.Util.CollectAxioms`) does not walk imported bodies. It reads each
imported declaration's axiom list, precomputed into its olean at serialization (`exportedAxiomsExt`). The module-mode
probe therefore reports the same data as a non-module probe, independently of which olean parts are mapped. Item (f)
is the independent body-level check: from every olean part directly, it finds no reachable project axiom, opaque,
unsafe or partial constant, and no direct user of `sorryAx`, `ofReduceBool` or `trustCompiler`.

## (d) Hidden hypotheses and vacuity

**Chain (source and compiled).**
- `Provider.layergarden_v2 := VineEst.layergarden_v2_proof`.
- `layergarden_v2_proof := Spine.layergarden_v2_of_V5 vineEstCanonLayerHalfMK`.
- `vineEstCanonLayerHalfMK := KindFinal.vineEstCanonLayerHalfMK_of_gates leafwise_coherent_approximation
  leafwise_incoherent_decay`.
- `layergarden_v2_of_V5 h := layergarden_v2_of_stage1_finalCount (stage1ReductionGate_of_V5' h) finalCount_half`.
- `stage1ReductionGate_of_V5' hV := Represents.stage1ReductionGate_of_V5 vineparam leafwise_incoherent_decay
  leafwise_coherent_approximation hV`.
- `layergarden_v2_of_stage1_finalCount := LGSpine.layergarden_v2_of_spine (spineInputs_of_stage1 hstage1) hcount`, with
  `spineInputs_of_stage1` = ⟨`leafwise_coherent_approximation`, `coherent_taylor`, `leafwise_incoherent_decay`,
  `coarse_spliced`, `ladder_fourier`, `hstage1`⟩.
- `finalCount_half := finalCount_half_of_low finalCount_low_half`, with `lowGardenBoundAll` built from
  `low_loop_class_bound_all`.

**Every input is a proved theorem.**
- The replay reads the real constant kinds from all olean parts. Every one of the 23 chain constants listed above,
  including `regularAsymptotics` (SEALED) and `vineEstCanonLayerHalfMK_of_gates`, is `theorem`, with
  `unsafe = false`.
- The four gate abbrevs (`V2Chain.LayergardenV2Gate`, `LGSpine.LayergardenV2Gate`, `FinalCountGateHalf`,
  `Stage1ReductionGate`) and `VINEPARAM` are `def : Prop`. `VineEstCanonLayerHalfMK` is a `def : WTParams → Prop`.
- None is a variable, axiom or `opaque`. The closed theorem types (`theorem X : Gate`) leave no room for section
  `variable`s.
- Across the whole tree, `evidence/sorryscan.py` finds 0 `axiom`/`opaque`/`constant` commands. It also finds 0 uses of
  `native_decide`, `implemented_by`, `debug.skipKernelTC`, `ofReduceBool`, `trustCompiler`, `elab_rules`,
  `macro_rules` or `addDecl`.

**No smuggled hypothesis.**
- The only binders of the chain theorems are discharged in the chain itself (`h`/`hV` by `vineEstCanonLayerHalfMK`;
  `hstage1` and `hcount` by `stage1ReductionGate_of_V5' …` and `finalCount_half`).
- `layergarden_v2_proof`'s type is exactly `LGSpine.LayergardenV2Gate`, as the replay's `EXACT` line shows.

**Gates against the frozen statement.**
- `V2Chain.LayergardenV2Gate` is token-for-token the frozen body (diff above). The proof establishes exactly the
  frozen type; it is not a variant with reordered quantifiers.
- The intermediate gates (`Stage1ReductionGate`, `FinalCountGateHalf`, `SpineInputs`, `VineEstCanonLayerHalfMK`) are
  hypotheses of conditional lemmas, each discharged by a proved theorem. Even if one were weak, it could not weaken the
  conclusion, whose type is fixed and is identical to the freeze elaboration (a).

**The frozen statement is not vacuous.**
- `WTPrefix` quantifies `γ ∈ (0,1)` and the data universally. Each prover choice (η₀, C₁, ν₀, δ₀, C₂, L₀) is followed by a
  non-empty universal range: η ∈ (0,η₀], ν ∈ (0,ν₀], δ ∈ (0,δ₀], L ≥ L₀.
- `τ★ = Dδ` with D ≥ 1 is met by δ = τ★/D for large D.
- The solution hypothesis `IsWKESolution φin τ★ φ` is inhabited for every φin and every small τ★, by the sealed
  `wkelwp` (τ_max > 0).
- In the body:
  - `1/2 < P.γ` is real division, `HDiv Real` in the raw `Expr`;
  - p = 0 < D;
  - `RemainderBound P 0 p` holds, since `SNormR` of 0 is 0, which is ≤ L^{-θ};
  - `Ioc p (p+1)` is non-empty, and N = 0 is allowed;
  - `R_{p+1} ≥ R_𝔇 = ⌊(log L)^{40d}⌋` is large for large L, so the m-range 2 ≤ m ≤ 10 R_{p+1} is non-empty;
  - `C₁` and `C₂` do not occur in Λ, θ, R, N or the conclusion.

**Source check (TeX L761–L779, re-read).**
- Conclusion (1) is (estgarden) for R = m ≥ 2.
- (2)(a) is the R = 1 diagonal statement.
- (2)(b) merges (estcouple) and (estcouple2).
- `RemainderBound` replaces the induction hypothesis, and t ∈ (p, p+1] extends the time p+1: deviations D1–D5 of
  WAVE-B v2 §4.2, approved in D7.
- `1/2 < γ` is ruled by D9 and D10 (erratum E1).

Five-bin count:

| Bin | Count | Binders |
|---|---|---|
| SOURCE | 6 | the source's own quantifiers: p < 𝔇, N ≤ N_{p+1}^4, 2 ≤ m ≤ 10R_{p+1}, ζ, balanced ζ, n |
| STANDING | 1 bundle | the `WTPrefix` parameter prefix (T L605–L615; sealed def): d ≥ 3, γ ∈ (0,1), η, φin ≥ 0, τ★ > 0, WKE solution φ, C₁, ν, δ, 𝔇 with τ★ = 𝔇δ, C₂, L |
| TYPING | 0 | |
| RULED | 3 | `1/2 < γ` (D10); `RemainderBound` replacing the induction hypothesis (D7, WAVE-B §4.2 D1); t ∈ (p, p+1] (D7, D2) |
| EXCESS | **0** | |

## (e) ABI hash

`scripts/abi_hash.py` defines the ABI hash as the sha256 of the stdout of `lake env lean` on the probe
`import <M>` / `#print <export>`.

| Build | Method | `#print` sha256 | Manifest |
|---|---|---|---|
| freeze-commit anchor (`by sorry`) and freeze-commit stub provider, compiled by me in `preseal/` with Lake's setup data of the identical-import v1 stub | `abi_hash.py`'s exact probe, plain `lake env lean`, scratch overlay first on `LEAN_PATH` | `1d50de53…` | old `abi_sha256` `1d50de53…` ✓ |
| same build | setup-file method (same transformation as `abi_hash_setup.py`) | `1d50de53…`; output byte-identical to the plain method | ✓ |
| sealed anchor (dev build) | `scripts/abi_hash_setup.py` as committed | `bdc21757…` | new `abi_sha256` `bdc21757…` ✓ |
| sealed anchor | plain method | fails: `failed to read … J1VI032.olean.private` (vm.max_map_count 65530, confirmed) | — |

- `diff` of the two prints (`preseal/abi/preseal-print.txt` vs `evidence/sealed-print-setup.txt`) is one line, line 22,
  the proof term: `< sorry` / `> WaveTurbulence.Provider.layergarden_v2`. The 21 type lines are byte-identical. **The
  `abi_sha256` change is due only to the proof term.**
- **Audit of `scripts/abi_hash_setup.py`.**
  - It differs from `abi_hash.py` in two ways:
    - the probe is a module file, `module` / `import all <M>` / `#print <export>`;
    - imports are resolved through `<M>`'s Lake setup file, plus `<M>`'s own artifacts and every project module's
      `.olean.private`.
  - It keeps the failure conditions (non-zero rc, any stderr, "error" in stdout) and hashes raw stdout.
  - `#print` output carries no file path.
  - Equality of the computed quantity, checked empirically:
    - byte-identical output on this very anchor's freeze version (above);
    - on `sumint_v1` (`0ae1fc75…`), `incoherentDecay_v1` (`73816979…`) and `main_v2` (`36fb4c1d…`), both
      `abi_hash_setup.py` and the plain `abi_hash.py` probe reproduce the manifest hashes
      (`evidence/abi_calib_{setup,plain}.txt`).
  - Limits of the tool:
    - it is single-anchor, with no check/write mode;
    - it takes the base closure from Lake's setup file, so it requires an up-to-date build, as `abi_hash.py` does.

## (f) Kernel replay

**Tool.** `replay/Replay.lean` is adapted from `/home/scott/wt-scratch/port-b4b3/probe/Replay.lean` (sha256
`b6bb1126…`; diff in the file header).
- Changes:
  - root module `WaveTurbulence.Frozen.Theorems.LayergardenV2`;
  - root constant `WaveTurbulence.layergarden_v2`;
  - chain kinds, exactness checks, reachable frozen theorems and a kind histogram added.
- The kernel logic is unchanged.
- `lean --run` cannot bind the `@[extern "lean_environment_add"]` shim in the interpreter (first attempt:
  `replay/Replay-quick.attempt1-interpreter.out`). As the earlier auditor did, I compiled it as a standalone `lean_exe`
  in `replay/exe/`, a scratch Lake project that depends only on Lean core (same toolchain commit `eb6cafb7`).
- `replay/replay.sh quick` ran from `/home/scott/WaveTurbulence-dev` under `lake env`, `nice -n 5`, as one process,
  with no other Lean process running.

**Method (R143).**
- Full import closure of the anchor module, read from olean headers: 21,089 modules (10,976 library, 10,113 project).
- Library constants enter the base kernel environment from their exported parts, trusted: 661,703 constants.
- Every project constant reachable from the root (types, values, inductive families) is read from **all** olean parts
  (exported, server, private), after an index of 223,348 names.
- One `Kernel.Environment.replay` of all of them: no shim, and no constant is turned into an axiom on failure.
- Quick mode only: a `WaveTurbulenceVineParam` theorem whose proof uses no project constant outside that library
  enters as its statement.

**Result** (`replay/Replay-quick.out`, sha256 `956b30e2…`):

```
reachable: 209040; lib refs: 9333; MISSING: 0 []; project modules loaded: 9217
same-name constants in two loaded modules: 1452; of these with different type (or, non-theorems, different value): 0 []
project AXIOMS reachable: []
project OPAQUE reachable: []
project UNSAFE/PARTIAL reachable: []
direct users of sorryAx/ofReduceBool/trustCompiler/ofReduceNat: []
core axioms referenced directly by project terms: [Quot.sound, Classical.choice, propext]
reachable constants from Frozen.Theorems modules: [layergarden_v2 (LayergardenV2), regularAsymptotics (RegularAsymptotics)]
reachable project constants by kind (before stubbing): inductive 472, ctor 659, def 18737, theorem 179706, rec 133
reachable project constants: 199707 in 9217 modules; VineParam proofs checked by statement only: 40618;
  VineParam theorems replayed WITH proofs (cross-library): 92875
REPLAY OK (5861s): 199707 constants, no shim, no constant turned into an axiom
Elapsed 1:38:18, max RSS 5.25 GB, exit 0
```

The run's exactness lines confirm the seal chain:
- the anchor's value is `WaveTurbulence.Provider.layergarden_v2`;
- the provider's value is `VineEst.layergarden_v2_proof`;
- the provider's type is `==` and `Expr.equal` to the anchor's type;
- `layergarden_v2_proof : LGSpine.LayergardenV2Gate`.

**The replayed oleans are origin/main's.**
- For all 10,085 project modules of the closure, the source hash in the module's Lake `.trace` equals Lake's
  `Hash.ofText` of the same file in the clean `cd80ff86` export: 0 mismatches (`evidence/tracecheck.out`).
- My Python `Hash.ofText` (`evidence/lakehash.py`) was first validated against three Lean-computed values.
- 1,791 `WaveTurbulenceVineParam` modules record the build root `WaveTurbulence-worktrees/port-vp`; their source text
  is identical to main's.

**Scope of quick mode.**
- 40,618 VineParam-internal certificate theorems are checked by statement only. Their proofs were kernel-checked when
  those modules were compiled.
- The tree contains no `debug.skipKernelTC`, `addDecl`, `elab_rules`, `native_decide` or `implemented_by` (token scan).
- Every cross-library proof (92,875 VineParam theorems, including the R136 DegreeBlock/`realization_directed_degrees`
  family) was replayed with its proof.
- Full mode was not run: quick alone took 1h38m single-threaded. It is
  `/home/scott/wt-scratch/seal-lg2/replay/replay.sh full`, if wt-orch wants the extra 40,618 proofs replayed.

This completes the R143 requirement that batch 4b-3 left open.

## (g) Status fields

- DRAFT_ANCHORS: **10**, all theorem anchors in state `DRAFT_SORRY`:
  - `WaveTurbulence/Frozen/Theorems/Main.lean`
  - `WaveTurbulence/Frozen/Theorems/Fixedpoint.lean`
  - `WaveTurbulence/Frozen/Theorems/Layergarden.lean`
  - `WaveTurbulence/Frozen/Theorems/LayergardenFlower.lean`
  - `WaveTurbulence/Frozen/Theorems/Propansatz.lean`
  - `WaveTurbulence/Frozen/Theorems/MainV2.lean`
  - `WaveTurbulence/Frozen/Theorems/PropansatzV2.lean`
  - `WaveTurbulence/Frozen/Theorems/FixedpointV2.lean`
  - `WaveTurbulence/Frozen/Theorems/LayergardenFlowerV2.lean`
  - `WaveTurbulence/Frozen/Theorems/LayergardenFlowerV3.lean`

  The manifest has 327 entries: 300 definitions SEALED, 17 theorems SEALED (now including `layergarden_v2`) and 10
  theorems DRAFT_SORRY.
- UNREGISTERED_SORRIES: **0**.
  - The guard is OK on the clean export.
  - My independent comment-aware scan of all 11,657 `.lean` files finds exactly 10 `sorry` tokens. They are the 10
    registered `by sorry` bodies of the files above. There is no `admit`.
- DRAFT_IMPORT_VIOLATIONS: **0**. The guard's quarantine pass is OK, and the 10 draft anchor/provider pairs are still in
  the lakefile quarantine list.
- SEALED_THIS_TURN: `WaveTurbulence.layergarden_v2`, audited here (seal `0567017f`, ABI `cd80ff86`).

## Minor observations (non-blocking)

1. The provider file has a duplicated `public section` line (L34, L36), both unclosed at EOF. This is harmless: the
   elaborated type is `Expr.equal` to the anchor's. Remove it at the next edit.
2. `abi_hash_setup.py` is a manual single-anchor tool. A note in `abi_hash.py`, or a `--setup` mode there, would keep
   one definition of the quantity.
3. `git fetch` (remote-tracking refs only) was run once in `/home/scott/WaveTurbulence-dev` at the start. It changed
   nothing: origin/main was already `cd80ff86`. No other write was made in any repository checkout.

## Addendum: concurrent landing during the audit

Another session landed PORT FT1 on main while the replay ran: `e2ec222b`, `51ae1d63` and `f9ee36e0`, then
`89e2e136` "abi_hash.py: fall back to the setup-file probe…". Dev's HEAD, and the local `origin/main` ref, moved
`cd80ff86 → 89e2e136` at 13:01 and 13:23 UTC. None of this affects the audit:
- `git diff --name-status cd80ff86 89e2e136` shows 176 added files (`Foundations/FlowerTop/**`) and two modified files:
  the root `WaveTurbulence.lean` and `scripts/abi_hash.py`.
- Unchanged: the anchor, the provider, the manifest, the lakefile, `abi_hash_setup.py` and every module of the anchor's
  closure.
- No olean part of the 10,085 closure modules was written after 11:52:48 UTC. All probes and the replay therefore read
  the same land_check build of `cd80ff86`.
- The trace check (run after the landing) still matches all 10,085 sources to the `cd80ff86` export.
- The post-seal `abi_hash.py` change makes `abi_hash.py` call `abi_hash_setup.py` when the plain probe hits the map
  limit. This matches (e)'s finding that both compute the same quantity, and removes minor observation 2.

## Probes and evidence (`/home/scott/wt-scratch/seal-lg2/`, untracked)

| File | Purpose | sha256 |
|---|---|---|
| `brief.pinned.md` | brief as received | `902015ad…` |
| `export/` | clean `git archive cd80ff86` | — |
| `evidence/LayergardenV2.{freeze,sealed}.lean` | anchor at `8d7ccb4a` / `cd80ff86` | `cf685431…` / `124bef5c…` |
| `evidence/regionhash.py` | prefix/suffix hashes, guard convention | `47cafce4…` |
| `evidence/guard.out` | guard + module check on the export | `da8eb212…` |
| `evidence/sorryscan.{py,out}` | sorry/admit/axiom/opaque/bypass scan | `de85064d…` / `34c9ce47…` |
| `probes/mksetup.py`, `probes/P1.lean`, `evidence/P1.out` | module-mode probe: axioms, exact type, defeq, `Expr` equality | `bc0a0423…`, `e9a76b25…`, `f789df8b…` |
| `evidence/P1-{anchor,provider}-type.txt`, `evidence/P1-gate-body.txt` | raw `Expr` dumps | `11750e25…` (both), `cd6d50c9…` |
| `probes/DumpType.lean`, `evidence/{preseal-anchor,sealed-anchor}-type*.txt` | type straight from oleans | `a75e943d…`, `11750e25…` (both) |
| `preseal/` (`mk.py`, `src/`, `overlay/`) | freeze-commit anchor + stub compiled with Lake setup data | `d46101f6…` (`mk.py`) |
| `preseal/abi/preseal-print{,-setup}.txt` | old ABI, plain / setup method | `1d50de53…` (both) |
| `probes/setup_print.py`, `evidence/sealed-print-setup.txt` | new ABI print | `145956fa…`, `bdc21757…` |
| `evidence/print-preseal-vs-sealed.diff` | one-line diff (proof term) | `9487f72a…` |
| `evidence/abi_calib_{setup,plain}.txt`, `evidence/abi_setup_lg2.out` | tool calibration on sumint, incoherentDecay, main_v2 | `0e9f99a6…`, `09a8e1f3…`, `92727f73…` |
| `evidence/lakehash.py`, `evidence/tracecheck.{py,out}` | build traces = origin/main sources | `43e361ab…`, `2e68366d…` / `53385bc5…` |
| `replay/Replay.lean`, `replay/replay.sh`, `replay/exe/` | kernel replay | `6c943568…`, `b8298ed6…`, binary `73821ab1…` |
| `replay/Replay-quick.out` | replay log | `956b30e2…` |
