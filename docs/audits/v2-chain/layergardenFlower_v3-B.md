# SEAL AUDIT — `layergardenFlower_v3`, KEY-B (refute-first, independent)

- Anchor: `WaveTurbulence.layergardenFlower_v3` (`WaveTurbulence/Frozen/Theorems/LayergardenFlowerV3.lean`), T Prop
  `flowerest1` (L2279–L2305), versioned successor frozen at `f8874a9b` (ruling D13).
- Seal commits: `e8019624` "Seal layergardenFlower_v3 with its proved assembly (SEAL-PREP chain)" and
  `1e51bebf3dbb0d4aa3c8b41a0de72ae0dc4e1ca4` "manifest: ABI hash of the sealed layergardenFlower_v3". Final main
  `1987105a`. Main checkout HEAD at audit time is `e1449ba4`, which differs from `1987105a` only in README/docs.
- Provider: `WaveTurbulence.Provider.layergardenFlower_v3` := `WaveTurbulence.Flower.Top.layergardenFlower_v3_proof`
  (`WaveTurbulence.Foundations.Flower.Top.Proof`), landed by the flower port `14451183` and merged at `c43c7b36`.
- Auditor: KEY-B. I wrote none of the anchor, the provider, the proof chain or the seal script, and never saw KEY-A's
  work. Work directory: `<scratch>/seal-audit-layergardenFlower_v3-B/`. The clean export is
  `export/` (`git archive 1e51bebf`). Everything outside my directory was only read.
- Order of work: I wrote the (h) source reconstruction from raw TeX before reading any Lean
  (`h-source-reconstruction.md`). I wrote the (h) table before opening the claim appendix (`h-binder-table.md`). I
  recorded my results for every item (`my-results-before-appendix.md`) before reading the claim appendix and the seal
  logs. The comparison is in §Disagreements.

## Verdict table

| Item | Verdict | One-line evidence |
|---|---|---|
| (a) Anchor bytes | **PASS** | The only change since `f8874a9b` is the body, now `by exact WaveTurbulence.Provider.layergardenFlower_v3`. Prefix `d7203fd6…` and suffix `9f481990…`, recomputed by my own script, equal the manifest. The manifest entry changed only in `state` and `abi_sha256`. All 107 `definition_closure` hashes match. The guard and the module check pass on the clean export. |
| (b) Provider | **PASS** | No anchor import, at source level or in Lake's resolved closure. Its type is `Expr.equal` to the anchor's. Its body is the bare `Flower.Top.layergardenFlower_v3_proof` (0 binders). Its export is used only by the anchor. The proof closure comes in through a private import only: an anchor-only probe sees just 109 project modules and no proof-closure constant. |
| (c) Axioms | **PASS** | The anchor, the provider, the flower theorem, `CompMK.flowerest1_of_B3s_D6b_452`, `Fam.layergardenFlower_v3_of_cores` and the consumed sealed anchor `regularAsymptotics` all depend only on `[propext, Classical.choice, Quot.sound]`. |
| (d) Hidden hypotheses / vacuity | **PASS** | I traced the chain to closed theorems; every named input is discharged by a theorem or `norm_num`. The root type has 0 binders. The replay finds no project axiom, opaque, unsafe/partial constant or `sorryAx` user. Non-vacuity witnesses compile, using only the standard axioms. |
| (e) ABI | **PASS** | Pre-seal `a4a61eea…` and post-seal `33a97fdc…` reproduced. The `#print` outputs differ only in the value line. The `pp.all` type and the raw `Expr` are byte-identical before and after the seal. |
| (f) Kernel replay | **PASS** (quick mode) | 213,961 constants in 10,465 modules: REPLAY OK, 8,415 s of kernel replay, 2:21:14 wall, 6.10 GB peak RSS. 40,618 WaveTurbulenceVineParam-internal theorem proofs were checked by statement only (quick mode). Every replayed olean traces to the seal commit's sources (11,671 modules, 35,013 olean parts). |
| (g) Status fields | **PASS** | DRAFT_ANCHORS 9; UNREGISTERED_SORRIES 0; DRAFT_IMPORT_VIOLATIONS 0; SEALED_THIS_TURN `layergardenFlower_v3`. Documentation finding: the README status block is stale (see (g)). |
| (h) Five-bin table | **PASS** | 36 binder rows: SOURCE 13, STANDING 15, TYPING 0, RULED 8, **EXCESS 0**. |

## (a) Anchor bytes

- File sha256: freeze `9652454ceeac7979…` (= brief's `9652454c…`); seal `14d13d64dc14f30c…`. Unchanged from `1e51bebf`
  to `1987105a`.
- `git log f8874a9b^..1e51bebf -- <anchor>` lists only `f8874a9b` (freeze) and `e8019624` (seal).
  `git diff f8874a9b 1e51bebf` is exactly `-  by sorry` / `+  by exact WaveTurbulence.Provider.layergardenFlower_v3`.
- My own hasher is `tools/anchor_hash.py`, written from the guard's convention:
  - prefix = all bytes through the newline that ends the `FROZEN_ANCHOR_PROOF_BEGIN` line;
  - suffix = all bytes from the start of the `FROZEN_ANCHOR_PROOF_END` line.

  The freeze and seal files give the same values, equal to the manifest: prefix
  `d7203fd68e46e103ff1327afc146a4a70d1a0b0153c0714edd70109467d0b258`, suffix
  `9f48199048606af986e4911abed0172f6e65c9c8c91f1c2874961ad85a7ea8d0`. Seal body:
  `  by exact WaveTurbulence.Provider.layergardenFlower_v3\n` (56 bytes, one line; limits 3 lines / 240 bytes).
- Manifest (`tools/manifest_cmp.py`, freeze `f8874a9b` against seal `1e51bebf`):
  - changed fields: exactly `abi_sha256` (`a4a61eea…` → `33a97fdc…`) and `state` (`DRAFT_SORRY` → `SEALED`);
  - the definition closure has 107 entries with 0 mismatches against the export;
  - 327 anchors before and after, none added or removed;
  - between the parent of `e8019624` and `1e51bebf`, the only changed manifest entry is this anchor's;
  - the entry is identical at `1987105a`.
- Guard: `check_index.sh` needs a git index, so I ran its two steps on the clean export:
  - `check_frozen_anchors.py --root export --manifest export/manifest/frozen.json` → `FROZEN-ANCHOR GUARD OK` (5 m 21 s);
  - `check_lean_modules.py` → `PASS (13118 Lean files, 0 comparator configurations)`.

  Logs: `logs-guard.txt`, `logs-modules.txt`.

## (b) Provider

- File `WaveTurbulence/Provider/LayergardenFlowerV3.lean`, sha256 `c5af7df1514af63b…`. Imports:
  - `public import Mathlib` and the same 15 `WaveTurbulence.Frozen.Defs.*` as the anchor;
  - `import WaveTurbulence.Foundations.Flower.Top.Proof`, a private `import`, and nothing else.
- It does not import its anchor:
  - source: the guard's reverse-import check, and my own import-graph scan (`tools/status_scan.py`);
  - Lake: `.lake/build/ir/WaveTurbulence/Provider/LayergardenFlowerV3.setup.json` has 20,671 modules (11,640 project
    modules) and none is `Frozen.Theorems.LayergardenFlowerV3`. Its only `Frozen.Theorems` module is
    `RegularAsymptotics`.
- Freeze environment of the anchor. Lake's setup for the anchor module lists exactly the 107 `Frozen.Defs` modules
  (equal as a set to the manifest `definition_closure`), plus `Provider.LayergardenFlowerV3` (`.olean` and
  `.olean.server` only), plus the library.
  - Probe P6, a module that imports only the anchor, loads 109 project modules.
  - The only project constants outside `Frozen.Defs` are `WaveTurbulence.Provider.layergardenFlower_v3` and
    `WaveTurbulence.layergardenFlower_v3`.
  - `Flower.Top.layergardenFlower_v3_proof`, `V2Chain.LayergardenFlowerV3Gate` and `CompMK.flowerest1_of_B3s_D6b_452`
    are not visible.
  - The provider's type is (a) below, so the frozen statement elaborates against Mathlib, its 15 `Frozen.Defs` and the
    provider theorem only.
- Statement identity.
  - The source text from `theorem layergardenFlower_v3 :` to `:=` is byte-identical in anchor and provider (1,290
    bytes). Both are preceded by `open Classical in` and use the same opens.
  - Elaborated (probe P5, all relevant modules `import all`): `provider.type == anchor.type`, `Expr.equal` true, hash
    `2344925519` for both. Universe parameters `[]` for both.
- Body. The anchor value is `WaveTurbulence.Provider.layergardenFlower_v3`. The provider value is the bare constant
  `WaveTurbulence.Flower.Top.layergardenFlower_v3_proof`. Sources: `#print` in P9, and the replay's `EXACT` lines.
- Flower theorem. Its type is exactly `.const WaveTurbulence.V2Chain.LayergardenFlowerV3Gate []`, with 0 binders and
  level parameters `[]`. Both checks compile:
  - `example : type_of% @WaveTurbulence.layergardenFlower_v3 = V2Chain.LayergardenFlowerV3Gate := rfl`;
  - the same for the flower theorem.
- The gate against the frozen text.
  - `abbrev LayergardenFlowerV3Gate` (`GateTypes.lean:123`, preceded by `open Classical in`) has the same 324 tokens,
    with the same whitespace after strip, as the anchor statement.
  - Elaborated, the gate body is not `==` the anchor type. A structural diff (probe P7) finds exactly 12 differing
    leaves.
  - All 12 are proofs of the Prop-valued class `Nat.AtLeastTwo` (for 2, 4, 100, 80 and 9). The gate's module replaced
    them with auxiliary theorems `V2Chain.LayergardenV2Gate._proof_1/2` and `LayergardenFlowerV2Gate._proof_1/2/3`.
  - Probe P8: each aux constant is a theorem in Prop whose value is the anchor's instance term. After inlining them the
    gate body is `==` the anchor type. The gate and the anchor therefore differ only by proof irrelevance, and the
    seal's `rfl` is sound.
- `Decidable` instances. The two occurrences of `if ∀ j, pat j = .plain` elaborate, in the anchor and in the gate
  (identical outside the 12 Prop leaves), to
  `@Nat.decidableForallFin (2 * Pm) (fun j => pat j = FixPat.plain) (fun a => WaveTurbulence.instDecidableEqFixPat
  (pat a) FixPat.plain)`. `Classical.propDecidable` does not occur (P3 `pp.all`).
- Export used only by the anchor. At `1e51bebf` and at `1987105a`, the provider module and export occur only in the
  anchor and the provider. Consumers use the frozen export `WaveTurbulence.layergardenFlower_v3`, for example
  `Provider/FixedpointV2.lean:85`.

## (c) Axioms

Probes P5 and P13 run `#print axioms`. The constants are: `WaveTurbulence.layergardenFlower_v3`,
`WaveTurbulence.Provider.layergardenFlower_v3`, `WaveTurbulence.Flower.Top.layergardenFlower_v3_proof`,
`WaveTurbulence.Flower.CompMK.flowerest1_of_B3s_D6b_452`, `WaveTurbulence.Flower.Fam.layergardenFlower_v3_of_cores`,
the consumed sealed anchor `WaveTurbulence.regularAsymptotics` (manifest `regularAsymptotics_v1`, SEALED), and
`WaveTurbulence.existsUnique_regCpl_decodes` (see (d)). Each gives
`depends on axioms: [propext, Classical.choice, Quot.sound]`.

The replay reports exactly two reachable `Frozen.Theorems` constants: `regularAsymptotics` and the anchor. (f) is the
independent check.

## (d) Hidden hypotheses and vacuity

1. Chain. `tools/iter_trace.py` + `probes/P10.tmpl` trace the chain to closed theorems. The trace is an `Expr` walk
   over 305 theorem values, with 92 modules `import all` so that their bodies are visible. Output:
   `probes/P12.iter6.out`. Every explicit Prop input of each conditional theorem, and what discharges it:
   - `Top.layergardenFlower_v3_proof` = `CompMK.flowerest1_of_B3s_D6b_452 (cθ := MkSlotsG.cθGen)`:
     - `hcθ := le_max_left 1 _`, with `cθGen = max 1 (max twoLayerB (filterB chiDNS))`;
     - `hB := MkSlotsI.markedClassRepresentsMK_prefix le_rfl`, of type `WTPrefix (MarkedClassRepresentsMK 452 cθGen)`;
     - `hReg := ProtWhole.regularComponentTargetI_of ProtPin.protBoundGate`.
   - `flowerest1_of_B3s_D6b_452` → `flowerest1_of_B3s_D6b`, with `hcP : 0 ≤ 452` and `hcP' : 452 ≤ 500` by `norm_num`.
   - `flowerest1_of_B3s_D6b` → `Stage1MKGate.stage1ReductionAtMKFull_of_B3s hB`, which gives `∃ C₀ ≥ 2`, then
     `flowerest1_of_gate` (`⟨C₀, by omega, hG⟩`).
   - `stage1ReductionAtMKFull_of_B3s` → `stage1ReductionAtMKFull_of` with `hIX := Stage1MKGate.b2eIX` and
     `hZ := Stage1MKGate.zeroVanish_prefix`.
   - `flowerest1_of_gate` → `flowerest1_of_B4_D6b` → `flowerest1_of_inputs` with `hD7 := SelRes.selSumTargetT`.
   - `flowerest1_of_inputs` → `CapsStable.flower_v3_of_marked 18000`:
     - `hB0 : 0 ≤ 18000` and `hB : 18000 ≤ 24000` by `norm_num`;
     - `hM := CompMK.markedComponentBoundAtI_18000`, which goes through `markedComponentBoundAtI_of` with
       `hNR := nonregPrefix` (via `wtPrefix_sel_of_full`).
   - `CapsStable.flower_v3_of_marked` → `CapsComp.flower_v3_of_marked_of_stable` with
     `hst := CapsStable.capsTwistStable`.
   - `CapsComp…` → `MkAsm.flower_v3_of_marked_of_caps` (`capsDecompF/G_of_stable hst`).
   - `MkAsm…` → `MkAsm.flower_v3_of_marked` (`coreF/GOfComponents_of_caps`).
   - `MkAsm.flower_v3_of_marked` → `Fam.layergardenFlower_v3_of_cores BcMK BcMK_hBc …`, where `BcMK d = 100000·d` and
     `BcMK_hBc` is a proved theorem.
   - `layergardenFlower_v3_of_cores` → `layergardenFlower_v3_of_families` (main's M1).

   The names match the brief's expected chain. The replay's `CHAIN` lines confirm that each listed name is a
   `theorem`, or a `def` for the gate, `BcMK` and `cθGen`, with `unsafe=false`.
2. No room for a premise. The root's type is the closed constant `LayergardenFlowerV3Gate`, with 0 binders, so no
   `variable` or `include` can add one. Its type is the anchor's, up to proof irrelevance (b). The replay finds 0
   project axioms, opaque, unsafe or partial constants, and 0 direct users of
   `sorryAx`/`ofReduceBool`/`trustCompiler`/`ofReduceNat`. It also finds 0 missing constants.
3. Budget parameters are instantiated, not assumed:
   - `cP = 452` with `0 ≤ cP ≤ 500` (`norm_num`);
   - `B = 18000` with `0 ≤ B ≤ 24000` (`norm_num`);
   - `BcMK = 10⁵ d` with `BcMK d + 80d + 3 < (100d)³` for `d ≥ 3` (the theorem `BcMK_hBc`);
   - `cθ = cθGen ≥ 1` (`le_max_left`);
   - `C₀ ≥ 2` comes from the existential of B4.
4. Non-vacuity. `probes/NV.lean` imports only the anchor; its axioms are the standard three. It compiles:
   - `prefix_ranges`: for every prover choice `η₀, ν₀, δ₀ > 0`, any `P₀` and any `L₀`, the ranges `η ∈ (0,η₀]`,
     `ν ∈ (0,ν₀]`, `Pm ≥ P₀` and `L ≥ L₀` are non-empty. There is also `δ = 1/D ∈ (0,δ₀]` with
     `D = ⌈1/δ₀⌉₊ + 1 ≥ 1` and `τ★ = 1 = D·δ`. `d = 3` and `γ = 3/4 ∈ (0,1)` with `1/2 < γ`.
   - `wke_zero`: `φin = 0` is Schwartz and `≥ 0`, and `IsWKESolution 0 τ (fun _ => 0)` holds for every `τ`.
   - `remainder_zero`: `RemainderBound P (fun _ _ => 0) p` holds for every `P` and `p`.
   - `windows`: `0 < D`; `1/2 ∈ Ioo 0 1`; `1/4 ∈ Ioo 0 (1/2)`; `N = 0 ≤ N_{p+1}^4`.
   - `hcut_none`: `cut2 = none` makes `hcut` vacuous.
   - `hcut_some`: for `cut2 = some j₂`, `cut1 = some j₁`, `d ≥ 1` and `L > 0`, a lattice point `n` with
     `(2^{j₁}L)^{10} ≤ ‖n/L‖` exists.
   - Every `FlowerKind`, every pattern vector, `dagger = none` or `some` and every `TreeKind` are inhabited. The
     couple premise `kind = .tr → dt = true` is satisfiable (`.L0` with any `dt`, `.tr` with `true`).
   - The exact-type `example`, with the frozen statement retyped and closed by `WaveTurbulence.layergardenFlower_v3`,
     compiles in the freeze environment.
5. Observation (not a defect). The chain consumes `WaveTurbulence.existsUnique_regCpl_decodes` and
   `WaveTurbulence.Reg.size_eq_order` from `Foundations.Molecule.B2CharacterizationProofs` and
   `Foundations.RegStruct.CodeOrders`.
   - The first has the same name as the sealed O2 export (`Frozen/Theorems/ExistsUnique_regCpl_decodes.lean`), the
     same statement text and the same proof route (`Reg.isRegularCouple_existsUnique_structure`). It is a proved
     theorem, replayed with its proof.
   - The sealed O2 module is not in this closure. Within the closure, the replay's olean index has 0 duplicate
     real declarations, only auto-generated `congr_simp`/`eq_N`/`_sparseCasesOn` lemmas. 0 same-name constants
     differ in type or value.
   - The two cannot be imported into one environment. This is harmless here, because the provider's import is
     private, but it is worth recording.

## (e) ABI

- Method: my own setup generator, `tools/mksetup.py`. It starts from Lake's `.lake/build/ir/<M>.setup.json`, adds
  `M`'s own artifacts, and lists private parts only for the modules I name. The probe is
  `module / import all <M> / #print <export>`. Lean v4.35.0 runs through the campaign throttle wrapper, `nice -n 10`.
- Post-seal: P1 against main's build gives sha256(stdout) = `33a97fdc4f3abb59a6d5e54468a15c0f2c8c243359efbfc70d62d3a4e9ba5044`,
  equal to the manifest.
- Pre-seal. I compiled the freeze-commit stub provider (`a208920d…`, imports only) and the freeze anchor
  (`9652454c…`, `by sorry`) into `probes/freezebuild/`, against main's `Frozen.Defs` oleans; the definitions are
  unchanged since the freeze. P2 gives `a4a61eeae7291bc1a7a03ae3e2e35b38e860bd8981efb9575b9a6cd45e91a840`, equal to
  the freeze manifest and the brief.
- `diff P1.out P2.out`: one line, the value: `WaveTurbulence.Provider.layergardenFlower_v3` against `sorry`.
- Fully explicit type, P3 (post) against P4 (pre): `set_option pp.all true` `#check` plus the raw `Expr`
  (`dbgToString`). The outputs (47,149 bytes) are identical except for my timing line. `hash` is `2344925519` in both.
  The new imports cause no elaboration drift in instances, coercions or notations.

## (f) Kernel replay

- Adapted from `<scratch>/seal-lg2/replay/` (`Replay.lean` sha256 `6c943568…`). I read it first. Diff:
  `replay/Replay.diff`, 75 lines. Changes:
  - root module and constant;
  - `wanted` chain list;
  - `EXACT` checks for anchor, provider and flower theorem;
  - an explicit `STUBBED` count and an honest final message;
  - module-list outputs.

  `replay.sh` sets `LEAN_PATH` to main's build itself, with no `lake env` in the main checkout, and uses `nice -n 10`.
  Exe source `replay/exe/Replay.lean`, sha256 `b663023c…`.
- Result (`replay/Replay-quick.out`):
  - closure: 22,647 modules (10,976 library, 11,671 project), from all olean headers, public and private imports;
  - reachable from `WaveTurbulence.layergardenFlower_v3`: 223,796 constants; library refs 9,835; MISSING 0;
  - project constants replayed: **213,961** in **10,465** modules (563 inductive, 776 ctor, 21,234 def, 191,244
    theorem, 144 rec before stubbing);
  - **REPLAY OK** in 8,415 s of kernel time; 2:21:14 wall; **6,099,228 KB** max RSS;
  - no shim, and nothing turned into an axiom on failure.
- Quick mode: 40,618 `WaveTurbulenceVineParam` theorems, whose proofs use no constant outside that library, were sent
  to the kernel as statements only.
  - Their used constants were still traversed and classified, so axiom, opaque and sorry detection covers them.
  - 92,875 VineParam theorems with cross-library proofs were replayed with their proofs.
  - Full mode, with nothing stubbed, was not run.
  - The template's final line "no constant turned into an axiom" is misleading in quick mode. My line says
    "(of which 40618 statement-only in quick mode)".
- Project axioms, opaque, unsafe or partial constants reachable: none. Direct users of
  `sorryAx`/`ofReduceBool`/`trustCompiler`/`ofReduceNat`: none. Core axioms referenced: `Quot.sound`,
  `Classical.choice`, `propext`. Same-name constants across loaded modules: 1,591, of which 0 differ in type or value.
- Oleans come from the seal commit's sources. I wrote `tools/lakehash.py`, Lake 4.35's `Hash.ofText` and
  `Hash.ofByteArray` (MurmurHash64A seed 11, mixed with nil 1723), validated against a live trace.
  - With it, `tools/trace_check.py` covers all **11,671** project modules of the replayed closure. The source hash
    recorded in each module's `.trace` equals the Lake hash of the file in my clean `git archive 1e51bebf`.
  - All **35,013** olean parts (`.olean`, `.olean.server`, `.olean.private`) hash to the trace's output hashes.
    Problems: 0. Output: `trace-check-replay-closure.out`.
  - Source roots: 9,856 in `<repo>`. 1,815 VineParam modules were built in
    `<worktrees>/port-vp`, with identical source content.
  - Dependency checkouts (mathlib `56a00585…` v4.35.0, batteries, aesop, Qq, proofwidgets, plausible, importGraph,
    LeanSearchClient, Cli) are clean at their `lake-manifest.json` revisions. That manifest is identical at
    `1e51bebf`. Toolchain: Lean 4.35.0, commit `eb6cafb7…` (trace); binary sha256 `bf8d54e4…`.

## (g) Status fields (seal commit `1e51bebf`, clean export; `tools/status_scan.py` plus the guard)

- **DRAFT_ANCHORS: 9**, each with exactly one `sorry` token in code, its registered body:
  - `WaveTurbulence/Frozen/Theorems/Fixedpoint.lean`
  - `WaveTurbulence/Frozen/Theorems/FixedpointV2.lean`
  - `WaveTurbulence/Frozen/Theorems/Layergarden.lean`
  - `WaveTurbulence/Frozen/Theorems/LayergardenFlower.lean`
  - `WaveTurbulence/Frozen/Theorems/LayergardenFlowerV2.lean`
  - `WaveTurbulence/Frozen/Theorems/Main.lean`
  - `WaveTurbulence/Frozen/Theorems/MainV2.lean`
  - `WaveTurbulence/Frozen/Theorems/Propansatz.lean`
  - `WaveTurbulence/Frozen/Theorems/PropansatzV2.lean`

  At `1987105a` there are 6 (after `fixedpoint_v2`, `propansatz_v2` and `main_v2` were sealed).
- **UNREGISTERED_SORRIES: 0.** My comment- and string-stripped scan finds `sorry`/`admit` only in those 9 files; the
  guard agrees.
- **DRAFT_IMPORT_VIOLATIONS: 0.** My source import-graph reachability check agrees with the guard.
- **SEALED_THIS_TURN: `layergardenFlower_v3`.** The only state change in the manifest between the parent of
  `e8019624` and `1e51bebf`. 18 SEALED theorem anchors follow, against 17 before.
- **Finding (documentation, not a seal defect).** `README.md` at `1e51bebf`, and still at HEAD `e1449ba4`, reads
  "DRAFT_ANCHORS: 10 theorem anchors at DRAFT_SORRY (… layergardenFlower v1/v2/v3 …)" and "SEALED: 17 theorems". It
  is stale: it lists v3 as a draft. Should be 9 at the seal commit, and 6 drafts with 21 sealed theorems at
  `1987105a`.

## (h) Five-bin binder table

The full table, with citations, is in `h-binder-table.md`. The source reconstruction (TeX re-hashed:
`493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb`) is in `h-source-reconstruction.md`. I expanded
`WTPrefixP`, `IsWKESolution`, `RemainderBound` (→ `SNormR`/`SNorm`, `Λ_q`, `θ_q`), `FlowerKind`, `FixPat`,
`TreeKind`, `WTParams.N` (→ `R`, `Rdown`), `latticePoint`, `jbr` and `Mom`.

| # | Binder | Bin | Citation |
|---|---|---|---|
| 1–2 | `d`, `3 ≤ d` | STANDING | T L314 |
| 3–4 | `γ`, `γ ∈ Ioo 0 1` | STANDING | T L314 |
| 5–6 | `∃ η₀ > 0`, `η ∈ Ioc 0 η₀` | STANDING | T L606 |
| 7–8 | `φin : 𝓢(Mom d, ℝ)`, `0 ≤ φin` | STANDING | T L314; D6 |
| 9 | `τstar > 0` | STANDING | T L314, L606 |
| 10 | `φ`, `IsWKESolution φin τstar φ` | STANDING (D6 reading) | T L598, L606; D6 closed-interval solution class |
| 11 | `∃ C₁ ≥ 1` | STANDING | T L608 |
| 12 | `∃ ν₀ > 0`, `ν ∈ Ioc 0 ν₀` | STANDING | T L608 |
| 13 | `∃ P₀`, `Pm ≥ P₀` | SOURCE | T L2279 ("P large enough depending on C₁") |
| 14 | `∃ δ₀ > 0`, `δ ∈ Ioc 0 δ₀` | STANDING | T L608, L2279 |
| 15 | `D ≥ 1`, `τstar = D·δ` | STANDING | T (defD) L609 |
| 16 | `∃ C₂ ≥ 1`, `∃ L₀ ≥ 2`, `L ≥ L₀` | STANDING | T L610 |
| 17 | `1/2 < P.γ` | RULED | D9, D10, E1 |
| 18 | `p`, `p < P.D` | SOURCE | T L708 |
| 19 | `R : ℕ → Mom d → ℝ` | RULED | D7 (deterministic core); T L689 |
| 20 | `RemainderBound P R p` | RULED | D7; T (ansatz2) L695, used at L949–L951 |
| 21 | `t ∈ Ioo p (p+1)` | SOURCE | T L2263 |
| 22 | `s ∈ Ioo p t` | SOURCE | T L2263 |
| 23 | `n n' : Fin d → ℤ` | SOURCE | T L2279, ℤ_L^d (latticePoint) |
| 24 | `ζ : ℤˣ` | SOURCE | T L2268, L2280 |
| 25 | `N ≤ N_{p+1}^4` | RULED | D7; T L2290, L2302–L2304 |
| 26 | `kind : FlowerKind` | SOURCE (+E42) | T L2280–L2281; E42 (𝒳 without the trivial tree) under D7 |
| 27 | `pat : Fin (2Pm) → FixPat` | RULED | D7; T L2312, L2331 |
| 28 | `dagger` | RULED | D7; T L2327, L2331 |
| 29 | `cut1 cut2 : Option ℕ` | SOURCE (+D13 form) | T L2283, L2285; D13/E34 |
| 30 | `∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, (2^{j₁}L)^{10} ≤ ‖k‖` | SOURCE | T L2285 |
| 31 | couple `t ∈ Ioo p (p+1)` | SOURCE | T L2309 |
| 32 | couple `k : Mom d` | SOURCE | T L2309 (general carrier, stronger) |
| 33 | couple `N ≤ N_{p+1}^4` | RULED | D7; T L2290 |
| 34 | couple `kind : TreeKind` | SOURCE | T L2309, L2312 |
| 35 | couple `dt : Bool` | SOURCE | T L2312 |
| 36 | couple `kind = .tr → dt = true` | RULED | D7; T L2312 (scope of the added couple conclusion) |

Counts: SOURCE 13 (rows 13, 18, 21, 22, 23, 24, 26, 29, 30, 31, 32, 34, 35); STANDING 15 (rows 1–12, 14, 15, 16,
taking 1–2, 3–4, 5–6 and 7–8 as one row each, i.e. 1, 3, 5, 7, 9, 10, 11, 12, 14, 15, 16 plus the four sub-binders
2, 4, 6, 8); TYPING 0; RULED 8 (rows 17, 19, 20, 25, 27, 28, 33, 36); **EXCESS 0**.

Conclusion check:
- The flower bound `⟨k−ζk′⟩^{−4Λ_{p+1}P} · L^{c(100d)³P} · δ^{2νN} · [M₁^{−80dP}] · [M₂^{−P/9}, plain only]`, with
  `c = 1` for plain patterns and `c = 2` otherwise, matches T L2280, L2283, L2285, L2302–L2303 and L2331.
- 𝒴 and 𝒲 replace the extra factor `e^{−100N_{p+1}}` by the per-order bound with `N > N_{p+1}` (D7).
- The couple clause matches T L2312 (D7).
- The bound applies to the deterministic garden sum rather than `E_p|·|^{2P}` (the D7 per-order core).

Notes:
- N1, quantifier order. `WTPrefixP` chooses `P₀` after `ν`, so `P₀` may also depend on `ν`; T L2279 says "depending
  on C₁". This is a mild weakening, but it is fixed in the D7-approved `WTPrefixP`, so not EXCESS.
- N2. `∃ C₁` and `∃ C₂` are unused by Q, so they are prover-chosen and harmless.
- N3. `1 ≤ D` is implied by `τstar = D·δ > 0`.
- N4. The sealed definitions in the conclusion are bound to their D7/D13 anchors through the verified closure hashes.
  - `flowerSumP` is `flowerSum` verbatim except for `cutWeight1/2` → `cutWeight1P/2P`.
  - `layergardenFlower_v3` is `layergardenFlower_v2` verbatim except for `flowerSum` → `flowerSumP`, the name, the
    provider import and the docstring.

  Both match D13.

## Disagreements (after my own results were written)

- **Claim appendix, (h).** Both tables give **EXCESS 0**, and the conclusions match. Bin and granularity
  differences:
  1. The appendix has 23 grouped rows (SOURCE 7, STANDING 11, RULED 5); I have 36 rows (SOURCE 13, STANDING 15,
     RULED 8).
  2. Its row 8 (`P₀`, `Pm ≥ P₀`) is STANDING; I classify it SOURCE, since P is a premise of `flowerest1` itself
     (T L2279).
  3. Its row 23 makes the whole couple clause RULED. I classify `t`, `k`, `kind`, `dt` as SOURCE (T L2309/L2312) and
     only `N ≤ N_{p+1}^4` and `kind = .tr → dt = true` as RULED.
  4. Its row 19 (`kind`) does not cite E42 (the kind 𝒳 excludes the trivial flower tree); I add it as a qualifier.
  5. The appendix does not note the `P₀`-after-`ν` quantifier order (my N1).

  None of these is EXCESS.
- **Seal logs, run `live-20261108T191351Z`.**
  - It aborted at "layergardenFlower_v3 exact-type probe". Its probe imported only the anchor and referenced
    `V2Chain.LayergardenFlowerV3Gate`, which is invisible there ("Unknown identifier"). This agrees with my (b)
    visibility result.
  - Main was reset to `c43c7b36`. No defect in the anchor.
- **Seal logs, run `live-20261108T193926Z`.** Its v3 steps agree with mine: pre-seal `a4a61eea…`, post-seal
  `33a97fdc…`, print diff `sorry` → provider, provider/anchor `pp.all` text equal, axioms OK, recheck body-only, 9
  drafts. Its `.print.out` files equal my P1/P2 outputs, except for a trailing `exit 0` its probe tool appends. Two
  points it does not cover:
  1. It checked gate = anchor by `rfl` (definitional equality) only. I find the gate's elaborated body differs from
     the anchor type in 12 Prop proofs, auxiliary `Nat.AtLeastTwo` lemmas; this is harmless (b).
  2. The run ends with **`SEAL ABORT: full ABI check`**: the `WaveTurbulence.Mom` probe failed only because elan
     printed an override notice on stderr, so `full_abi.log` has no complete 327-anchor result. The brief's header
     ("full 327-anchor ABI OK") is not supported by these logs. My own recomputation is below.
- **Kernel replay.** The seal logs contain no replay. My replay is the only one evidenced here.

- **Full 327-anchor ABI (resolving the previous point).** `tools/full_abi.py` (sha256 `a2d7a3a9…`) recomputes the
  ABI of every manifest anchor against main's build. It uses my setup generator, one niced Lean per anchor, and
  compares with the `1987105a` manifest. Result: **327 OK, 0 different, 0 probe failures** (`full-abi.out`,
  `051f01df…`). The brief's claim therefore holds at `1987105a`, by my recomputation, even though the seal script's
  own full check aborted.

## Evidence (sha256)

- `export/WaveTurbulence/Frozen/Theorems/LayergardenFlowerV3.lean` `14d13d64dc14f30c6613321542f96ae7a3dfb4995a7e64059945b493254363be`
- `freeze-LayergardenFlowerV3.lean` (`f8874a9b`) `9652454ceeac79794a9070fd0c03f6e8609520d45af57ff8442d880a7feb74af`
- `export/WaveTurbulence/Provider/LayergardenFlowerV3.lean` `c5af7df1514af63bfa1fe609e33883508955d2b0c386ff2b27f08e9783497c16`
- `export/manifest/frozen.json` (`1e51bebf`) `f341769b642cc97d5060c458542872fe54b780dde573157875b01f34b082a95d`
- `probes/P1.out` (post-seal `#print`) `33a97fdc4f3abb59a6d5e54468a15c0f2c8c243359efbfc70d62d3a4e9ba5044`
- `probes/P2.out` (pre-seal `#print`) `a4a61eeae7291bc1a7a03ae3e2e35b38e860bd8981efb9575b9a6cd45e91a840`
- `replay/exe/Replay.lean` `b663023c7f6ff269e492930c66f66224ca6a105e6d6a98b08ad96a6993bd4515`; template
  `6c943568febffab154aecf5313bb04ee266b398a2c26ba855f1f8320c23ee98e`; diff `replay/Replay.diff`
  `1d3e77ca62e988cece028040f7708017d912489af827387cfe468fafe128f007`
- Tools: `tools/anchor_hash.py` `e40b03ca…`, `tools/mksetup.py` `b4bd3bab…`, `tools/lakehash.py` `ef8c2e70…`,
  `tools/trace_check.py` `537fbc16…`, `tools/status_scan.py` `7e7ac657…`, `tools/manifest_cmp.py` `f90bf6a6…`,
  `tools/full_abi.py` `a2d7a3a9…`, `tools/iter_trace.py` `40752ba3…`
- `probes/NV.lean` `c5433ba4…`; `replay/Replay-quick.out` `d787f57a…`; `trace-check-replay-closure.out` `e868858b…`;
  `full-abi.out` `051f01df…`
- Probes, all in `probes/`: P1–P13, NV, P12.iter*; outputs `*.out`. Replay: `replay/Replay-quick.out`.
- Machine discipline: Lean ran one process at a time, `nice -n 10`, through the campaign throttle wrapper. The peak
  was 6.1 GB (replay); probes used 3–5 GB.

## Findings that do not block the seal (for wt-orch)

1. `README.md`'s status block is stale at `1e51bebf` and at HEAD `e1449ba4`. It still lists `layergardenFlower_v3` as a
   draft ("10" drafts, "17 theorems" sealed).
2. The seal script's last run ended in `SEAL ABORT: full ABI check`, caused by elan's override notice on stderr. My
   full recomputation (327/327 OK) shows the manifest is right, but the script's check should run with
   `ELAN_NO_OVERRIDE_NOTICE=1`.
3. The kernel replay ran in quick mode only: 40,618 VineParam-internal certificate proofs were checked by statement
   only. The template's "no constant turned into an axiom" message hides this.
4. `WaveTurbulence.existsUnique_regCpl_decodes` exists twice: once as the sealed O2 export, and once as a same-statement
   proved theorem in `Foundations.Molecule.B2CharacterizationProofs`, which this chain uses. The two cannot be
   imported together.
5. The quantifier order in the D7-approved `WTPrefixP` lets `P₀` depend on `ν` as well as `C₁` (T L2279 says
   `C₁`). This is a mild, approved weakening.

`layergardenFlower_v3` may be recorded as PROVED (key B)
