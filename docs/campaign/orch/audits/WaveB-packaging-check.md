# Audit: Wave B tier B1 packaging check (`waveb-snap-4` against `waveb-snap-3`)

Auditor: `wt-orch` (Opus), refute-first. Date: 2026-11-03. Task 9a.

## Inputs

**Snapshot.** `/home/scott/wt-scratch/waveb-snap-4/`. All 14 entries of `SHA256SUMS` verify.

| File | sha256 | Δ lines vs snap 3 |
|---|---|---|
| `WaveB1-Core.lean` | `0b8477d9…` | 311 |
| `WaveB1-System.lean` | `8f4014fb…` | 690 (the proofs section moved out) |
| `WaveB1-Statements.lean` | `4592f5c3…` | 49 |
| `WaveB1-Sumint.lean` | `8863d8fa…` | 0 |
| `WaveB1-Lemmas.lean` (new, not frozen, 858 lines) | `7cf6df82…` | — |
| Core-, System-, Statements-probes | `8932feb2…`, `bbd812cc…`, `65b91224…` | 1 each (`+ public import WaveBDraft.Lemmas`) |
| Deferred, Deferred-probes, Bridges | `3bfcf873…`, `dc4c15fb…`, `3f58ca3a…` | 0 |
| `FreezeList.lean` (new) | `847cc81a…` | — |
| `FREEZE-LIST.md` (new) | `0fadaa62…` | — |
| `DESIGN.md` | `0d795ac6…` | 43 (CL-16–CL-18, file table) |

**Baseline.** `waveb-snap-3`, checked PASS in `WaveB-final-check.md`. My snapshot-3 build sources are byte-identical to it.

**Additional input.** The drafter's CANON proofs: `/home/scott/wt-scratch/canon/`, five files. They were built
against `canon/snap/`, which I checked byte-identical to snapshot 3 for Core, System and Statements.

## Verdict: PASS. Freeze-ready; no REQUIRED items.

- **The changes are packaging only.** Machine-checked against snapshot 3 (§2): with proofs erased, every frozen
  definition has the same value and type, reducibility, instance status and priority, and axioms. The only value
  changes are the two `DecidableEq` instances that replaced `deriving`, and those are propositionally unique.
- **Instance names are unchanged.** All 32 explicit names coincide with the names Lean auto-generated in snapshot 3.
  So no elaborated statement changes, down to the `Expr`.
- **Dependencies are closed** (§3).
  - The import closure of the four frozen modules contains only Mathlib/core, Wave A `WaveTurbulence.Frozen.Defs.*`
    and the four frozen modules. `WaveB1-Lemmas` cannot be reached.
  - No frozen declaration uses a project theorem or an anchor.
  - Exactly the 11 anchors depend on `sorryAx`. Everything else uses at most `propext, Classical.choice, Quot.sound`.
- **FREEZE-LIST is complete and correct** (§4).
  - My independent enumeration gives the same 202 names.
  - Kinds and files match the environment.
  - The *uses* column matches my independent closure edge for edge (834 edges), under its documented convention for
    shared auxiliaries.
- **All files elaborate** (§1): the 11 Lean files as modules, plus `FreezeList.lean`.
- **`canonicalCharacterization` is unaffected** (§5). Its snapshot-4 type is identical to snapshot 3's. The drafter's
  proof ports to snapshot 4 with one extra import, and the proved type is **syntactically** (`==`) the snapshot-4
  anchor, with standard axioms.

## 1. Elaboration (snapshot 4, my build root, one `lake env lean` at a time, `nice -n 5`)

| Module | Errors | `sorry` | Other warnings |
|---|---|---|---|
| Core | 0 | 0 | 0 |
| System | 0 | 0 | 0 |
| Statements | 0 | 10 (B1.1–B1.5, B1.7–B1.11) | 0 |
| Sumint | 0 | 1 (`sumint`, B1.6) | 0 |
| Lemmas | 0 | 0 | 0 |
| CoreProbes, SystemProbes, StatementsProbes | 0 | 0 | 0 |
| Deferred | 0 | 1 (`layergardenFlower`, deferred B1.12) | 0 |
| DeferredProbes, Bridges | 0 | 0 | 0 |
| `FreezeList.lean` (run) | 0 | — | 0; prints 202 rows |

- **Build order.** System, Statements and Sumint were compiled **before** Lemmas existed in the build root. So no
  frozen file needs Lemmas (CL-17's claim).
- **The `instance_reducible` attribute ordering** produces no warnings.

## 2. "Only packaging changed": verdict table

**Machine check.** `scratch/WaveB-pack-dump.lean` dumps every constant of the four frozen modules and of Lemmas, with:
- the type and the definition value, normalized by `Meta.transform`: every proof subterm (`isProof`) is replaced
  by one constant, and metadata is dropped;
- the reducibility status, instance flag and priority, and `collectAxioms`.

It ran against the snapshot-3 and snapshot-4 builds; `scratch/WaveB-pack-cmp.py` compares the two dumps.

**Results.**
- **Constants in both snapshots.** Types are identical after normalization, except:
  - hygienic binder names that carry the module name (`inst._@.WaveBDraft.System…` →
    `inst._@.WaveBDraft.Lemmas…`, in moved lemmas);
  - two auxiliary `_proof_1` constants (`GNode.root`, `GBranch.child`).
- **Values.** Identical for all definitions except `instDecidableEqTTree` and `instDecidableEqMarkTag`.
- **Reducibility, instance status and priority, axioms:** no difference.
- **Only in snapshot 3.** Compiler-generated constants:
  - the auxiliaries of the old proofs;
  - `MarkTag.ofNat` and `MarkTag.ofNat_ctorIdx` (from `deriving DecidableEq` on an enumeration);
  - `instDecidableEqTTree.decEq` and its auxiliaries.
  - A grep of every `.lean` file under `/home/scott/wt-scratch` and `WaveTurbulence-dev/WaveTurbulence` finds no
    consumer of any of them.
- **Only in snapshot 4.** `TTree.decEq` (with its compiler auxiliaries), new `_proof_n`/`_simp_n` auxiliaries, and
  the `_private` auxiliaries of the moved lemmas, now under the `WaveBDraft.Lemmas` prefix.

| Change (DESIGN CL) | Declarations | Verdict | Evidence |
|---|---|---|---|
| CL-16: `instance` becomes `@[instance_reducible, instance] def inst…` | 30: 24 Core, 3 System, 3 Statements | NEUTRAL | **The names equal the snapshot-3 auto-generated names**, so no instance constant was renamed. The value is identical. Reducibility is `instanceReducible`, the same as the snapshot-3 `instance` command. Priority is 1000 in both. `instFintypeFreeBranch` stays `noncomputable`. |
| CL-16: `deriving DecidableEq` becomes explicit | `TTree.decEq` with `instDecidableEqTTree`, and `instDecidableEqMarkTag` | NEUTRAL | `Decidable p` is a subsingleton, so the change has no propositional content. The new `TTree.decEq` is structural and reduces under `decide`: the module-mode probe proves `TTree.leaf ≠ TTree.node …` and `Fintype.card MarkTag = 2` by `decide`. The removed auto constants are unused. |
| CL-16: explicit `expose` omitted (the brief said `@[instance, expose] def`) | the 32 instance-defs | ACCEPT | From a **downstream module** (`scratch/WaveB-pack-expose.lean`, `module` header, public imports only), every definition of the four frozen modules shows as `defnInfo` (340, auxiliaries included). The 103 axiom-view constants are all theorems: anchors, `_proof_n`, equation lemmas, `injEq`, Prop projections. So the enclosing `@[expose] public section` does expose every definition and instance body. Checks by `rfl` and `decide` through `GNode.root` and `instFintypeGNode` (card = 8) succeed. |
| CL-17: proofs inlined into definitions | `GNode.root`, `GLeaf.toNode`, `GBranch.toNode`, `GBranch.child`, `LayeredGarden.parentLayer`, `instFintypeG{Node,Leaf,Branch}` | NEUTRAL | With proofs erased, the values are identical to snapshot 3. Only proof arguments changed: named lemmas became local `by` blocks. The inlined proofs restate the old lemma statements by induction. |
| CL-17: lemmas moved to `WaveB1-Lemmas.lean` | 50 theorems: 9 Core, 35 System, the 2 `χ₀` lemmas, the 4 lattice-sum lemmas | NEUTRAL (verbatim) | Text diff: the System proofs section is byte-identical; the other three blocks differ only by added `namespace`/`section`/`variable` wrappers and headers. Names are unchanged (fully qualified). Lemmas contains no definitions, instances or attributes, so no simp set or instance set changed. |
| CL-17: probes import Lemmas | 3 probe files | NEUTRAL | A one-line diff each. |
| CL-18: `FREEZE-LIST.md` and `FreezeList.lean` | — | CORRECT (§4) | — |
| Untouched | Sumint, Deferred, Deferred-probes, Bridges | — | 0-line diffs. |

## 3. Dependency closure (`scratch/WaveB-pack-deps.lean` + `WaveB-pack-freezelist.py`)

**The environment** imports only `WaveBDraft.Statements` and `WaveBDraft.Sumint`. Lemmas is **not** loaded.

**Import closure, project modules only.**
- the four frozen modules;
- Wave A: `Frozen.Defs.{Mom, LatticePoint, CollisionOp, IsWKESolution, InitialCoeff, PartialDeriv,
  NormLaplacian, TorusFourierCoeff, IsSmoothNLSSolution, KineticTime, StdComplexGaussian}`.

There is no Foundations module, no `WaveBDraft.Lemmas` and no probe module. Lemmas imports Statements, so a
frozen file importing it would create a cycle.

**Constant closure.** For each of the 202 declarations I traversed the type, the value and the constructor types.
Frozen-module auxiliaries are expanded transitively.
- Every constant reached is in a frozen module, in Mathlib/core, or one of 9 Wave A **definitions**:
  `Mom`, `latticePoint`, `collisionOp`, `IsWKESolution`, `initialCoeff`, `torusFourierCoeff`,
  `IsSmoothNLSSolution`, `kineticTime`, `stdComplexGaussian`.
- **No frozen declaration uses a theorem of any project module.** No Wave A theorem, and no anchor from a definition
  or from another anchor.
- **Axioms.** `sorryAx` occurs in exactly the 11 anchors. All other frozen constants use at most `propext`,
  `Classical.choice` and `Quot.sound`.

**Freeze set.** The 11 anchors are the set confirmed in Task 8b: `propansatz`, `layergarden`, `fixedpoint`,
`nlsAkBridge` (its type is unchanged, so `hD : 1 ≤ D` is kept), `wkeTaylor`, `countLemma`, `atomCountLemma`,
`quadExpSum2`, `quadExpSum3`, `canonicalCharacterization` and `sumint`.

## 4. FREEZE-LIST

| Claim | Check | Result |
|---|---|---|
| 202 declarations | My own filter over the environment excludes constructors, recursors, projections, matchers, `_`-prefixed components and the compiler suffixes. It yields 208 names: the same 202, plus `TTree.{leaf,node}.elim`, `MarkTag.{lower,equal}.elim`, `TTree.brecOn.{go,eq}` (compiler-generated, correctly excluded). | ✓ complete; nothing extra |
| 11 / 148 / 4 / 5 / 2 / 32 | Theorems, definitions, abbrevs (reducible: `TTree.Path`, `Slot`, `SumintShape.VIdx`, `SumintShape.TVar`), structures (`WTParams`, `Garden`, `LayeredGarden`, `SumintShape`, `SumintDatum`), inductives (`TTree`, `MarkTag`), instance-defs. These are checked against `ConstantInfo` and the reducibility status. The environment has 39 instance constants; the other 7 are compiler `_sizeOf_inst`. | ✓ |
| Per file 94 / 58 / 28 / 22 | Module of each name | ✓ |
| *uses* column | My independent direct-use closure, expanding `_proof_n`, `match_n` and `_private` auxiliaries without attributing them to their namesake (the convention in FREEZE-LIST's header), gives 834 edges, **identical**. Without that convention there are 24 one-way extras. Each goes through an auxiliary that Lean shares across declarations, e.g. `chi0`, `AnsatzAt`, `timeFT` → `coupling._proof_1`; `IsCanonH` → `IsCanonG.match_1`; `TTree.branching._f` → `TTree.order.match_1`. These are not semantic dependencies. | ✓ |
| `.md` = generator output | `FreezeList.lean` run on my build vs the `.md` rows: names, kinds, files and *uses* are identical, each file in source order. | ✓ |
| *source* column | Every row has one. 32 fall back to a section header (31 Core, 1 System) and 46 to the module docstring (21 System, 10 Statements, 15 Sumint); both are marked. | ✓ as labelled (O2) |
| Header claims | "No frozen declaration uses a proved theorem of the project"; "every proved non-anchor lemma is in Lemmas"; "imports only Frozen.Defs, Mathlib, each other" | ✓ (§3) |

## 5. `canonicalCharacterization` (packet D3 CANON) after CL-16+

**Statement.**
- The type is unchanged between snapshots 3 and 4. It is identical after proof erasure, and it contains no renamed
  instance constant, since no instance constant was renamed.
- Every definition it mentions has an identical value: `IsCanonG/C/H/GC`, `CanonCriterion`, `CanonInd`,
  `TopDecomp`, `TopDecompWith`, `IrreducibleAt`, `TopRegion`, `BelowSet`, `AttachLinkedOn`, `attachNodes`, `roots`,
  `IsPlain`, `IsFlowerGarden`, `IsCouple`, `Incomparable`.
- **So no CL-16+ edit affects it.**

**Port test.**
- I copied the five CANON files to my scratchpad (the originals are untouched). The only edit was the one the
  README predicts: `+ public import WaveBDraft.Lemmas` in `Basic`.
- Built against my snapshot-4 modules, all five compile with 0 errors and 0 `sorry`, including the drafter's
  `example … = type_of% @WaveTurbulence.canonicalCharacterization := rfl`.

**Checks** (`scratch/WaveB-pack-canoncheck.lean`):
- `WaveTurbulence.Canon.canonicalCharacterization` and the snapshot-4 anchor have **syntactically equal** types
  (`Expr ==`), which is stronger than the drafter's definitional `rfl`;
- the proof's axioms are `propext, Classical.choice, Quot.sound`;
- `truncSum_couple_eq_truncSumC` and `truncSum_couple_offDiag` (layergarden (2)(a)) use the same axioms.

## REQUIRED

None.

## OPTIONAL

- **O1. DESIGN "Checks after these edits" is stale and misplaced.**
  - The block moved below CL-18, so it reads as the post-CL-18 state. Its first bullet still says "13 draft anchors:
    12 theorems in `WaveB1-Statements.lean`" (pre-CL-12 wording).
  - **Add a "After CL-16–CL-18" entry:** all 12 files elaborate; the `sorry`s are 10 in Statements, 1 in Sumint and
    the deferred B1.12 in Deferred; frozen modules were compiled without Lemmas; 202 frozen declarations.
  - **Relabel the old bullets** with their CL ranges.
- **O2. Source column precision.**
  - The 46 `(file)` fallbacks are honest but sometimes misleading. All 21 System ones cite the module docstring
    "WAVE-B §2.3; T L545–L564; T Def `defcm`", which does not fit, for example:
    - `SNorm` (T (normX)/(normX2), L581–L585);
    - `timeFT`;
    - `phaseIntegral` (T Def `defkg`);
    - `jbr`, `single`, `slotOrder`, `partialMom`, `iterPartial`.
  - The next stage (source-level dependency graph anchored to frozen declarations) will need per-declaration
    citations. Add a TARGET citation to the docstrings of the 46 fallback rows before or right after the freeze.
    This is docstring-only, so it does not change meaning.
- **O3. Shared auxiliaries.** Tooling that attributes `X._proof_n` / `X.match_n` to `X` by name prefix will report
  spurious edges, e.g. `chi0 → coupling` or `IsCanonH → IsCanonG`. FREEZE-LIST's convention is the right one; keep
  it in any later manifest or dependency checker.
- **O4. Reproducibility.** `gen_freeze.py` is cited but is not in the snapshot. Its output is verified (§4), but
  land it next to `FreezeList.lean`.
- **O5. Forward note for B2 (not B1).**
  - `WaveB2-Molecules.lean` uses `TTree.branching_of_append_mem` in `TTree.dropLast_mem_branching`, which the body
    of the definition `GNode.parent` uses. The use is at L159 of the live draft and L158 of my stage-2/3 snapshot.
  - That lemma is now in `WaveB1-Lemmas.lean`. Against snapshot 4, the B2 drafts elaborate only with
    `import WaveBDraft.Lemmas`, and a frozen B2 would then depend on a non-frozen lemma.
  - **Fix:** apply the CL-17 treatment at B2 packaging time, i.e. inline the proof in `GNode.parent`. This
    complements my 9b O2 (re-elaborate B2 against snapshot 4).
  - The B2 probes reach `finite_chi0Vec_lattice` through `SystemProbes`, which now imports Lemmas, so they keep
    working.

## Author questions

None blocking.
- **Confirmation (no action needed if yes).** The CANON proofs land under Foundations importing the frozen files
  **and** the landed successor of `WaveB1-Lemmas`. The port test shows this one import is all they need.

## Probes (untracked, `scratch/`)

| File | sha256 | Purpose |
|---|---|---|
| `WaveB-pack-dump.lean` | `3aad9159…` | normalized environment dump (run on both snapshots; the snapshot-3 copy drops the Lemmas import) |
| `WaveB-pack-cmp.py` | `d03bac68…` | dump comparison |
| `WaveB-pack-deps.lean` | `83c73cb0…` | import closure and per-constant uses, without Lemmas |
| `WaveB-pack-freezelist.py` | `873274df…` | independent enumeration, kinds, closure, project-theorem and Wave A scan, *uses* comparison |
| `WaveB-pack-expose.lean` | `f9041f67…` | module-mode exposure check plus `decide`/`rfl` unfolding checks |
| `WaveB-pack-canoncheck.lean` | `32b44335…` | CANON port: syntactic statement equality and axioms |
