# Wave B tier-B2 freeze (ruling D8): landing plan

Prepared by `wt-orch` (Task 36), 2026-11-04.
- Branch **`w/freeze-b2`**, worktree `/home/scott/WaveTurbulence-worktrees/freeze-b2`. It is stacked on
  **`w/freeze-b1`** (tip `1c6b8c8`, see `FREEZE-B1-PLAN.md`), whose base is main `1ecb500`.
- **Nothing is landed or pushed.** The B2 freeze lands after the B1 freeze (D7), and only after the author approves
  the B2 final candidate as ruling D8.

## 1. What the branch contains (on top of `w/freeze-b1`)

| # | Commit | Content |
|---|---|---|
| 1 | `a013926` | **Guard: mutual blocks.** Definition anchors of one `mutual … end` block may share their file. **Needs your sign-off** (shared infrastructure). |
| 2 | `cd422f2` | **The B2 freeze** from `waveb2-snap-final`: 69 definition anchors (60 files), 7 `DRAFT_SORRY` theorem anchors, 7 provider stubs, manifest, quarantine, root imports. |
| 3 | `ae68961` | Seal O1 `RegCpl.exists_decodes`. Adds `Foundations/RegStruct` (151 modules) and the non-frozen `Foundations/WaveB/{FrozenB2, RegularHeldOut}`. |
| 4 | `ce9f4ac` | Seal O2 `existsUnique_regCpl_decodes`. |
| 5 | `f3edbaa` | Seal O3 `RegChain.exists_decodesTree`. |
| 6 | `5dadf10` | Seal O4 `existsUnique_regChain_decodesTree`. |
| 7 | `884ab44` | Seal O5 `RegCpl.size_eq_order`. |
| 8 | `1729afe` | Seal B2.2 `incoherentDecay`. Adds `Foundations/IncohInst` (104 modules). **Needs main's `Foundations/Incoh`** (§2, step C.5). |

The commits are linear. Merging any prefix of them is a consistent state, given the B1 branch below it.

### Commit 1: why the guard changes

**The problem.** The freeze set has nine `mutual` groups: the inductives `RegCpl`/`RegChain`, and eight mutually
recursive pairs over them (`trees`/`plug`, `pairsAt`, `wf`, `size`, `linksAt`, `dominant`, `JB`/`JBchain`,
`Mstar`/`Nstar`). Lean cannot split a mutual group across files. The guard required exactly one declaration per
frozen file, so these 18 declarations could not be frozen.

**The change.** Each member keeps its own manifest entry (export, source range, ABI, approval), and the members share
one file. The guard accepts a file owned by several entries only if all of these hold:
- every owner is a definition anchor with the same `full_file_sha256`;
- the file has exactly one `mutual … end` block and declares nothing outside it;
- the block declares exactly the owners' exports, none private, each a `def`, `abbrev`, `structure` or `inductive`.

The lexer also treats `mutual` as a block, so its bare `end` no longer closes the enclosing namespace.

**Checks.**
- On main, the patched guard's report is byte-identical to the current guard's (four files there contain mutual
  blocks).
- Refute tests on a copy of the branch fail for the intended reason:
  - a declaration outside the block;
  - two entries sharing a non-mutual file;
  - a member renamed.

  The restored copy passes.

**The alternative**, if you prefer it: one entry per mutual block. That gives 67 B2 entries and needs a new manifest
field and an ABI over all members. I chose the variant that keeps the schema and `abi_hash.py` unchanged.

### The freeze commit (2)

**From** `/home/scott/wt-scratch/waveb2-snap-final`: B2-CL-1 to CL-22, on B1 snapshot 9. `SHA256SUMS` verifies; its
digest is `b3db9c4367a8…`.

**The freeze set** (`FREEZE-LIST.md`, CL-22) has 76 declarations:
- **7 theorem anchors**: B2.1 `regularAsymptotics`, B2.2 `incoherentDecay`, O1–O5;
- **69 definitions**: 62 `def`, 2 `abbrev`, 1 `structure`, 3 `inductive`, 1 instance.
- The 89 held-out declarations are not frozen. They stay in the draft files.

**Files.**
- `WaveTurbulence/Frozen/Defs/`: 51 single-declaration files and 9 mutual-block files. A mutual-block file is named
  by its members' stems in source order, e.g. `RegCplRegChain.lean`.
- `WaveTurbulence/Frozen/Theorems/`: 7 anchors, each with the five `FROZEN_ANCHOR` markers and body `by sorry`.
- `WaveTurbulence/Provider/`: 7 stubs.

**Generation.** The B1 generator (Task 22), adapted.
- Each file holds the snapshot text verbatim, in its exact snapshot context (opens, namespace, variables).
- **Imports** are the frozen dependencies, computed from the compiled snapshot by the B1 metaprogram, extended so
  that B1's Core and System declarations are owners.
  - For all 76 rows, the B2 uses and the B1/Wave A uses agree exactly with `FREEZE-LIST.md`.
  - Every non-B2 dependency is a definition anchor already in the manifest (B1 or Wave A).

**`manifest/frozen.json`:** +76 entries in Wave A's schema.
- `approved_at` is **"PENDING-D8"**, with `approval_ref` `docs/DECISIONS.md#D8`.
- `contract` and `source_group`: `dh-long.b2.<name>`, `NOT_SPLIT`.
- `definition_closure` as for B1.
- `abi_sha256` is computed with `abi_hash.py`'s own `abi_hash`. Each member of a mutual block has its own ABI.

**Quarantine and root.** The lakefile quarantine gets +14 modules (the 7 anchors and their providers). The root gets
+60 definition imports.

### The seals (commits 3–8)

The B1 pattern:
- anchor body `by sorry` → `by exact WaveTurbulence.Provider.<export>` (prefix and suffix hashes unchanged);
- the provider;
- manifest `state` → SEALED, with the ABI recomputed;
- the quarantine lifted;
- the root imports added.

**O1–O5** (wt-resonant's REG-STRUCT; the providers are `waveb2-snap-final/providers/`, Task 32).
- The providers restate their anchors with implicit data binders and `by assumption` autoParams. Only their
  imports are renamed.
- **`Foundations/RegStruct/**`:** 151 of the 154 pinned REG-STRUCT modules. Bytes are checked against
  `REGSTRUCT-SHA256SUMS` at port time; only imports are renamed (verified mechanically).
- **The other three map to existing modules:**
  - `WaveBDraft.Core` → `FrozenB1`;
  - `WaveB2Draft.RegularDefs` → `RegularHeldOut`;
  - `WaveBDraft.CoreTreeLemmas` → `Foundations/WaveB/Lemmas`. Its nine lemmas are text-identical to lemmas of
    B1's sorry-free `Lemmas`, ported by the `canonicalCharacterization` seal; porting it again would duplicate
    their names.
- **`Foundations/WaveB/FrozenB2`:** imports `FrozenB1` and the 69 B2 definition anchors, and declares nothing.
- **`Foundations/WaveB/RegularHeldOut`** (non-frozen).
  - It is `WaveB2-Regular.lean` without its module doc, its frozen declarations (imported through `FrozenB2`) and
    its `sorry`'d §4 theorems (O1–O5 and `regular_count_le`). What remains is `MiniTreeCode.equiv` and seven
    instances.
  - The proofs need them, e.g. `instFintypeMiniTreeCode`. Task 32 and INCOH-INST built on the whole draft file, so
    they had them.
  - Each removed frozen chunk was checked to be verbatim in its frozen file.
  - Its constants are identical to the snapshot's (§3).

**B2.2 `incoherentDecay`** (wt-l2s's INCOH-INST).
- **The proof was built on snapshot 8's `System`.** I re-checked it on snapshot 9 first (`audits/INCOH-INST-snap9.md`).
  - Three files needed proof repairs (mine, no statement changes): `TimeBridge` (the `sumint` repair),
    `IncohInst/NormBridge`, `RegrefDraft/NormShift`.
  - All 264 modules compile.
  - The type audit passes with an independent snapshot-9 reference (B1 included): the literal theorem type and all
    215 reachable definitions.
  - The snapshot-8 proof fails it at `XNorm`.
- **`Foundations/IncohInst/**`:** 104 modules, with imports renamed only (plus the three repairs).
  - `IncohInst.*` (74);
  - `LinksDraft` (19) → `IncohInst.Links`;
  - `LayerRegDraft` (3) → `IncohInst.LayerReg`;
  - `EnhancedDraft` (2) → `IncohInst.Enhanced`;
  - `RegrefDraft` (5) and `SpatialBridge` → `IncohInst.Regref`.
- **The other 160 closure modules map to existing ones:**
  - REG-STRUCT as for O1;
  - `TimeBridge`/`Words`/`MultiIndices` → `Foundations/Sumint` (byte-identical scratch sources);
  - `WaveBDraft.System` → `FrozenB1`;
  - `WaveB2Draft.Regular` → `RegularHeldOut`;
  - `RegrefDraft.StatementsDefs` → `FrozenB2`. It restates `timeBox`, `timeBoxGt`, `InputRemainder` and `regBound`
    under the frozen names, text-identical to the frozen definitions.
- **The provider** is the anchor's statement, verbatim in its context, proved by
  `WaveTurbulence.IncohInst.incoherentDecay`. The anchor has no binders.
- **Dependency on main.** The proof imports 606 Wave A and Foundations modules, all byte-identical on main (at
  `fb053c9`) to those INCOH-INST used. 353 of them postdate the branch base: 352 in `Foundations/Incoh`, one in
  `Foundations/WKE` (`FREEZE-B2-MAIN-DEPS.txt`).

**Duplicate check.** The branch tip `1729afe`, with main's whole `WaveTurbulence/` tree (at `8f5c3f3`) laid over it,
2759 files: `land_check`'s duplicate and sorry scans were both OK. The first attempt found that REG-STRUCT's
`CoreTreeLemmas` duplicated nine lemmas of B1's `Lemmas`; it is now mapped, not ported.

## 2. Landing steps (orchestrator, on `main`)

**A. First, `w/freeze-b1`'s steps A–C** (`FREEZE-B1-PLAN.md`). In particular, its commit 2 (the `merge_branch.sh`
fix) must be on main before any branch with SEALED theorem anchors is merged.

**B. Sign-off and approval.**
1. Sign off commit 1 (the guard).
2. The author approves the B2 final candidate as **ruling D8**. Draft for `docs/DECISIONS.md`:

> D8 — 2026-11-?? — Scott ("…", in reply to the complete Wave B tier-B2 code shown for approval:
> `/home/scott/wt-scratch/waveb2-snap-final`, SHA256SUMS `b3db9c43…`, on B1 snapshot 9) — **Wave B tier B2 approved
> and frozen**: 7 `DRAFT_SORRY` theorem anchors (B2.1 `regularAsymptotics`, B2.2 `incoherentDecay`, and the decoding
> obligations O1 `RegCpl.exists_decodes`, O2 `existsUnique_regCpl_decodes`, O3 `RegChain.exists_decodesTree`, O4
> `existsUnique_regChain_decodesTree`, O5 `RegCpl.size_eq_order`) and 69 sealed definitions (FREEZE-LIST.md,
> B2-CL-22; 89 declarations held out, B2.3 among them). Audits: `WaveB2-stage1.md`, `WaveB2-stage23.md`,
> `WaveB2-handoff.md` (addenda 1–7), `WaveB2-independent-audit.md` (re-checks 1–2). Packaging (semantics-neutral): one
> declaration per file under `WaveTurbulence/Frozen/`, except that each of nine `mutual` blocks is one file shared by
> its members' entries (guard change `a013926`).

**C. Merge.**
1. Merge the freeze: `scripts/merge_branch.sh cd422f2` (with `a013926`). The O1–O5 seals may follow in the same
   merge or later.
2. Fill the date and check that no placeholder remains:

   ```bash
   sed -i 's/"approved_at": "PENDING-D8"/"approved_at": "2026-11-DD"/' manifest/frozen.json
   git add manifest/frozen.json
   grep -c PENDING-D8 manifest/frozen.json   # must print 0
   ```

   **The guard accepts the placeholder**, so the grep is the only check.
3. Add the D8 entry to the same commit.
4. Run the gate.
   - `scripts/land_check.sh`.
   - The ABI check, `python3 -I scripts/abi_hash.py --root . --manifest manifest/frozen.json`: it must print
     **317 `OK`** (241 + 76) and exit 0.
   - Commit and push.
5. **The B2.2 seal (`1729afe`) needs main's `Foundations/Incoh`** (352 modules) and
   `Foundations/WKE/TaylorGateNorm`, as of `fb053c9` (unchanged at `6118bca` and `8f5c3f3`).
   - Merge it only into a main that has them with the same bytes. The 353 paths and the check command are in
     `FREEZE-B2-MAIN-DEPS.txt`; the `git diff` must be empty.
   - On a main where they have changed, re-run the INCOH build before merging.
6. **Status after all eight commits:**
   - DRAFT_ANCHORS 6 + 1: B1's six, plus B2.1 `regularAsymptotics`;
   - SEALED_THIS_TURN 6.

**Seal audit.** I wrote the providers' ports, the two aggregators, `RegularHeldOut` and the three F80 repairs. Under the
two-key rule, the audit before marking O1–O5 and B2.2 PROVED must be someone else's.

**Rollback** before pushing: `git merge --abort` or `git reset --hard ORIG_HEAD`.

## 3. Verification (wt-orch; no `lake build`, per my brief)

**Build.** Every new module was compiled with `nice -n 5 lake env lean -o`, one at a time, in the worktree's
`.lake/build`:
- the freeze: 74 modules;
- O1: 154 modules plus the provider and the anchor;
- O2–O5: two modules each;
- B2.2: 104 modules plus the provider and the anchor.

0 errors. The warnings are the `sorry`s of the anchors still `DRAFT_SORRY` and style-linter warnings in unchanged
ported files.

**Statements identical to the snapshot.** The normalized constant dump of Tasks 22, 28 and 34: matchers and
auxiliaries delta-expanded, proofs erased.
- `WaveB2Draft.{Regular, Statements}` against the 67 frozen modules: **all 150 frozen constants identical**. The 45
  snapshot-only constants all belong to held-out declarations.
- `RegularHeldOut` against the snapshot: **its 8 constants identical** (`MiniTreeCode.equiv` and the seven
  instances).

**Guard and gates.** After every commit:
- FROZEN-ANCHOR GUARD OK;
- `check_index` OK and `check_lean_modules` PASS;
- `land_check`'s duplicate and sorry scans OK;
- the root module elaborates.

**ABI.** Full check on the clean tip `1729afe` (`python3 -I scripts/abi_hash.py --root . --manifest
manifest/frozen.json`): **317 `OK`** (241 Wave A and B1, 76 B2), exit 0.

**Axioms.** The five decoding anchors and `incoherentDecay` each depend on [propext, Classical.choice, Quot.sound].

## 4. Status at the branch tip

```text
DRAFT_ANCHORS: 7 at the tip (B1: Main, Propansatz, Layergarden, Fixedpoint, WkeTaylor, LayergardenFlower;
  B2: RegularAsymptotics); 13 after the B2 freeze commit alone
UNREGISTERED_SORRIES: 0 (sorry scan; guard)
DRAFT_IMPORT_VIOLATIONS: 0 (guard quarantine check)
SEALED_THIS_TURN: 6 on the branch, none landed (RegCpl.exists_decodes, existsUnique_regCpl_decodes,
  RegChain.exists_decodesTree, existsUnique_regChain_decodesTree, RegCpl.size_eq_order, incoherentDecay)
```

## 5. Caveats

- **Commit 1 changes the guard.** It needs your sign-off. The alternative is in §1.
- **`RegularHeldOut` puts eight held-out draft declarations into Foundations**, non-frozen, under their draft names
  (`WaveTurbulence.instFintypeMiniTreeCode` and so on). A later freeze of any of them must move them, not copy them.
- **Draft copies of other packets.** `Foundations/IncohInst/{Links, LayerReg, Enhanced, Regref}` are INCOH-INST's
  copies of the LINKS, LAYERREG, ENHANCED and REGREF drafts (namespaces `WaveTurbulence.Links`,
  `WaveTurbulence.Regref`). When those packets land, they must reuse these modules, or replace them in one commit, or
  their names will clash.
- **The three F80 proof repairs are mine.**
  - wt-l2s's and wt-anfourier's scratch still have the snapshot-8 versions.
  - INCOH-INST's own type audit could not see B1 changes (I-1, `INCOH-INST-snap9.md`).
- **The worktree's `.lake/build`** is a copy of `freeze-b1`'s, plus links to dev's oleans for the 259 main modules the
  B2.2 proof needs. Nothing was written into `WaveTurbulence-dev`.
