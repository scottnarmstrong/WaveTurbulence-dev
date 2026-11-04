# Wave B tier-B1 freeze (ruling D7): landing plan

Prepared by `wt-orch` (Task 22), 2026-11-04.
- Branch **`w/freeze-b1`**, worktree `/home/scott/WaveTurbulence-worktrees/freeze-b1`, based on main `1ecb500`.
- Main has had no change under `WaveTurbulence/`, `manifest/`, `scripts/` or `lakefile.lean` since that base.
- **Nothing is landed or pushed.** The freeze lands only after the author approves snapshot 6 as ruling D7.

## 1. What the branch contains

| # | Commit | Content |
|---|---|---|
| 1 | `4a97152` | **Guard: Lean Unicode identifiers.** `scripts/check_frozen_anchors.py` accepted only ASCII names, and three approved B1 exports are not ASCII: `SumintDatum.M₀`, `SumintDatum.M₁`, `SumintDatum.ℓVec`. The identifier classes now follow Lean core's `isLetterLike`/`isSubScriptAlnum`. The guard still passes on main. **Needs your sign-off** (it changes the guard). |
| 2 | `d36c45e` | **`merge_branch.sh` keeps SEALED theorem anchors in the root.** The script rebuilt the root import list from `Frozen/Defs`, `Foundations` and `Paper` only. The merge after the `wkelwp` seal (`53e73e4`) therefore silently dropped `public import WaveTurbulence.Frozen.Theorems.Wkelwp`, and **on main today the sealed `wkelwp` anchor is in no build target**. This commit fixes the script and restores the import. **Needs your sign-off.** |
| 3 | `4bb013d` | **The B1 freeze**: 214 definition anchors, 12 `DRAFT_SORRY` theorem anchors, 12 provider stubs, manifest, quarantine, root imports. |
| 4 | `c61f8a6` | Seal `countLemma` (B1.7). |
| 5 | `c6a8602` | Seal `atomCountLemma` (B1.8). |
| 6 | `d8d6c0a` | Seal `nlsAkBridge` (B1.4). Adds the `FrozenB1` aggregator and the NLS bridge port. |
| 7 | `d8c578b` | Seal `canonicalCharacterization` (B1.11). Adds the B1 Lemmas and CANON ports; needs commit 6's aggregator. |

The commits are linear. Merging any prefix of them is a consistent state.

### The freeze commit (3)

**From snapshot 6 (6b)**, `/home/scott/wt-scratch/waveb-snap-6` (SHA256SUMS verified; audit `WaveB-snapshot6.md`):
- **214 definition anchors**, one declaration per file, in `WaveTurbulence/Frozen/Defs/<Name>.lean`:
  - 167 `def`, 33 instance `def`s, 5 `structure`, 5 `inductive`, 4 `abbrev`;
  - every one is a SEALED whole-file anchor.
- **12 theorem anchors**, `DRAFT_SORRY`, in `WaveTurbulence/Frozen/Theorems/<Name>.lean`. Each has the five
  `FROZEN_ANCHOR` markers and the body `by sorry`, and its prefix imports its provider.
- **12 provider stubs** in `WaveTurbulence/Provider/<Name>.lean`: imports and module doc only, like Wave A's
  `Provider/Main.lean`.

**Generation.** A script produced the files from the snapshot text.
- Each file holds the declaration's docstring and text **verbatim**, inside the exact context it had in snapshot 6:
  - the file-level `open`s;
  - the enclosing `namespace`/`section`;
  - every `variable` in scope, in order, including the `variable {tree}` rebinding;
  - the one-shot `variable (tree) in` / `open Classical in`;
  - `universe u`.
- The only edit is in the 12 theorems: `:= by\n  sorry` becomes `:=` + the marked body `by sorry`, as in Wave A.
- **Imports** are the declaration's frozen dependencies: the owners of every constant in its type, body and
  auxiliary proofs, as B1's `FreezeList.lean` computes them, extended to Wave A. Three files also import the type
  named in a copied `variable` line they do not use: `epsCoef`, `resFactor` → `Garden`; `nodeSign` → `TTree`.
- **File names** are the CamelCase of the name; `M₀`, `M₁`, `ℓVec` become `SumintDatumM0`, `SumintDatumM1`,
  `SumintDatumEllVec`. No collisions. No clash with any existing project declaration (checked lexically with the
  guard's resolver).

**`manifest/frozen.json`:** +226 entries in Wave A's schema and key order.
- `author_approval`: `approved_by` "Scott Armstrong", **`approved_at` "PENDING-D7"** (placeholder),
  `approval_ref` `docs/DECISIONS.md#D7`, `approval_version` "1".
- `source.revision`: the TARGET sha256. `source.range`: the FREEZE-LIST source column (instances: "no source
  object (instance definition)").
- `contract` and `split_policy.source_group`: `dh-long.b1.<name>`; `NOT_SPLIT`; ruling D7.
- `definition_closure`: the transitive frozen-definition imports, with sha256.
- Definitions: `full_file_sha256`.
- Theorems: `prefix_sha256`/`suffix_sha256` (the checker's regions), the implementation
  `WaveTurbulence.Provider.<Name>` / `WaveTurbulence.Provider.<name>`, and an empty `draft_allowlist`.
- `abi_sha256`: from `scripts/abi_hash.py --write`.

**`lakefile.lean`:** the 12 B1 anchors and their 12 providers join `quarantinedModules`, which are built as extra
globs.

**`WaveTurbulence.lean`:** +214 `public import WaveTurbulence.Frozen.Defs.*`, sorted. DRAFT anchors are not
imported.

### The seals (commits 4–7)

**Pattern (Wave A `53e73e4`).** Each seal changes only:
- the anchor's registered body, `by sorry` → `by exact WaveTurbulence.Provider.<name>` (prefix and suffix hashes
  unchanged);
- the provider, which restates the anchor's statement verbatim in its context and proves it;
- the manifest `state` (→ SEALED) and `abi_sha256` (recomputed with `abi_hash.py`'s own `abi_hash`);
- the quarantine (the anchor and its provider leave it);
- the root imports: the anchor and any new Foundations modules.

| Seal | Provider proof | New non-frozen modules |
|---|---|---|
| `countLemma` | `CountLemmas.countLemma_bound` (landed). It is stated with `CountLemmas.NearLattice`, whose body is the frozen `NearLattice`'s, so the term checks by unfolding (my COUNT audit note). | none |
| `atomCountLemma` | `CountLemmas.atomCountLemma_bound` (landed), as above. | none |
| `nlsAkBridge` | `NLSBridge.nlsAkBridge hd L γ δ hL hδ D hD α T hα hT`. The provider makes the data binders implicit and the hypotheses `by assumption` autoParams (the `wkelwp` pattern), so the anchor body is the bare `by exact`. | `Foundations/WaveB/FrozenB1` (aggregator: imports the 227 definition anchors, declares nothing); `Foundations/NLS/AkBridgeDefinitions`, `Foundations/NLS/AkBridge` = wt-l2s `/home/scott/wt-scratch/nls-bridge/{BridgeDefinitions,NlsAkBridge}.lean` (sha256 `fd14df95…`, `16f2a467…`; audit `NLS-BRIDGE.md`), imports renamed only |
| `canonicalCharacterization` | `Canon.canonicalCharacterization p LG`, with `p` and `LG` implicit in the provider. | `Foundations/WaveB/Lemmas` = snapshot 6's sorry-free `WaveB1-Lemmas.lean` (`c7312be4…`), importing the aggregator instead of `WaveBDraft.Statements`. `Foundations/Canon/{Basic,Decomp,Main}` = `/home/scott/wt-scratch/canon4/Canon-*.lean` (`20b96033…`, `00465e45…`, `1effa3e2…`), imports renamed. Main also drops its `example` that type-checked against the DRAFT anchor, because a non-anchor file may not mention a DRAFT export. |

- `Canon-Trunc` and `Canon-Finite` import `Main` but the proof does not use them. They stay in scratch for the
  counting packets.
- Every ported file was diffed against its source: the only differences are the import lines and that `example`.

## 2. Landing steps (orchestrator, from `/home/scott/WaveTurbulence-dev` on `main`)

**Step A — now, independent of D7 (after your sign-off on commits 1–2).**

1. `scripts/merge_branch.sh d36c45e`, then `scripts/land_check.sh`, then commit and push.
2. This lands the guard change, the merge-script fix, and the restored `wkelwp` root import.
3. **Do this before step C.** The `merge_branch.sh` that runs during a merge is main's copy: bash has already opened
   the old file when `git merge` replaces it. Merging the whole branch with the old script would silently drop
   the five sealed theorem imports from the root: `wkelwp` and seals 4–7. `land_check.sh` would still pass,
   because those anchors would then be built by no target.

**Step B — the author approves (ruling D7).** Record D7 in `docs/DECISIONS.md` after D6, in its style. Draft:

> D7 — 2026-11-?? — Scott ("…", in reply to the complete Wave B tier-B1 code shown for approval: snapshot 6,
> `/home/scott/wt-scratch/waveb-snap-6`, SHA256SUMS `f6c44531…`) — **Wave B tier B1 approved and frozen**:
> 12 `DRAFT_SORRY` theorem anchors (B1.1–B1.12: `propansatz`, `layergarden`, `fixedpoint`, `nlsAkBridge`,
> `wkeTaylor`, `sumint`, `countLemma`, `atomCountLemma`, `quadExpSum2`, `quadExpSum3`,
> `canonicalCharacterization`, `layergardenFlower`) and 214 sealed definitions (FREEZE-LIST.md of snapshot 6).
> Audits: `WaveB-snapshot6.md` and the earlier Wave B audits. Packaging (semantics-neutral): one declaration
> per file under `WaveTurbulence/Frozen/`, as D6; the guard accepts Lean Unicode identifiers.

**Step C — merge the freeze, and the seals with it or later.**

1. Merge.
   - Freeze only: `scripts/merge_branch.sh 4bb013d`.
   - Freeze with seals 4–7: `scripts/merge_branch.sh w/freeze-b1`, or any commit between them.
2. Fill the date in the staged merge, then check that no placeholder remains:

   ```bash
   sed -i 's/"approved_at": "PENDING-D7"/"approved_at": "2026-11-DD"/' manifest/frozen.json
   git add manifest/frozen.json
   grep -c PENDING-D7 manifest/frozen.json   # must print 0
   ```

   - Use Wave A's `YYYY-MM-DD` format.
   - **The guard only requires the key to be present: it accepts the placeholder.** The grep is the only check.
   - The date is in no hashed region, so no hash changes.
3. Add the D7 entry from step B to the same commit.
4. Check the root import list: `git diff d8c578b -- WaveTurbulence.lean` (or against the merged commit) should
   show only modules main added since `1ecb500`.
5. Run the gate.
   - `scripts/land_check.sh`: duplicate and sorry scans, `lake build WaveTurbulence` including the quarantine globs,
     and `check_index.sh`.
   - Expect about 245 new modules (214 definitions, 12 anchors, 12 providers, 7 Foundations), mostly 4–7 s each.
6. Check the ABI hashes: `python3 -I scripts/abi_hash.py --root . --manifest manifest/frozen.json`. It must print
   **241 `OK`** and exit 0.
7. Commit and push.
8. Update the status:
   - DRAFT_ANCHORS: **13** after the freeze alone (`main` + 12 B1); **9** with seals 4–7 (`main` + `propansatz`,
     `layergarden`, `fixedpoint`, `wkeTaylor`, `sumint`, `quadExpSum2`, `quadExpSum3`, `layergardenFlower`).
   - SEALED_THIS_TURN: 0 or 4.

**Seals landed later.** Merge them in order (`c61f8a6`, `c6a8602`, `d8d6c0a`, `d8c578b`). Each merges cleanly over
the date fill: the seal diffs touch only the `state`/`abi_sha256` lines, not `approved_at`. Run the same gate after
each.

**Seal audit.** I wrote the four providers. Under the two-key rule, the audit before marking them PROVED must be
someone else's. It should check:
- the frozen bytes (prefix/suffix hashes) are unchanged;
- the provider statements;
- the `autoParam`/implicit rebinding in the `nlsAkBridge` and `canonicalCharacterization` providers;
- the axioms.

The proofs themselves were audited earlier: NLS-BRIDGE PASS, COUNT PASS, and CANON on snapshot 5.

**Rollback** before pushing: `git merge --abort` (staged merge) or `git reset --hard ORIG_HEAD`.

## 3. Verification (wt-orch, on the branch; no `lake build`, per my brief)

**Build.**
- I compiled every frozen, provider and new Foundations module with `nice -n 5 lake env lean -o`, one at a time,
  into the worktree's `.lake/build`:
  - the freeze: 255 modules (Wave A's included);
  - the seals: 2 + 2 + 5 + 6 modules.
- 0 errors. The only warnings are `declaration uses 'sorry'` on the DRAFT anchors.

**Statements identical to snapshot 6.**
- Snapshot 6 (`WaveBDraft.*`) and the frozen layout declare the **same fully qualified names**. They cannot be loaded
  into one environment, and a renamed copy would reference different constants. So I dumped every constant of each
  environment (name, universe levels, type, value) and compared the two dumps.
- **Raw types: all 226 declarations identical**, including all 12 theorem statements. 194 definition values are
  raw-identical too.
- The other 32 values differ only in the names of auxiliary proofs and matchers. Lean shares and numbers these per
  module (`_proof_1` vs `_proof_11`, a matcher `TTree.order.match_1` living in another module).
- After delta-expanding matchers and auxiliaries and erasing proofs, all **423** non-auxiliary constants are
  identical: declarations, constructors, recursors and projections. No constant is on only one side; 0 differences.
- For the four sealed anchors there is also a one-environment check. Each provider's proof (the snapshot-5/landed
  statement) elaborates against the frozen statement, and the anchor's `by exact` closes it.

**Guard and scans.**
- After every commit, `check_frozen_anchors.py` gives FROZEN-ANCHOR GUARD OK on the working tree.
- `check_index.sh` gives GUARD OK and `check_lean_modules: PASS` on the staged tree (1430 → 1437 files).
- `land_check.sh`'s duplicate and sorry scans: OK.

**ABI.**
- Freeze: `abi_hash.py --write` filled 226 hashes, and the 15 Wave A anchors printed `OK` (unchanged).
- Seals: each recomputed with `abi_hash.py`'s own `abi_hash`. A cross-check on `countLemma` and on the unchanged
  `wkelwp`/`atomCountLemma` printed `OK`.
- Branch tip `d8c578b`, clean tree, full check mode (`python3 -I scripts/abi_hash.py --root . --manifest
  manifest/frozen.json`): **241 `OK`**, exit 0.

**Axioms.** `countLemma`, `atomCountLemma`, `nlsAkBridge` and `canonicalCharacterization` each depend on
[propext, Classical.choice, Quot.sound].

**Root.** After every commit, `lake env lean WaveTurbulence.lean` elaborates the root (all imports resolve) with
exit 0.

## 4. Status at the branch tip

```text
DRAFT_ANCHORS: 9 at the tip (13 after the freeze commit alone)
  WaveTurbulence/Frozen/Theorems/{Main, Propansatz, Layergarden, Fixedpoint, WkeTaylor, Sumint,
  QuadExpSum2, QuadExpSum3, LayergardenFlower}.lean
UNREGISTERED_SORRIES: 0 (sorry scan outside Frozen/; guard)
DRAFT_IMPORT_VIOLATIONS: 0 (guard quarantine check)
SEALED_THIS_TURN: 4 on the branch, none landed
  (countLemma, atomCountLemma, nlsAkBridge, canonicalCharacterization)
```

## 5. Caveats

- **Commits 1 and 2 change shared infrastructure** (the guard and the merge script) and need your sign-off.
  Without commit 1, the three Unicode exports fail the guard's export regex; renaming them would change approved
  statements.
- **`approved_at` is a placeholder**, and the guard does not reject it. Use the grep in step C.2.
- **I did not run `lake build`** (brief). `land_check.sh` does, at landing.
- **The worktree's `.lake/build`** holds my compiled modules. Its `Foundations/` is a tree of symlinks into the dev
  build plus the seven new modules, for local checks only. Nothing was written into `WaveTurbulence-dev`.
