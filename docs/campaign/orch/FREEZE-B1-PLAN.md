# Wave B tier-B1 freeze (ruling D7): landing plan

Prepared by `wt-orch` (Task 22), 2026-11-04. **Rebuilt from snapshot 9 in Task 34b, with seven seals.**
- Branch **`w/freeze-b1`**, worktree `/home/scott/WaveTurbulence-worktrees/freeze-b1`, based on main `1ecb500`.
- Since that base, main has added Foundations modules and root imports, which `merge_branch.sh` regenerates. Main has
  not touched `manifest/`, `scripts/`, `lakefile.lean`, `Frozen/` or `Provider/`. The 221 Wave A and Foundations
  modules that the `sumint` seal imports (transitively) are byte-identical at `1ecb500` and on main.
- **Nothing is landed or pushed.** The freeze lands only after the author approves snapshot 9 as ruling D7.
- Earlier versions are superseded and kept as local branches: `w/freeze-b1-snap6` (`d8c578b`), `w/freeze-b1-snap7`
  (`1778395`), `w/freeze-b1-snap8` (`7bd9e36`).

## 1. What the branch contains

| # | Commit | Content |
|---|---|---|
| 1 | `4a97152` | **Guard: Lean Unicode identifiers.** `scripts/check_frozen_anchors.py` accepted only ASCII names, and three approved B1 exports are not ASCII: `SumintDatum.M₀`, `SumintDatum.M₁`, `SumintDatum.ℓVec`. The identifier classes now follow Lean core's `isLetterLike`/`isSubScriptAlnum`. The guard still passes on main. **Needs your sign-off** (it changes the guard). |
| 2 | `d36c45e` | **`merge_branch.sh` keeps SEALED theorem anchors in the root.** The script rebuilt the root import list from `Frozen/Defs`, `Foundations` and `Paper` only. The merge after the `wkelwp` seal (`53e73e4`) therefore silently dropped `public import WaveTurbulence.Frozen.Theorems.Wkelwp`, and **on main today the sealed `wkelwp` anchor is in no build target**. This commit fixes the script and restores the import. **Needs your sign-off.** |
| 3 | `f2d1fb6` | **The B1 freeze from snapshot 9**: 214 definition anchors, 12 `DRAFT_SORRY` theorem anchors, 12 provider stubs, manifest, quarantine, root imports. |
| 4 | `d5d8abc` | Seal `countLemma` (B1.7). |
| 5 | `f3a94e8` | Seal `atomCountLemma` (B1.8). |
| 6 | `e0a7732` | Seal `nlsAkBridge` (B1.4). Adds the `FrozenB1` aggregator and the NLS bridge port. |
| 7 | `1082daf` | Seal `canonicalCharacterization` (B1.11). Adds the B1 Lemmas and CANON ports; needs commit 6's aggregator. |
| 8 | `02c4e46` | Seal `quadExpSum2` (B1.9). Adds `Foundations/WeylSums/FrozenBridge`. |
| 9 | `ad5c545` | Seal `quadExpSum3` (B1.10). Uses commit 8's `FrozenBridge`. |
| 10 | `1c6b8c8` | Seal `sumint` (B1.6). Adds `Foundations/Sumint/**` (404 modules); uses commit 6's aggregator. |

The commits are linear. Merging any prefix of them is a consistent state.

### The freeze commit (3)

**From snapshot 9**, `/home/scott/wt-scratch/waveb-snap-9`:
- `SHA256SUMS` verifies; its digest is `30263a992199…`.
- Snapshot 9 was built by wt-orch (Task 34b) as snapshot 8 plus F80 (`CHANGES-9.md`, DESIGN CL-23). The independent
  auditor is checking that delta.
- **The successive fixes:**
  - snapshot 7 = 6 + F68: `PatValid`'s `dChild` designation is a layer-`p` node (`WaveB-snapshot7.md`);
  - snapshot 8 = 7 + F78: `coupleSum`'s `∂_t` roots are layer-`p` branching nodes (`WaveB-snapshot8.md`);
  - snapshot 9 = 8 + F80: `XNorm`'s guard asks for `C^{Λ₁}` slices for almost every frequency, with no per-frequency
    `⊤` (`WaveB2-independent-audit.md`, "Norm measurability").
- Everything else is audited in `WaveB-snapshot6.md` and the earlier Wave B audits.

**Contents:**
- **214 definition anchors**, one declaration per file, in `WaveTurbulence/Frozen/Defs/<Name>.lean`:
  - 167 `def`, 33 instance `def`s, 5 `structure`, 5 `inductive`, 4 `abbrev`;
  - every one is a SEALED whole-file anchor.
- **12 theorem anchors**, `DRAFT_SORRY`, in `WaveTurbulence/Frozen/Theorems/<Name>.lean`. Each has the five
  `FROZEN_ANCHOR` markers and the body `by sorry`, and its prefix imports its provider.
- **12 provider stubs** in `WaveTurbulence/Provider/<Name>.lean`: imports and module doc only, like Wave A's
  `Provider/Main.lean`.

**Against earlier freezes, the frozen files that differ:**
- against the snapshot-8 freeze (`8b470ff`): only `XNorm.lean` (F80);
- against the snapshot-7 freeze (`200d9c3`): also `CoupleSum.lean` (F78), which imports `GBranchToNode`;
- against the snapshot-6 freeze (`4bb013d`): also `LayeredGardenPatValid.lean` and `FlowerSum.lean` (F68).

In the manifest, against the snapshot-8 freeze, only `XNorm`'s file hash and ABI and `XNormRestr`'s definition
closure change.

**Generation.** A script produced the files from the snapshot text.
- Each file holds the declaration's docstring and text **verbatim**, inside the exact context it had in the
  snapshot:
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
- `abi_sha256`:
  - reused from the previous freeze for byte-identical files;
  - recomputed with `abi_hash.py`'s own `abi_hash` for each changed file (`XNorm`: `870fbcb1…`, was `ae1b198a…`);
  - unchanged for the dependent `XNormRestr` (re-checked OK), and `coupleSum` (F78) OK;
  - verified by the full check of §3.

**`lakefile.lean`:** the 12 B1 anchors and their 12 providers join `quarantinedModules`, which are built as extra
globs.

**`WaveTurbulence.lean`:** +214 `public import WaveTurbulence.Frozen.Defs.*`, sorted. DRAFT anchors are not
imported.

### The seals (commits 4–10)

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
| `canonicalCharacterization` | `Canon.canonicalCharacterization p LG`, with `p` and `LG` implicit in the provider. | `Foundations/WaveB/Lemmas` = snapshot 9's sorry-free `WaveB1-Lemmas.lean` (`c7312be4…`, byte-identical to snapshots 6–8), importing the aggregator instead of `WaveBDraft.Statements`. `Foundations/Canon/{Basic,Decomp,Main}` = `/home/scott/wt-scratch/canon4/Canon-*.lean` (`20b96033…`, `00465e45…`, `1effa3e2…`), imports renamed. Main also drops its `example` that type-checked against the DRAFT anchor, because a non-anchor file may not mention a DRAFT export. |
| `quadExpSum2` | From the landed `WeylSums.quadExpSum2_bound` (TARGET Lemma 5.3, `7899941`). `intro`, then `obtain` the constants, then `simpa only` with the definition of `bilinearLatticeSum` and the two identities. | `Foundations/WeylSums/FrozenBridge`, shared with `quadExpSum3`. It proves `chi0Vec_eq_latticeCutoff` (frozen `chi0Vec` = landed `latticeCutoff`, from `chi0_eq_draft_formula`) and `eZ_eq_e` (`rfl`). |
| `quadExpSum3` | From the landed `WeylSums.quadExpSum3_bound` (TARGET `lemcubic`, `8a39e44`), the same pattern, also unfolding `cubicLatticeSum`, `cubicQuadraticForm` and `timeSquareWindow`. The Bool convention agrees (`true` ↦ `⟨x,z⟩`). | none (uses `FrozenBridge`) |
| `sumint` | wt-anfourier's `WaveTurbulence.Sumint.sumint` (`/home/scott/wt-scratch/sumint`, scratch commit `4700924`, `HANDOFF.md`; pinned by wt-orch, 432 files, list digest `ad0605e83892…`). The anchor has no binders, so the provider is the anchor's statement with this term. | `Foundations/Sumint/**`: the 404-module import closure of `Sumint/Sumint.lean`, ported with only their imports renamed (`Sumint.X` and `MultiIndices`, `TimeBridge`, `Words` → `WaveTurbulence.Foundations.Sumint.*`). The local `WaveBDraft.{Core, System, SumintData}` imports → the `FrozenB1` aggregator. The local Core and SumintData are snapshot 9's Core and Sumint (minus the anchor), byte for byte; the local System is snapshot 8's, which differs only in `XNorm` (F80). **One proof repair (mine), in `TimeBridge.lean`:** three proofs of its `XNorm` bridge lemmas at `Λ₁ = 0` rewrote with the old guard and now use the a.e. guard; no statement changes, and none of its five `XNorm` lemmas is used elsewhere in the closure. All modules are modules; the largest has 156 lines; no forbidden tokens. |

**Exactness of the Weyl-sum seals.** Each landed statement equals its anchor up to the two `FrozenBridge` identities:
the same quantifier order, the same time window (`timeSquareWindow L (T₀L^{2γ})` is the anchor's set) and the same
phase terms in the same order. Each provider restates its anchor verbatim (checked by text comparison).

**Ported files.**
- `Canon-Trunc` and `Canon-Finite` import `Main` but the proof does not use them. They stay in scratch for the
  counting packets.
- Every ported file was diffed against its source. The only differences are the import lines, Canon Main's `example`,
  and the `TimeBridge.lean` repair for snapshot 9:
  - `XNorm_zero_order_eq_mixedFourierNorm`: `ite_eq_left hi` / `ite_eq_right hi` become
    `ite_eq_left (And.intro hi (Or.inl rfl))` / `ite_eq_right (not_and_of_not_left _ hi)`, and the simp lemmas for
    the removed inner `if` are dropped;
  - `XNorm_zero_eq_XNorm00`: `split_ifs` now gives four cases (the guards differ syntactically); the two mixed
    cases are contradictory.
  - wt-anfourier's scratch (`/home/scott/wt-scratch/sumint`) still has the snapshot-8 versions; I did not edit it.

## 2. Landing steps (orchestrator, from `/home/scott/WaveTurbulence-dev` on `main`)

**Step A — now, independent of D7 (after your sign-off on commits 1–2).**

1. `scripts/merge_branch.sh d36c45e`, then `scripts/land_check.sh`, then commit and push.
2. This lands the guard change, the merge-script fix, and the restored `wkelwp` root import.
3. **Do this before step C.** The `merge_branch.sh` that runs during a merge is main's copy: bash has already opened
   the old file when `git merge` replaces it. Merging the whole branch with the old script would silently drop the
   eight sealed theorem imports from the root: `wkelwp` and seals 4–10. `land_check.sh` would still pass, because
   those anchors would then be built by no target.

**Step B — the author approves (ruling D7).** Record D7 in `docs/DECISIONS.md` after D6, in its style. Draft:

**Approved 2026-11-04 17:1x UTC.** Scott, in this session: "I approve all", in reply to wt-orch's list of what would unblock landing: (1) approve D7 (B1, snapshot 9, review page `docs/review/WAVE-B-B1.md` regenerated from snapshot 9), then land `w/freeze-b1`, then D8 (B2, `waveb2-snap-final`, review page `docs/review/WAVE-B-B2.md`) and land `w/freeze-b2`; (2) second-key audits of the 13 seals by someone other than wt-orch; (3) audit, then port, the finished scratch packets. Pins re-verified at 17:12 UTC: `waveb-snap-9` SHA256SUMS `30263a992199…` and `waveb2-snap-final` SHA256SUMS `b3db9c4367a8…`, every listed file OK. Landing (and committing D7/D8 to `docs/DECISIONS.md`) is the orchestrator's; wt-orch does not land. The same reply signs off step A (commits 1–2).


> D7 — 2026-11-04 — Scott ("I approve all", in reply to the complete Wave B tier-B1 code shown for approval: snapshot 9,
> `/home/scott/wt-scratch/waveb-snap-9`, SHA256SUMS `30263a99…`) — **Wave B tier B1 approved and frozen**:
> 12 `DRAFT_SORRY` theorem anchors (B1.1–B1.12: `propansatz`, `layergarden`, `fixedpoint`, `nlsAkBridge`,
> `wkeTaylor`, `sumint`, `countLemma`, `atomCountLemma`, `quadExpSum2`, `quadExpSum3`,
> `canonicalCharacterization`, `layergardenFlower`) and 214 sealed definitions (FREEZE-LIST.md of snapshot 9).
> Includes the F68 fix (`PatValid`'s `dChild` designation is a layer-`p` node), the F78 fix (`coupleSum`'s `∂_t`
> roots are layer-`p` branching nodes) and the F80 fix (`XNorm`'s a.e. `C^{Λ₁}` guard). Audits:
> `WaveB-snapshot6.md`, `WaveB-snapshot7.md`, `WaveB-snapshot8.md`, the independent audit of the snapshot-9 delta,
> and the earlier Wave B audits. Packaging (semantics-neutral): one declaration per file under
> `WaveTurbulence/Frozen/`, as D6; the guard accepts Lean Unicode identifiers.

**Note for the author page.** `docs/review/WAVE-B-B1.md` shows snapshot 7, with a hold note for F78. Before
presenting it, move it to snapshot 9:
- the `coupleSum` clause (F78; `CHANGES-8.md`);
- the `XNorm` definition (F80; `CHANGES-9.md`);
- the new hashes: `WaveB1-Flower.lean` `fd2b5e501d04…`, `WaveB1-System.lean` `cc53aad3acd7…`, `FREEZE-LIST.md`
  `d38088f72f4c…`, `SHA256SUMS` digest `30263a992199…`.

The B2 page (`WAVE-B-B2.md`) already names snapshot 9 as its B1 base.

**Step C — merge the freeze, and the seals with it or later.**

1. Merge.
   - Freeze only: `scripts/merge_branch.sh f2d1fb6`.
   - Freeze with seals 4–10: `scripts/merge_branch.sh w/freeze-b1`, or any commit between them.
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
4. Check the root import list: `git diff 1c6b8c8 -- WaveTurbulence.lean` (or against the merged commit) should
   show only modules main added since `1ecb500`.
5. Run the gate.
   - `scripts/land_check.sh`: duplicate and sorry scans, `lake build WaveTurbulence` including the quarantine globs,
     and `check_index.sh`.
   - Expect about 650 new modules (214 definitions, 12 anchors, 12 providers, 8 Foundations, 404
     `Foundations/Sumint`), mostly 4–10 s each.
6. Check the ABI hashes: `python3 -I scripts/abi_hash.py --root . --manifest manifest/frozen.json`. It must print
   **241 `OK`** and exit 0.
7. Commit and push.
8. Update the status:
   - DRAFT_ANCHORS: **13** after the freeze alone (`main` + 12 B1); **6** with seals 4–10 (`main` + `propansatz`,
     `layergarden`, `fixedpoint`, `wkeTaylor`, `layergardenFlower`).
   - SEALED_THIS_TURN: 0 or 7.

**Seals landed later.** Merge them in order (`d5d8abc`, `f3a94e8`, `e0a7732`, `1082daf`, `02c4e46`, `ad5c545`,
`1c6b8c8`). Each merges cleanly over the date fill: the seal diffs touch only the `state`/`abi_sha256` lines, not
`approved_at`. Run the same gate after each.

**Seal audit.** I wrote the seven providers. Under the two-key rule, the audit before marking them PROVED must be
someone else's. It should check:
- the frozen bytes (prefix/suffix hashes) are unchanged;
- the provider statements;
- the `autoParam`/implicit rebinding in the `nlsAkBridge` and `canonicalCharacterization` providers;
- the `FrozenBridge` identities;
- for `sumint`, that the 404 ported modules differ from the scratch sources only in their import lines, except the
  three `TimeBridge.lean` proofs (§1, "Ported files");
- the axioms.

The proofs themselves were audited or checked earlier: NLS-BRIDGE PASS, COUNT PASS, CANON on snapshot 5, the
landed Weyl-sum lemmas, and `sumint` by its author's exact-type check, which you verified against snapshot 8's text
(the `sumint` statement is unchanged in snapshot 9; on the branch the provider's proof elaborates against it).

**Rollback** before pushing: `git merge --abort` (staged merge) or `git reset --hard ORIG_HEAD`.

## 3. Verification (wt-orch, on the branch; no `lake build`, per my brief)

**Build.**
- I compiled every frozen, provider and new Foundations module with `nice -n 5 lake env lean -o`, one at a time,
  into the worktree's `.lake/build`:
  - in Task 22, the freeze from snapshot 6: 255 modules;
  - in Tasks 28 and 34b, the modules whose source changed with snapshots 7–9 (`LayeredGardenPatValid`,
    `FlowerSum`, `CoupleSum`, `XNorm`, `XNormRestr`, the B1.12 provider stub and anchor; every other module has
    byte-identical source);
  - the seven seals: 2 + 2 + 5 + 6 + 3 + 2 + 406 modules.
- 0 errors. The warnings are `declaration uses 'sorry'` on the DRAFT anchors, and 16 style-linter warnings (unused
  simp arguments, `<;>`, unreferenced names) in 11 ported Sumint files that I did not change.

**Snapshot 9 itself** (built by me, Task 34b).
- All 11 B1 modules, in two environments (my Wave A glue root, and dev's build), with 0 errors. The only `sorry`s
  are the 12 anchors.
- On dev's build the 7 B2 modules (probes included) also compile on snapshot 9, with the same `sorry`s.

**Statements identical to the snapshot.**
- Snapshot 6 against the frozen layout (Task 22).
  - The two declare the **same fully qualified names**. They cannot be loaded into one environment, and a renamed copy
    would reference different constants. So I dumped every constant of each environment (name, universe levels,
    type, value) and compared the two dumps.
  - Raw types: all 226 declarations identical. After delta-expanding matchers and auxiliaries and erasing proofs,
    all **423** non-auxiliary constants are identical.
- Snapshot 6 → 7 → 8 → 9 (the same dump): exactly `PatValid` and `flowerSum` (F68), then `coupleSum` (F78), then
  `XNorm` (F80) differ.
- The frozen files that changed are exactly those, each the new snapshot text in its snapshot context.
- For the sealed anchors there is also a one-environment check. Each provider's proof elaborates against the frozen
  statement, and the anchor's `by exact` closes it.

**Guard and scans.**
- After every commit, `check_frozen_anchors.py` gives FROZEN-ANCHOR GUARD OK on the working tree.
- `check_index.sh` gives GUARD OK and `check_lean_modules: PASS` on the staged tree (1430 files after the freeze commit, 1842 at the tip).
- `land_check.sh`'s duplicate and sorry scans: OK.

**ABI.**
- Freeze and seals: as in §1. The six earlier seals' ABIs are identical to Task 28's.
- Branch tip `1c6b8c8`, clean tree, full check mode (`python3 -I scripts/abi_hash.py --root . --manifest
  manifest/frozen.json`): **241 `OK`**, exit 0. `sumint`'s ABI is `0ae1fc75…`.

**Axioms.** `countLemma`, `atomCountLemma`, `nlsAkBridge`, `canonicalCharacterization`, `quadExpSum2`,
`quadExpSum3` and `sumint` each depend on [propext, Classical.choice, Quot.sound].

**Root.** After every commit, `lake env lean WaveTurbulence.lean` elaborates the root (all imports resolve) with
exit 0.

## 4. Status at the branch tip

```text
DRAFT_ANCHORS: 6 at the tip (13 after the freeze commit alone)
  WaveTurbulence/Frozen/Theorems/{Main, Propansatz, Layergarden, Fixedpoint, WkeTaylor,
  LayergardenFlower}.lean
UNREGISTERED_SORRIES: 0 (sorry scan outside Frozen/; guard)
DRAFT_IMPORT_VIOLATIONS: 0 (guard quarantine check)
SEALED_THIS_TURN: 7 on the branch, none landed
  (countLemma, atomCountLemma, nlsAkBridge, canonicalCharacterization, quadExpSum2, quadExpSum3, sumint)
```

## 5. Caveats

- **Commits 1 and 2 change shared infrastructure** (the guard and the merge script) and need your sign-off.
  Without commit 1, the three Unicode exports fail the guard's export regex; renaming them would change approved
  statements.
- **`approved_at` is a placeholder**, and the guard does not reject it. Use the grep in step C.2.
- **I did not run `lake build`** (brief). `land_check.sh` does, at landing.
- **The worktree's `.lake/build`** holds my compiled modules. Its `Foundations/` is a tree of symlinks into the dev
  build plus the new modules (the eight seal modules and `Foundations/Sumint/`), for local checks only. Nothing
  was written into `WaveTurbulence-dev`.
- **Snapshot 9 was built by me**, not by the B1 drafter. Its one change is the auditor's text; the independent
  auditor is checking the delta.
- **The branch was rewritten** (it is unlanded). The snapshot-6, -7 and -8 versions are kept as the local branches
  `w/freeze-b1-snap6`, `w/freeze-b1-snap7` and `w/freeze-b1-snap8`.
