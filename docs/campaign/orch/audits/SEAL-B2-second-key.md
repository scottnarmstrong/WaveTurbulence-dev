# Second-key seal audit: the six Wave B tier-B2 seals (main `3e2de9d`)

- **Auditor:** an independent refute-first auditor (a fresh subagent, given none of wt-orch's conclusions), 2026-11-04.
- **Evidence:** `/home/scott/wt-scratch/seal-audit-b2/`:
  - `tools/`
  - `closure-all.txt`
  - `regstruct-diff.txt`, `incohinst-diff.txt`, `sumint-diff.txt`
  - `lean/abi_*/out.txt`, `lean/SealCheck.out`
  - `lean/digest/` (the draft-vs-frozen digest; `digest.diff` is empty)
  - `pins.tar.gz`
- **Transcription:** the auditor's harness refused report files, so wt-orch transcribed this from the auditor's final
  message. The verdicts and findings are the auditor's.

## Verdicts

| seal | anchor | verdict |
|---|---|---|
| O1 | `RegCpl.exists_decodes` | **PROVED** |
| O2 | `existsUnique_regCpl_decodes` | **PROVED** |
| O3 | `RegChain.exists_decodesTree` | **PROVED** |
| O4 | `existsUnique_regChain_decodesTree` | **PROVED** |
| O5 | `RegCpl.size_eq_order` | **PROVED** |
| B2.2 | `incoherentDecay` | **PROVED** |

No checklist item failed.

## Shared evidence

- **G1. Guard.**
  - On `git archive` exports of HEAD and of `3e2de9d`: `FROZEN-ANCHOR GUARD OK`.
  - On the live main checkout it fails, because of the untracked, git-ignored `scratch/Draft.lean`. This is the same
    finding as N1 in the B1 audit.
- **G2. Olean consistency.** The auditor reimplemented Lake's trace hashing (MurmurHash64A, seed 11) over the
  1156-module union closure.
  - Every trace records the hash of the current source.
  - Every on-disk olean matches its trace.
  - All 3211 project import edges are consistent (0 mismatches).
- **G3. ABI hashes:** all six `abi_hash.py` probes equal the manifest's `abi_sha256`.
- **G4. Types.**
  - The `@` form `example : type_of% @anchor := @Provider.export` elaborates for all six.
  - After stripping `autoParam`/`optParam`, the provider and anchor types are alpha-equal for all six. For B2.2 the
    raw types are also equal.
  - The literal non-`@` form fails for O1–O5 by construction (implicit data binders, `by assumption` hypotheses).
  - No provider has a hypothesis beyond the anchor's binders.
  - B2.2's `incoherentDecay_core` chooses ν₀ = δ₀ = C₂ = 1 and L₀ after δ and D, which the prefix order allows. It
    leaves some anchor hypotheses unused, so it proves something stronger than stated.
- **G5. Axioms.**
  - The six anchors and six providers use only `[propext, Classical.choice, Quot.sound]`.
  - `check_axioms.py` reports 12 declarations, all ok.
  - A scan of the 1156 closure files finds no forbidden command or attribute outside comments.
- **G6. Meaning.** The auditor ran an independent draft build of snapshot 9 plus B2 final (0 errors; the 10 documented
  `sorry` warnings).
  - The six anchor types under `pp.all` are byte-identical between the draft and frozen environments (sha256
    `1cc77fcf…`).
  - All 212 reachable project constants have identical type and value hashes, after normalizing auxiliary names.
  - All 287 `Frozen/Defs` modules in the closure are verbatim in the approved drafts.
  - Each anchor's `definition_closure` equals the frozen-definition import closure of its statement (44, 44, 48, 48,
    33, 110).

## Ports (only import lines normalized)

- **RegStruct (151).**
  - All are identical after normalization.
  - Import renaming: `X` → `Foundations.RegStruct.X`; `RegularDefs` → `RegularHeldOut`; `CoreTreeLemmas` →
    `Foundations.WaveB.Lemmas`. The nine `CoreTreeLemmas` lemmas appear verbatim in `Lemmas.lean`.
- **IncohInst (104).** 100 are identical. The 4 that differ are exactly the claimed exceptions:
  - `NormBridge`: `XNorm_le_mixed`, a proof-only F80 repair.
  - `Regref/NormShift`: `XNorm_shift`, a proof-only F80 repair.
  - `Links/TreeLemma`: `{α : Type*}` added, statement-neutral (`9755388`).
  - `TreeSpineEndpoints`: `variable {w : ℕ}` added, statement-neutral (`9755388`).
- **`TimeBridge`** (Sumint): only proof bodies of two theorems differ.
- **`FrozenB2` copies:** the four `StatementsDefs` definitions are verbatim in the frozen files.
- **Foundations on main:** `Foundations/Incoh` and `WKE` equal `w/wke-l2s`.
- **Held-out declarations and aggregators:**
  - `RegularHeldOut` holds exactly `MiniTreeCode.equiv` and the seven instances, verbatim from the draft. Its only
    `sorry` token is in the module docstring.
  - `FrozenB1` and `FrozenB2` declare nothing; they are imports only.
- **Quarantine:**
  - No provider's closure contains a `Frozen.Theorems` module.
  - Each provider is imported only by its anchor.
- **Mutual files:** all 9 have exactly one `mutual` block, which declares exactly the entries' exports.

## Five-bin binder tables

**EXCESS = 0** for every anchor.
- **O1/O3:** `wf` encodes the side conditions of `propstructure` (b) (L854), RULED under D8.
- **O2/O4:** SOURCE hypotheses `IsRegularCouple` / `IsRegularTree` (`propstructure`, L851–L857). The trivial object is
  also covered, which is harmless.
- **O5:** RULED code–carrier relation.
- **B2.2:**
  - STANDING: the `WTPrefix` regime (L605–L615), `p < D`, R real on ℝ^d (L951), `InputRemainder` with the finite
    𝔖^{40d,40d} norm in place of C^∞ (RULED), `n ≤ N_{p+1}^4`, order 2n via O5.
  - SOURCE: the layer conditions (L670, L678, L682) and g ≥ 1 (L953).
  - Conclusion: TARGET bounds the sum of the two norms; the anchor bounds each norm separately with the existential
    C₁. This matches up to the constant.

## Minor observations (no FAIL)

1. The guard on the live checkout gives a false alarm from `scratch/Draft.lean` (as in B1 N1).
2. `check_frozen_anchors.py` enforces provider quarantine only for DRAFT_SORRY anchors. For sealed anchors, "only the
   anchor imports the provider" rested on the auditor's manual check.
3. The O1–O5 provider docstrings still say "Quarantined while the anchor is DRAFT_SORRY". This is stale.
4. The `1729afe` commit message says 154 byte-identical REG-STRUCT copies. 153 are; the 154th is the `RegularDefs` shim,
   which is not ported.
5. B2.2 cites "standing assumptions of L946–L951". The standing paragraph is L951.

## Not run

- No kernel replay of the oleans (e.g. `lean4checker`).
- The Foundations packages that predate this landing were not diffed.
- B2.1 was not audited (it is still DRAFT_SORRY).
