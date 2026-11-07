# Second-key seal audit: the seven Wave B tier-B1 seals (main `cff2654`)

- **Auditor.** An independent refute-first auditor (a fresh subagent with no access to wt-orch's conclusions), 2026-11-04.
- **Evidence** is in `/home/scott/wt-scratch/seal-audit-b1/`: Lean check outputs `lean/*.out`, the pinned manifest entries, the
  checker runs, the sumint port diff, a pinned scratch copy of sumint at `4700924`, and the scripts.
- **Who wrote this file.** The auditor's harness could not write `REPORT.md`, so wt-orch transcribed it here from the
  auditor's final message. The verdicts and findings are the auditor's.

## Verdicts

| Seal | Verdict |
|---|---|
| B1.4 `nlsAkBridge` | **PROVED** |
| B1.6 `sumint` | **PROVED** |
| B1.7 `countLemma` | **PROVED** |
| B1.8 `atomCountLemma` | **PROVED** |
| B1.9 `quadExpSum2` | **PROVED** |
| B1.10 `quadExpSum3` | **PROVED** |
| B1.11 `canonicalCharacterization` | **PROVED** |

No checklist item failed for any seal.

## Checks (all seven passed each)

1. **Pin.**
   - The manifest entries are unchanged from `cff2654` to HEAD.
   - Snapshot 9's `SHA256SUMS` digest is `30263a99…`; all 15 files verify.
   - The TARGET tex is `493eef6b…`.
   - The prefix, suffix and ABI hashes match; the ABI hashes were recomputed independently.
2. **Bytes.**
   - The frozen statements and docstrings are byte-equal to snapshot 9.
   - Re-elaborating them gives an identical type (for `nlsAkBridge` and `sumint`, identical up to generated variable names).
   - Git history has two commits per file: the freeze `f2d1fb6` and the seal. The seal changed only the proof body, the
     ABI hash and the state.
3. **Provider types.**
   - `example : type_of% @A := @Provider.A` elaborates for all seven.
   - Five providers are `Expr.equal` to their anchors, or equal up to generated variable names.
   - `nlsAkBridge` and `canonicalCharacterization` differ only in which binders are implicit after `autoParam`
     stripping. Without `@`, implicit-lambda elaboration fails for these two; that is normal Lean, not a type
     disagreement.
   - No EXCESS hypotheses anywhere in the providers.
4. **Definition bridges.**
   - `FrozenB1` imports 227 frozen definition modules and declares nothing.
   - Four helpers share a name with a frozen definition:
     - `CountLemmas.NearLattice`, `NLS.epsCoef` and `NLS.aNonlin` are equal to the frozen ones by `rfl`;
     - `Fourier.chi0` has a different body, linked by proved theorems (`chi0_eq_draft_formula`,
       `chi0Vec_eq_latticeCutoff`).
   - None of the four appears in a provider's type.
   - Every B1 definition file in the closure is verbatim in snapshot 9.
5. **sumint port** (404 modules, against scratch `4700924`).
   - 31 files are byte-identical; 372 differ only in import lines.
   - Only `TimeBridge.lean` differs beyond that: three proof-only hunks in two theorems
     (`XNorm_zero_order_eq_mixedFourierNorm`, `XNorm_zero_eq_XNorm00`), no statement change.
   - The commit message says "three proofs"; precisely, it is three hunks in two theorems.
   - Scratch `WaveBDraft`: Core equals snapshot 9 byte for byte; System equals snapshot 8 (snapshot 9 minus F80).
6. **Axioms.**
   - All seven anchors, their providers and the underlying lemmas use only `[propext, Classical.choice, Quot.sound]`.
   - A scan of all 1025 closure modules finds no `sorry`, `native_decide`, `axiom`, `skipKernelTC` or
     `implemented_by`, and no custom elaborators.
7. **Quarantine.**
   - No provider imports a `Frozen.Theorems` module or another provider.
   - Each provider is imported only by its anchor.

## Five-bin classification

**EXCESS = 0** for every anchor. The non-literal premises are author-approved deviations under D7 (RULED):

| Anchor | RULED premises (D7) |
|---|---|
| `nlsAkBridge` | rapidly decreasing data in item 2; `Measurable c`; the selection device `∀ U`; `t ∈ [0,T]` |
| `sumint` | explicit `A`; `Λ_v ≥ 1`; unit time intervals in `[0,𝔇]`; integer shift coefficients summing to 1; `M ≤ N_1^4` |
| `countLemma` | explicit `c₀`; `|r| ≤ c₀` when `P = 1` |
| `atomCountLemma` | `k ≠ 0` when `ε = −1`; the omitted (atomcountbd3) bound, a conclusion-side deviation |
| `quadExpSum2`, `quadExpSum3` | `T₀ = 𝔇δ` |
| `canonicalCharacterization` | the construction read as a decomposition of a given garden |

## Finding N1 (not about the seals)

- **Symptom.** `scripts/check_frozen_anchors.py --root .` exits 1 on the main checkout `/home/scott/WaveTurbulence-dev`.
- **Cause.** The untracked, git-ignored `scratch/Draft.lean` (a Wave A draft from 2026-11-03) has `sorry` at lines 124
  and 147, and the checker scans every `.lean` file under the root.
- **Scope.** On clean `git archive` copies of HEAD and `cff2654` the checker passes. `scripts/check_index.sh`, used by
  `land_check.sh`, checks the index only and is unaffected.
- **Recommendation.** Move the file out of the tree, or have the checker skip untracked files. wt-orch has not touched
  it: it is not wt-orch's file.

## Other observations

- `Foundations/Canon/Main.lean` says its theorem is the "statement of snapshot 3, verbatim". This is stale wording only;
  the type matches the anchor.
- The meaning of the definition bodies was not re-audited. They were tied to the approved versions by hash and by
  verbatim match with the snapshot.
