# Delta audit 1: Wave B fixes (snapshot 2) against stage-1 R1 and stage-2 R2–R4

Auditor: `wt-orch` (Opus), refute-first. Date: 2026-11-03. Task 6b.

## Inputs

**Snapshot.** `/home/scott/wt-scratch/waveb-snap-2/`; `sha256sum -c SHA256SUMS` passes. The files:

| File | sha256 |
|---|---|
| `WaveB1-Core.lean` | `9e6c6b4d…3088e3f0` |
| `WaveB1-System.lean` | `70a762bd…b55be2c8` |
| `WaveB1-Core-probes.lean` | `58f7ac3f…976ced40` |
| `WaveB1-System-probes.lean` | `331a31f2…5063a86a` |
| `WaveB1-Statements.lean` | `4a6fe805…c68accd5` |
| `DESIGN.md` | `d40536f5…0f31a117` |

The changelog is DESIGN.md CL-1 … CL-11. I diffed every file against `waveb-snap-1`.

**Scope.**
- My own items: stage-1 R1 and stage-2 R2–R4, plus every definition the fixes touched in Core and System.
- Whether all seven files elaborate together.
- The stage-3 auditor verifies its own R1–R9 in parallel. I did not re-audit the Statements items, except where they
  consume changed Core/System definitions.

**Toolchain and build.**
- Lean v4.35.0, Mathlib v4.35.0, worktree `w/orch` at `b4d5fcd` (main `481663b`).
- `WaveTurbulence/` is identical to main `c50be65`, the base CL-6 aligned to.
- I recompiled the Foundations and frozen dependencies, one module at a time with `lake env lean -o`, `nice -n 5`
  (twenty modules: Torus, NLS/{FourierEquation, AkSystem}, Cumulant/Basic, frozen Defs).
- I then compiled the seven snapshot files as modules `WaveBDraft.{Core, CoreProbes, System, SystemProbes,
  Statements, StatementsProbes, Sumint}`.

## Verdict

**All four of my REQUIRED items are closed exactly, and the files elaborate together.**

**Elaboration.** All seven files elaborate as modules, with 0 errors:

| Module | Time | `sorry`s |
|---|---|---|
| Core | 39 s | 0 |
| CoreProbes | 90 s | 0 |
| System | 53 s | **0** |
| SystemProbes | 38 s | 0 |
| Statements | 37 s | 11 |
| StatementsProbes | 36 s | 0 |
| Sumint | 103 s | 1 |

The 12 `sorry`s are exactly the draft anchors:
- `propansatz`, `layergarden`, `fixedpoint`, `nlsAkBridge`, `wkeTaylor`;
- `countLemma`, `atomCountLemma`, `quadExpSum2`, `quadExpSum3`, `canonicalCharacterization`;
- the deferred `layergardenFlower`;
- `sumint`.

This matches the DESIGN claim. The proved obligations `summable_kernelK_summand`, `truncSum_untruncated` and
`contDiff_of_SNormR_lt_top`, and the regression probes `e1_trunc`, `e1_canon2`, `figLG_trunc` and `figLG_canon3`,
depend only on `[propext, Classical.choice, Quot.sound]`.

**One new REQUIRED item (D1), in a definition that CL-8 moved into System.**
- `truncSumHζ` is identically 0 for kind ≠ 0: the 𝒴 and 𝒲 flower sums are empty sums.
- **Cause:** its `IsTrunc p (N_{p+1}) (N_p)` forces every initial flower tree to have at most N_{p+1} layer-p
  branching nodes. `FlowerRestr` kinds 1 and 2 force more than N_{p+1}.
- **Proof:** `truncSumHζ_kind_ne_zero` in Lean, sorry-free.
- **History:** the defect was already in snapshot 1, in the Statements file (stage-3 scope). The stage-3 audit did
  not flag it.
- **Impact:** the only consumer, B1.12, is deferred (stage-3 R8). Its kind ≠ 0 clause is therefore vacuous (0 ≤
  RHS). `truncSumHζ` must be fixed before it is frozen, or kept out of the freeze set together with B1.12.

## 1. REQUIRED items: closure check

| Item | Required change (stage 1 / stage 2 audit) | Snapshot 2 | Verdict | Evidence |
|---|---|---|---|---|
| **Stage-1 R1** (`attachedOrder` merges attached gardens) | `AttachLinkedOn p u u' := u ∈ 𝒰 ∧ u' ∈ 𝒰 ∧ AttachLinked u u'`; `attachedOrder` sums over the `EqvGen (AttachLinkedOn p)` class; add the E1 garden as a unit test; B1.11(2) names `AttachLinkedOn` | Core §7 (CL-7): **verbatim** my definition and my `attachedOrder` body. `AttachLinked`'s body is unchanged; its docstring is corrected. Core-probes gains the E1 garden with `e1_canon2`, `e1_topOrder`, `e1_attachedOrder_le` and **`e1_trunc : e1LG.IsTrunc 1 2 1`** (the snapshot-1 draft rejected it). `canonicalCharacterization` (2) now quantifies `EqvGen (LG.AttachLinkedOn p)`. | **CLOSED exactly** | `diff` of Core: the only non-docstring changes are `open NLS`, `AttachLinkedOn` and the one-token change in `attachedOrder`. The probes elaborate; `e1_trunc` and `figLG_trunc` use standard axioms. |
| **Stage-2 R2** (`summable_kernelK_summand` false) | Add `hlone : ∀ j, #{ℓ in tree j : IsLone ℓ} ≤ 1`; update `kernelK`'s docstring | **Exactly this `hlone`** (CL-8). `hF` is weakened to "every *input leaf* ℓ has `Summable (n ↦ \|F 𝔏_ℓ (k₀ + n/L)\|)`" (stage-3 O5). A weaker hypothesis makes the lemma stronger, and it is still true. The obligation is **proved** (no `sorry`). The `kernelK` docstring states the junk-0 regime. `summable_KTstar_summand` and `IsPairedTree.summable_KTstar_summand` are added. | **CLOSED** (and strengthened) | My counterexample `lone3` violates the new hypothesis (`lone3_violates_hlone`, by `decide`). The non-summability `summable_kernelK_summand_needs_hlone` still holds, so `hlone` cannot be dropped. `#print axioms summable_kernelK_summand` gives standard axioms. |
| **Stage-2 R3** (`maxBracketPow` wrong for θ < 0) | `ENNReal.ofReal (((⨆ i, Real.sqrt (1 + lam i ^ 2)) ⊔ 1) ^ θ)` | **Verbatim** (CL-8), with a correct docstring | **CLOSED exactly** | `maxBracketPow_neg_lt_one : maxBracketPow (-1) ![0, 3] < 1`. TARGET's weight is 10^{−1/2}; snapshot 1 gave ≥ 1. It also agrees with Foundations `timeWeight` (Infra-review-2). |
| **Stage-2 R4** (`ContDiff ℝ ⊤` = analytic in `AnsatzAt` (2)) | Drop the conjunct (preferred), or use `∞` | **Dropped** (option B). New `contDiff_of_SNormR_lt_top : SNormR Λ₁ Λ₂ F < ⊤ → ContDiff ℝ Λ₁ F`. The docstring of item (2) explains this. The same deletion is made in `RemainderBound` and `layergarden` (stage-3 R1/R2), with the regression guard `remainderBound_iff` (`Iff.rfl`) in Statements-probes. | **CLOSED exactly** | `grep ContDiff` over all snapshot-2 files: no `⊤`/`ω` occurrence outside docstrings. The only remaining `ContDiff ℝ Λ₁` are the 𝔖/𝔛 guards and the new lemma. |

**My stage-1/2 OPTIONAL items.**
- **Applied:**
  - stage-1 O1–O5: the width note, junk ranges, `omegaNode_latticeDecoration`, `IsPairedTree.sign_lone` with its
    probe, the E1 probe;
  - stage-2 O1 (the `XNorm` guard reading), O3 (`truncSumH` deleted, a single `truncSumHζ`), O5 (the `SNorm`
    reading), O7 (the `kernelK` junk-0 docstring).
- **Not applied, and recorded in DESIGN:** stage-2 O2 (`treeTerm` summability), O4 (a non-trivial `kDomain` probe),
  O6 (`SNormRestr`). I accept that; see §3.

## 2. New definitions and changed definitions: refute-first check

| Decl (snapshot 2) | Change | Verdict | Reason |
|---|---|---|---|
| `AttachLinkedOn`, `attachedOrder` (Core) | R1 | FAITHFUL | As argued in stage 1 §2. The classes are exactly the irreducible components of the garden rooted at 𝒰 (T L897). |
| `IsASolution` (System §A) | **removed** (CL-6); `AnsatzAt` (1) uses `NLS.IsAkSolution P.L P.γ P.δ p (initialCoeff …) (a ω)` | FAITHFUL | The landed class `IsAkBounded` has weight (1+‖n/L‖²)^{(d+1)/2}, identical to the removed draft's `jbr(n/L)^{d+1}`. The argument order (L γ δ 𝔇 c a) is correct (it elaborates, and 𝔇 = p and c = û_in are the only ℝ and data slots). Uniqueness is quantified over `IsAkSolution … b`, i.e. in the class. Meaning unchanged. |
| `kernelK` (docstring only) | R2 / O7 | OK | — |
| `topCountBelow`, `FlowerRestr` (moved Statements → System, CL-8) | moved unchanged | FAITHFUL on their own | They are T L2271–L2272 with "order" = number of layer-p branching nodes (L2290). (Y-1) is Ntr < topOrder. (Y-2) bounds every child of the root. (W-1) is again Ntr < topOrder. (W-2) bounds every sibling of 𝔣. (W-3) is topOrder − topCountBelow(𝔣^pr) ≤ Ntr: replacing 𝔣^pr by a flower removes exactly its layer-p subtree count. |
| `truncSumHζ` (moved, CL-8; `truncSumH` deleted) | moved unchanged | **WRONG for kind ≠ 0 (D1)** | See §2a. For kind 0 it is ℋ^tr_{p+1} with flower signs ζ·ζ_j, i.e. 𝒳^ζ (L2271, L2288). The trivial-flower-tree question (stage-2 A1) stays open; it is recorded in B1.12's docstring. |
| `maxBracketPow` | R3 | FAITHFUL | — |
| `AnsatzAt` | R4, CL-6 | FAITHFUL | Item (2) is now exactly (ansatz1)–(ansatz2). The rest is unchanged (diff). |
| `chi0_eq_zero_of_one_le_abs`, `finite_chi0Vec_lattice` (new lemmas) | CL-1 | OK | The box is [⌊L(a_j−1)⌋, ⌈L(a_j+1)⌉], correct since χ₀ vanishes off (−1,1). It makes the B1.9/B1.10 `tsum`s genuine finite sums (CL-4). |
| Proof-section lemmas (CL-3, CL-5): `sum_rule`, `eq_zero_of_leaves_zero`, `eq_zero_of_roots_leaves_zero`, `IsPairedTree.lone_value`, `IsPairedTree.sign_lone`, `layer_le_of_isDesc`, `eq_of_mem_attachNodes`, `sum_orderBelow_attachNodes_le`, `attachedOrder_le_order`, `topOrder_le_order`, `WTParams.N_le_N_pred`, `norm_phaseIntegral_le`, `abs_epsDec_le_one`, `card_lone_le_one`, `summable_KTstar_summand` (both forms), `truncSum_untruncated` | new, proved | OK | The statements are the source facts:
  - `sum_rule`: ζ_a κ_a = Σ_{ℓ below a} ζ_ℓ κ_ℓ (T L640–L642);
  - `lone_value`: ζ_lo κ_lo = ζ_𝔯 κ_𝔯 (T L643: k_𝔯 = k_{ℓ_lo});
  - `N_le_N_pred` is stated for q ≥ 1, correctly.

  No definition depends on them, and all are sorry-free. |

The definitions section of System (before "Proofs of the obligations") differs from snapshot 1 only in the rows
above; `diff` confirms this. Core differs only in `AttachLinkedOn`/`attachedOrder`, docstrings and `open NLS`.

### 2a. D1: `truncSumHζ` is empty for kind ≠ 0 (REQUIRED before freezing `truncSumHζ`)

**The defect.**
- `truncSumHζ P F p N kind ζ t s n n'` sums over layered gardens satisfying `LG.IsTrunc p (P.N (p+1)) (P.N p)`, whose
  first conjunct is `∀ j, topOrder p j ≤ N_{p+1}`.
- It also requires `LG.FlowerRestr p (P.N (p+1)) kind`, whose kind-1 and kind-2 clauses both begin with
  `N_{p+1} < topOrder p j` for every j.
- For w ≥ 1 these contradict each other. The support is empty and the sum is 0.

**Lean evidence.** `truncSumHζ_kind_ne_zero` (`scratch/WaveB-delta1-probes.lean`, sorry-free, standard axioms):

```lean
theorem truncSumHζ_kind_ne_zero {P : WTParams} {F : ℕ → Mom P.d → ℝ} {p N w : ℕ} (hw : 0 < w)
    {kind : Fin 3} (hk : kind ≠ 0) (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) :
    truncSumHζ P F p N (w := w) kind ζ t s n n' = 0
```

**Source.**
- L2288 defines ℋ^tr_{p+1}: initial flower trees of order ≤ N_{p+1}, attached gardens of order ≤ N_p.
- It continues: "For 𝒴 and 𝒲 we have the same formulas, but we also require the initial trees to satisfy
  (Y-1)–(Y-2) or (W-1)–(W-3)."
- Read literally, this is the same contradiction. L2272, however, says that the (Y)/(W) requirements put the order
  in [N_{p+1}+1, 3N_{p+1}+1]. So the 𝒴/𝒲 kernels consist of trees with more than N_{p+1} top nodes, and their moment
  expansion produces flower gardens whose initial trees exceed N_{p+1}.
- The intended reading is: for 𝒴/𝒲, the (Y)/(W) bounds replace the bound N_{p+1}, and the bound N_p on attached
  gardens stays. This is a FINDINGS candidate: T L2288 is empty for 𝒴/𝒲 if read literally.

**Consequence.** B1.12's kind ≠ 0 conjunct (`∀ kind ≠ 0, ‖truncSumHζ … kind …‖ ≤ …`) is vacuously true. The
𝒴/𝒲 estimates, which the parametrix needs (W = 𝒳(1−ℒ₁)−1 small), would be lost silently. The stage-3 audit's
O1 argument ("(Y)/(W) force N ≥ 2P(N_{p+1}+1)") assumes a non-empty support.

**Exact Lean change** (`WaveB1-System.lean` §D). Replace the `IsTrunc` conjunct of `truncSumHζ`:

```lean
noncomputable def truncSumHζ (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : Fin 3) (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) : ℂ :=
  ∑ᶠ (LG : LayeredGarden w) (_ : IsCanonH (p + 1) LG ∧
      (kind = 0 → ∀ j, LG.topOrder p j ≤ P.N (p + 1)) ∧
      (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧ LG.garden.order = N ∧
      LG.FlowerRestr p (P.N (p + 1)) kind ∧
      ∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ →
        LG.garden.sign ℓ.toNode = ζ * LG.garden.sig ℓ.1.1),
    KGflower P.L P.γ P.δ F LG t s n n'
```

- This elaborates: `truncSumHζ'` in `scratch/WaveB-delta1-fix.lean`.
- It is unchanged for kind 0: `truncSumHζ'_zero` proves equality with the snapshot's definition, sorry-free.
- For kinds 1 and 2, `FlowerRestr` already bounds each initial tree by 3N_{p+1}+1:
  - (Y-2): the root plus three children's subtrees, each ≤ N_{p+1};
  - (W-2)/(W-3): (tree minus the subtree at 𝔣^pr) ≤ N_{p+1}, and that subtree is 𝔣^pr plus two siblings, each
    ≤ N_{p+1}.
- `finite_truncSumHζ_support` needs its predicate updated. The order bound `order = N` keeps the support finite, so
  the proof is unchanged in substance.
- **Alternative**, if B1.12 stays deferred: keep `topCountBelow`, `FlowerRestr` and `truncSumHζ` out of the freeze
  set with B1.12, and record D1 for packet X1.

## 3. OPTIONAL

- **O1. Stale DESIGN text.**
  - §5 L240 and L318 still describe "the classed `IsASolution`".
  - L265 still mentions `truncSumH`.
  - Q8 (L397–L398) still says "`truncSumHζ` (in the statements file)".

  The changelog is right; the body is not.
- **O2. Integration with Foundations (Infra-review-2 S1–S4), not yet applied.**
  - Wave B still defines its own `chi0`/`chi0Vec`, equal pointwise to `Fourier.chi0` (bridge probe in Infra-review-2).
  - It still has its own norm family next to `Fourier.{spatialNorm, mixedFourierNorm, timeFourierNorm, …}`.
  - `wkeTaylorTerm` still has no bridge to `WKE.taylorU`.

  None of these is a defect of the definitions. The bridges should exist before provers start on B1.5/B1.9/B1.10,
  so that the landed estimates apply to the frozen objects.
- **O3. Stage-2 O2, O4, O6 remain unapplied, as recorded.**
  - O4 (a non-trivial `kDomain`/`KG` probe) is still worth adding. All `kernelK` probes use gardens with no free
    branching node, or δ = 0.

## 4. Probes

Untracked, in `scratch/`; they import the snapshot-2 modules built as described above.

**`WaveB-delta1-probes.lean`** (193 lines, sha256 `7e833665…df111f1`). Every result depends only on `[propext,
Classical.choice, Quot.sound]`.
- R2:
  - `lone3_violates_hlone`;
  - `summable_kernelK_summand_needs_hlone`, the stage-2 counterexample re-proved against snapshot 2.
- R3: `maxBracketPow_neg_lt_one`.
- D1: `truncSumHζ_kind_ne_zero`.
- `#print axioms` for the snapshot's own `summable_kernelK_summand`, `truncSum_untruncated`,
  `contDiff_of_SNormR_lt_top`, `e1_trunc`, `e1_canon2`, `figLG_trunc` and `figLG_canon3`.

**`WaveB-delta1-fix.lean`** (34 lines, sha256 `f46eac36…87bd537`):
- the D1 replacement `truncSumHζ'`;
- `truncSumHζ'_zero` (it agrees with the snapshot at kind 0).
