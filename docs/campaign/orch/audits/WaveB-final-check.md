# Final check: Wave B tier-B1 freeze set (snapshot 3 against fix list 3)

Auditor: `wt-orch` (Opus). Date: 2026-11-03. Task 8b.

## Inputs

- **Snapshot.** `/home/scott/wt-scratch/waveb-snap-3/`; `sha256sum -c SHA256SUMS` passes for all 11 entries.
- **Fix list.** `docs/campaign/orch/WAVEB-FIXLIST-3.md`.
- **Changelog.** DESIGN.md CL-12 … CL-15.
- **Baseline.** I diffed every file against `waveb-snap-2`, the snapshot of my delta audit.
- **Tree.** `w/orch` at `c43515f` (main merged).
- **Toolchain.** Lean v4.35.0, Mathlib v4.35.0.
- **Build.** No `lake build`. The dependencies were compiled one module at a time with `lake env lean -o`, `nice -n 5`;
  their sources are unchanged since my Task 6b/7 builds, and `Foundations/WKE/Taylor` was added for the bridges.
  All ten snapshot files were then compiled as modules `WaveBDraft.*`, in import order.

## Verdict

**PASS. The freeze set as listed in §4 can be frozen.**

- Every REQUIRED item of fix list 3 is applied exactly. So are the OPTIONAL items and the sumint D7 question.
- The diff against snapshot 2 contains **only** logged edits.
- The four freeze-set files import only frozen Wave A definitions and each other. The frozen Defs import only Mathlib.
- All ten files elaborate with 0 errors. The `sorry`s are exactly the 11 freeze-set anchors plus the deferred B1.12.
- The bridges S1, S2 and S4 are proved, with standard axioms.

There are two notes for the freeze manifest (§4.3); neither blocks the freeze.

## 1. Fix list 3: item by item

| Item | Required change | Snapshot 3 | Verdict |
|---|---|---|---|
| **1. N1** (`nlsAkBridge` at 𝔇 = 0) | `(hD : 1 ≤ D)` right after `(D : ℕ)`, plus docstring deviation D3 | `nlsAkBridge … (D : ℕ) (hD : 1 ≤ D) (α T : ℝ) …` (`#check` confirmed). D3 is in the docstring: "at 𝔇 = 0 the a-system on [0,0] is void … item (2) is false there". This matches my Task 7 finding T7-1 and its probe. | **APPLIED** |
| **2. N-guard** (𝔛 norms) | C^{Λ₁} regularity of k ↦ F̂(λ,k) only when Λ₁ ≥ 1; none at order 0; keep the time-integrability guard | `XNorm`: `if Λ₁ = 0 ∨ ContDiff ℝ Λ₁ (timeFT F lam)`, with the integrability guard kept. `XNorm00` never had a momentum guard. `SNorm` is unchanged, which is correct since the ruling concerns 𝔛 and every 𝔖 use has Λ₁ ≥ 1. With Λ₁ = 0 the only multi-index is ρ = 0, so `iterPartial 0 F = F` and no derivative junk can enter. | **APPLIED** |
| **3. Closure policy** | Freeze-set definitions depend only on frozen Wave A definitions and Mathlib; bridges for S1–S4; S1, S2, S4 proved; unproved bridges listed as provider obligations; fix references broken by namespace moves | See the rows below. | **APPLIED** |
| 3a. Imports | — | Core imports `Frozen/Defs/{Mom, LatticePoint, IsWKESolution}`. System imports `WaveBDraft.Core` and `Frozen/Defs/{CollisionOp, InitialCoeff}`. Statements imports `WaveBDraft.System` and `Frozen/Defs/{IsSmoothNLSSolution, TorusFourierCoeff, KineticTime, StdComplexGaussian}`. Sumint imports `WaveBDraft.System`. The frozen Defs import only `Mathlib` and each other. Hence no freeze-set constant can come from Foundations. | OK |
| 3b. Self-contained replacements | — | Each new definition has the landed body, with a definitional bridge:<br>• `epsCoef` (Core) = (defcoef0) = landed `NLS.epsCoef`;<br>• `aNonlin` (System) = landed `NLS.aNonlin`, with `resFactor` of lattice points standing for `NLS.resonance`;<br>• `IsASolution L γ δ T c a` = landed `NLS.IsAkSolution`: data, the class weight (1+‖n/L‖²)^{(d+1)/2}, and ∂ₜ = 𝒞₊ within [0,T];<br>• `jointCumulant` = (eqncm) = landed `cumulant`, with 𝕂(∅) = 1 as before.<br>`treeTerm` uses `resFactor (latticePoint …)`. `AnsatzAt` (1) and (3) and `nlsAkBridge` (1), (2) use `IsASolution` and `jointCumulant` with the **same argument order** as the snapshot-2 `IsAkSolution`/`cumulant` calls. No `open NLS` remains. | OK |
| 3c. Bridges | S1, S2, S4 proved | `WaveB1-Bridges.lean` elaborates. These depend only on `[propext, Classical.choice, Quot.sound]`:<br>• S2: `epsCoef_eq_nls`, `aNonlin_eq_nls`, `isASolution_iff_nls`, `jointCumulant_eq_cumulant`, `resFactor_latticePoint_eq_resonance`, `omegaNode_latticeDecoration_eq_resonance`;<br>• S1: `chi0_eq_fourier_chi0`, `chi0Vec_eq_chi0Tensor`;<br>• S4: `wkeTaylorTerm_eq_taylorU`. Its statement `wkeTaylorTerm (φ (δ * p)) δ p n t k = WKE.taylorU hd φ δ p n t k`, for all n, t, k, is exactly the instance B1.5 consumes. | OK |
| 3d. S3 (norms) | listed as provider obligations | DESIGN CL-12 lists three norm bridges as provider obligations:<br>• `SNormR = spatialNorm`;<br>• `XNorm`/`XNormRestr` against `mixedFourierNorm` and its restriction;<br>• `XNorm00`/`XNorm00Restr` against `timeFourierNorm`, noting that Foundations still lacks a vector-variable-type 𝔛^{θ,0,0} for `sumint`.<br>This matches Infra-review-2 S3. | OK |
| **4. D1** (deferred flower objects) | Keep `truncSumHζ`, `FlowerRestr`, `KGflower`, `layergardenFlower`, `WTPrefixP`, `topCountBelow` out of the freeze set, marked as deferred | All six now live only in `WaveB1-Deferred.lean`. Its header says "DEFERRED drafts (not in the freeze set; packet X1)" and records D1 ("`truncSumHζ` is identically 0 for kinds 1, 2"). `finite_truncSumHζ_support` moved to `WaveB1-Deferred-probes.lean`. None of the six occurs in Core, System, Statements or Sumint (checked by `grep`; the freeze-set modules build without the Deferred module). | **APPLIED** |
| OPTIONAL O1–O5 (delta-stage-3 §7) | apply | CL-15:<br>• O1: the `countLemma` docstring notes the unused η binder;<br>• O2: the `canonicalCharacterization` docstring says "kind 0 (𝒳)";<br>• O3: recorded for the B2 drafts;<br>• O4: DESIGN refreshed;<br>• O5: the glue list includes `IsASolution.mono`, the decoration-shift bridge, the Duhamel identity, mass conservation, a.s. rapid decay and `measurableSet_smoothDataSet`. | **APPLIED** |
| QUESTION: sumint D7 | answer in DESIGN | DESIGN Q9 answers "yes; datum not extended". I checked it independently in §3. | **CONSISTENT** |

## 2. No unlogged changes (diff against snapshot 2)

| File | Changed lines | Content of the diff | Logged in |
|---|---|---|---|
| `WaveB1-Core.lean` | 16 | The `Foundations/NLS/AkSystem` import is removed; `epsCoef` is defined with the landed body; docstrings; `open NLS` removed | CL-12 |
| `WaveB1-System.lean` | 120 | The `Cumulant/Basic` import is removed. `aNonlin`, `IsASolution` and `jointCumulant` are added. `KGflower`, `topCountBelow`, `FlowerRestr` and `truncSumHζ` are removed. `treeTerm` uses `resonance` → `resFactor ∘ latticePoint`. `XNorm` gets the guard. `AnsatzAt` uses `IsASolution` and `jointCumulant`. Docstrings change. | CL-12, CL-13, CL-14 |
| `WaveB1-Statements.lean` | 73 | `nlsAkBridge`: `hD` and `IsAkSolution` → `IsASolution`. B1.12 and `WTPrefixP` are removed. Docstrings (D3, O1, O2); `open NLS` removed. | CL-14, CL-15 |
| `WaveB1-Sumint.lean` | 0 | — | — |
| `WaveB1-Core-probes.lean` | 18 | `omegaNode_latticeDecoration` is restated against `resFactor`; the `NLS.resonance` bridge moves to Bridges | CL-12 |
| `WaveB1-System-probes.lean` | 12 | `finite_truncSumHζ_support` moved out | CL-14 |
| `WaveB1-Statements-probes.lean` | 0 | — | — |

No other definition or statement changed. In particular:
- the kernels and the shared sums are unchanged;
- the norms are unchanged except for the `XNorm` guard;
- `AnsatzAt` is unchanged except for the two renamings;
- the statements B1.1–B1.3, B1.5, B1.7–B1.11 and `sumint` are unchanged.

My earlier fixes are intact: stage-1 R1 (`AttachLinkedOn`), stage-2 R2 (`summable_kernelK_summand`), R3
(`maxBracketPow`) and R4 (no `ContDiff ℝ ⊤`).

## 3. Elaboration, axioms, and the sumint D7 answer

**Elaboration.** All modules elaborate with 0 errors:

| Module | `sorry`s | Notes |
|---|---|---|
| Core | 0 | — |
| CoreProbes | 0 | — |
| System | 0 | — |
| SystemProbes | 0 | — |
| Statements | **10** | L71 `propansatz`, L105 `layergarden`, L131 `fixedpoint`, L184 `nlsAkBridge`, L224 `wkeTaylor`, L252 `countLemma`, L288 `atomCountLemma`, L354 `quadExpSum2`, L369 `quadExpSum3`, L473 `canonicalCharacterization` |
| StatementsProbes | 0 | — |
| Sumint | **1** | L260 `sumint` |
| Deferred | 1 | L96 `layergardenFlower`, outside the freeze set |
| DeferredProbes | 0 | — |
| Bridges | 0 | — |

**Axioms.** These use only `[propext, Classical.choice, Quot.sound]`:
- `summable_kernelK_summand`, `truncSum_untruncated`, `contDiff_of_SNormR_lt_top`;
- `finite_support_quadSum2`, `summable_quadSum3`;
- `e1_trunc`, `figLG_canon3`;
- all nine bridges.

**Sumint D7 (Q9): consistent with the consumer.**
- The only black-box consumer is Prop `vineest` (T L1723ff). In step (A-i), L1797, `k = T₁x + h₁` and `ℓ = T₂x + h₂`
  with h_j depending only on the boundary vectors (k_{𝔲₁}, k_{𝔲₁₁}, k_{𝔲₂₁}, k_{𝔲₂₂}) = (e,f,g,h); (B) and (C)
  "also hold".
- Every relation used there is homogeneous linear with integer coefficients: branching k_𝔫 = k_{𝔫₁} − k_{𝔫₂} + k_{𝔫₃},
  equal paired leaves, x's as differences (L1797, (C-i), (C-ii)), r = e − f, and x₀ⁱ depending linearly on earlier
  variables. So h₁ and h₂ are integer combinations of (e,f,g,h) with **no constant offset**.
- Evaluating at the constant decoration (all vectors v, x = 0) is legal because v − v + v = v. It gives **coefficient
  sum 1** in each component.
- That is exactly the datum's `H_coset : ∀ v, ∑ c, H₁ v c = 1 ∧ ∑ c, H₂ v c = 1`, which forces k, ℓ ∈ w̲ + ℤ_L^d as
  `sumint` requires. The ladder bound (redladder2) reuses only parts of the proof.
- Not extending the datum is correct. `WaveB1-Sumint.lean` is byte-identical to snapshot 2.

## 4. The exact freeze set

### 4.1 Anchor statements (11; sorry'd until proved)

Ten are in `WaveB1-Statements.lean`, and one is in `WaveB1-Sumint.lean`. In WAVE-B numbering:

| WAVE-B | Anchor | File |
|---|---|---|
| B1.1 | `propansatz` | Statements |
| B1.2 | `layergarden` | Statements |
| B1.3 | `fixedpoint` | Statements |
| B1.4 | `nlsAkBridge` | Statements |
| B1.5 | `wkeTaylor` | Statements |
| B1.6 | `sumint` | Sumint |
| B1.7 | `countLemma` | Statements |
| B1.8 | `atomCountLemma` | Statements |
| B1.9 | `quadExpSum2` | Statements |
| B1.10 | `quadExpSum3` | Statements |
| B1.11 | `canonicalCharacterization` | Statements |

So "10 statements + `canonicalCharacterization` + `sumint`" in the brief counts `canonicalCharacterization` twice. The
freeze set has **nine** statements B1.1–B1.5 and B1.7–B1.10, plus B1.11, plus B1.6: **11 anchors**. B1.12 is
deferred.

### 4.2 Definition anchors (every non-theorem declaration of the four files; namespace `WaveTurbulence`)

**`WaveB1-Core.lean`** (67 definitions, counting structures, inductives and abbrevs, plus 24 instances; the file's 9 proved `TTree`/forest lemmas are covered in §4.3(a)):
- **Parameters:** `WTParams` (structure), `WTPrefix`, `WTParams.{theta, Lambda, Rdown, R, N, gamma0, gamma1}`.
- **Trees:** `TTree` (inductive), `TTree.Path`, `TTree.{order, pre, nodes, leaves, branching, pathSign}`.
- **Forests:** `forestSet`, `GNode`, `GLeaf`, `GBranch`, `GLeaf.toNode`, `GBranch.{toNode, child}`,
  `GNode.{root, IsDesc, Incomparable, leavesBelow, orderBelow}`, `nodeSign`.
- **Gardens:** `MarkTag` (inductive), `Garden` (structure), `Garden.{IsFlower, IsLone, IsPlain, IsBalanced,
  IsFlowerGarden, order, sign, zeta, CompletelyPaired, leavesOf, Irreducible}`, `IsCouple`, `IsPairedTree`.
- **Decorations:** `IsDecoration`, `IntDecoration`, `GenDecoration`, `cosetDecoration`, `epsCoef`, `epsDec`,
  `resFactor`, `omegaNode`.
- **Layerings and canonical gardens:** `IsLayering`, `LayeredGarden` (structure), `LayeredGarden.{parentLayer,
  CanonCriterion, OnStem}`, `IsCanonG`, `IsCanonC`, `IsCanonH`.
- **Truncation:** `LayeredGarden.{attachNodes, topOrder, AttachLinked, AttachLinkedOn, attachedOrder, IsTrunc}`.
- **Instances (anonymous):**
  - `DecidableEq` and `Fintype` for `GNode`/`GLeaf`/`GBranch`;
  - `Decidable` for `IsDesc`, `Incomparable`, `IsFlower`, `IsLone`, `IsPlain`, `IsBalanced`, `IsFlowerGarden`,
    `CompletelyPaired`, `Irreducible`, `IsCouple`, `IsPairedTree`, `IsLayering`, `CanonCriterion`, `OnStem`,
    `IsCanonG`, `IsCanonC`, `IsCanonH`;
  - `Fintype MarkTag`.

**`WaveB1-System.lean`**, definitions section only (55 definitions + 3 instances):
- **§A:** `jbr`, `zpowSign`, `coupling`, `aNonlin`, `IsASolution`, `jointCumulant`.
- **§B:** `IsSymmetricEvent`.
- **§C (kernels):** `GBranch.{IsChildOf, IsParentOf}`, `Garden.{IsFlowerParent, IsLoneParent, FreeBranch,
  extendTime}`, `phaseProd`, `phaseIntegral`, `kDomain`, `inputLeaves`, `kernelK`, `KG`, `KQstar`, `KQ`, `KTstar`.
- **§D (sums):** `IsCanonGC`, `inputsF`, `truncSum`, `truncSumC`.
- **§E (Duhamel):** `single`, `IsBranchConsistent`, `TreeDecoration`, `treeSign`, `treeTimeDomain`, `treeTerm`,
  `treeTermN`, `aTr`, `Slot`, `slotCountB`, `slotOrder`, `Lop`.
- **§F (norms):** `partialMom`, `iterPartial`, `SNorm`, `SNormR`, `timeFT`, `maxBracketPow`, `XNorm`, `XNorm00`,
  `XNormRestr`, `XNorm00Restr`, `ZNormOn`, `ZNorm`, `ZSpace`.
- **§G–§I:** `chi0`, `chi0Vec`, `wkeTaylorTerm`, `AnsatzAt`.
- **Instances:** `Decidable (IsParentOf)`, `Decidable (IsFlowerParent)`, `Fintype FreeBranch`.

**`WaveB1-Statements.lean`** (15 definitions + 3 instances): `IsGaussianData`, `IsBalancedSig`, `jbrProd`,
`RemainderBound`, `coupleRemainder`, `NearLattice`, `eZ`, `LayeredGarden.{BelowSet, leavesBelowSet, TopRegion,
TopDecompWith, TopDecomp, IrreducibleAt, CanonInd, roots}`, and three `Decidable` instances.

**`WaveB1-Sumint.lean`** (21 definitions, counting structures and abbrevs): `SumintShape` (structure) and `SumintShape.{n, VIdx, M, LexLt, TVar,
xSlot, ySlot, x0Slot, uSlot}`; `IsUnitCoeff`; `SumintDatum` (structure) and `SumintDatum.{kVec, ℓVec, Admissible,
timeDom, phase, expr, M₀, M₁}`; `WTPrefixA`.

### 4.3 Two notes for the manifest (not blocking)

**(a) Proved theorems inside the definition closure.**
- Core's `GNode.root`, `GLeaf.toNode`, `GBranch.toNode`, `GBranch.child`, `LayeredGarden.parentLayer` and the `Fintype`
  instances use proved lemmas as proof terms in their bodies: `TTree.{nil_mem_nodes, leaves_subset_nodes,
  branching_subset_nodes, child_mem_nodes, dropLast_mem_nodes}` and `mem_forestSet`.
- Those proofs in turn use `TTree.{mem_pre, cons_mem_pre}`.
- So the anchor checker's `definition_closure` reaches **eight sorry-free theorems**. Either list them in the manifest
  as frozen proved lemmas, or confirm that the checker treats theorem constants in definition bodies as opaque.

**(b) Proved non-anchor lemmas in the freeze-set files.**
- These are:
  - 35 theorems in System, from "Proofs of the obligations" on: `summable_kernelK_summand`, `truncSum_untruncated`,
    `sum_rule`, `IsPairedTree.lone_value`, `contDiff_of_SNormR_lt_top`, …;
  - System's `chi0_eq_zero_of_one_le_abs` and `finite_chi0Vec_lattice`;
  - Statements' `finite_support_quadSum{2,3}` and `summable_quadSum{2,3}`.
- They are sorry-free with standard axioms, and no definition depends on them.
- Decide whether they are frozen with the files, harmless since they are proved, or moved to a provider file, so that
  the frozen surface is exactly §4.1 + §4.2 (+ 4.3(a)).

**A note for providers (not a defect).** `WaveTurbulence.epsCoef` (Wave B) and `WaveTurbulence.NLS.epsCoef`
(Foundations) coexist, and so do `aNonlin` and `NLS.aNonlin`. A file that `open`s `NLS` and uses the bare names gets
an ambiguity error. `WaveB1-Bridges.lean` shows the qualified pattern.

## 5. Deferred (not frozen)

`WaveB1-Deferred.lean` holds the packet-X1 drafts: `KGflower`, `LayeredGarden.topCountBelow`,
`LayeredGarden.FlowerRestr`, `truncSumHζ`, `WTPrefixP`, and B1.12 `layergardenFlower` (sorry). D1 (`truncSumHζ`
empty for kinds 1, 2) is documented there for X1. It must be fixed before any of these is frozen; my delta-1 report
has the fix.
