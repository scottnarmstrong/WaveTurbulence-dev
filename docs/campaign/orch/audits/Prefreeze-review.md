# Pre-freeze scratch review (Task 11): CANON, SYS-DEFS/DUHAMEL, COMB-CORE

Auditor: `wt-orch` (Opus), refute-first. This reviews **statements**, not proofs: exact types against snapshot 5,
hypotheses callers must supply, and junk values. Date: 2026-11-03. Item 4 (main-glue2, main-assembly) passed in Task 10
and is skipped.

## Inputs

All reviewed read-only.

**`/home/scott/wt-scratch/canon4/`** (CANON ported to the freeze-ready packaging). `canon/` differs only in the `Lemmas`
import of `Basic`.
- `Canon-Basic` `20b96033ada6…`
- `Canon-Decomp` `00465e4522ad…`
- `Canon-Finite` `3d44154424d9…`
- `Canon-Main` `1effa3e296dc…`
- `Canon-Trunc` `aeca93093db5…`

Its `snap/` copy is **snapshot 4**: Core, System, Statements and Lemmas are byte-identical to `waveb-snap-4`.

**`/home/scott/wt-scratch/duhamel/`** (snapshot 5; its `snap/` copy is byte-identical to `waveb-snap-5`).
- `Sys-API` `41ed2d91f839…`, `Sys-Kernel` `105880f2f31d…`, `Sys-Duhamel` `4f4f58564a1f…`, `Sys-TreeRec` `bf5915d67b09…`.
  These are the SYS-DEFS files. `API` and `Kernel` are byte-identical to `../sysdefs/`; `Duhamel` and `TreeRec` differ
  only in three docstring lines.
- `Sys-Final` `6b214477f2ef…`, `Duh-Carriers` `3388c955a05f…`, `Duh-Meas` `e5d8c9bdb0b4…`, `Duh-Time` `415c26ef0225…`,
  `Duh-Node` `ad46528e60e1…`.
- `/home/scott/wt-scratch/sysdefs/` is superseded by `duhamel/` (see L1).

**`/home/scott/wt-scratch/comb-core/`** (44 modules, aggregate `CombCore.lean` `0d61935bc80d…`). It is built against a
copied **snapshot-2** Core (sha `9e6c6b4d…` = `waveb-snap-2/WaveB1-Core.lean`).

**Sources.**
- TARGET: L625–L660, L826, L845–L847 (Def `subobject`), L1295–L1325.
- Snapshot 5 statements: `canonicalCharacterization`, `layergarden`, `fixedpoint`; System `ZNorm`, `ZSpace`, `Lop`,
  `aTr`.

**Build.** My own, on snapshot 5: my `waveb5` modules plus the needed landed Foundations, compiled in my scratch root.
One `lake env lean` at a time, `nice -n 5`.
- CANON: 5 modules. SysDraft: 9 modules, plus the 10-module `Cumulant` closure. COMB-CORE: 44 modules plus the aggregate.
- All compiled with **0 errors and 0 `sorry`**. COMB-CORE needed the two port edits of §3.

## Verdict summary

| Package | Verdict |
|---|---|
| CANON | **PASS on snapshot 5.** `Canon.canonicalCharacterization` has **exactly** (`Expr ==`) the snapshot-5 anchor type. `layergarden` (2)(a) follows **verbatim** from `truncSum_couple_offDiag`. Truncation bridges and finiteness/enumeration are faithful; the `∑ᶠ` sums are proved genuine. |
| SYS-DEFS / DUHAMEL | **PASS on snapshot 5** (as in `duhamel/`; 206 declarations, no `sorry`). `duhamel_iff_Lop'` and the tree recursion are faithful. Every hypothesis callers must supply is **dischargeable**, but two helper lemmas for the gate provers are missing (O1, O2). |
| COMB-CORE | **PASS in meaning; NOT yet on snapshot 5 as written.** It is pinned to snapshot 2's Core and fails on snapshot 5 without **two port edits** (L2). With them, all 44 modules and the aggregate compile on snapshot 5, and the 36 audited principal exports keep standard axioms. Definitions of embedded objects match TARGET Def `subobject`. |

**Axioms** (`scratch/Task11-axioms*.lean`, on snapshot 5): 51 principal exports (36 COMB-CORE, 15 SysAPI/Duhamel) and
the 11 CANON exports in `Task11-canon-check.lean` use only `propext, Classical.choice, Quot.sound`.

## 1. CANON

| Declaration | Verdict | Reason |
|---|---|---|
| `Canon.canonicalCharacterization` | **EXACT** | `type == WaveTurbulence.canonicalCharacterization.type` against snapshot 5 (my build), standard axioms. Earlier it was checked against snapshot 3 (README) and snapshot 4 (Task 9a). |
| `truncSum_couple_offDiag` (layergarden (2)(a)) | **EXACT** | `scratch/Task11-canon-check.lean` proves the snapshot-5 conjunct `∀ n : Fin 2 → (Fin P.d → ℤ), n 0 ≠ n 1 → truncSum P (inputsF P R) (p+1) N t ![1,-1] n = 0` directly from it. The lemma holds for every `F`, `q`, `N`. |
| `truncSum_couple_eq_truncSumC` | FAITHFUL | The lattice couple sum with diagonal roots `(n, n)` and signature `(+,−)` equals `truncSumC` at `k = n/L`. Via `KG_eq_KQ` and the decoration shift `shiftDec`, with `isCanonGC_iff_isCanonC` for the class. |
| `truncSumC_untruncated` | FAITHFUL | For `N ≤ N_q` the truncation is vacuous. This is the couple analogue of `truncSum_untruncated` (Lemmas). |
| `isEmpty_genDecoration_of_unbalanced`, `kernelK_eq_zero_of_unbalanced`, `truncSum_eq_zero_of_unbalanced` | FAITHFUL | Momentum conservation `Σ ζ_j n_j = 0`. |
| `finite_layeredGardens`, `finite_canon{G,C,H,GC}`, `canon{G,C,H}Finset` (with `mem_` iff lemmas), `ncard_layerings_le` | FAITHFUL | — |
| `finite_truncSum(C)_support`, `truncSum_eq_sum`, `truncSumC_eq_sum` | FAITHFUL; **no junk** | The `∑ᶠ` in `truncSum`/`truncSumC` has finite support and equals a `Finset` sum, so the frozen sums are genuine, not junk 0. |

**Note.** The README says "the statement of snapshot 3". Update it to "snapshot 5 (Task 11)" when landing.

## 2. SYS-DEFS API and DUHAMEL

### 2.1 Verdict table (principal statements)

| Declaration | Verdict | Hypotheses callers supply, and whether they are dischargeable |
|---|---|---|
| `IsASolution.{toNLS, ofNLS, initial, hasDerivWithinAt, mono, unique, eq_add_integral, tsum_normSq_eq, continuousOn, exists_norm_le, summable_norm}` | FAITHFUL | `0 < L` only. These are the definitional bridge to `NLS.IsAkSolution` plus the landed facts. |
| `IsASolution.glue` | FAITHFUL | `0 ≤ p ≤ q`; a solution on `[0,p]`; `b p = a p`; a bound `sup (1+|n/L|²)^{(d+1)/2} |b t n| ≤ C`; and the derivative identity on `[p,q]`. **Dischargeable** for `b = a^tr + b_fp` with `b_fp ∈ ZSpace` (Λ = (5/4)Λ_{p+1} ≥ 50d > d+1), the `aTr` bound of `fixedpoint`, and the derivative from the integral form via `hasDerivWithinAt_of_eq_add_integral`. The last step needs O2. |
| `AnsatzAt.*` accessors (`measurableSet`, `nested`, `prob_ge`, `isASolution`, `remainder_bound`, `error_bound`, `two_point`, …) | FAITHFUL | Literal projections of the audited `AnsatzAt` conjuncts. |
| `jointCumulant_*` (empty, singleton, scaling, moment–cumulant inversion, gauge/translation vanishing, `congr_map`, products formula) | FAITHFUL | `jointCumulant` is the landed `cumulant` (`rfl`). The inversion is a purely algebraic identity, so it is also valid when moments are junk. The vanishing lemmas need measurability and invariance of the joint law, which `IsGaussianData`/`IsSymmetricEvent` give. |
| `aNonlin_eq_tsum_pairs`, `aNonlin_eq_tsum_aNonlinTerm`, `norm_aNonlinTerm_le`, `summable_aNonlinTerm`, `aNonlin_sum` | FAITHFUL | Summability is a separate hypothesis wherever a `tsum` is manipulated. |
| `kernelK_congr_inputs`, `KG/KQ_congr_inputs`, `truncSum(C)_congr_inputs`, `truncSum(C)_inputsF_congr` | FAITHFUL | Locality: only `F_0, …, F_{q−1}` (respectively `R_0, …, R_{q−1}`) enter `𝒦^tr_q`. |
| `summable_KG_summand` | FAITHFUL | Requires `Summable |F r (m/L)|` for all `r`. Dischargeable for `inputsF P R`: the `R` bound of `RemainderBound`/`AnsatzAt` gives decay ⟨k⟩^{−Λ}. |
| `treeTerm_node` (O-TR1) | FAITHFUL | `𝒥_{node l m r}(t) = ∫_p^t 𝒞₊(𝒥_l, 𝒥̄_m, 𝒥_r)` for summable data and `t ≥ p`. The middle conjugation matches the snapshot sign convention (F9). |
| `intervalIntegrable_treeTriple` (O-TR2), `stronglyMeasurable_treeTerm`, `tsum_norm_treeTerm_le` | FAITHFUL | Summable data only. |
| `treeRecursion`, `treeRecursion_of`, `TreeRecursion` | FAITHFUL | `t ≥ p` and summable `a(p)`. The latter comes from `IsASolution.summable_norm` on `Fev p`. |
| **`duhamel_iff_Lop'`** | FAITHFUL | For `t ≥ p`: `A = a^tr + IccExtend b` solves `A(t) = a(p) + ∫_p^t 𝒞₊(A, Ā, A)` iff `IccExtend b t = Σ_{j≤3} ℒ_j b t`. Uses the frozen `Lop`/`aTr` with `IccExtend` on `[p, p+1]`; for `t > p+1` it is the constant extension, true but beside the point. See the hypotheses below. |
| `duhamel_iff_Lop`, `integral_aNonlin_aFull`, `sum_low_eq_aTr_sub`, `Lop_self`, `aTr_of_le`, `treeTermN_eq_sum`, `summable_norm_*` | FAITHFUL | — |

### 2.2 Hypotheses of `duhamel_iff_Lop'` at the use site (fixed point `b ∈ ZSpace`, `p < 𝔇`)

- **`haP : Summable ‖a(p)‖`** from `IsASolution.summable_norm`.
- **`hb : ∀ s, Summable ‖b s ·‖`** from `ZNorm b < ⊤`: `‖b s m‖ ≤ Z·⟨m/L⟩^{−Λ}` with Λ = (5/4)Λ_{p+1}. Here Λ_{p+1} =
  (40d)^{𝔇−p} ≥ 40d, since `p < 𝔇` in `fixedpoint`.
- **`hint`** (slots containing `b`). Each integrand is a countable sum of (continuous phase) × (measurable `treeTermN`
  or continuous `IccExtend b`) factors with summable bounds that are uniform in `s ∈ [p,t]` (`tsum_norm_treeTerm_le`,
  the Z bound). So it is strongly measurable and bounded, hence interval integrable. **Dischargeable, but no lemma
  provides it yet (O1).**

## 3. COMB-CORE

### 3.1 Snapshot drift (the main finding)

COMB-CORE imports a copied **snapshot-2** Core. Since then Core changed in two ways:
- **Snapshot 2 → 3:** `epsCoef` became self-contained (`WaveTurbulence.epsCoef`, the same body as `NLS.epsCoef`), and
  Core stopped importing `NLS.AkSystem`.
- **Snapshot 3 → 4 (CL-17):** nine Core lemmas moved to `WaveB1-Lemmas`.

COMB-CORE uses six of the moved lemmas (`mem_pre`, `cons_mem_pre`, `nil_mem_nodes`, `dropLast_mem_nodes`,
`mem_forestSet`, `leaves_subset_nodes`) and `open … NLS` (`Decorations.lean`).

**Port test** (`scratch/Task11-combcore-port.patch`): `+ public import WaveBDraft.Lemmas` in `Trees.lean`, and
`open Finset NLS` → `open Finset` in `Decorations.lean`. With these, all 44 modules and `CombCore` compile on snapshot 5
(0 errors, 0 warnings).

**The statements' meaning is unchanged.** Between snapshots 2 and 5, Core's only definitional change is the `epsCoef`
move (same body; bridge `epsCoef_eq_nls`). Task 9a showed snapshots 3 → 5 to be packaging-only. The 36 principal
exports keep standard axioms.

### 3.2 Verdict table (principal exports)

| Group | Verdict | Notes |
|---|---|---|
| Trees: `card_leaves`, `card_nodes`, `finite_order_le`, `treeZeta_neg` | FAITHFUL | `2n+1` leaves, `3n+1` nodes, child signs, ζ(𝒯) under conjugation. |
| Gardens: `plain_signature_counts`, `component_eq_or_disjoint`, `componentGarden_irreducible`, `sum_component_orders`, `multiCouple_component_signs`, `conjugateCouple_isCouple`, `pairedTree_root_eq_lone`, `couple_root_values_eq`, `finite_gardens` | FAITHFUL | Balance and fixed-point-freeness are stated under `IsPlain` (marked leaves are handled, not silently excluded). Components are indexed by increasing tree index; no canonical order is claimed. |
| Decorations: `decoration_ext`, `sum_rule`, `sum_signed_roots_eq_zero`, `omegaNode_eq_inner`, `omegaNode_add_const`, `epsDec_ne_zero_iff`, `epsDec_add_const`, `eq_zero_of_roots_leaves_zero` | FAITHFUL | `epsDec_ne_zero_iff` is exactly the support `𝔊` of (defset) at every branching node. The `Ω` identity is `2⟨k₁ − k, k − k₃⟩`. |
| `finite_decorations_bounded_lattice_leaves`, `…_coset_leaves` | FAITHFUL | Finiteness is derived from boundedness **on the lattice** `latticePoint L` with `L > 0`. Bounded real sets are not claimed finite. |
| Layerings: `LayeredGarden.layer_le_of_isDesc`, `RootedSubforest.isLayering_induced`, `finite_layeredGardens` | FAITHFUL | — |
| Embedded objects: `IsSubCouple G a b := CompletelyPaired (leavesBelow a ∪ leavesBelow b)`; `IsSubPairedTree G a b := a.IsDesc b ∧ CompletelyPaired (leavesBelow a \ leavesBelow b)`; `exists_embedded_couple`, `embeddedPairedTree_isPairedTree`, `embeddedPairedTree_order`, `embeddedPairedTree_graft` | **FAITHFUL to Def `subobject`** (L846) | Incomparability of the two sub-couple roots and sign compatibility are **proved consequences**, not extra premises. `a.IsDesc b` (b below a, `b = a` allowed) matches TARGET's descendant convention ("we allow 𝔪 = 𝔫", L627); `b = a` gives the trivial paired tree. |
| Replacement and collapse: `graftLeafPairForest_order`, `collapseSubCoupleForest_order`, `…_leaves`, `insertCouple_plain`, `insertCouple_order`, `insertCouple_leaf_count` | FAITHFUL | `insertCouple` builds the actual garden with the inherited pairing. It needs `G.pair ℓ ≠ ℓ` (a non-marked leaf), which the source's "replace a leaf pair" presupposes. |

## REQUIRED (at the move into Foundations; no change to any statement)

- **L1. SYS-DEFS:** land the `duhamel/` versions. Do **not** move `sysdefs/Sys-Obligations.lean`: it is the superseded
  file with the two `sorry`s, replaced by `Duh-Meas`/`Duh-Node`/`Sys-Final`. Take `Sys-Duhamel`/`Sys-TreeRec` from
  `duhamel/` (docstrings only differ).
- **L2. COMB-CORE:** apply the two port edits of §3.1, or reprove the six moved lemmas locally, and re-run the module
  checks against the frozen files. As written, the scratch does **not** compile on snapshot 5.

## OPTIONAL

- **O1** (gate provers): a lemma `b ∈ ZSpace L Λ p` (Λ > d) ⇒ `hb` and `hint` of `duhamel_iff_Lop'`, i.e. summability
  and interval integrability of every slot integrand containing `b`. Everything needed is in place (§2.2).
- **O2** (gate provers): **time continuity** of the tree terms and of `𝒞₊(A, Ā, A)`, needed for `glue`'s derivative
  premise through `hasDerivWithinAt_of_eq_add_integral` (`ContinuousOn F`). There is no continuity lemma for `treeTerm`
  in the packet. It is immediate: `treeTerm_node` makes each non-leaf `𝒥_T(t)` an integral `∫_p^t` of an
  interval-integrable function, hence continuous, and leaves are constant.
- **O3** (deduplicate at landing): `Comb.sum_rule`, `Comb.eq_zero_of_roots_leaves_zero`,
  `Comb.LayeredGarden.layer_le_of_isDesc` duplicate `WaveB1-Lemmas` results, and `Comb.finite_layeredGardens`
  duplicates `Canon.finite_layeredGardens`. Keep one of each, or make one an alias of the other.
- **O4.** Update the CANON README ("snapshot 3" → snapshot 5) and the COMB-CORE HANDOFF ("byte-identical to the audited
  snapshot" → snapshot **2**).

## Probes (untracked, `scratch/`)

| File | sha256 | Purpose |
|---|---|---|
| `Task11-canon-check.lean` | `f16ad4dde6f3…` | `canonicalCharacterization` `==` the snapshot-5 anchor; `layergarden` (2)(a) derived exactly; axioms of 11 CANON exports |
| `Task11-axioms.lean` | `731692fdf44a…` | Axioms of 36 COMB-CORE and 11 SysAPI/Duhamel principal exports, on snapshot 5 |
| `Task11-axioms-isasolution.lean` | `3b69ac758f9d…` | Axioms of the 4 `IsASolution` API lemmas (`toNLS`, `glue`, `eq_add_integral`, `tsum_normSq_eq`) |
| `Task11-combcore-port.patch` | `a82a279d1044…` | The two port edits that make COMB-CORE compile on snapshot 5 |
