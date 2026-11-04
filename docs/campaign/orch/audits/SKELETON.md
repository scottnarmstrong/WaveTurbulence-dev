# Statement audit: wt-resonant's SKELETON (C3)

Auditor: `wt-orch`, refute-first. Date: 2026-11-04 (Task 33a). Findings only; nothing was edited.

**Scope.** `/home/scott/wt-scratch/skeleton` (`HANDOFF.md`, `validation/SOURCE-EXPORTS.md`), against:
- DH21 Props 4.13–4.14, Remark 4.15 and Cor 4.16;
- DH21-2 Props 4.4–4.6 and TARGET Prop 4.6 (`propstructure2`);
- the E4 uniqueness argument (DH21 L833, DH21-2 L641);
- FINDINGS F77.

## Verdict

**PASS.**
- Each exported statement is the source's statement, on actual ordered source gardens, with no added source premise.
- The E4 claim is proved as stated.
- F77 is a valid erratum, stronger than recorded.
- **A clean rebuild of all 371 modules from the pinned sources: 0 errors.** The handoff's last validation was not a
  clean rebuild; 325 artifacts predated an import's artifact.
- All nine exports use [propext, Classical.choice, Quot.sound].
- **Findings:**
  - S-1 (REQUIRED before freezing a count): the counts lack a finiteness conjunct;
  - S-2, S-3 (integration notes): the B2 inputs are pre-CL-16 copies, and the CL-22 anchor names are imported from
    scratch.

## 1. Inputs

**Pin.** I pinned the tree at 07:53 UTC: 660 files, list digest `6619defc1f77…`. It was unchanged at the end.
- `HANDOFF.md` `df1da257150c…`; `SkeletonWork.lean` `ba853b535a29…`.
- `SourceStructure` `4ad44aaed04d…`, `SourceTwoStageStructure` `9f7addec2a14…`, `SourceCounts` `b5516c95f136…`,
  `Raw` `83b3ee1b7d2d…`, `PrimeGraph` `5a373ead20ca…`.

**Clean rebuild (mine).**
- I rebuilt `SkeletonDraft.*` (370 modules) and `SkeletonWork` from the pinned sources, in topological order, into my
  scratch.
- The base was the skeleton directory's REG-STRUCT/CombSnapshot/B1/B2 oleans (none stale) and resonant's Wave A
  build. I read both and wrote to neither.
- **371/371 modules, 0 errors, 2272 s.** The only warnings are linter notes in 14 modules: unused `simp` arguments and
  variables, and `if_pos` deprecations. There is no `sorry`.
- **Why it was needed.** In the packet's own artifacts, 325 of 358 `SkeletonDraft` oleans were older than the oleans
  of `Raw` and `PrefixStretch`. Those two were recompiled at 07:42–07:45 from sources last edited at 00:59 and 02:26.
  The handoff says its final sweep "was not a clean rebuild". The rebuild settles it.

## 2. Statements against the source

**The carrier and the operations.**
- **Gardens.** `Garden w` is B1's ordered source forest with root signs and the leaf partner involution. `IsPlain`
  excludes marks and unpaired leaves.
- **Raw forests.** `Raw w` is the literal forest, root signs and oriented pair set.
- **The steps.** `Raw.opA` replaces a leaf pair by a (1,1)-mini couple with a B2 mini-couple code: DH21 Def 4.12, step
  A. `Raw.opB` replaces any node by a mini tree carrying the old subtree at its lone slot: step B, with B2's
  six-code table. Each step is guarded by `Raw.Valid`.
- **`Reconstructs`** is the reflexive-transitive closure of these steps.
- **Prime.**
  - `IsPrimeGarden G := G.IsPlain ∧ ¬ Nonempty (MiniOccurrence G)` is literally TARGET Prop 4.6's "does not contain
    any embedded (1,1)-mini-couple or mini-tree".
  - `isPrimeGarden_iff_raw_prime` proves it equal to DH21 Def 4.12's "not obtainable by step A or B"
    (`Prime := Valid ∧ ∀ S, ¬ Expand S R`).

| export | type (abridged) | source |
|---|---|---|
| `existsUnique_prime_reconstructs` | plain `G` → `∃! S, IsPrimeGarden S ∧ Reconstructs S G` | DH21 4.13 (L816), DH21-2 4.4 (L619): unique skeleton |
| `couple_regular_iff_prime_skeleton_trivial` | couple `G`, prime `S` reconstructing it → `IsRegularCouple G ↔ IsTrivialGarden S` | DH21 4.13, last sentence |
| `regularMulticouple_iff_prime_skeleton_trivial` | plain `G`, prime `S`, `G` reduces to `S` → `IsRegularMulticouple G ↔ IsTrivialGarden S` | DH21-2 4.4, last sentence |
| `existsUnique_prime_with_replacements`, `existsUnique_reconstructionData` | unique prime `S` and unique replacement data `D` (regular trees at branches, regular couples at leaf pairs) decoding to `G` | DH21 Remark 4.15, DH21-2 4.5, TARGET 4.6 |
| `existsUnique_twoStageRepresentation`, `twoStageRepresentation_unique_data` | unique intermediate `H`: bare chains at the branches of `S` decode to `H`, then couples at the leaf pairs of `H` (trivial chains) decode to `G`; both stages' data unique | DH21 4.14 (L824), DH21-2 4.5 (L629) |
| `twoStageRepresentation_regular_subcouple_trivial` | every regular embedded subcouple of `H` is trivial | E4: DH21 L833, DH21-2 L641 |
| `sourceCoupleCount_uniform` | `Nat.card {G // order ≤ m ∧ plain ∧ Reconstructs S G} ≤ (12¹²)^m` | DH21 Cor 4.16 |
| `sourceGardenCount_uniform` | the same at width `2R`, `≤ (12⁶)^{m+R}` | DH21-2 4.6, TARGET 4.6 |

**Assessment.**
- **4.13 / 4.4.** The skeleton is unique and actual. Regularity is equivalent to a trivial skeleton for couples, and
  for gardens through a literal root-pair partition into regular induced couples (`IsRegularMulticouple`).
- **4.14 / 4.15 / 4.5.**
  - `TwoStageRepresentation` is DH21's two stages: (i) a regular chain at each branching node, through
    `IsBareInflation` (bare chains, trivial couples); (ii) a regular couple at each leaf pair of the intermediate.
  - The intermediate is unique **among all two-stage representations**, not only among constructed ones.
  - The data of both stages are unique.
  - The one-stage form (Remark 4.15, TARGET 4.6) is `existsUnique_prime_with_replacements`.
- **E4** is exactly the omitted claim "`𝒬_int` contains no nontrivial regular sub-couple". The proof does not assume
  the source's further, unproved "maximal regular sub-couple containment" step. Uniqueness is proved by a separate
  composition argument.
- **Counts.** "Couples with skeleton `𝒬_sk` and `n(𝒬) ≤ n`" are counted as all plain gardens reconstructible from a
  fixed plain `S`, which contains them. That is stronger: `S` need not be prime. The constants are absolute; the
  source's are unspecified.
- **Generality.** The width is arbitrary in 4.13/4.14/E4, more general than the source's even width. The counts
  specialize to `2` and `2R`.

## 3. F77 (DH21 Cor 4.16, proof L850/L852)

- **Confirmed, and stronger than recorded.** The displayed `Σ_{n₁+⋯+n_m ≤ n} C₀^{n₁}⋯C₀^{n_m} ≤ (2C₀)^n` fails **for
  every `C₀ > 0`**, not only for the even-scale example.
- Its top term alone is `C(n+m−1, m−1)·C₀^n`. At `m = n = 8` that is `6435·C₀⁸ > 256·C₀⁸`. F77's even-scale count,
  `C(11,7) = 330 > 256`, is also correct.
- **The corollary itself is true.** Since `m ≤ n`, a factor `2^m ≤ 2^n` is absorbed into the constant. SKELETON proves
  it with explicit constants.
- **Minor erratum, in a proof only.**

## 4. Findings

**S-1 (REQUIRED before any count is frozen or consumed as a source fact).** Both counts are bare
`Nat.card {…} ≤ C^m`.
- On an infinite type `Nat.card = 0`, so the inequality alone does not certify a finite family. This is the hazard
  B2's R15-2 fixed in `regular_count_le` with explicit `Finite` conjuncts.
- The families are finite: each proof injects into a finite type, since `Nat.card_le_card_of_injective` needs
  `Finite` of the target.
- **Fix: add a `Finite {…}` conjunct.** In the rebuilt environment I checked that it follows from the proof's own
  injection with `Finite.of_injective` (a compiled `example`).

**S-2 (integration).**
- The packet is built on wt-resonant's pinned B2 inputs: REG-STRUCT's `RegularDefs`, the pre-CL-16 copy of §1–§3,
  and snapshot-6 B1, whose Core/System equal snapshot 7's.
- At the port it must be rebuilt on the final B2 definitions, as Task 32 did for REG-STRUCT (161 modules, 0 errors).
  That copy differs only in seven instance names.

**S-3 (integration, CL-22).**
- The closure imports `B2CharacterizationProofs`, which declares `RegCpl.exists_decodes`,
  `existsUnique_regCpl_decodes`, … under their native names.
- Since CL-22 these are frozen B2 anchors. `RegularMulticouples` and `ReconstructionUniqueFixedCore` use them.
- At the port, import the frozen anchors (sealed by `waveb2/providers/`) instead. The statements are identical, so the
  proofs need no change.

**Note.** These are pre-freeze candidates. If any is frozen, it needs its own source review, binder by binder, and
author approval; this audit is not that approval.
