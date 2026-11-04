# COUNT audit (Task 16b): `countLemma_bound` and `atomCountLemma_bound` against snapshot-5 B1.7 and B1.8

Auditor: `wt-orch` (Opus), refute-first. Date: 2026-11-04.

## Subject and evidence

**Subject.** Landed `f56f6bb`, `WaveTurbulence/Foundations/CountLemmas/`:
- `CountLemma.lean` (`85d708e0cdbb…`) proves `CountLemmas.countLemma_bound`;
- `AtomCount.lean` (`ec4e20c939d7…`) proves `CountLemmas.atomCountLemma_bound`;
- `LatticeSets.lean` (`a6fb8150aac3…`) defines `CountLemmas.NearLattice`.

**Reference.** Snapshot-5 `WaveB1-Statements.lean`: `countLemma` (B1.7, L252) and `atomCountLemma` (B1.8, L288), with
`NearLattice` defined in the same file. My compiled snapshot-5 `WaveBDraft.Statements` is byte-identical to that file.

**Evidence: my own build.**
- I compiled the 154-module closure of `CountLemma` and `AtomCount` from this worktree's sources (main `017cff0`
  merged), one `lake env lean` at a time: 0 errors, 0 `sorry`.
- `scratch/Task16b-count-check.lean` (`fbf085e12b23…`) imports `WaveBDraft.Statements` (snapshot 5) together with
  both landed modules, so the types are compared **in one environment**.

## Verdict: PASS for both, up to one named definition

| Check | `countLemma_bound` vs B1.7 | `atomCountLemma_bound` vs B1.8 |
|---|---|---|
| Raw `Expr ==` | false (only `NearLattice` differs) | false (only `NearLattice` differs) |
| After renaming `CountLemmas.NearLattice ↦ NearLattice` | `==` **true**, `Expr.equal` **true** (binder names and info identical) | `==` **true**, `Expr.equal` **true** |
| Constants in the landed type but not in the anchor | only `CountLemmas.NearLattice` | only `CountLemmas.NearLattice` |
| `isDefEq` (default transparency) | true | true |
| `example : type_of% @WaveTurbulence.countLemma := @CountLemmas.countLemma_bound` (and the B1.8 analogue) | elaborates | elaborates |
| Universe parameters | none / none | none / none |
| Axioms of the landed theorem | `[propext, Classical.choice, Quot.sound]` | same |

**`NearLattice`.** `WaveTurbulence.NearLattice` (snapshot) and `WaveTurbulence.CountLemmas.NearLattice` (landed,
`@[expose]`) have identical types and identical bodies (`‖latticePoint L n − a‖ ≤ 1`).

**No smuggled hypothesis.** This follows from the identity above. All binders are retained exactly:
- the `∃ η₀ ∀ η ∈ (0, η₀]` binder of B1.7 (unused in the bound, witnessed by `η₀ = 1`);
- `c₀ ≥ 1`;
- the order `∀ δ ∃ L₀` (L₀ may depend on δ);
- the `P` cases;
- B1.8's `nk ≠ 0` guard for `ε = −1`;
- the reading of `|k| ≥ L^{−γ+η}`;
- the finiteness conjuncts.

The handoff's claim "exact draft statement comparison PASS (declaration name only changed)" is confirmed at `Expr`
level, with this one qualification.

## For the post-freeze seal (both become seals right after the Wave B freeze)

- **The provider must use the frozen predicate.** The frozen anchors will refer to the frozen B1 `NearLattice`. A
  provider statement written with `CountLemmas.NearLattice` would close the anchor by `by exact` (it is defeq,
  because the definition is `@[expose]`), but it would **not** be `Expr`-equal. The seal checklist ("provider
  statement equals the anchor") expects `Expr` equality.
- **Recommended landing:**
  - make the provider state the theorem with the frozen `NearLattice`;
  - either redefine `CountLemmas.NearLattice` as that frozen definition, or prove `CountLemmas.NearLattice = NearLattice`
    by `rfl` once and rewrite.

  After that, the type comparison above should give raw `Expr ==` **true**. I will re-check it at the seal.
- `latticePoint` and `Mom` are already the frozen Wave A definitions in both types. No other bridge is needed.
