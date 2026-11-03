# DEGEN F53 audit (Task 14c): which ladder definition B2 should adopt

Auditor: `wt-orch` (Opus), refute-first. Date: 2026-11-03.

## Inputs

**wt-ansob.**
- `wt-scratch/degen/ERRATUM-B2-LADDER.md` (`b52f8172e303…`);
- `src/Degen/SourceLadder.lean` (`98800d95dbb1…`), which defines `SourceLadder`, `sourceMaximalLadders` and
  `sourceCountA`;
- `src/Degen/MaximalLadderDisjoint.lean` (`9db836839b74…`), which contains `chordLadder` and the disjointness
  theorem;
- `src/MoleculeDefs.lean`. This is identical to B2 snapshot cfd93a08 minus §3 (the garden molecule), and its `IsLadder`
  is the old induced predicate. I checked this by diff.

**wt-gauss-hc.** The current B2 draft `wt-scratch/waveb2/WaveB2-Molecules.lean` (`c39be9dc3954…`). Its `IsLadder`
(L305–L309) is already rewritten as **B2-CL-2** (`DESIGN.md` L325ff).

**Sources.**
- TARGET L1384–L1386 (Def `defvine`), L1498 and L1505 (coherent ladders);
- DH23 L789–L808 (Def 5.1) and L529;
- `Vines.png`, lower-right panel.

**Evidence: my own build.** I compiled the 14-module closure of `Degen.MaximalLadderDisjoint` (the DEGEN modules plus
`MoleculeDefs/Basic/Components`) myself, on my snapshot-5 `WaveBDraft.Core`.
- 0 errors and 0 `sorry`; the only warnings are unused-section-variable linter warnings.
- On top of it I ran the probe `scratch/Task14c-ladder-probe.lean` (`7a71d3041ac6…`). All results below are kernel
  checked with `[propext, Classical.choice, Quot.sound]`.

## Verdicts

| Item | Verdict |
|---|---|
| F53: the old induced B2 `IsLadder` is a draft defect | **CONFIRMED** |
| wt-ansob's `SourceLadder` is the source's definition | **PASS**: it is the reading to adopt |
| The B2-CL-2 rewrite now in `WaveB2-Molecules.lean` L305–L309 | **FAIL on one clause.** It dropped the induced clause correctly, but it also dropped "rails are **single** bonds". Fix: R1. |

## The source definition

- **TARGET L1384.** "ladders as illustrated in Figure … We require each ladder to have m+1 ≥ 2 double bonds, and that
  each pair of two parallel single bonds must have opposite directions. Define the length of a ladder to be m ≥ 1."
- **DH23 L790.** The same text, with length = (number of double bonds) − 1.
- **DH23 L529.** Ladders are the "type II chains … formed by single and double bonds".
- **The figure.** It shows vertical double rungs and horizontal single rails with arrows, the top and bottom rails
  opposite. Dashed lines mark the continuation and the end stubs ("may be inserted between pairs of parallel bonds").
  Each end atom carries one further bond, drawn dashed, and nothing constrains where that bond goes.
- **Multiplicity words are exact.** The sources distinguish single, double, triple and quadruple bonds (DH23 L582,
  L591: "quadruple bond", "triangle of three double bonds", "triple bonds").
- **TARGET L1498 and L1505.** A ladder is coherent "if any two atoms connected by a double bond are in the same
  layer", and the proof names the atoms "u_j and v_j (which are connected by a double bond)". So a ladder's double
  bonds are exactly its rungs.

### `SourceLadder` clause by clause

| Clause | Source |
|---|---|
| `1 ≤ m` | "m+1 ≥ 2 double bonds", "length m ≥ 1" |
| `Injective (Sum.elim u v)`, atoms in `M` | the figure: 2(m+1) distinct atoms |
| `bondsBetween (u j) (v j) = 2` | rungs are double bonds (a triple bond at an end rung is correctly excluded) |
| `bondsBetween (u_j, u_{j+1}) = 1`, `bondsBetween (v_j, v_{j+1}) = 1` | "parallel **single** bonds" |
| `Directed (u_j, u_{j+1}) ↔ Directed (v_{j+1}, v_j)` | "opposite directions" |
| no induced bond-count clause | the figure leaves the end atoms' further bond free |

- **No shape is missed.** Since `u_j` and `v_j` are paired by rungs, relabelling covers every rail arrangement
  (`sourceLadder_swap` and `sourceLadder_reverse`).
- **Extra bonds sit only at the ends.** An interior atom has degree 4 from its rung and two rails, and `IsMolecule`
  gives `deg = outdeg + indeg ≤ 4`. So an extra bond, including a chord between two end atoms, can only sit at end
  atoms. That is exactly the freedom the figure leaves.

### Why the reading matters downstream

The sources sum over "all the maximal ladders" and treat them as disjoint:
- DH23 `kqmainest2` L1681: q ladders plus m′ atoms in none;
- TARGET `ladderl1old` L1994, and L2081, L2133, L2172;
- TARGET L2239: "adding back at most C₀ρ̄ **disjoint** maximal ladders".

The two readings give opposite results on this point:
- **Induced reading.** The kernel counterexample is reproduced: `chordLadder_isMolecule` and
  `maximalLadders_not_pairwiseDisjoint`. The molecule has 6 atoms and 11 bonds; the 6-atom ladder fails the count
  (11 ≠ 10), so `{0,1,3,4}` and `{1,2,4,5}` are both maximal and overlap.
- **Selected reading.**
  - `sourceMaximalLadders_pairwiseDisjoint_of_degree_le_four : (∀ x ∈ M.atoms, M.deg x ≤ 4) →
    (sourceMaximalLadders M).PairwiseDisjoint id` holds with standard axioms, needing only the degree bound.
  - On the counterexample, the whole molecule is the unique maximal ladder (`chordLadder_source_full_mem_maximal`).

So the selected reading is the one under which the source's implicit disjointness is true.

## The B2-CL-2 rewrite drops single rails

The current B2 rail clause is
`∀ j : Fin m, ∃ x y, atom x = u_j ∧ atom (mate x) = u_{j+1} ∧ atom y = v_{j+1} ∧ atom (mate y) = v_j ∧ out x = out y`.
It asks only for **some** bond on each rail, so rails of multiplicity 2 are admitted.

**Kernel witness `dblRail`.**
- Atoms `u₀,u₁,v₀,v₁ = 0,1,2,3`. Rungs `0⇄2` and `1⇄3`, a **double** u-rail `0⇄1`, and a single v-rail `3→2`.
- This is an actual molecule (`dblRail_isMolecule`): out- and in-degrees ≤ 2, connected, and atom 2 has degree 3.

| Statement | Current B2-CL-2 | `SourceLadder` (and the old B2) |
|---|---|---|
| `(0,1;2,3)` is a ladder | **yes** (`dblRail_CL2`) | **no**, for every length and labelling (`dblRail_not_source`, `dblRail_not_old`) |
| maximal ladders | `univ ∈ maximalLadders` (`dblRail_univ_mem_maximalCL2`): q = 1, free atoms 0, ρ = 1 | `∅` (`dblRail_sourceMaximal_empty`): q = 0, ρ = 4 |

- **The source excludes this.** Here `0⇄1` is a double bond, so it is not a "parallel single bond". The rungs would
  also not be "the" double bonds of the ladder, which breaks L1498's coherence rule.
- **Scope.** The defect only arises at length 1. For `m ≥ 2` every rail has an interior endpoint, which is saturated by
  its rung and two rails, so degree ≤ 4 forces single rails.
- **Effect.**
  - B2's `maximalLadders`, `q`, `ρ` and the ladder product in `𝔄` differ from the source on molecules containing
    this configuration.
  - DEGEN's disjointness theorem does not cover the B2-CL-2 predicate. Its proof uses single rails
    (`unique_double_partner_of_single_rail`), and in `dblRail` the atom `u₀` has two double partners.
- **With single rails the two clauses agree.** If both rails have multiplicity 1, the dart clause (`out x = out y`) is
  equivalent to `Directed (u_j, u_{j+1}) ↔ Directed (v_{j+1}, v_j)`, because the unique bond on each rail fixes the
  darts. So restoring the multiplicity is the whole fix.
- **wt-gauss-hc's `chordLadder` probes remain valid.** The chord ladder's rails are single, and `chordLadder_CL2` and
  Degen's `chordLadder_source_full` both hold.

## Recommendations

- **R1. Adopt `SourceLadder` verbatim as B2 `IsLadder`.** This is snapshot cfd93a08's predicate with **only** the
  last conjunct (the `groupBonds` card) deleted:
  ```
  1 ≤ m ∧ Function.Injective (Sum.elim u v) ∧ (∀ j, u j ∈ M.atoms ∧ v j ∈ M.atoms) ∧
    (∀ j, M.bondsBetween (u j) (v j) = 2) ∧
    (∀ j : Fin m, M.bondsBetween (u j.castSucc) (u j.succ) = 1 ∧
      M.bondsBetween (v j.castSucc) (v j.succ) = 1 ∧
      (M.Directed (u j.castSucc) (u j.succ) ↔ M.Directed (v j.succ) (v j.castSucc)))
  ```
  Then `Degen.sourceMaximalLadders M` and B2's `M.maximalLadders` have the same body, and DEGEN's disjointness theorem
  and `sourceCountA` transfer without a bridge. A `rfl` check of these identifications should be part of the fix.
- **R2. If the dart form is preferred**, conjoin `bondsBetween … = 1` for both rails, and prove the equivalence with
  `SourceLadder` once.
- **R3.** Replace the `maximalLadders` docstring's "This is not formalized" with a pointer to
  `sourceMaximalLadders_pairwiseDisjoint_of_degree_le_four`. Its degree hypothesis follows from `IsMolecule`.
- **R4.** Add `dblRail` to `WaveB2-Molecules-probes.lean` as a molecule that the fixed predicate rejects.
- **R5. FINDINGS.**
  - F53 is confirmed; it becomes resolved once the fix lands.
  - The rail-multiplicity regression in B2-CL-2 is our own draft defect, not a source erratum. It should be logged
    with the fix; the number is for the orchestrator to assign.

## Probes

`scratch/Task14c-ladder-probe.lean` (untracked) proves:
- `chordLadder_CL2`, `dblRail_isMolecule`, `dblRail_bonds`, `dblRail_CL2`, `dblRail_univ_mem_maximalCL2`;
- `dblRail_not_source`, `dblRail_not_old`, `dblRail_sourceMaximal_empty`.

It also prints the axioms of Degen's `chordLadder_isMolecule`, `maximalLadders_not_pairwiseDisjoint`,
`chordLadder_source_full_mem_maximal` and `sourceMaximalLadders_pairwiseDisjoint_of_degree_le_four`. All are standard.

## Re-check against B2-CL-3, 2026-11-03 (late)

**Correction to the inputs above.** My `IsLadder` reading (the dart form, "L305–L309") was taken **before**
wt-gauss-hc's 23:32 rewrite. The hash I recorded for the file, `c39be9dc3954…`, was taken **after** it, so that hash
is of the B2-CL-3 file, not of the text I audited. The dart-form finding stands for the version it describes.

**Current file.**
- `wt-scratch/waveb2/WaveB2-Molecules.lean` `c39be9dc3954…` (23:32): B2-CL-3, `IsLadder` at L309–L314.
- A later docstring-only edit, `608b74282334…` (23:38:59), changes only the `maximalLadders` docstring (L326–L327).
- I compiled `c39be9dc…` and its `WaveB2-Regular.lean` (`ad72ce4be39e…`) **from source** on my snapshot-5 `WaveBDraft`
  modules: 0 errors. The only `sorry`s are the draft's registered obligations: 5 in Regular, and one in Molecules,
  `Garden.isMolecule_molecule` at L228.
- I ran `scratch/Task14c-cl3-probe.lean` (`46ff6dad8161…`) against these **actual** B2 definitions, not a copy. All
  results use `[propext, Classical.choice, Quot.sound]`.

| Check | Result |
|---|---|
| `IsLadder` body vs `Degen.SourceLadder` body | **identical** after whitespace normalization, conjunct for conjunct, including `bondsBetween … = 1` on both rails and the `Directed ↔` clause |
| The rest of the molecule definitions vs DEGEN's `MoleculeDefs` | The only code differences are the deleted `groupBonds` conjunct and the omitted §3. All other diffs are docstrings. So DEGEN's theorems are about exactly these definitions. |
| `dblRail` rejected | `dblRail_not_ladder : ∀ m u v, ¬ dblRail.IsLadder u v`, and `dblRail.maximalLadders = ∅`. `dblRail` is an actual molecule (`dblRail_isMolecule`). ✓ |
| `chordLadder`: the whole molecule is the unique maximal ladder | `chord_maximalLadders : chordLadder.maximalLadders = {univ}`. The old overlapping pair `{0,1,3,4}`, `{1,2,4,5}` is not maximal. `chordLadder_isMolecule` holds. ✓ |
| Disjointness in every molecule | `Degen.sourceMaximalLadders_pairwiseDisjoint (M) (hM : M.IsMolecule)` (`MaximalLadderDisjoint.lean` L724), standard axioms in my build (`scratch/Task14c-disjoint-axioms.lean`). Since the bodies are identical, it is a statement about B2's `maximalLadders`. |

**R1: CONFIRMED adopted.** B2-CL-3 `IsLadder` is `SourceLadder` verbatim, and the rail-multiplicity regression is
gone. R2 is moot. R4 is not yet in `WaveB2-Molecules-probes.lean` (23:34), so add `dblRail` there or in the
probe-adjacent ladder file.

**R3.** wt-gauss-hc's new `WaveB2-Ladders.lean` (B2-CL-4, 23:38:37, 737 lines, no `sorry` text) ports the theorem as
`Molecule.maximalLadders_pairwiseDisjoint (M) (hM : M.IsMolecule)`, with the same statement shape as DEGEN's, via
`_of_degree_le_four` and `deg_le_four`. I read only the statement; I have **not** compiled or audited that file.

F53 can be marked resolved once B2-CL-3 lands in the next snapshot.
