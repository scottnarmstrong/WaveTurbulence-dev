# Pre-freeze statement audit: DEGEN (wt-ansob)

Auditor: `wt-orch`, refute-first, findings only. Date: 2026-11-04 (Task 26b).

**Scope.**
- The 43 principal results of `/home/scott/wt-scratch/degen` (`src/Degen/AxiomAudit.lean`) against:
  - DH21 Lemmas 9.13 (`increF`, L2140) and 9.14 (`cutlem`, L2144);
  - DH23 §10.5 (`extradegen`, L1979–L1989);
  - TARGET `GAP.degenerate.tame` (Prop `subpro` (3), L2044);
  - the corrected `remtame` (L2152; FINDINGS F48).
- Whether they are stated about the current B2 definitions.

## Verdict

**PASS WITH ONE REQUIRED INTEGRATION ITEM (D-1).** The statements match the sources, mostly in stronger form, and the
F48 correction is implemented exactly.

- **D-1 (REQUIRED).** Like CLCN, DEGEN is built on MOLE's extraction of the stage-2/3 B2 molecules. Its
  `WaveTurbulence.Molecule.IsLadder` is the pre-CL-3 induced ladder, which clashes by name with current B2.
- **What D-1 affects.**
  - Only one result reaches the stale constant: `maximalLadders_not_pairwiseDisjoint`, the counterexample that
    motivated CL-3.
  - DEGEN's own `SourceLadder`, `sourceMaximalLadders` and `sourceCountA` are, after CL-3, **definitionally the
    current** `IsLadder`, `maximalLadders` and `countA`, up to names (§3).
- **Other findings.** Two OPTIONAL items (D-2, D-3).

## 1. Inputs and pins

**Pin.** `/home/scott/wt-scratch/degen`: 70 files copied and hashed at 03:37:44 UTC (digest `3501f35b179203e3…`).
Re-verified unchanged at 03:42 UTC.

**Packet build.** The packet's `build/`, read-only, together with MOLE's `build/`, `waveb/build` (B1 Core) and the
dev build, as in its `check.sh`. DEGEN imports MOLE's `MoleculeDefs`, `MoleculeBasic` and `MoleculeGroups` and B1
`WaveBDraft.Core`, not `WaveB2Draft`.

**The `snapshot/` file.** `snapshot/WaveB2-Molecules.lean` (`cd5568730a8c…`) is a reference snapshot only. It is not
imported, and it equals none of snap-1, snap-2 or current.

## 2. Statements against the sources

### DH21 Lemma 9.14 (`cutlem`)

Source: for a partition `X ∪ X'` with crossing bonds `ℓ₁ … ℓ_r`, `Σ ζ_j k_{ℓ_j} = c₀(c_v)` and
`|Σ ζ_j|k_{ℓ_j}|² − Γ₀| ≤ nδ⁻¹L⁻²`; if `r = 1`, `k_{ℓ₁}` is determined by `(c_v)`.

- `cut_momentum`: `Σ_{boundaryDarts S} ζ_x·kvec(x) = Σ_{v∈S} c_v`, exact, with `c₀ = Σ_S c_v`.
- `cut_energy`: `|Σ ζ_x‖kvec x‖² − Σ_S β_v| ≤ |S|·δ⁻¹L^{−2γ}`.
  - This has `|S| ≤ n`, so it is stronger.
  - It uses TARGET's restriction scale `L^{−2γ}` (B2 `IsRestricted`) and the Euclidean norm, where DH21 has
    `|·|_β`, `L⁻²`. This is the TARGET specialization.
- `single_boundary_momentum_unique`: one boundary dart means its label is equal across all decorations with the
  same `c`.
- **Faithful.**

### DH21 Lemma 9.13 (`increF`)

Source: in a bridgeless molecule, each new component after removing `Y` is joined to `Y` by at least 2 bonds, so
there are at most `h/2` new components.

- `two_mul_card_newComponents_le`: no bridge implies `2·#newComponents ≤ #boundaryDarts(Y)`.
- The per-component form is `isBridge_of_single_boundary`.
- `numComponents_eraseAtoms_eq_card_newComponents` and the induced-erasure lemmas, `isMolecule_eraseAtoms` among
  them, are the graph ingredients.
- **Faithful.**

### TARGET `subpro` (3) (`GAP.degenerate.tame`)

Source: "degenerate (≡ ZG) atom … tame if the values of `k_ℓ` for all `ℓ ↔ v` are equal, and equal a fixed value in
`(k₁,…,k_{2R})` if `d(v) < 4`. Then any degenerate/ZG atom that is not a hinge atom must be tame."

- `garden_nonhinge_degenerate_tame` (integer labels) and `garden_nonhinge_zero_gap_tame` (physical momenta):
  - for a plain garden, a decoration with fixed root values, and any atom set `H` (the hinge atoms);
  - in the support of the reduced `ε` coefficient (`reducedEps G H κ · Z ≠ 0`);
  - every degenerate atom outside `H` is `TameAt` the root values.
- `garden_nonhinge_low_degree_fixed_root`: for `d(b) < 4` the fixed value is the label of a root `j` chosen
  **before** the decoration. This is the structural "fixed value in `(k₁,…,k_{2R})`".
- The statement holds for an arbitrary excluded set `H` and for every supported decoration, which is stronger than
  the source.
- The source's claim concerns `𝕄_sb`, whose non-hinge atoms are original skeleton branching nodes with their
  original bonds, so the garden-molecule form applies.
- **Faithful.**

### Corrected `remtame` (F48)

F48 is already CONFIRMED (`audits/F48-check.md`).

**(i) Single crossing bond.**
- `countE_conditioned_erase_single_crossing_exists_post`: `v` tame (`ConstantAt`), and a component `S` whose
  boundary is a single dart touching `v`. Then `∃ q` with `𝔈(M) ≤ 𝔈(M∖v; labels at v fixed to q)`.
- With `conditioned_new_tame_neighbor_fixed` and the `sourceCountA_…_single_crossing` versions, this is the
  corrected "exactly one **bond** connecting the component to `v`" branch.
- The low-degree branch, `d(v) < 4` with fixed root values, is
  `gardenDegenerateSupport_countE_erase_low_degree` / `garden_sourceCountA_erase_low_degree_exists`.

**(ii) The negation.** `circuitRank_erase_four_le_sub_two`: for a connected `M` with `d(v) = 4` and **no** new
component with exactly one boundary dart, `χ(M∖v) ≤ χ(M) − 2`. This is the consistently negated criterion.

**Faithful to F48's adopted correction.** The counterexample `RemtameCounterexample` is retained as evidence.

### DH23 §10.5

**(4) The degenerate `ε`-atom of degree 4.**
- `Δχ ≤ −2`: `sourceCountA_conditioned_erase_strong_exists` gives
  `𝔄(M) ≤ 2·3^d(4/η)⁴·L^{−d+2γ+η}·𝔄(M∖v; q, inherited scales)` for some `q`.
  - The source has `𝔇 ≲ L^{−d+2γ+η}`.
  - My recomputation: `L^d` choices for the common label times the normalization change
    `L^{−2(d−γ)}(C₁^{−1}δ^{1/2})²` gives `L^{−d+2γ}B²` with `B ≤ 1`, and the ladder-product change costs the
    `(4/η)⁴L^η`.
  - **Faithful**, with the constant made explicit.
- `Δχ ≥ −1`: `garden_sourceCountA_erase_weak_four_exists` (and the conditioned version) gives
  `𝔄(M) ≤ 𝔄(M∖v; q)` for some `q`, with the gap restrictions transported.
  - The source fixes `k` by the bridge and replaces the labels by an arbitrary non-degenerate configuration. Lean
    removes the atom with the bridge-fixed label instead, with no loss.
  - **A valid and stronger route**; see D-3.

**(2) A degree-2 degenerate atom.**
- `sourceCountA_conditioned_erase_degree_two_prescribed_le`: connected, all degrees even, `d(z) = 2`, constant and
  prescribed labels at `z`. Then `𝔄(M) ≤ L^{−d+γ}·C₁^{−1}δ^{1/2}·𝔄(M∖z)`.
- The source has `𝔇 ≲ L^{−d+γ+η}`, so the Lean bound is stronger.
- "All degrees even" is the source's couple setting: one degree-2 atom in place of two degree-3 atoms, every other
  atom of degree 4. It guarantees `Δχ = −1`.
- **Faithful.**

**(1) Regular couples, trees and vines.** Out of scope here, as the packet states: these remainders belong to the
analytic packets.

**(3) The cutting process.** Covered by the hypotheses: the conditioned admissibility predicates are carried by
literal conjunction (`GardenScaledDegenerateSupport … Extra`), so no source restriction is released.

## 3. Are the statements about the current B2 definitions?

**Method.** The closure comparison of `LINKS-prefreeze.md` §3, by name, from the 43 principal results.

**Result.** 157 project constants in the closure; 81 exist in current B1/B2 (B1 Core 40, MOLE's `MoleculeDefs` 36,
`GardenMoleculeDefs` 3, `Mom`, `latticePoint`).
- **80 identical.**
- **1 differs: `Molecule.IsLadder`.** It is the stage-2/3 induced ladder; current B2 has `IsLadder = SourceLadder`
  (CL-3).
- `Garden.pair_unmarked` occurs only inside an erased proof (CL-12 moved it to the probes). It carries no meaning.

**Which results reach the stale `IsLadder`?** A per-root reachability check finds exactly one:
`maximalLadders_not_pairwiseDisjoint`. That is the induced-ladder counterexample (ERRATUM-B2-LADDER), the defect
CL-3 removed. Under current B2 the maximal ladders of every molecule (`IsMolecule`) are pairwise disjoint
(`maximalLadders_pairwiseDisjoint`, `WaveB2-Ladders.lean`), so the statement does not transfer. It is historical
evidence about the superseded definition and must not be ported under B2's names.

**DEGEN's source ladders against current B2.** Normalized definitions were compared across the two environments,
with DEGEN's names mapped to B2's.
- `Degen.SourceLadder` ≡ current `Molecule.IsLadder`.
- `Degen.SourceLadderSet` ≡ current `IsLadderSet`.
- `Degen.sourceMaximalLadders` ≡ current `maximalLadders`.
- `Degen.sourceCountA` ≡ current `countA`, after one unfolding of `sourceLadderProduct`
  (`∏_{S ∈ sourceMaximalLadders} ladderWeight^{ladderLength}`) and alpha-renaming `C1`/`C₁`.

The handoff's "no equality to the unchanged induced B2 `countA` is claimed" is therefore outdated. B2 has since
adopted the source ladders, and the equality now holds definitionally.

## 4. Checks

- **Axioms.** I re-ran `src/Degen/AxiomAudit.lean` against the packet build: 43 declarations, all
  `[propext, Classical.choice, Quot.sound]`.
- **Exports.** All 43 statements printed in the packet environment.

## 5. Findings

**D-1 (REQUIRED for integration, not a fidelity defect). Re-point DEGEN to the current B2.**
- Import the frozen B2 `Molecules` instead of MOLE's extraction.
- Replace `Degen.SourceLadder`, `SourceLadderSet`, `sourceMaximalLadders`, `sourceLadderProduct` and `sourceCountA` by
  B2's `IsLadder`, `IsLadderSet`, `maximalLadders` and `countA`, with `rfl` / one-unfold bridges (§3).
- Drop or rename `maximalLadders_not_pairwiseDisjoint` and `chordLadder`. They speak about the superseded definition.
- Same mechanism as CLCN C-1.

**D-2 (OPTIONAL). The tame predicate and B2-CL-15.**
- DEGEN's `TameAt M roots labels b` (all incident labels equal; if `d(b) < 4`, equal to some root label) is the
  integer-label form of B2's drafted `Molecule.IsTame L w kFix κ v`, with `kFix` the image of the `2R` root vectors.
- This agrees with CL-15's `kFix.card ≤ 2R` and supports the G8 question (Q6). A bridge lemma
  `TameAt ⇒ IsTame (kFix := image of the roots)` would connect DEGEN's GAP to B2.3's `DecorationHyp.epsLGTame`.

**D-3 (OPTIONAL). The DH23 §10.5(4) weak branch route.**
- The source keeps the atom and replaces its labels by "arbitrary non-degenerate configurations". DEGEN deletes the
  atom with a bridge-fixed label.
- Both give a lossless reduction. The B2.3 / G8 consumer should cite DEGEN's form explicitly, since it changes the
  post-operation molecule (atom removed instead of relabelled).

**Notes (no action).**
- F48 is implemented consistently in both branches.
- No other source defect was claimed, and I found none.
