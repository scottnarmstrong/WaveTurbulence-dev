# MOLE pre-freeze audit (Task 17): F57, F58, F59, and the B2 definitions behind MOLE's exports

Auditor: `wt-orch` (Opus), refute-first. Date: 2026-11-04. **Findings only: nothing under `wt-scratch/mole` was
edited.**

## Inputs (copied and hashed at first read)

**wt-nt's MOLE scratch** (`/home/scott/wt-scratch/mole`), copied at 00:14:27 UTC:
- `HANDOFF.md` `4a37910b8c02…`;
- `src/MoleculeBlockEdgeCase.lean` `fa4f40583d41…`;
- `src/MoleculeDefs.lean` `ca94ccd55f9b…`;
- `src/GardenMoleculeDefs.lean` `21eda53f8d39…`;
- `src/MoleculeCountingQuantities.lean` `98b342f3dd36…`;
- `src/MoleculeCutOperation.lean` `66d8c19b36d3…`;
- all 81 modules of `validation/modules.txt`, including `src/WaveBDraft/Core.lean` (= the snapshot-5 Core, and also
  the snapshot-6 Core).

**MOLE's pins.** B2 is `waveb2-snap-1/stage23`, with Molecules `cfd93a08…`. B1 is `waveb-snap-5`.

**Live B2** (`/home/scott/wt-scratch/waveb2`), copied at 00:14:46 UTC:
- `WaveB2-Molecules.lean` `608b74282334…`;
- `WaveB2-Regular.lean` `ad72ce4be39e…`;
- `WaveB2-Statements.lean` `e50aaa9418da…`;
- `WaveB2-Ladders.lean` `1e5458ba0e9b…`.

**Sources.**
- TARGET `defblock` (L1328–L1331), `disjointlem` (L1337–L1341), `propcplmol` (L1303–L1306), (defdev) (L2135);
- DH23 `Revision_Submit.tex` Def 4.10 (L712–L716).

**Evidence: my own builds.**
- **MOLE.** I rebuilt all 81 modules from my copy, one `lake env lean` at a time: 0 errors, 0 warnings, 0 `sorry`.
  MOLE's own `validation/Axioms.lean`, run on my build, prints 48 of 48 with only `propext`, `Classical.choice`,
  `Quot.sound`.
- **Live B2.** I compiled the live `WaveB2-Molecules.lean` from source on snapshot 5. The only `sorry` is the draft
  obligation `Garden.isMolecule_molecule`.

## Verdicts

| Item | Verdict |
|---|---|
| (i) F57 counterexample against TARGET `defblock` / DH23 Def 4.10 | **CONFIRMED**. The same molecule also falsifies TARGET `disjointlem` / DH23 Lemma 4.11 as literally stated (new, kernel-checked). |
| (i) The connectedness clause for B2 | **Recommend R1–R3 below:** connected atomic group for blocks; connected adjoint for hyper-blocks. |
| (ii) F58 as a B2 statement item | The B2 obligation is already correct (positive order). A **docstring fix** is needed, plus a rule for any future count statement (R4). |
| (ii) F59 as a B2 statement item | **Docstring false** in three ℝ≥0∞ cases. Recommend R5. |
| (iii) MOLE's exports concern the unchanged B2 definitions | **Yes**, up to the CL-3 `IsLadder` change. The 3 affected exports re-check under the live definition. |

## (i) F57: blocks need connectedness

**The example** (`MoleculeBlockEdgeCase`, verified in my build).
- `disconnectedBlocks`: atoms `0..4`; loops at `0`, `2`, `4`; opposite double bonds `1⇄2` and `3⇄4`.
- It satisfies B2's `IsMolecule`: in/out-degrees ≤ 2, and every component has an atom of degree < 4.

**Against the source text.**
- `A = {0,1,2}` is a block in TARGET's sense: the joints are `0` (its loop gives out 1, in 1) and `1` (out 1, in 1
  through `1⇄2`); atom `2` has degree 4. `B = {0,3,4}` likewise.
- The two share exactly the joint `0` and no other atom.
- TARGET L1330 / DH23 L716 assert that their union is "either a block or a hyper-block". It is neither: atoms `0`, `1`
  and `3` all have degree 2 in the union (`disconnectedBlocks_union_not_block`, `…_not_hyperBlock`).
- The cause: the shared joint's two incidences are the **same** loop, counted in both A and B.

**It also falsifies `disjointlem` (DH23 Lemma 4.11) as stated.**
- `scratch/Task17-disjointlem.lean` (`06a42419bc8d…`) proves that the same `A` and `B` satisfy **every** premise:
  - `A ⊄ B`, `B ⊄ A`, `A ∩ B = {0}`;
  - (i) the interiors `{2}` and `{4}` are connected;
  - (ii)/(iii) deleting the interior atom leaves exactly two components, `{0}` and `{1}` (respectively `{0}` and `{3}`),
    containing the respective joints.
- Exactly one joint is common, so only alternative (b), "can be concatenated", can apply, and it fails.
- Axioms: `[propext, Classical.choice, Quot.sound]`.
- So conditions (i)–(iii) do **not** imply that a block is connected: `A` is disconnected, with `0` isolated together
  with its loop. MOLE's `molecule_overlap_classification` needs the extra connectedness (its `BlockRealization`).
- **F57's scope should be extended to `disjointlem` (L1337–L1341).**

**Why connectedness is the right correction.**
- DH23's `BlockConc.png` draws each block as one blob, with both bonds of each joint entering it. There are no joint
  loops, and the shared joint has two bonds into each blob. A connected block cannot carry a loop at a joint: the loop
  would use both of the joint's incidences and isolate it.
- With connected blocks, the shared joint gets 2+2 distinct incidences. Interior atoms are saturated, so only the two
  outer joints can be joined, and a doubled join is excluded by non-saturation.
- MOLE proves the resulting classification (`molecule_overlap_classification`, `blocks_concatenate_connected`).
- "No loop at a joint" alone would rescue the concatenation sentence, but not MOLE's proof of Lemma 4.11 (c). I
  recommend connectedness.

**R1. Add to `WaveB2-Molecules.lean` §2, and add the conjunct to `IsBlock`:**

```lean
/-- The atomic group `S` is connected: any two of its atoms are joined by a path of bonds of `S`
(T Def `defblock`, figures; F57). -/
def GroupConnected (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S,
    Relation.EqvGen (fun a b => ∃ x, M.InGroup S x ∧ M.atom x = a ∧ M.atom (M.mate x) = b) u v

def IsBlock (S : Finset V) (j₁ j₂ : V) : Prop :=
  S ⊆ M.atoms ∧ j₁ ∈ S ∧ j₂ ∈ S ∧ j₁ ≠ j₂ ∧
    M.outIn S j₁ = 1 ∧ M.inIn S j₁ = 1 ∧ M.outIn S j₂ = 1 ∧ M.inIn S j₂ = 1 ∧
    (∀ v ∈ S, v ≠ j₁ → v ≠ j₂ → M.degIn S v = 4) ∧ M.GroupConnected S
```

- The relation is exactly the adjacency of MOLE's `induced M S` (darts of `S`). MOLE's `GroupConnected` additionally
  asks `S.Nonempty`, which `j₁ ∈ S` supplies. A one-line bridge therefore transfers MOLE's theorems.
- `GroupConnected` is undecidable as written. `IsBlock`'s `Decidable` instance must then be dropped, or computed
  through `SimpleGraph`/finite reachability. No B2 statement relies on deciding `IsBlock`.
- **Effect on `IsVine`: none.** Its template isomorphism already forces `S` to be connected, because every expanded
  vine template is connected.

**R2. If B2 needs hyper-blocks** (for `disjointlem`, HV and HVC), define the hyper-block through its **connected
adjoint**, as MOLE does: a bond `e` with `M.ends e = s(j₁,j₂)` such that `S` is an `IsBlock` with joints `j₁, j₂` in
`M` with `e` removed.
- Connectedness of the hyper-block itself is not enough: the adjoint may split into two pieces, one at each joint.
- Adopt MOLE's `eraseBond`/`IsHyperBlock` verbatim, together with `GroupConnected` of the adjoint.

**R3. Log the `disjointlem` extension in FINDINGS (F57 scope).** Every frozen statement that takes "`𝔹` is a block"
as a premise should use the connected `IsBlock`.

## (ii) F58 and F59 as B2 statement items

**F58 (`propcplmol`).**
- B2's only `propcplmol` statement is `Garden.isMolecule_molecule`, with `IsPlain`, couple-or-irreducible, and
  `1 ≤ G.order`. It is therefore already restricted to positive order.
- It is stronger in hypotheses than needed: MOLE proves `garden_isMolecule : ∀ G, G.molecule.IsMolecule` with no
  hypothesis at all.
- **The docstring is wrong:** it says "connected", but `IsMolecule` does not assert connectedness.
- **R4.**
  - Correct the docstring.
  - If B2 freezes the count and rank content of `propcplmol` (n atoms; `E = 2n−1` or `E = 2n−R`; `χ = n` or
    `χ = n−R+1`; connectedness; the couple degree classification), carry `1 ≤ G.order` in **both** sentences.
  - MOLE's `irreducible_garden_bonds_add_width_half`, `irreducible_garden_circuitRank`,
    `irreducible_garden_molecule_connected`, `plain_couple_degree_cases` and `plain_couple_circuitRank` already have
    exactly that form. `trivialPair_bond_count_counterexample` shows the qualifier is needed.

**F59 (deviation).**
- `deviation Apre Apos := Apre / Apos` in `ℝ≥0∞`. Its docstring, "the least ℐ with `𝔄_pre ≤ ℐ 𝔄_pos`", is false in
  three cases:
  - `Apos = 0 < Apre`: no ℐ works, since `⊤·0 = 0`, yet the value is `⊤` (MOLE's
    `deviation_zero_denominator_counterexample`);
  - `Apos = ⊤`, `Apre ≠ 0`: the value is `0`, but the infimum is not attained;
  - `(⊤, ⊤)`: the value is `0`.
- `deviation` occurs in **no** B2 statement, only in its definition. Its consumers are the per-operation bounds of
  TARGET L2135ff.
- **R5.**
  - Preferred: state those bounds literally as (defdev), `𝔄_pre ≤ ℐ · 𝔄_pos`, and drop `deviation`.
  - Alternatively, correct the docstring and freeze the characterization with its exact side conditions:
    `deviation_le_iff_of_zero_compatible (Apos ≠ ⊤) (Apos = 0 → Apre = 0)`.
  - MOLE supplies both side conditions for cuts (`countA_ne_top` for `L > 0`; the cut preserves `𝔄 = 0`).

## (iii) MOLE's exports and the live B2 definitions

**Elaborated comparison** (`scratch/Task17-mole-dump.lean` `71ef1f9b5410…`, `scratch/Task17-b2live-dump.lean`
`aae817679226…`).
- MOLE's `MoleculeDefs` + `GardenMoleculeDefs` have 210 constants; the live `WaveB2Draft.Molecules` has 211.
- **209 are common, and all agree in type and value** after hygiene normalization, **except
  `WaveTurbulence.Molecule.IsLadder`**. That is the CL-3 change: the induced `groupBonds` clause was removed (Task 14c).
- The remaining two differences are expected:
  - live-only: `Garden.isMolecule_molecule`, the draft obligation that MOLE deliberately does not import;
  - a module-private auxiliary `IsLadderGap._proof_1`, whose name differs only by module.

**Exports that reach the changed definition.** I computed this by closure over definition bodies. Of the 48 audited
exports, exactly **three** reach `IsLadder`, all through `countA → maximalLadders → IsLadderSet`:
`countA_ne_top`, `cut_deviation_mul_eq`, `cut_deviation_le_iff`.

**Swap test.**
- I replaced `IsLadder` in a copy of MOLE's `MoleculeDefs` with the live B2 body; it is textually identical to
  `SourceLadder`.
- I rebuilt the 14-module closure of `MoleculeCutOperation` and `MoleculeCountingQuantities`: 0 errors.
- All three exports compile unchanged, with `[propext, Classical.choice, Quot.sound]`. Their proofs treat the ladder
  product abstractly.
- The other 45 exports do not reach any changed definition.

**Conclusion.**
- Every MOLE export is a statement about the current B2 definitions. Rebasing MOLE's imports onto the frozen modules
  is mechanical; only `IsLadder` changes, and it has been checked.
- B1: MOLE's Core is the snapshot-5 Core, byte-identical to the snapshot-6 Core.
- **After R1, MOLE's `BlockRealization`, `GroupConnected`, `IsHyperBlock`, `InteriorDeletionProperty` and
  `TwoComponents` must be stated over (or bridged to) B2's new definitions** before MOLE's overlap results serve
  frozen anchors.

## Probes (untracked, `scratch/`)

- `Task17-disjointlem.lean`;
- `Task17-mole-dump.lean`;
- `Task17-b2live-dump.lean`.

The swap build is in my scratchpad (`mole-swap/`).
