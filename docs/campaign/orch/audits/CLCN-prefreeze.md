# Pre-freeze statement audit: CLCN (packet M3, wt-nt)

Auditor: `wt-orch`, refute-first, findings only. Date: 2026-11-04 (Task 24b).

**Scope.**
- The 16 principal exports of `/home/scott/wt-scratch/clcn` against TARGET:
  - `block_clcn` (L1345–L1366);
  - `cnblock` (L1367–L1376);
  - `blockchainprop` (L1379–L1382);
  - with the F57 connected-block convention.
- Whether they are stated about the current B2 definitions.

## Verdict

**PASS WITH ONE REQUIRED INTEGRATION ITEM (C-1).** The statements match the sources, in places in a stronger form.

- **C-1 (REQUIRED).** They are stated over the **stage-2/3** B2 molecule definitions, through MOLE's extraction.
  Against current B2, exactly one constant differs: `Molecule.IsBlock`, which CL-5 made connected. The difference is
  bridged by the existing `isBlock_iff_mole`.
- **Consequence.** Because the extraction re-declares B2's names (`WaveTurbulence.Molecule.IsBlock`, …), the packet
  cannot be loaded beside the current or frozen B2 without re-pointing.
- **Other findings.** Two OPTIONAL items (C-2, C-3).

## 1. Inputs and pins

**Pin.** `/home/scott/wt-scratch/clcn`: 200 files hashed at 03:13:47 UTC (digest `f160c990f7502595…`). Re-verified
unchanged at 03:26 UTC.

**Packet build.** The packet's `build/` together with the accepted MOLE `build/` (`/home/scott/wt-scratch/mole`),
both read-only, as in the packet's `check.sh`.

**Inputs** (packet `DRAFTS.md`):
- B1 Core: snapshot 5, through MOLE's copy; byte-identical to snapshot 6.
- B2 molecules and `Garden.molecule`: MOLE's extraction of `waveb2-snap-1/stage23`.
- DEGEN: 5 byte-identical copies.
- COMB-CORE: 5 modules rebuilt locally.

## 2. Statements against the sources

Every statement below was printed with `#check @…` / `#print` in the packet environment.

**Representation of a block: `GardenBlockSegment G`.** The fields are `atoms`, `leftJoint`, `rightJoint`,
`block : G.molecule.IsBlock atoms leftJoint rightJoint` (the stage-2/3 degree-only predicate) and
`connected : Mole.GroupConnected G.molecule atoms`. This is a block in the F57 convention.

### `block_clcn` (1): the CL/CN dichotomy

`block_geometric_dichotomy G B` gives `CL(left, right) ∨ CL(right, left) ∨ CN(left, right)`, as `Nonempty` of the
geometric data. `geometric_alternatives_exclusive` gives the three pairwise exclusions. Together these are "up to
symmetry, exactly one". The garden width is arbitrary, which is stronger than TARGET's `2R`.

**`CLGeometricData G S upper lower`** checked against TARGET (a). Here `a.IsDesc a'` means `a'` is a descendant of `a`.

| Source (a) | Field |
|---|---|
| (i) `𝔲₁₁ = upper.child excluded` has the sign of `𝔲₁` | `excluded_sign` |
| (i) `𝔲₂₁` and `𝔲₂₂` have signs `+` and `−` | `positive_sign = 1`, `negative_sign = −1`, and `distinct` |
| (ii) `𝔲₂` is a descendant of `𝔲₁` | `lower_descendant : upper.IsDesc lower` |
| (ii) `𝔲₂` is not a descendant of `𝔲₁₁` | `lower_not_excluded` |
| `𝒢[𝔹]` = descendants of `𝔲₁` not of `𝔲₁₁, 𝔲₂₁, 𝔲₂₂` | `realization` |
| (iii) its leaves are completely paired | `complete_pairing` (unmarked, partner inside) |

- `realization` is stronger than the source: it identifies `𝒢[𝔹]` with the block's intrinsic incidence realization.
- An extra conclusion, `parentPattern`, records which joint has its parent inside `S`.

**`CNGeometricData G S a b`** checked against TARGET (b).

| Source (b) | Field |
|---|---|
| (i) the excluded children have the signs of their parents | `excludedA_sign`, `excludedB_sign` |
| (ii) `𝔲₂` is a descendant of `𝔲₁₁` or not a descendant of `𝔲₁`, and symmetrically | `separatedA`, `separatedB` |
| (iii) realization and complete pairing | `realization`, `complete_pairing` |
| (extra) neither joint's parent is inside `S` | `parentPattern` |

**Faithful.**

### `block_clcn` (2): splicing

- `clSpliceMoleculeIso`, given `hB : G.molecule.IsBlock S a b` and `hCL : CLParentPattern G S a b`, gives
  `GardenMoleculeIso (clSplicedGarden hB hCL) (contractGroup G.molecule S)`.
- It holds for the degree-only block with a CL parent pattern, without the connectedness hypothesis (stronger).
- The spliced garden is constructed explicitly (handoff: the changed forest, retained-leaf transport, inherited
  marks and pairing, signs).
- `contractGroup` merges the block's atoms into one and **deletes** the internal bonds. TARGET says "merging all the
  atoms in `𝔹` … into one single atom". After splicing, `𝔲₁` keeps only its three new children and its parent, so the
  internal bonds disappear. Deleting them, rather than keeping loops, is the right reading.
- I did not re-derive the child positions of `𝔲₂₁, 𝔲₂₂` ("determined by their signs") inside `clSplicedGarden`. The
  molecule isomorphism, which is the consumed fact, does not depend on them.
- **Faithful.**

### `cnblock`

`cnblock_component_bound`, for `G : Garden (2R)`, `G.IsPlain`, `1 ≤ R`, and `F : Finset (GardenBlockSegment G)`
pairwise atom-disjoint with every `B ∈ F` satisfying `IsCNOrRootCL G B`:
`(removeBlockFamily G F).numComponents ≤ 2R ∧ (= 2R → ∃ v ∈ atoms, deg v = 0)`.
- **`IsCNOrRootCL`.** The CN parent pattern, or the CL pattern `(left, right)` with
  `deg left + deg right ≤ 6`. This is TARGET's root block: total joint degree at most 6. See C-2 on the orientation.
- **`removeBlockFamily`.** Keeps the joints, removes every other atom of the family, and removes every internal
  bond. TARGET: "removing all non-joint atoms and all bonds `ℓ ∈ 𝔹`".
- **The conclusion.** "At most `2R` connected components; with exactly `2R`, one is an isolated atom" (degree 0).
- **`IsPlain`** is TARGET's ordinary garden (all leaves paired). `1 ≤ R` only excludes the empty forest, where the
  isolated-atom clause would be vacuous.
- `cnblock_component_excess_bound` restates the bound as `numComponents − 1 ≤ 2R − 1`, the form used in excessprop1 (3).
- **Faithful.** The proof differs from TARGET's (a deficit-parity argument), which is allowed.

### `blockchainprop`

`B` is a block or hyper-block concatenated from `m ≥ 2` blocks.

**(1) At most one `𝔹_j` is CN.**
- `chain_at_most_one_cn`: any `List.IsChain SegmentFollows` of segments has at most one CN segment.
- `SegmentFollows`: consecutive segments share exactly their common joint.
- No hypothesis on the union and none on `m`, so this covers blocks and hyper-blocks and is stronger than TARGET.
- `hyper_cannot_concatenate` separately proves that a hyper-block cannot be extended.

**(2) If `𝔹` is a block and all `𝔹_j` are CL, then `𝔹` is CL.**
- `chain_all_cl_parent_pattern` assumes:
  - a chain of segments `A :: rest`, each with a CL parent pattern in either orientation;
  - every segment contained in `whole`;
  - `G.molecule.IsBlock whole A.left last.right`.

  It concludes a CL parent pattern for `whole`.
- See C-3: the conclusion is the parent pattern, and the CL *type* follows through the dichotomy.

**(3) One CN `𝔹_j`: after splicing all other (CL) blocks, `𝔹` becomes that single (CN) block.**
- `chain_with_cn_parent_pattern`: `whole` then has the CN parent pattern.
- `MarkedGardenChain.splicing_leaves_cn` / `splicedFocusIso`: the molecule obtained from the chain's atom carrier
  is a `DirectedMoleculeIso` to `induced G.molecule focus.atoms`. That molecule is the quotient by every CL
  ingredient's identifications, keeping the old half-edges outside their internal bonds.
- This represents the result at the molecule level, by simultaneous contraction (C-3).

**Faithful** at the level the consumers use: molecules and parent patterns.

## 3. Are the statements about the current B2 definitions?

**Method.** The closure comparison of `LINKS-prefreeze.md` §3, from the 16 principal statements of
`validation/AxiomAudit.lean`.
- MOLE's extraction keeps B2's names, so I compared by name: every project constant in the closure that also exists
  in the current B1/B2 build.

**Result.** 228 project constants in the closure.
- 169 are packet-local: `Mole.*`, `Comb.*`, or `Degen.*`.
- 59 exist in current B1/B2. Of these, **58 are identical** (all B1 Core constants used, `Molecule` and its fields,
  `dartsAt`, `deg`, `degIn`/`inIn`/`outIn`, `InGroup`, `numComponents`, `SameComponent`, `Adj`, `Garden.molecule`,
  `GNode.parent`, `GardenDart`, …).
- **1 differs: `WaveTurbulence.Molecule.IsBlock`.** The packet's version is the stage-2/3 one, without CL-5's last
  conjunct `GroupConnected S`.
- `Garden.pair_unmarked` occurs only inside an erased proof. CL-12 moved it to the probes. It carries no meaning.

**Bridge.** The current probe `isBlock_iff_mole` states
`M.IsBlock S j₁ j₂ ↔ IsBlockDeg M S j₁ j₂ ∧ moleGroupConnected M S`. Here `IsBlockDeg` is the stage-2/3 body (it
matches the packet's `IsBlock`), and `moleGroupConnected` is MOLE's `GroupConnected`. So:
- **`GardenBlockSegment`** (old `IsBlock` ∧ MOLE `GroupConnected`) is exactly the current `IsBlock`.
- **Theorems with an old-`IsBlock` hypothesis** (`clSpliceMoleculeIso`, `chain_all_cl_parent_pattern`,
  `chain_with_cn_parent_pattern`) apply to current blocks, because current `IsBlock` implies the old body.

## 4. Checks

- **Axioms.** I re-ran `validation/AxiomAudit.lean` against `clcn/build:mole/build`: 16 declarations, all
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.
- **Exports.** All printed statements elaborated in the packet environment.

## 5. Findings

**C-1 (REQUIRED for integration, not a fidelity defect). Re-point the packet to the current B2.**
- The packet, and MOLE's extraction under it, declares `WaveTurbulence.Molecule.IsBlock` with the pre-CL-5 body,
  under the same name as the current or frozen B2 declaration. It therefore cannot be imported together with B2.
- At integration:
  - import the frozen B2 `Molecules` instead of the extraction;
  - turn `GardenBlockSegment.block` into the current `IsBlock`, so the `connected` field becomes redundant (derive it
    from `IsBlock`, or keep it and supply it from `isBlock_iff_mole`);
  - re-check the proofs that destructure `IsBlock`, since its conjunct count changes from 9 to 10.
- The statements' meaning is unchanged (§3). The work is mechanical, and the same applies to MOLE itself.

**C-2 (OPTIONAL). The CL orientation in `IsCNOrRootCL`.**
- A root (CL) block counts only with `leftJoint` as the upper joint: `CLParentPattern … left right`.
- Every block can be presented in that orientation, by swapping the joints (`block_swap_joints`). The set in
  `cnblock_component_bound` is chosen by the consumer, so nothing is lost.
- A docstring remark would prevent a consumer from presenting a root CL block in the other order and silently
  falling outside the hypothesis.

**C-3 (OPTIONAL). `blockchainprop` (2)/(3) give parent patterns and a molecule-level splice.**
- *For (2):* the CL type of `whole` follows from its CL parent pattern by `block_geometric_dichotomy` and
  `geometric_alternatives_exclusive`. This needs `whole` as a `GardenBlockSegment`. With the current `IsBlock`
  (connected) that is immediate (C-1). With the old `IsBlock` hypothesis it needs the union to be connected, which
  holds for a concatenation.
- *For (3):* TARGET's "doing splicing at all other (CL) blocks" is iterated garden splicing (`block_clcn` (2)). The
  packet proves the simultaneous molecule quotient instead. The two agree because each single splice's molecule is
  the contraction (`clSpliceMoleculeIso`), but iterating contractions is not stated as a lemma.
- Two short corollaries — "CL pattern + segment ⇒ CL type" and "iterated single splices = simultaneous quotient" —
  would let consumers quote the source wording directly. No current consumer needs the garden-level iterate.

**Notes (no action).**
- F57: `GardenBlockSegment` carries connectedness, and every theorem quantifying over blocks as source objects uses
  it.
- The `cnblock` proof route differs from TARGET's (deficit parity instead of the generalized-forest enumeration).
- No source erratum was claimed, and I found none.
