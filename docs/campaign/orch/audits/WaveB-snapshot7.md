# Delta audit: Wave B snapshot 7 (F68), against snapshot 6

Auditor: `wt-orch`, refute-first. Date: 2026-11-04 (Task 28).

**Scope.**
- The one change of `/home/scott/wt-scratch/waveb-snap-7` (`CHANGES-7.md`, DESIGN CL-21, FINDINGS F68).
- Whether `PatValid`'s new argument changes any other frozen meaning.

## Verdict

**PASS.**
- The delta is exactly the declared change.
- It is faithful to TARGET L2331.
- Among the 423 elaborated constants of the five freeze files, exactly two change: `LayeredGarden.PatValid` and
  `flowerSum`.
- Their only frozen dependents are `flowerSum` and B1.12 `layergardenFlower`. B1.12's statement text and elaborated
  type are unchanged; its meaning changes only through `flowerSum`, as intended.

## 1. Inputs

**Snapshot 7.** `SHA256SUMS` verifies. I copied it and re-verified the copy (digest of `SHA256SUMS`
`a0445482719a…`) at 04:52 UTC.

**Snapshot 6.** My verified copy from Task 18, the basis of `WaveB-snapshot6.md`.

**Files.**
- Changed: `WaveB1-Flower.lean`, `WaveB1-Flower-probes.lean`, `DESIGN.md` and `FREEZE-LIST.md`.
- Byte-identical: `WaveB1-Core.lean`, `-System`, `-Statements`, `-Sumint`, `-Lemmas`, `-Bridges`, the other probes and
  `FreezeList.lean`.
- `CHANGES-6.md` was replaced by `CHANGES-7.md`.

## 2. The textual delta

The `diff` of `WaveB1-Flower.lean` against snapshot 6:
- `PatValid` gains the argument `(p : ℕ)` before `(j : Fin w)`;
- its `dChild i` clause gains the conjunct `∧ LG.layer b.toNode = p`;
- its docstring gains a four-line paragraph citing F68 and T L2331;
- `flowerSum`'s validity conjunct becomes `∀ j, LG.PatValid p j (pat j)`, where `p` is `flowerSum`'s own argument.

The probe file changes only at the second call site (`finite_flowerSum_support`). Nothing else differs.

## 3. Fidelity of the new conjunct (TARGET L2331, F68)

TARGET (L2331, item (7) of the proof of (newnormn)): "the `∂_s` derivative introduces an extra `δ(t_𝔫 − s)`
factor with `𝔫` being the parent or a non-flower child of `𝔣^pr`", applied after "replacing `𝒥̃_𝒯` by `𝒥^†_𝒯`"
(item (5)).

- `𝒥^†_𝒯` is the single flower-tree kernel. A node `𝔫` carries a time variable `t_𝔫` only if it is a branching node
  of the flower tree.
- Under `IsCanonH (p+1)`, the flower tree's branching nodes are its layer-`p` branching nodes. The children of
  `𝔣^pr` in lower layers are roots of attached gardens, which are leaves of the flower tree and have no time variable.
- So a `dChild` designation must be a layer-`p` branching node. `b : GBranch` already gives "branching"; the new
  conjunct gives "layer `p`".
- `dParent` needs no change: `𝔣^pr`'s parent lies on the stem, which is in layer `p`.

**Faithful.** F68's description of the snapshot-6 defect is confirmed: there, `flowerSum (dChild i)` admitted gardens
whose designated child is an attached-garden root, which the moment expansion never produces.

## 4. No other frozen meaning changes

**My own snapshot-7 build.**
- I took my snapshot-6 build and rebuilt `Flower` and `FlowerProbes` from snapshot 7, in the dev environment plus
  my Wave A glue: 0 errors.
- The only `sorry` is B1.12's anchor. The probes are clean.

**Elaborated comparison.** I dumped every constant of `WaveBDraft.{Core, System, Statements, Sumint, Flower}`
(matchers and auxiliaries delta-expanded, proofs erased), as in Task 22, for both snapshots.
- 423 constants on each side; none only on one side.
- **Exactly 2 differ:**
  - `LayeredGarden.PatValid`: the type gains `Nat` after `LG`; the body gains the conjunct;
  - `flowerSum`: its body passes `p` to `PatValid`.
- Everything else is identical, including `layergardenFlower`'s type and `fixPat`.

**Freeze lists.** `FreezeList.lean` on the snapshot-7 build gives the same 226 rows (names, kinds, modules). The only
`uses` change is `PatValid` gaining `GBranch.toNode`, through the new conjunct.

**Dependents.** The transitive dependents of `PatValid` in the freeze set are exactly `flowerSum` and B1.12
`layergardenFlower`.
- `fixedpoint`, the X3 consumer named in F68, does not depend on `flowerSum`.
- `PatValid`'s `plain`, `dRoot` and `dParent` cases do not use `p`. Patterns other than `dChild` mean exactly what
  they meant in snapshot 6.

## 5. Consequences for the freeze branch (Task 28)

`w/freeze-b1` was rebuilt from snapshot 7 (see `FREEZE-B1-PLAN.md`).
- Against the snapshot-6 freeze, only two frozen files differ: `LayeredGardenPatValid.lean` and `FlowerSum.lean`.
  The new `PatValid` file imports `GBranchToNode`, and its source column now cites "T L2331" from the new docstring.
- In the manifest, only these change:
  - those two files' hashes and ABIs;
  - `PatValid`'s source range;
  - the definition closures of `flowerSum` and `layergardenFlower`.
- `layergardenFlower`'s ABI is unchanged, because its printed statement is unchanged.
