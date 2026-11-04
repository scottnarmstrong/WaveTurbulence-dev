# Delta audit: Wave B snapshot 8 (F78), against snapshot 7

Auditor: `wt-orch`, refute-first. Date: 2026-11-04 (Task 34).

**Scope.**
- The one change of `/home/scott/wt-scratch/waveb-snap-8` (`CHANGES-8.md`, DESIGN CL-22, FINDINGS F78).
- Whether it changes any other frozen meaning.

## Verdict

**PASS.**
- The delta is exactly the declared change.
- It is faithful to TARGET L2312.
- Of the 423 elaborated constants of the five freeze files, **exactly one changes: `coupleSum`**.
- Its only frozen dependent is B1.12 `layergardenFlower`. B1.12's statement text and elaborated type are unchanged;
  its meaning changes only through `coupleSum`'s `∂_t` clause, as intended.

## 1. Inputs

**Snapshot 8.** `SHA256SUMS` verifies. I copied it and re-verified the copy at 09:23 UTC. Digest of `SHA256SUMS`:
`138033c99cab…`.

**Snapshot 7.** My verified copy from Task 28, the basis of `WaveB-snapshot7.md`.

**Files.**
- Changed: `WaveB1-Flower.lean`, `WaveB1-Flower-probes.lean`, `DESIGN.md` and `FREEZE-LIST.md`.
- Byte-identical: `WaveB1-Core.lean`, `-System`, `-Statements`, `-Sumint`, `-Lemmas`, `-Bridges`, the other probes and
  `FreezeList.lean`.
- `CHANGES-7.md` was replaced by `CHANGES-8.md`.

## 2. The textual delta

The `diff` of `WaveB1-Flower.lean` against snapshot 7:
- **The clause.** In `coupleSum`, it becomes
  `dt = true → ∀ j : Fin 2, ∃ b : GBranch LG.garden.tree, b.1 = (j, []) ∧ LG.layer b.toNode = p`. It was the same
  without the layer conjunct.
- **The docstring** now reads "the roots are layer-`p` branching nodes". It gains a paragraph citing F78: `∂_t 𝒥_• = 0`,
  so a couple whose top tree is trivial, with a lower-layer garden attached at its root, is excluded.

The probe file changes only in the two probes that restate the clause: `coupleSum_tr`, in its `dt = false`
equivalence, and `finite_coupleSum_support`. Nothing else differs.

`FREEZE-LIST.md` changes only in its title and in the `coupleSum` row, which gains the frozen dependency
`GBranch.toNode`. `DESIGN.md` gains CL-22 and the file-table note.

## 3. Fidelity of the new conjunct (TARGET L2312, F78)

**TARGET.** (L2312, proof of Prop `fixedpoint`, Part 1): "we can treat the time derivative `∂_t a_k^tr` (which simply
contains an extra `δ(t_𝔯 − t)` factor in `𝒥_𝒯` …) … The same holds also for `∂_t(ℒ₀)_k(t)`."

**The argument.**
- `a^tr = ∑_{n(𝒯) ≤ N_{p+1}} 𝒥_𝒯`, over trees in the top layer `p` (L2309). So `∂_t a^tr = ∑ ∂_t 𝒥_𝒯`, with
  `∂_t 𝒥_• = 0` for the trivial tree.
- The extra factor `δ(t_𝔯 − t)` sits at the root `𝔯` of a nontrivial top tree, which is a layer-`p` branching node.
- In the moment expansion of `𝔼_p|∂_t a^tr|²`, the couple's two roots are these two top roots.
- Under `IsCanonC (p+1)`, a couple may have one trivial top tree `•` whose leaf carries an attached lower-layer garden.
  Its root is then a lower-layer branching node.
  - The snapshot-7 clause, "the root is branching", admitted it and pinned that node's time to `t`.
  - The expansion never produces it.
- **"Root branching and in layer `p`" is exactly "top tree nontrivial"**, since every node of a top tree is in layer
  `p`. So the new conjunct is the faithful condition.

**Unaffected.**
- **Kind `ℒ₀`.** `TreeKindOK .L0` already forces `n(𝒯_j) > N_{p+1}`, so its top trees are nontrivial.
- **`dt = false`.** The clause is vacuous there.

**Faithful.** F78's description of the snapshot-7 defect is confirmed.

## 4. No other frozen meaning changes

**My own snapshot-8 build.**
- I took my snapshot-7 build and rebuilt `Flower` and `FlowerProbes` from snapshot 8, in the dev environment plus
  my Wave A glue: 0 errors.
- The only `sorry` is B1.12's anchor. The probes are clean.

**Elaborated comparison.** I dumped every constant of `WaveBDraft.{Core, System, Statements, Sumint, Flower}` with
matchers and auxiliaries delta-expanded and proofs erased, as in Tasks 22 and 28.
- 423 constants on each side; none only on one side.
- **Exactly one differs: `coupleSum`.**

**Freeze lists.**
- **`FreezeList.lean`** on the snapshot-8 build gives the same 226 rows.
  - The only change in uses is `coupleSum` gaining `GBranch.toNode`.
  - The source lines of `WTPrefixP` and `layergardenFlower` move by 4, because the docstring above them is longer.
- **The meta table** (`FreezeMeta.lean`) differs from snapshot 7's in the same way.

**Dependents.** The transitive dependents of `coupleSum` in the freeze set: **only B1.12 `layergardenFlower`**.
`fixedpoint` and the other anchors do not use it.

## 5. Consequences for the freeze branch (Task 34)

**Superseded as the freeze input.** Snapshot 9 (= snapshot 8 + F80, `WaveB-snapshot9.md`) replaced it in Task 34b;
this section records the snapshot-8 build, kept as `w/freeze-b1-snap8` (tip `7bd9e36`). Everything above still holds
for snapshot 9: its F80 change does not touch `coupleSum`.

`w/freeze-b1` was rebuilt from snapshot 8 (see `FREEZE-B1-PLAN.md`).
- Against the snapshot-7 freeze (`200d9c3`, kept in `w/freeze-b1-snap7`), **only one frozen file differs:
  `CoupleSum.lean`**. It has the new conjunct and docstring, and the import `GBranchToNode`.
- **In the manifest, only these change:**
  - `coupleSum`'s file hash and ABI;
  - `layergardenFlower`'s definition closure.
- **ABIs.**
  - `coupleSum` was recomputed: `e95f7a53…`, was `08353e0b…`.
  - `layergardenFlower`'s ABI is unchanged, since its printed statement is unchanged.
  - All other entries are reused from the byte-identical files.
