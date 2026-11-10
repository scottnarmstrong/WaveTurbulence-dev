# HANDOFF: CX-FLOWER-S1 — R11 STOP

The packet stops at the brief's explicit Dirac-factor gate. `OBSTRUCTION.md` gives the concrete two-corolla example, the endpoint argument, the two attempted routes, and the precise boundary between Lean-checked identities and mathematical reasoning. The obstruction concerns the plain positive-order bounded-mass spine representation, not TARGET's estimate.

## Files and exact results

All new declarations are in `WaveTurbulence.FlowerStage1`.

- `src/FlowerDirac.lean`: `corolla_all_parents`, `corolla_fixed`, `corolla_no_free_times`; the generic shrinking-box bound `norm_timeIntegral_le_box`; the actual `norm_splicedTimeIntegral_le` (all branch layers zero, common root time t≥0 implies norm≤t^G.order); `corolla_fixed_timeIntegral` (all parent phases removed, integral=1); `corollaLabels` and `corollaDecoration` (dimension 3, roots 0, flowers 1).
- `src/FlowerCorolla.lean`: `corolla_eps` (=1), `corolla_phase` (=1 with no phase removal), `corolla_plain_timeIntegral` (=1 for the literal plain flower free-time integral), `no_uniform_time_mass_bound` (a>0 forbids a≤C·t for every 0<t<1).
- `src/FlowerTimeAverage.lean`: `norm_average_splicedTimeIntegral_le`, the same shrinking-volume bound after integration against weights with integrable norm.
- `build.sh`, `fresh.sh`, `check.sh`; `FARM-SOURCES.txt`; `COPIED-SHA256SUMS`; pinned interface/source copies in `pinned/`; exact-type/axiom probes in `audit/` (archived as text after checking); build/check logs in `logs/`.

No flower constructor or complete Sound is delivered. `Represents` was not proved. The pair-type-family amendment was not changed or depended upon. Nothing outside this scratch packet was edited.

## Reuse, copies, and source readings

Proofs import the existing canonical `WaveBDraft.CoreProbes.flowerGarden` and its namespace; it is not redefined. SourceSplicedKernel and WaveBDraft.Flower are imported from the read-only farm. The RedSplice/S4 construction and Sound interfaces were inspected but not copied into executable new modules: their prime/irreducible/positive-order construction cannot discharge the fixed-time mismatch. The farm includes redsplice/bld-fresh9, flower-spine-u/build-fresh7, subpro/bld-disj-fresh and bld-fresh37, followed by redsplice/bld and lib, in that priority order. All links are dependencies, never writable build outputs.

`COPIED-SHA256SUMS` records full SHA256 values and original paths for the pinned copies read during the obstruction analysis: RedSplicePiece, RedSpliceAmend7, SubproFinal2, Stage1Interface, SourceSplicedKernel, FS9 Gates/Defs, and CoreProbes. They are evidence snapshots, not duplicate compiled code. Own source hashes are in `SRC-SHA256SUMS`.

Readings used:

- TARGET L2259–2265: marked flowers, optional pairing, no irreducibility, and the Dirac fixed-parent-time formula.
- TARGET L2280–2306: flowerest1 and adjustments (1)–(7), especially L2295's fixing of parent frequencies; L2287's moments without irreducibility.
- TARGET L2312: analogous fixed-root-time derivative for couples.
- TARGET Stage 1, `redsplice0`/`redsplice`/`stage1red`, and Prop subpro L2040–2051: ordinary skeleton/splicing construction and decorated support, used for comparison.
- R9, R11, R12, R23, R24, R28, R37, R44–R48 and R47-FINAL/F7: shared interface ownership, mandatory stop, and pair-type amendment scope.
- S2a `RedSplicePiece.lean` lines 41–95 and `RedSpliceAmend7`; S4 `SubproFinal2` and S4-DISJ handoff/progress: ordinary producer/reuse boundaries.
- `pinned/Stage1Interface.lean`, Sound fields `plain`, `order_pos`, `layer_le`, and RepresentsInt; `pinned/SourceSplicedKernel.lean` lines 35–95: no fixed-time field, bounded amplitudes, all branch times integrated.

## flowerest1 adjustments

1. Root-weight/non-flower-leaf transfer: not implemented; independent of the obstruction. The example has fixed k−k', so its weight is constant in t.
2. Flower/parent changes and Dirac trace: **blocked** by R11. The actual canonical example, valid decoration, epsilon, phase cancellation, and time integral are checked. Parent-frequency fixing does not restore an integrated time coordinate.
3. Arbitrary k,k': the example uses the allowed k=0, k'=(1,1,1)/L.
4. Special-node vines: not implemented; the two-corolla regular completion has no cancellation vine needed to cause the obstruction.
5. Stem-layer preservation: the example is `IsCanonH 1` with every layer zero; no twist argument can alter the time-coordinate mismatch.
6. M2 integration gain: no cutoff in the example, so it cannot repair the base case; not implemented.
7. Stem-preserving twists with M2: not implemented; no M2 cutoff in the example.

Neither AMEND7 field nor S4 support is claimed for a flower constructor. The imported ordinary producer fields remain unchanged.

## Checks

See the final check record at the end of this file.

## Uncertainties / errata / deviations

The whole `FlowerStage1At` negation and its finite lattice-support bound are not Lean theorems here. The checked results establish the fixed-time=1 versus plain-time≤t^order mismatch and its persistence under finite-mass frequency averaging. The full auxiliary-gate obstruction is the explicit mathematical endpoint argument in OBSTRUCTION.md. No suspected counterexample to TARGET's bound is asserted.

The requested construction is intentionally not papered over by a conditional Sound theorem or a weakened gate. R11 expressly requires stopping when the Dirac factor cannot be absorbed into a plain G_sb. A compatible fixed-time/componentwise analytic interface would require an orchestrator-owned statement decision; this packet makes no such change.

## FlowerTwist (R53)

R53 was read and added to scope. Its explicit stop condition is met before the special-node restriction can be applied: the requested `FamilyReconstruction.outputs` relation cannot have a marked flower as either its source state or an output.

Exact checked statements, namespace `WaveTurbulence.FlowerStage1` (`src/FlowerTwistGap.lean`):

```lean
canonH_not_plain {w p : ℕ} (LG : LayeredGarden w) (hw : 0 < w)
    (hH : IsCanonH (p + 1) LG) : ¬ LG.garden.IsPlain

no_flower_family_state {w p : ℕ} {ι : Type*} (LG : LayeredGarden w)
    (hw : 0 < w) (hH : IsCanonH (p + 1) LG)
    (A : LFTwist.FamilyReconstruction w ι) : A.layered ≠ LG

family_outputs_plain {w p : ℕ} {kind : Bool} {ι : Type*}
    (A : LFTwist.FamilyReconstruction w ι) (L : List ι) {LH : LayeredGarden w}
    (h : LH ∈ A.outputs p kind L) : LH.garden.IsPlain

no_flower_family_output {w p : ℕ} {kind : Bool} {ι : Type*}
    (A : LFTwist.FamilyReconstruction w ι) (L : List ι) (LH : LayeredGarden w)
    (hw : 0 < w) (hH : IsCanonH (p + 1) LH) : LH ∉ A.outputs p kind L

no_flower_canonicalObject {w p : ℕ} {kind : Bool} (LG : LayeredGarden w)
    (hw : 0 < w) (hH : IsCanonH (p + 1) LG) : ¬ LFTwist.CanonicalObject p kind LG
```

The decisive fields are not just a missing preservation lemma:

- Main `LFTwist/FamilyState.lean` lines 13–19: `decodes : data.Decodes plain layered.garden`.
- Main `SkeletonDraft/ReconstructionForest.lean` lines 60–61: `Decodes ... G := G.IsPlain ∧ ...`.
- Main `LFTwist/FamilyOutputs.lean` lines 19–20: outputs are precisely `B.layered` of another such state.
- Main `LFTwist/CanonicalObject.lean` lines 17–19 and 28–33: only ordinary G/C constructors, both plain; every non-skipped `FamilyOperation` requires this canonical index.

Therefore adding an avoidance predicate to `outputs` cannot produce any marked flower. Pairing and unmarking the flowers changes the garden. To use that route one needs a genuine completion-and-remarking lift, a marked-leaf transport independent of the exceptional attachments, and a canonicity treatment for reducible completions (or componentwise operations). A general `IsCanonH` does not supply `IsCanonG` for its plain completion: irreducibility is deliberately absent in TARGET L2261/L2287. The current API supplies no marked reconstruction state or corresponding output/mark transport theorem. The ordinary-leaf correspondence in LFTWIST-LEAFMAP is also restricted to the ordinary slots of this plain API.

This is an API-extension gap, not a claim that flower LF twisting is mathematically impossible. No `FlowerTwist`/`FlowerTwistClosed` is exported as an empty or identity-only substitute. No (4)/(5)/(7) preservation theorem is claimed. LG-SPINE must not pin such a substitute from this packet.

Main's FamilyState and FamilyOutputs sources were compared with the universe scratch versions used by the build farm: the only differences are import paths. Both versions and the other relevant main API files are copied under `pinned/r53/`, with full hashes appended to `COPIED-SHA256SUMS`. A separate main-namespace audit probe is also attempted; its outcome is recorded in the final checks.


## Final check record (2026-11-05)

- `./fresh.sh build-fresh-r53` → exit 0. `logs/fresh-r53.out` records FlowerDirac, FlowerCorolla, FlowerTimeAverage, FlowerTwistGap all exit 0. New output directory, topological order, one nice-5 compile at a time. No warnings/errors in the four fresh module logs. This is a fresh rebuild of **this packet's four modules**; upstream project/Mathlib dependencies were reused read-only, not rebuilt.
- `./check.sh audit/Axioms.lean` → exit 0, `logs/Axioms.log`: all 17 listed results use only `propext`, `Classical.choice`, `Quot.sound`.
- `./check.sh audit/TypeCheck.lean` → exit 0, `logs/TypeCheck.log`: independently restated types for the principal time bound, literal flower integral, epsilon, mass contradiction, weighted average, and the three R53 exclusions. The requested constructor/Sound target does not exist; no exact-type check of those targets is claimed.
- `EXTRA_LP=<repo>/.lake/build/lib/lean ./check.sh audit/MainTwistGap.lean` → exit 0, `logs/MainTwistGap.log`: the five R53 exclusion lemmas also compile directly against `WaveTurbulence.Foundations.Molecule.LFTwist.FamilyOutputs`; the three printed main-audit results use only the standard axioms. Initial cache lookup attempts selected the cumul worktree's nonexistent main module; setting LEAN_PATH inside `lake env` fixed the lookup. No main modules were rebuilt.
- Hygiene: `logs/hygiene.log` records a clean prohibited-token scan over src/; four modules, 270 lines total, maximum file length 107. All have copyright/module/public imports/module documentation/public sections. No dependency artifacts were removed or changed.
- `SRC-SHA256SUMS` records the four final source hashes. `COPIED-SHA256SUMS` records pinned upstream source hashes. Audit probes have been archived as `audit/*.lean.txt`; transient `.lean` examples and print commands were removed after checking.

STOPPED cx-flower-s1: R11 fixed-time traces conflict with the plain positive-order bounded-mass interface; R53 FamilyReconstruction inputs and outputs exclude marked canonical flowers.
