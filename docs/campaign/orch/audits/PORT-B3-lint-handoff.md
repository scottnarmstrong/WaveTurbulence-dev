# Batch-3 Spine lint-port handoff

`nice -n 5 lake build WaveTurbulence.Foundations.Spine.SourceProviders` in `/home/scott/WaveTurbulence-worktrees/port-b3a`: build 8 exit 0, `Build completed successfully (11489 jobs)`. The complete log is `build-8.log`. All Spine areas have 0 warning lines; 33 warnings were replayed from outside Spine and are outside this packet. `git diff --check` exit 0. No dependency rebuild, staging, commit or landing was performed.

Axiom audit: `nice -n 5 lake env lean /home/scott/wt-scratch/port-b3a/SourceProvidersAudit.lean` exit 0; each of all seven exported Spine wrapper theorems printed `[propext, Classical.choice, Quot.sound]` (`axioms-root.log`). An earlier non-module scratch probe failed while reading an imported private artifact; the root-prepared module probe supersedes it and passed.

Changes: deprecated names replaced by current equivalents; `mul_le_one₀` calls replaced with the same constituent inequality; unused simp arguments and dead tactics removed; redundant individual `@[expose]` removed only under existing exposed public sections; unused binder names alpha-renamed with unchanged types and premise order, including requested `CountingChoices.LadderGaps` names. Mapped SNorm/Jbr references explicitly qualified to `WaveTurbulence.Induct`. The seven final provider declarations and all meaning-carrying definition bodies remain unchanged. Some ordinary helper telescope instances were omitted when Lean identified them unused; call sites compile. Additional internal helper telescope changes: `volume_Ω_lt_top` omits unused measurability argument and DecidableEq, three callers updated; `rung_total_F/X/Y/Z` omit unused standing inputs and four callers updated; `tree_err_single30` omits four unused helper inputs and its caller updated; `interiorAtoms_subset`, `ir_injective`, and `incoh_le` omit unused Ctx receiver and in-scope field-notation callers now use receiver-free names. The root-owned `LeafSingularOutput` helper likewise omits hd, with its in-scope caller updated by root. These are internal helper API changes and require review, but do not alter the source-facing providers.

The exact owned changed files are listed below; root-owned excluded files are not in this list. The staged index was pre-existing and was not touched. Independent audit of the complete port and clean landing remains with root.

Owned changed files by area: CoarseSplicedDraft: 1, IncohLeafwise: 5, PL2330Draft: 7, PL234Draft: 14, Spine root: 99, coarse_spliced: 1.

- `WaveTurbulence/Foundations/Spine/AmpExpansion.lean`
- `WaveTurbulence/Foundations/Spine/Arith1.lean`
- `WaveTurbulence/Foundations/Spine/Assembly2.lean`
- `WaveTurbulence/Foundations/Spine/Assembly3.lean`
- `WaveTurbulence/Foundations/Spine/AtomSlots.lean`
- `WaveTurbulence/Foundations/Spine/AtomWeight.lean`
- `WaveTurbulence/Foundations/Spine/BlockInt.lean`
- `WaveTurbulence/Foundations/Spine/BondProd.lean`
- `WaveTurbulence/Foundations/Spine/BoxSup.lean`
- `WaveTurbulence/Foundations/Spine/ChainBound.lean`
- `WaveTurbulence/Foundations/Spine/ChainDec.lean`
- `WaveTurbulence/Foundations/Spine/ChainExpand.lean`
- `WaveTurbulence/Foundations/Spine/ChainMol.lean`
- `WaveTurbulence/Foundations/Spine/ChartAff.lean`
- `WaveTurbulence/Foundations/Spine/ClassCount.lean`
- `WaveTurbulence/Foundations/Spine/CoarseSplicedDraft/LadderCounts.lean`
- `WaveTurbulence/Foundations/Spine/CoherentTruncation.lean`
- `WaveTurbulence/Foundations/Spine/Corner.lean`
- `WaveTurbulence/Foundations/Spine/Count.lean`
- `WaveTurbulence/Foundations/Spine/DecoupleFin.lean`
- `WaveTurbulence/Foundations/Spine/Engine2.lean`
- `WaveTurbulence/Foundations/Spine/Engine3.lean`
- `WaveTurbulence/Foundations/Spine/Engine4.lean`
- `WaveTurbulence/Foundations/Spine/EpsIE.lean`
- `WaveTurbulence/Foundations/Spine/Factor.lean`
- `WaveTurbulence/Foundations/Spine/FibreBij.lean`
- `WaveTurbulence/Foundations/Spine/FibreFactor.lean`
- `WaveTurbulence/Foundations/Spine/FibreSum.lean`
- `WaveTurbulence/Foundations/Spine/Final1.lean`
- `WaveTurbulence/Foundations/Spine/Final2.lean`
- `WaveTurbulence/Foundations/Spine/Final3a.lean`
- `WaveTurbulence/Foundations/Spine/Final3b.lean`
- `WaveTurbulence/Foundations/Spine/Final3c.lean`
- `WaveTurbulence/Foundations/Spine/Final3d.lean`
- `WaveTurbulence/Foundations/Spine/Final3e.lean`
- `WaveTurbulence/Foundations/Spine/Final4c.lean`
- `WaveTurbulence/Foundations/Spine/FinalArith.lean`
- `WaveTurbulence/Foundations/Spine/FiniteSupp.lean`
- `WaveTurbulence/Foundations/Spine/GardenPos.lean`
- `WaveTurbulence/Foundations/Spine/GenBridge1.lean`
- `WaveTurbulence/Foundations/Spine/GenBridge2.lean`
- `WaveTurbulence/Foundations/Spine/GenBridge3.lean`
- `WaveTurbulence/Foundations/Spine/GenBridge4.lean`
- `WaveTurbulence/Foundations/Spine/GenBridge5.lean`
- `WaveTurbulence/Foundations/Spine/GenClass1.lean`
- `WaveTurbulence/Foundations/Spine/GenClass2.lean`
- `WaveTurbulence/Foundations/Spine/GenClass3.lean`
- `WaveTurbulence/Foundations/Spine/GenClass4.lean`
- `WaveTurbulence/Foundations/Spine/GenSplit.lean`
- `WaveTurbulence/Foundations/Spine/GenSum.lean`
- `WaveTurbulence/Foundations/Spine/Glue.lean`
- `WaveTurbulence/Foundations/Spine/Glue1.lean`
- `WaveTurbulence/Foundations/Spine/Glue3.lean`
- `WaveTurbulence/Foundations/Spine/Glue4.lean`
- `WaveTurbulence/Foundations/Spine/Glue5.lean`
- `WaveTurbulence/Foundations/Spine/Glue7.lean`
- `WaveTurbulence/Foundations/Spine/Glue8.lean`
- `WaveTurbulence/Foundations/Spine/Glue9.lean`
- `WaveTurbulence/Foundations/Spine/GroupVol.lean`
- `WaveTurbulence/Foundations/Spine/HingeStep3.lean`
- `WaveTurbulence/Foundations/Spine/IncohLeafwise/CoupleKernelFromInputs.lean`
- `WaveTurbulence/Foundations/Spine/IncohLeafwise/Gate.lean`
- `WaveTurbulence/Foundations/Spine/IncohLeafwise/KernelScaling.lean`
- `WaveTurbulence/Foundations/Spine/IncohLeafwise/OneRootKernelFromInputs.lean`
- `WaveTurbulence/Foundations/Spine/IncohLeafwise/TreeKernelFromInputs.lean`
- `WaveTurbulence/Foundations/Spine/IndGood.lean`
- `WaveTurbulence/Foundations/Spine/KLemma.lean`
- `WaveTurbulence/Foundations/Spine/KernelCore.lean`
- `WaveTurbulence/Foundations/Spine/Kinds.lean`
- `WaveTurbulence/Foundations/Spine/LadderDecayFinal.lean`
- `WaveTurbulence/Foundations/Spine/LadderFactor.lean`
- `WaveTurbulence/Foundations/Spine/LadderL1.lean`
- `WaveTurbulence/Foundations/Spine/LadderL1Fixed.lean`
- `WaveTurbulence/Foundations/Spine/LadderTime.lean`
- `WaveTurbulence/Foundations/Spine/LocAlg.lean`
- `WaveTurbulence/Foundations/Spine/MolGamma.lean`
- `WaveTurbulence/Foundations/Spine/MolLadder.lean`
- `WaveTurbulence/Foundations/Spine/MolPres.lean`
- `WaveTurbulence/Foundations/Spine/MolRung.lean`
- `WaveTurbulence/Foundations/Spine/OrderZeroMomentumWeight.lean`
- `WaveTurbulence/Foundations/Spine/Outer.lean`
- `WaveTurbulence/Foundations/Spine/PL2330Draft/CoupleInd.lean`
- `WaveTurbulence/Foundations/Spine/PL2330Draft/Lead.lean`
- `WaveTurbulence/Foundations/Spine/PL2330Draft/Piece.lean`
- `WaveTurbulence/Foundations/Spine/PL2330Draft/Piece2.lean`
- `WaveTurbulence/Foundations/Spine/PL2330Draft/PieceTree.lean`
- `WaveTurbulence/Foundations/Spine/PL2330Draft/Prod4.lean`
- `WaveTurbulence/Foundations/Spine/PL2330Draft/TreeGate.lean`
- `WaveTurbulence/Foundations/Spine/PL234Draft/CoherentTaylor.lean`
- `WaveTurbulence/Foundations/Spine/PL234Draft/CoupleGate.lean`
- `WaveTurbulence/Foundations/Spine/PL234Draft/CoupleInduction.lean`
- `WaveTurbulence/Foundations/Spine/PL234Draft/CoupleStep.lean`
- `WaveTurbulence/Foundations/Spine/PL234Draft/CoupleTop.lean`
- `WaveTurbulence/Foundations/Spine/PL234Draft/Gate61CHelpers.lean`
- `WaveTurbulence/Foundations/Spine/PL234Draft/LowApp.lean`
- `WaveTurbulence/Foundations/Spine/PL234Draft/PieceCouple.lean`
- `WaveTurbulence/Foundations/Spine/PL234Draft/PieceTree.lean`
- `WaveTurbulence/Foundations/Spine/PL234Draft/SepCalc.lean`
- `WaveTurbulence/Foundations/Spine/PL234Draft/TaylorCode.lean`
- `WaveTurbulence/Foundations/Spine/PL234Draft/TaylorPointwise.lean`
- `WaveTurbulence/Foundations/Spine/PL234Draft/TreeBottom.lean`
- `WaveTurbulence/Foundations/Spine/PL234Draft/WeightedPointwise.lean`
- `WaveTurbulence/Foundations/Spine/PhiFamily.lean`
- `WaveTurbulence/Foundations/Spine/Poisson1D.lean`
- `WaveTurbulence/Foundations/Spine/RegularCodeSumBound.lean`
- `WaveTurbulence/Foundations/Spine/RestInv.lean`
- `WaveTurbulence/Foundations/Spine/RungBall.lean`
- `WaveTurbulence/Foundations/Spine/RungBallTime.lean`
- `WaveTurbulence/Foundations/Spine/RungBudget.lean`
- `WaveTurbulence/Foundations/Spine/RungFull.lean`
- `WaveTurbulence/Foundations/Spine/RungSupp.lean`
- `WaveTurbulence/Foundations/Spine/RungTotal.lean`
- `WaveTurbulence/Foundations/Spine/Selection2.lean`
- `WaveTurbulence/Foundations/Spine/SourceCountingData.lean`
- `WaveTurbulence/Foundations/Spine/SourceVineGapObjects.lean`
- `WaveTurbulence/Foundations/Spine/SourceVineObjects.lean`
- `WaveTurbulence/Foundations/Spine/SubLadder.lean`
- `WaveTurbulence/Foundations/Spine/Support.lean`
- `WaveTurbulence/Foundations/Spine/TimeDrop.lean`
- `WaveTurbulence/Foundations/Spine/TimeLemma3.lean`
- `WaveTurbulence/Foundations/Spine/TimeReindex.lean`
- `WaveTurbulence/Foundations/Spine/TimeWeights.lean`
- `WaveTurbulence/Foundations/Spine/Valley.lean`
- `WaveTurbulence/Foundations/Spine/WeightSplit.lean`
- `WaveTurbulence/Foundations/Spine/WeightedSmoothMultiplier.lean`
- `WaveTurbulence/Foundations/Spine/XNormWeightPointwise.lean`
- `WaveTurbulence/Foundations/Spine/coarse_spliced/Count.lean`

Suspected errata: none discovered. Deviations: internal helper telescope reductions and binder alpha-renames as above.

READY lint-port-b3
