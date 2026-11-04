# FREEZE-LIST: Wave B tier B1 (snapshot 6: freeze-ready packaging, DESIGN CL-16–CL-18, CL-20)

Generated from the compiled modules `WaveBDraft.{Core, System, Statements, Sumint, Flower}` by the Lean metaprogram
`FreezeList.lean` (next to this file) and `gen_freeze.py`. Each row is one declaration of the five frozen files:
its kind, its file, the TARGET/DH source it cites, and the other frozen declarations its type and body use.
The source comes from the declaration's docstring. Where that has no citation, it is the citation of the
enclosing section header, marked `(section)`, or else of the file's module docstring, marked `(file)`.

**Counts.**
- **12 theorems**, the anchors B1.1–B1.12. B1.6 `sumint` is in `WaveB1-Sumint.lean`, B1.12
  `layergardenFlower` in `WaveB1-Flower.lean`, the others in `WaveB1-Statements.lean`.
- **167 definitions**, **4 abbrevs**, **5 structures** and **5 inductives**.
- **33 instances**, each a named `@[instance_reducible, instance] def` (a literal `def`).
  The former `deriving DecidableEq` clauses of `TTree` and `MarkTag` are now explicit definitions:
  `TTree.decEq`, `instDecidableEqTTree`, `instDecidableEqMarkTag` and, for `FixPat` (`WaveB1-Flower.lean`),
  `FixPat.decEq` and `instDecidableEqFixPat`.

**Closure.**
- No frozen declaration uses a proved theorem of the project. The facts that definition bodies need are proved
  inline in `by` blocks; the elaborator stores these as auxiliary `….proof_n` constants, which belong to their
  definition.
- Every proved non-anchor lemma is in the non-frozen `WaveB1-Lemmas.lean`.
- The five files import only `WaveTurbulence.Frozen.Defs.*` (Wave A), Mathlib, and each other.

**The *uses* column.**
- It lists frozen declarations only. Mathlib and Wave A constants are omitted.
- Structure projections, constructors and recursors are folded into their structure or inductive.

## `WaveB1-Core.lean` (94 declarations)

| declaration | kind | TARGET / DH source | uses (frozen) |
|---|---|---|---|
| `WTParams` | structure | L605–L615 | — |
| `WTPrefix` | def | WAVE-B §1.2; T L605–L615 | `WTParams` |
| `WTParams.theta` | def | T (parameters), L611 | `WTParams` |
| `WTParams.Lambda` | def | T (parameters), L611 | `WTParams` |
| `WTParams.Rdown` | def | T (parameters2), L612 | `WTParams` |
| `WTParams.R` | def | T (parameters2) | `WTParams`, `WTParams.Rdown` |
| `WTParams.N` | def | T (parameters2) | `WTParams`, `WTParams.R` |
| `WTParams.gamma0` | def | T (defgamma1), L613 | `WTParams` |
| `WTParams.gamma1` | def | T (defgamma1), L613 | `WTParams` |
| `TTree` | inductive | T Def `deftree`; DH21 Def 2.1 | — |
| `TTree.decEq` | def | (section) T Def `deftree`, L625–L631 | `TTree` |
| `instDecidableEqTTree` | instance (def) | — (DecidableEq instance for `TTree`; no source object) | `TTree`, `TTree.decEq` |
| `TTree.Path` | abbrev | (section) T Def `deftree`, L625–L631 | — |
| `TTree.order` | def | (section) T Def `deftree`, L625–L631 | `TTree` |
| `TTree.pre` | def | (section) T Def `deftree`, L625–L631 | `TTree.Path` |
| `TTree.nodes` | def | (section) T Def `deftree`, L625–L631 | `TTree`, `TTree.Path`, `TTree.pre` |
| `TTree.leaves` | def | (section) T Def `deftree`, L625–L631 | `TTree`, `TTree.Path`, `TTree.pre` |
| `TTree.branching` | def | (section) T Def `deftree`, L625–L631 | `TTree`, `TTree.Path`, `TTree.pre` |
| `TTree.pathSign` | def | (section) T Def `deftree`, L625–L631 | `TTree.Path` |
| `forestSet` | def | (section) T Def `defgarden`, L632–L638 | `TTree`, `TTree.Path` |
| `GNode` | def | (section) T Def `defgarden`, L632–L638 | `TTree`, `TTree.Path`, `TTree.nodes` |
| `GLeaf` | def | (section) T Def `defgarden`, L632–L638 | `TTree`, `TTree.Path`, `TTree.leaves` |
| `GBranch` | def | (section) T Def `defgarden`, L632–L638 | `TTree`, `TTree.Path`, `TTree.branching` |
| `instDecidableEqGNode` | instance (def) | — (DecidableEq instance for `GNode`; no source object) | `GNode`, `TTree`, `TTree.Path`, `TTree.nodes` |
| `instDecidableEqGLeaf` | instance (def) | — (DecidableEq instance for `GLeaf`; no source object) | `GLeaf`, `TTree`, `TTree.Path`, `TTree.leaves` |
| `instDecidableEqGBranch` | instance (def) | — (DecidableEq instance for `GBranch`; no source object) | `GBranch`, `TTree`, `TTree.Path`, `TTree.branching` |
| `instFintypeGNode` | instance (def) | — (Fintype instance for `GNode`; no source object) | `GNode`, `TTree`, `TTree.Path`, `TTree.nodes`, `forestSet` |
| `instFintypeGLeaf` | instance (def) | — (Fintype instance for `GLeaf`; no source object) | `GLeaf`, `TTree`, `TTree.Path`, `TTree.leaves`, `forestSet` |
| `instFintypeGBranch` | instance (def) | — (Fintype instance for `GBranch`; no source object) | `GBranch`, `TTree`, `TTree.Path`, `TTree.branching`, `forestSet` |
| `GLeaf.toNode` | def | (section) T Def `defgarden`, L632–L638 | `GLeaf`, `GNode`, `TTree`, `TTree.Path`, `TTree.leaves`, `TTree.nodes` |
| `GBranch.toNode` | def | (section) T Def `defgarden`, L632–L638 | `GBranch`, `GNode`, `TTree`, `TTree.Path`, `TTree.branching`, `TTree.nodes` |
| `GBranch.child` | def | (section) T Def `defgarden`, L632–L638 | `GBranch`, `GNode`, `TTree`, `TTree.Path`, `TTree.branching`, `TTree.nodes`, `TTree.pre` |
| `GNode.root` | def | (section) T Def `defgarden`, L632–L638 | `GNode`, `TTree`, `TTree.Path`, `TTree.nodes`, `TTree.pre` |
| `GNode.IsDesc` | def | T L627 | `GNode`, `TTree`, `TTree.Path`, `TTree.nodes` |
| `instDecidableIsDesc` | instance (def) | — (Decidable instance for `IsDesc`; no source object) | `GNode`, `GNode.IsDesc`, `TTree`, `TTree.Path`, `TTree.nodes` |
| `GNode.Incomparable` | def | (section) T Def `defgarden`, L632–L638 | `GNode`, `GNode.IsDesc`, `TTree` |
| `instDecidableIncomparable` | instance (def) | — (Decidable instance for `Incomparable`; no source object) | `GNode`, `GNode.Incomparable`, `GNode.IsDesc`, `TTree`, `instDecidableIsDesc` |
| `GNode.leavesBelow` | def | (section) T Def `defgarden`, L632–L638 | `GLeaf`, `GLeaf.toNode`, `GNode`, `GNode.IsDesc`, `TTree`, `instDecidableIsDesc`, `instFintypeGLeaf` |
| `GNode.orderBelow` | def | (section) T Def `defgarden`, L632–L638 | `GBranch`, `GBranch.toNode`, `GNode`, `GNode.IsDesc`, `TTree`, `instDecidableIsDesc`, `instFintypeGBranch` |
| `nodeSign` | def | (section) T Def `defgarden`, L632–L638 | `TTree.Path`, `TTree.pathSign` |
| `MarkTag` | inductive | WAVE-B v2 §2.2.2; T (timepairtree); T (kqflower) | — |
| `instDecidableEqMarkTag` | instance (def) | — (DecidableEq instance for `MarkTag`; no source object) | `MarkTag` |
| `instFintypeMarkTag` | instance (def) | — (Fintype instance for `MarkTag`; no source object) | `MarkTag`, `instDecidableEqMarkTag` |
| `Garden` | structure | T Def `defgarden`, L632–L638; DH21-2 Def 4.1; L2259–L2263; WAVE-B v2 §2.2.2 | `GLeaf`, `MarkTag`, `TTree`, `TTree.Path`, `TTree.leaves`, `nodeSign` |
| `Garden.IsFlower` | def | (section) T Def `defgarden`, L632–L638 | `GLeaf`, `Garden`, `MarkTag` |
| `Garden.IsLone` | def | (section) T Def `defgarden`, L632–L638 | `GLeaf`, `Garden`, `MarkTag` |
| `Garden.instDecidableIsFlower` | instance (def) | — (Decidable instance for `IsFlower`; no source object) | `GLeaf`, `Garden`, `Garden.IsFlower`, `MarkTag`, `instDecidableEqMarkTag` |
| `Garden.instDecidableIsLone` | instance (def) | — (Decidable instance for `IsLone`; no source object) | `GLeaf`, `Garden`, `Garden.IsLone`, `MarkTag`, `instDecidableEqMarkTag` |
| `Garden.IsPlain` | def | T Def `defgarden` | `GLeaf`, `Garden`, `MarkTag` |
| `Garden.instDecidableIsPlain` | instance (def) | — (Decidable instance for `IsPlain`; no source object) | `GLeaf`, `Garden`, `Garden.IsPlain`, `MarkTag`, `instFintypeGLeaf` |
| `Garden.IsBalanced` | def | (section) T Def `defgarden`, L632–L638 | `Garden` |
| `Garden.instDecidableIsBalanced` | instance (def) | — (Decidable instance for `IsBalanced`; no source object) | `Garden`, `Garden.IsBalanced` |
| `Garden.IsFlowerGarden` | def | T Def `defflower` | `GLeaf`, `Garden`, `Garden.IsFlower`, `MarkTag`, `TTree.Path`, `TTree.leaves`, `instFintypeGLeaf` |
| `Garden.instDecidableIsFlowerGarden` | instance (def) | — (Decidable instance for `IsFlowerGarden`; no source object) | `GLeaf`, `Garden`, `Garden.IsFlower`, `Garden.IsFlowerGarden`, `Garden.instDecidableIsFlower`, `MarkTag`, `TTree.Path`, `TTree.leaves`, `instFintypeGLeaf` |
| `Garden.order` | def | (section) T Def `defgarden`, L632–L638 | `Garden`, `TTree.order` |
| `Garden.sign` | def | (section) T Def `defgarden`, L632–L638 | `GNode`, `Garden`, `TTree.Path`, `TTree.nodes`, `nodeSign` |
| `Garden.zeta` | def | T Def `defgarden` | `GBranch`, `GBranch.toNode`, `Garden`, `Garden.sign`, `instFintypeGBranch` |
| `Garden.CompletelyPaired` | def | (section) T Def `defgarden`, L632–L638 | `GLeaf`, `Garden` |
| `Garden.instDecidableCompletelyPaired` | instance (def) | — (Decidable instance for `CompletelyPaired`; no source object) | `GLeaf`, `Garden`, `Garden.CompletelyPaired`, `instDecidableEqGLeaf`, `instFintypeGLeaf` |
| `Garden.leavesOf` | def | (section) T Def `defgarden`, L632–L638 | `GLeaf`, `Garden`, `TTree.Path`, `TTree.leaves`, `instFintypeGLeaf` |
| `Garden.Irreducible` | def | T L636 | `Garden`, `Garden.CompletelyPaired`, `Garden.leavesOf` |
| `Garden.instDecidableIrreducible` | instance (def) | — (Decidable instance for `Irreducible`; no source object) | `Garden`, `Garden.CompletelyPaired`, `Garden.Irreducible`, `Garden.instDecidableCompletelyPaired`, `Garden.leavesOf` |
| `IsCouple` | def | T L634–L635 | `Garden`, `Garden.IsPlain` |
| `instDecidableIsCouple` | instance (def) | — (Decidable instance for `IsCouple`; no source object) | `Garden`, `Garden.IsPlain`, `Garden.instDecidableIsPlain`, `IsCouple` |
| `IsPairedTree` | def | T L637 | `GLeaf`, `Garden`, `Garden.IsLone`, `MarkTag`, `instFintypeGLeaf` |
| `instDecidableIsPairedTree` | instance (def) | — (Decidable instance for `IsPairedTree`; no source object) | `GLeaf`, `Garden`, `Garden.IsLone`, `Garden.instDecidableIsLone`, `IsPairedTree`, `MarkTag`, `instFintypeGLeaf` |
| `IsDecoration` | def | T Def `defdec` | `GBranch`, `GBranch.child`, `GBranch.toNode`, `GLeaf`, `GLeaf.toNode`, `GNode`, `Garden` |
| `IntDecoration` | def | T Def `defdec` | `GNode`, `GNode.root`, `Garden`, `IsDecoration` |
| `GenDecoration` | def | T Def `defflower` | `GLeaf`, `GLeaf.toNode`, `GNode`, `GNode.root`, `Garden`, `Garden.IsFlower`, `IsDecoration` |
| `cosetDecoration` | def | T L643 | `GNode`, `Garden` |
| `epsCoef` | def | T (defcoef0), L556–L561 | — |
| `epsDec` | def | T (defepscoef); T (defcoef0) | `GBranch`, `GBranch.child`, `GNode`, `Garden`, `epsCoef`, `instFintypeGBranch` |
| `resFactor` | def | T (res) | — |
| `omegaNode` | def | T (defomega) | `GBranch`, `GBranch.child`, `GBranch.toNode`, `GNode`, `Garden`, `resFactor` |
| `IsLayering` | def | T Def `deflayer` | `GBranch`, `GBranch.child`, `GBranch.toNode`, `GLeaf`, `GLeaf.toNode`, `GNode`, `Garden` |
| `instDecidableIsLayering` | instance (def) | — (Decidable instance for `IsLayering`; no source object) | `GBranch`, `GBranch.child`, `GBranch.toNode`, `GLeaf`, `GLeaf.toNode`, `GNode`, `Garden`, `IsLayering`, `instFintypeGBranch`, `instFintypeGLeaf` |
| `LayeredGarden` | structure | (section) T Def `deflayer`, L649–L656 | `GNode`, `Garden`, `IsLayering` |
| `LayeredGarden.parentLayer` | def | T Prop `canonequiv` | `GNode`, `Garden`, `LayeredGarden`, `TTree`, `TTree.Path`, `TTree.nodes`, `TTree.pre` |
| `LayeredGarden.CanonCriterion` | def | T Prop `canonequiv` | `GLeaf`, `GNode`, `GNode.Incomparable`, `GNode.leavesBelow`, `Garden`, `Garden.CompletelyPaired`, `LayeredGarden`, `LayeredGarden.parentLayer`, `instDecidableEqGLeaf` |
| `LayeredGarden.instDecidableCanonCriterion` | instance (def) | — (Decidable instance for `CanonCriterion`; no source object) | `GLeaf`, `GNode`, `GNode.Incomparable`, `GNode.leavesBelow`, `Garden`, `Garden.CompletelyPaired`, `Garden.instDecidableCompletelyPaired`, `LayeredGarden`, `LayeredGarden.CanonCriterion`, `LayeredGarden.parentLayer`, `instDecidableEqGLeaf`, `instDecidableIncomparable`, `instFintypeGNode` |
| `LayeredGarden.OnStem` | def | T Def `defflower` | `GLeaf`, `GLeaf.toNode`, `GNode`, `GNode.IsDesc`, `Garden`, `Garden.IsFlower`, `LayeredGarden` |
| `LayeredGarden.instDecidableOnStem` | instance (def) | — (Decidable instance for `OnStem`; no source object) | `GLeaf`, `GLeaf.toNode`, `GNode`, `GNode.IsDesc`, `Garden`, `Garden.IsFlower`, `Garden.instDecidableIsFlower`, `LayeredGarden`, `LayeredGarden.OnStem`, `instDecidableIsDesc`, `instFintypeGLeaf` |
| `IsCanonG` | def | T Def `defcanon`, L657–L668; T Prop `canonequiv`, L889 | `Garden.Irreducible`, `Garden.IsPlain`, `LayeredGarden`, `LayeredGarden.CanonCriterion` |
| `IsCanonC` | def | T Def `defcanon`; T Prop `canonequiv` | `IsCouple`, `LayeredGarden`, `LayeredGarden.CanonCriterion` |
| `IsCanonH` | def | T Def `defflower` | `GNode`, `Garden`, `Garden.IsFlowerGarden`, `LayeredGarden`, `LayeredGarden.CanonCriterion`, `LayeredGarden.OnStem` |
| `instDecidableIsCanonG` | instance (def) | — (Decidable instance for `IsCanonG`; no source object) | `Garden.Irreducible`, `Garden.IsPlain`, `Garden.instDecidableIrreducible`, `Garden.instDecidableIsPlain`, `IsCanonG`, `LayeredGarden`, `LayeredGarden.CanonCriterion`, `LayeredGarden.instDecidableCanonCriterion` |
| `instDecidableIsCanonC` | instance (def) | — (Decidable instance for `IsCanonC`; no source object) | `IsCanonC`, `IsCouple`, `LayeredGarden`, `LayeredGarden.CanonCriterion`, `LayeredGarden.instDecidableCanonCriterion`, `instDecidableIsCouple` |
| `instDecidableIsCanonH` | instance (def) | — (Decidable instance for `IsCanonH`; no source object) | `GNode`, `Garden`, `Garden.IsFlowerGarden`, `Garden.instDecidableIsFlowerGarden`, `IsCanonH`, `LayeredGarden`, `LayeredGarden.CanonCriterion`, `LayeredGarden.OnStem`, `LayeredGarden.instDecidableCanonCriterion`, `LayeredGarden.instDecidableOnStem`, `instFintypeGNode` |
| `LayeredGarden.attachNodes` | def | T Prop `canonequiv` | `GNode`, `Garden`, `LayeredGarden`, `LayeredGarden.parentLayer`, `instFintypeGNode` |
| `LayeredGarden.topOrder` | def | (section) T Def `defgtr`, L731–L732 | `GBranch`, `GBranch.toNode`, `Garden`, `LayeredGarden`, `TTree.Path`, `TTree.branching`, `instFintypeGBranch` |
| `LayeredGarden.AttachLinked` | def | (section) T Def `defgtr`, L731–L732 | `GLeaf`, `GNode`, `GNode.leavesBelow`, `Garden`, `LayeredGarden` |
| `LayeredGarden.AttachLinkedOn` | def | T Prop `canonequiv` | `GNode`, `Garden`, `LayeredGarden`, `LayeredGarden.AttachLinked`, `LayeredGarden.attachNodes` |
| `LayeredGarden.attachedOrder` | def | (section) T Def `defgtr`, L731–L732 | `GNode`, `GNode.orderBelow`, `Garden`, `LayeredGarden`, `LayeredGarden.AttachLinkedOn`, `LayeredGarden.attachNodes` |
| `LayeredGarden.IsTrunc` | def | T Def `defgtr`, L731–L732; T L2288 | `GNode`, `Garden`, `LayeredGarden`, `LayeredGarden.attachNodes`, `LayeredGarden.attachedOrder`, `LayeredGarden.topOrder` |

## `WaveB1-System.lean` (58 declarations)

| declaration | kind | TARGET / DH source | uses (frozen) |
|---|---|---|---|
| `jbr` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | — |
| `zpowSign` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | — |
| `coupling` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | — |
| `aNonlin` | def | T L553–L564 | `epsCoef`, `resFactor` |
| `IsASolution` | def | T (akeqn); L545–L564; WAVE-B §2.3.2 | `aNonlin` |
| `jointCumulant` | def | T Def `defcm` | — |
| `IsSymmetricEvent` | def | T L567–L569; WAVE-B §2.3.4 | — |
| `GBranch.IsChildOf` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | `GBranch`, `TTree`, `TTree.Path`, `TTree.branching` |
| `GBranch.IsParentOf` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | `GBranch`, `GLeaf`, `TTree`, `TTree.Path`, `TTree.branching`, `TTree.leaves` |
| `instDecidableIsParentOf` | instance (def) | — (Decidable instance for `IsParentOf`; no source object) | `GBranch`, `GBranch.IsParentOf`, `GLeaf`, `TTree`, `TTree.Path`, `TTree.branching`, `TTree.leaves` |
| `Garden.IsFlowerParent` | def | T (kqflower) | `GBranch`, `GBranch.IsParentOf`, `GLeaf`, `Garden`, `Garden.IsFlower` |
| `Garden.IsLoneParent` | def | T (timepairtree) | `GBranch`, `GBranch.IsParentOf`, `GLeaf`, `Garden`, `Garden.IsLone` |
| `instDecidableIsFlowerParent` | instance (def) | — (Decidable instance for `IsFlowerParent`; no source object) | `GBranch`, `GBranch.IsParentOf`, `GLeaf`, `Garden`, `Garden.IsFlower`, `Garden.IsFlowerParent`, `Garden.instDecidableIsFlower`, `instDecidableIsParentOf`, `instFintypeGLeaf` |
| `Garden.FreeBranch` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | `GBranch`, `Garden`, `Garden.IsFlowerParent` |
| `instFintypeFreeBranch` | instance (def) | — (Fintype instance for `FreeBranch`; no source object) | `GBranch`, `Garden`, `Garden.FreeBranch`, `Garden.IsFlowerParent`, `instDecidableIsFlowerParent`, `instFintypeGBranch` |
| `Garden.extendTime` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | `GBranch`, `Garden`, `Garden.FreeBranch`, `Garden.IsFlowerParent`, `instDecidableIsFlowerParent` |
| `phaseProd` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | `GBranch`, `GBranch.toNode`, `GNode`, `Garden`, `Garden.sign`, `instFintypeGBranch`, `omegaNode` |
| `phaseIntegral` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | `GBranch`, `GNode`, `Garden`, `Garden.FreeBranch`, `Garden.extendTime`, `instFintypeFreeBranch`, `phaseProd` |
| `kDomain` | def | T L674 | `GBranch`, `GBranch.IsChildOf`, `GBranch.toNode`, `Garden`, `Garden.IsLoneParent`, `LayeredGarden` |
| `inputLeaves` | def | T (defkg0) | `GLeaf`, `GLeaf.toNode`, `Garden`, `Garden.sign`, `MarkTag`, `instFintypeGLeaf` |
| `kernelK` | def | WAVE-B v2 §2.4.1; T Def `defkg` | `GBranch`, `GLeaf`, `GLeaf.toNode`, `GNode`, `GNode.root`, `Garden`, `Garden.IsFlower`, `Garden.order`, `Garden.zeta`, `GenDecoration`, `IsDecoration`, `LayeredGarden`, `cosetDecoration`, `coupling`, `epsDec`, `inputLeaves`, `kDomain`, `phaseIntegral` |
| `KG` | def | T (defkg0), L671–L674 | `GBranch`, `Garden`, `LayeredGarden`, `kernelK` |
| `KQstar` | def | T (timecouple), L678–L680 | `GBranch`, `Garden`, `LayeredGarden`, `TTree.Path`, `TTree.branching`, `kernelK` |
| `KQ` | def | T L678 | `KQstar`, `LayeredGarden` |
| `KTstar` | def | T (timepairtree), L681–L684 | `GBranch`, `Garden`, `LayeredGarden`, `kernelK` |
| `IsCanonGC` | def | (section) WAVE-B v2 §2.4.3 | `Garden`, `Garden.Irreducible`, `Garden.IsPlain`, `LayeredGarden`, `LayeredGarden.CanonCriterion` |
| `inputsF` | def | T (ansatz3), L703 | `WTParams` |
| `truncSum` | def | T (expgarden), L762; T (ansatz3); WAVE-B v2 §2.4.3; T Def `defgtr` | `Garden`, `Garden.order`, `IsCanonGC`, `KG`, `LayeredGarden`, `LayeredGarden.IsTrunc`, `WTParams`, `WTParams.N` |
| `truncSumC` | def | T L678 | `Garden.order`, `IsCanonC`, `KQ`, `LayeredGarden`, `LayeredGarden.IsTrunc`, `WTParams`, `WTParams.N` |
| `single` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | `TTree` |
| `IsBranchConsistent` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | `GBranch`, `GBranch.child`, `GBranch.toNode`, `GNode`, `TTree` |
| `TreeDecoration` | def | T Def `defdec` | `GNode`, `GNode.root`, `IsBranchConsistent`, `TTree`, `single` |
| `treeSign` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | `GNode`, `TTree`, `TTree.Path`, `TTree.nodes`, `nodeSign`, `single` |
| `treeTimeDomain` | def | T L714 | `GBranch`, `GBranch.IsChildOf`, `TTree`, `single` |
| `treeTerm` | def | T (defjt), L710–L714 | `GBranch`, `GBranch.child`, `GBranch.toNode`, `GLeaf`, `GLeaf.toNode`, `GNode`, `GNode.root`, `IsBranchConsistent`, `TTree`, `TTree.order`, `TreeDecoration`, `coupling`, `epsCoef`, `instFintypeGBranch`, `instFintypeGLeaf`, `resFactor`, `single`, `treeSign`, `treeTimeDomain`, `zpowSign` |
| `treeTermN` | def | T (defjn) | `TTree`, `TTree.order`, `treeTerm` |
| `aTr` | def | T (defbk) | `treeTermN` |
| `Slot` | abbrev | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | — |
| `slotCountB` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | `Slot` |
| `slotOrder` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | `Slot` |
| `Lop` | def | L717–L725; WAVE-B §2.5.2 | `Slot`, `aNonlin`, `slotCountB`, `slotOrder`, `treeTermN` |
| `partialMom` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | — |
| `iterPartial` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | `partialMom` |
| `SNorm` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | `iterPartial`, `jbr` |
| `SNormR` | def | T (normX2), L585 | `SNorm` |
| `timeFT` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | — |
| `maxBracketPow` | def | T (normX) | — |
| `XNorm` | def | T (normX), L581 | `iterPartial`, `jbr`, `maxBracketPow`, `timeFT` |
| `XNorm00` | def | T L589 | `maxBracketPow`, `timeFT` |
| `XNormRestr` | def | T (locnorm), L589 | `XNorm` |
| `XNorm00Restr` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | `XNorm00` |
| `ZNormOn` | def | T (defznorm), L594 | `jbr` |
| `ZNorm` | def | T L787 | `jbr` |
| `ZSpace` | def | T L787; WAVE-B §2.5.3 | `ZNorm` |
| `chi0` | def | T L617–L623 | — |
| `chi0Vec` | def | (file) WAVE-B §2.3; T L545–L564; T Def `defcm` | `chi0` |
| `wkeTaylorTerm` | def | T (wketaylor2), L753–L755 | — |
| `AnsatzAt` | def | T Prop `propansatz`; WAVE-B §2.6.7; WAVE-B §5 | `IsASolution`, `IsSymmetricEvent`, `SNormR`, `WTParams`, `WTParams.Lambda`, `WTParams.N`, `WTParams.R`, `WTParams.theta`, `inputsF`, `jbr`, `jointCumulant`, `truncSum`, `zpowSign` |

## `WaveB1-Statements.lean` (28 declarations)

| declaration | kind | TARGET / DH source | uses (frozen) |
|---|---|---|---|
| `IsGaussianData` | def | (file) WAVE-B v2 §4 | — |
| `IsBalancedSig` | def | (file) WAVE-B v2 §4 | — |
| `jbrProd` | def | (file) WAVE-B v2 §4 | `jbr` |
| `propansatz` | theorem | T Prop `propansatz`, L689–L707; WAVE-B v2 §4.1; T L819 | `AnsatzAt`, `IsGaussianData`, `WTParams`, `WTPrefix` |
| `RemainderBound` | def | T (ansatz2); L949–L951 | `SNormR`, `WTParams`, `WTParams.Lambda`, `WTParams.theta` |
| `coupleRemainder` | def | (file) WAVE-B v2 §4 | `WTParams`, `inputsF`, `truncSumC`, `wkeTaylorTerm` |
| `layergarden` | theorem | T Prop `layergarden`, L761–L779; T L776; WAVE-B v2 §4.2; T L762 | `IsBalancedSig`, `RemainderBound`, `SNorm`, `WTParams`, `WTParams.Lambda`, `WTParams.N`, `WTParams.R`, `WTParams.theta`, `WTPrefix`, `coupleRemainder`, `inputsF`, `jbrProd`, `truncSum` |
| `fixedpoint` | theorem | T Prop `fixedpoint`, L780–L794; WAVE-B v2 §4.3 | `AnsatzAt`, `IsGaussianData`, `IsSymmetricEvent`, `Lop`, `WTParams`, `WTParams.Lambda`, `WTParams.N`, `WTPrefix`, `ZNorm`, `ZSpace`, `aTr`, `jbr` |
| `nlsAkBridge` | theorem | T L540–L566; L817–L819; WAVE-B v2 §4.4 | `IsASolution`, `ZNormOn`, `jbr` |
| `wkeTaylor` | theorem | T (wketaylor); L752–L758; WAVE-B §5 | `SNormR`, `WTParams`, `WTParams.Lambda`, `WTPrefix`, `wkeTaylorTerm` |
| `NearLattice` | def | (file) WAVE-B v2 §4 | — |
| `countLemma` | theorem | T Lemma `countlem`, L2459–L2466 | `NearLattice` |
| `atomCountLemma` | theorem | T Lemma `atomcountlem`, L2467–L2478; T L2472; T L1293–L2339 | `NearLattice` |
| `eZ` | def | (file) WAVE-B v2 §4 | — |
| `quadExpSum2` | theorem | T Lemma `lemlayer2`, L970–L977; DH23 Lemma 6.6 | `chi0Vec`, `eZ` |
| `quadExpSum3` | theorem | T Lemma `lemcubic`, L1554–L1593 | `chi0Vec`, `eZ` |
| `LayeredGarden.BelowSet` | def | (file) WAVE-B v2 §4 | `GNode`, `GNode.IsDesc`, `Garden`, `LayeredGarden` |
| `LayeredGarden.instDecidableBelowSet` | instance (def) | — (Decidable instance for `BelowSet`; no source object) | `GNode`, `GNode.IsDesc`, `Garden`, `LayeredGarden`, `LayeredGarden.BelowSet`, `instDecidableIsDesc` |
| `LayeredGarden.leavesBelowSet` | def | (file) WAVE-B v2 §4 | `GLeaf`, `GLeaf.toNode`, `GNode`, `Garden`, `LayeredGarden`, `LayeredGarden.BelowSet`, `LayeredGarden.instDecidableBelowSet`, `instFintypeGLeaf` |
| `LayeredGarden.TopRegion` | def | T Def `defcanon` | `GNode`, `GNode.IsDesc`, `Garden`, `LayeredGarden`, `LayeredGarden.BelowSet` |
| `LayeredGarden.TopDecompWith` | def | T Def `defcanon` | `GLeaf`, `GLeaf.toNode`, `GNode`, `Garden`, `Garden.IsFlower`, `LayeredGarden`, `LayeredGarden.TopRegion`, `instDecidableEqGNode` |
| `LayeredGarden.TopDecomp` | def | (file) WAVE-B v2 §4 | `GNode`, `Garden`, `LayeredGarden`, `LayeredGarden.TopDecompWith`, `instDecidableEqGNode` |
| `LayeredGarden.IrreducibleAt` | def | T Def `defcanon` | `GNode`, `Garden`, `Garden.CompletelyPaired`, `LayeredGarden`, `LayeredGarden.leavesBelowSet` |
| `LayeredGarden.instDecidableIrreducibleAt` | instance (def) | — (Decidable instance for `IrreducibleAt`; no source object) | `GNode`, `Garden`, `Garden.CompletelyPaired`, `Garden.instDecidableCompletelyPaired`, `LayeredGarden`, `LayeredGarden.IrreducibleAt`, `LayeredGarden.leavesBelowSet`, `instDecidableEqGNode`, `instFintypeGNode` |
| `LayeredGarden.instDecidableTopRegion` | instance (def) | — (Decidable instance for `TopRegion`; no source object) | `GNode`, `GNode.IsDesc`, `Garden`, `LayeredGarden`, `LayeredGarden.BelowSet`, `LayeredGarden.TopRegion`, `LayeredGarden.instDecidableBelowSet`, `instDecidableEqGNode`, `instDecidableIsDesc`, `instFintypeGNode` |
| `LayeredGarden.CanonInd` | def | T Def `defcanon` | `GNode`, `GNode.Incomparable`, `Garden`, `Garden.CompletelyPaired`, `LayeredGarden`, `LayeredGarden.IrreducibleAt`, `LayeredGarden.TopDecomp`, `LayeredGarden.leavesBelowSet` |
| `LayeredGarden.roots` | def | (file) WAVE-B v2 §4 | `GNode`, `GNode.root`, `Garden`, `LayeredGarden`, `instDecidableEqGNode` |
| `canonicalCharacterization` | theorem | T Def `defcanon`, L657–L668; L888–L897; T Def `defgtr`; T L2288 | `GNode`, `GNode.Incomparable`, `Garden`, `Garden.IsFlowerGarden`, `Garden.IsPlain`, `IsCanonC`, `IsCanonG`, `IsCanonGC`, `IsCanonH`, `IsCouple`, `LayeredGarden`, `LayeredGarden.AttachLinkedOn`, `LayeredGarden.CanonInd`, `LayeredGarden.TopDecomp`, `LayeredGarden.TopDecompWith`, `LayeredGarden.attachNodes`, `LayeredGarden.roots`, `instDecidableEqGNode` |

## `WaveB1-Sumint.lean` (22 declarations)

| declaration | kind | TARGET / DH source | uses (frozen) |
|---|---|---|---|
| `SumintShape` | structure | (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6 | — |
| `SumintShape.n` | def | (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6 | `SumintShape` |
| `SumintShape.VIdx` | abbrev | (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6 | `SumintShape`, `SumintShape.n` |
| `SumintShape.M` | def | (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6 | `SumintShape`, `SumintShape.n` |
| `SumintShape.LexLt` | def | (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6 | `SumintShape`, `SumintShape.VIdx`, `SumintShape.n` |
| `SumintShape.TVar` | abbrev | (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6 | `SumintShape` |
| `SumintShape.xSlot` | def | (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6 | `SumintShape`, `SumintShape.VIdx`, `SumintShape.n` |
| `SumintShape.ySlot` | def | (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6 | `SumintShape`, `SumintShape.VIdx`, `SumintShape.n` |
| `SumintShape.x0Slot` | def | (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6 | `SumintShape`, `SumintShape.VIdx`, `SumintShape.n` |
| `SumintShape.uSlot` | def | (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6 | `SumintShape`, `SumintShape.VIdx`, `SumintShape.n` |
| `IsUnitCoeff` | def | (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6 | — |
| `SumintDatum` | structure | T L1595–L1625 | `IsUnitCoeff`, `SumintShape`, `SumintShape.TVar`, `SumintShape.VIdx`, `SumintShape.n` |
| `SumintDatum.kVec` | def | (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6 | `SumintDatum`, `SumintShape`, `SumintShape.VIdx`, `SumintShape.n` |
| `SumintDatum.ℓVec` | def | (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6 | `SumintDatum`, `SumintShape`, `SumintShape.VIdx`, `SumintShape.n` |
| `SumintDatum.Admissible` | def | T L1603–L1622 | `IsUnitCoeff`, `SNorm`, `SumintDatum`, `SumintShape`, `SumintShape.LexLt`, `SumintShape.M`, `SumintShape.TVar`, `SumintShape.VIdx`, `SumintShape.n` |
| `SumintDatum.timeDom` | def | T L1612–L1613 | `SumintDatum`, `SumintShape`, `SumintShape.TVar` |
| `SumintDatum.phase` | def | (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6 | `SumintDatum`, `SumintShape`, `SumintShape.TVar`, `SumintShape.VIdx`, `SumintShape.uSlot`, `SumintShape.x0Slot`, `SumintShape.xSlot`, `SumintShape.ySlot` |
| `SumintDatum.expr` | def | T L1608–L1611 | `SumintDatum`, `SumintDatum.kVec`, `SumintDatum.phase`, `SumintDatum.timeDom`, `SumintDatum.ℓVec`, `SumintShape`, `SumintShape.TVar`, `SumintShape.VIdx`, `SumintShape.n` |
| `SumintDatum.M₀` | def | T L1622–L1623 | `SumintDatum`, `SumintShape` |
| `SumintDatum.M₁` | def | (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6 | `SumintDatum`, `SumintShape`, `SumintShape.VIdx`, `SumintShape.n` |
| `WTPrefixA` | def | WAVE-B v2 §4.6 | `WTParams` |
| `sumint` | theorem | T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6 | `SumintDatum`, `SumintDatum.Admissible`, `SumintDatum.M₀`, `SumintDatum.M₁`, `SumintDatum.expr`, `SumintShape`, `SumintShape.M`, `SumintShape.TVar`, `WTParams`, `WTParams.N`, `WTPrefixA`, `XNorm00Restr`, `jbr` |

## `WaveB1-Flower.lean` (24 declarations)

| declaration | kind | TARGET / DH source | uses (frozen) |
|---|---|---|---|
| `Garden.extendFix` | def | (file) T L2327; T L2283–L2285; T L2331 | `GBranch`, `Garden` |
| `kDomainFix` | def | T L2331 | `GBranch`, `GBranch.IsChildOf`, `GBranch.toNode`, `Garden`, `LayeredGarden` |
| `phaseProdOff` | def | T L2327 | `GBranch`, `GBranch.toNode`, `GNode`, `Garden`, `Garden.sign`, `instDecidableEqGBranch`, `instFintypeGBranch`, `omegaNode` |
| `kernelKgen` | def | (file) T L2327; T L2283–L2285; T L2331 | `GBranch`, `GLeaf`, `GLeaf.toNode`, `GNode`, `GNode.root`, `Garden`, `Garden.IsFlower`, `Garden.extendFix`, `Garden.order`, `Garden.zeta`, `GenDecoration`, `IsDecoration`, `LayeredGarden`, `cosetDecoration`, `coupling`, `epsDec`, `inputLeaves`, `instFintypeGBranch`, `kDomainFix`, `phaseProdOff` |
| `FixPat` | inductive | T L2312 | — |
| `FixPat.decEq` | def | (file) T L2327; T L2283–L2285; T L2331 | `FixPat` |
| `instDecidableEqFixPat` | instance (def) | — (DecidableEq instance for `FixPat`; no source object) | `FixPat`, `FixPat.decEq` |
| `dyadicCut` | def | T L2283–L2285 | `chi0` |
| `LayeredGarden.topCountBelow` | def | T L2290 | `GBranch`, `GBranch.toNode`, `GNode`, `GNode.IsDesc`, `Garden`, `LayeredGarden`, `instDecidableIsDesc`, `instFintypeGBranch` |
| `LayeredGarden.IsFlowerNode` | def | (file) T L2327; T L2283–L2285; T L2331 | `GLeaf`, `GLeaf.toNode`, `GNode`, `Garden`, `Garden.IsFlower`, `LayeredGarden` |
| `LayeredGarden.IsTopLeaf` | def | T L2283 | `GNode`, `Garden`, `LayeredGarden`, `LayeredGarden.parentLayer`, `TTree.Path`, `TTree.leaves`, `TTree.nodes` |
| `LayeredGarden.fixPat` | def | T L2264 | `FixPat`, `GBranch`, `GBranch.IsChildOf`, `Garden`, `Garden.IsFlowerParent`, `LayeredGarden`, `TTree.Path`, `TTree.branching`, `instDecidableIsFlowerParent`, `instFintypeGBranch` |
| `LayeredGarden.PatValid` | def | (file) T L2327; T L2283–L2285; T L2331 | `FixPat`, `GBranch`, `GBranch.IsChildOf`, `Garden`, `Garden.IsFlowerParent`, `LayeredGarden`, `TTree.Path`, `TTree.branching` |
| `LayeredGarden.cutWeight1` | def | T L2283 | `GNode`, `Garden`, `LayeredGarden`, `LayeredGarden.IsFlowerNode`, `LayeredGarden.IsTopLeaf`, `TTree.Path`, `TTree.nodes`, `dyadicCut`, `instFintypeGNode` |
| `LayeredGarden.cutWeight2` | def | T L2285 | `GBranch`, `GBranch.toNode`, `GNode`, `Garden`, `Garden.IsFlowerParent`, `LayeredGarden`, `LayeredGarden.OnStem`, `LayeredGarden.instDecidableOnStem`, `TTree.Path`, `TTree.branching`, `dyadicCut`, `instDecidableIsFlowerParent`, `instFintypeGBranch`, `omegaNode` |
| `LayeredGarden.sibWeight` | def | T L2327 | `GBranch`, `GBranch.child`, `GNode`, `Garden`, `Garden.IsFlowerParent`, `LayeredGarden`, `LayeredGarden.IsFlowerNode`, `TTree.Path`, `TTree.branching`, `instDecidableIsFlowerParent`, `instFintypeGBranch` |
| `FlowerKind` | inductive | T (operatorxker); T L2273 | — |
| `TreeKind` | inductive | T (trterm); T L2312 | — |
| `LayeredGarden.FlowerKindOK` | def | T L2290 | `FlowerKind`, `GBranch`, `GBranch.child`, `GBranch.toNode`, `Garden`, `Garden.IsFlowerParent`, `LayeredGarden`, `LayeredGarden.IsFlowerNode`, `LayeredGarden.topCountBelow`, `LayeredGarden.topOrder`, `TTree.Path`, `TTree.branching` |
| `LayeredGarden.TreeKindOK` | def | T L2312 | `GBranch`, `GBranch.child`, `Garden`, `LayeredGarden`, `LayeredGarden.topCountBelow`, `LayeredGarden.topOrder`, `TTree.Path`, `TTree.branching`, `TreeKind` |
| `flowerSum` | def | T (flowerexp2), L2287–L2290 | `FixPat`, `FlowerKind`, `GBranch`, `GLeaf`, `GLeaf.toNode`, `GNode`, `Garden`, `Garden.IsFlower`, `Garden.IsFlowerParent`, `Garden.order`, `Garden.sign`, `IsCanonH`, `LayeredGarden`, `LayeredGarden.FlowerKindOK`, `LayeredGarden.PatValid`, `LayeredGarden.attachNodes`, `LayeredGarden.attachedOrder`, `LayeredGarden.cutWeight1`, `LayeredGarden.cutWeight2`, `LayeredGarden.fixPat`, `LayeredGarden.sibWeight`, `TTree.Path`, `TTree.leaves`, `WTParams`, `WTParams.N`, `instDecidableIsFlowerParent`, `instFintypeGBranch`, `kernelKgen` |
| `coupleSum` | def | T L2312 | `GBranch`, `GNode`, `Garden`, `Garden.order`, `IsCanonC`, `LayeredGarden`, `LayeredGarden.TreeKindOK`, `LayeredGarden.attachNodes`, `LayeredGarden.attachedOrder`, `TTree.Path`, `TTree.branching`, `TreeKind`, `WTParams`, `WTParams.N`, `kernelKgen` |
| `WTPrefixP` | def | T L2279–L2280 | `WTParams` |
| `layergardenFlower` | theorem | T Prop `flowerest1`, L2279–L2305; T L2306–L2338; WAVE-B v2 §4.15; T L2280; T (flowerest2); T (newnormn); T L2331; T L2312; T L2290 | `FixPat`, `FlowerKind`, `RemainderBound`, `TreeKind`, `WTParams`, `WTParams.Lambda`, `WTParams.N`, `WTPrefixP`, `coupleSum`, `flowerSum`, `inputsF`, `instDecidableEqFixPat`, `jbr` |

