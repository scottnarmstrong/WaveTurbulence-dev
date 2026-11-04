# FREEZE-LIST: Wave B tier B2 (B2-CL-18: consumer-reachable closure; after CL-13 to CL-17)

Generated from the compiled modules `WaveB2Draft.{Regular, Molecules, Statements}` by the Lean metaprogram
`FreezeList.lean` and `gen_freeze.py` (next to this file), adapted from B1's. Each row is one declaration of
the freeze set: its kind, the TARGET/DH source it cites, the other B2 declarations its type, body and
auxiliary proofs use, and the B1 and Wave A owners they use (which its frozen file must import). The source
comes from the docstring, else the enclosing section header `(section)`, else the module doc `(file)`.

**Scope (B2-CL-18, orchestrator ruling of 2026-11-04: small frozen surface).** The frozen consumers are B2.1
`regularAsymptotics`, B2.2 `incoherentDecay` and the characterization obligations of `WaveB2-Regular.lean` and
`WaveB2-Molecules.lean`. The freeze set is these theorems and **exactly the B2 declarations they reach**
(transitively, through types, bodies and auxiliary proofs). Everything else is held out with B2.3 (listed at the
end, 76 declarations):
- the B2.3 section of `WaveB2-Statements.lean` (13: `rigidity` and its 12 helpers);
- 43 declarations of Regular and Molecules used only by B2.3;
- 20 declarations used by no theorem at all: 11 instance-side declarations (`MiniTreeCode.equiv`, `Molecule.instDecidableDirected`, `Molecule.instDecidableEqGapKind`, `instDecidableDecodes`, `instDecidableDecodesTree`, `instDecidableEqMiniTreeCode`, `instDecidableEqVineType`, `instDecidableMatchesCouple`, `instDecidableMatchesPairedTree`, `instDecidableMatchesTreeCouple`, `instFintypeMiniTreeCode`) and 9 definitions of molecule operations that later packets consume (`IsDeviation`, `Molecule.IsAlphaCut`, `Molecule.IsCutData`, `Molecule.IsHyperBlock`, `Molecule.cut`, `Molecule.eraseBond`, `Molecule.sigma`, `VineType.IsBad`, `deviation`).

Checked by the generator: the freeze set is closed (no frozen declaration uses a held-out one).

**Counts.**
- **9 theorems**: the anchors B2.1 `regularAsymptotics` and B2.2 `incoherentDecay`, and the
  characterization obligations: `Garden.isMolecule_molecule`, `RegChain.exists_decodesTree`, `RegCpl.exists_decodes`, `RegCpl.size_eq_order`, `existsUnique_regChain_decodesTree`, `existsUnique_regCpl_decodes`, `regular_count_le`.
- **71 definitions**, **3 abbrevs**, **2 structures**, **3 inductives**.
- **1 instance**, a named `@[instance_reducible, instance] def` (B2-CL-16; B1 CL-16 convention). No `deriving` clause (B2-CL-12).

**Closure.** No frozen definition uses a proved theorem of the project: structure projections, constructors
and recursors are folded into their structure or inductive, and auxiliary `proof_n`/`match_n` constants into
their definition. The three files import only `WaveBDraft.System` (B1), `Mathlib.Analysis.Calculus.DSlope`
and each other.

## `WaveB2-Regular.lean` (71 declarations)

| declaration | kind | TARGET / DH source | uses (B2) | uses (B1 / Wave A) |
|---|---|---|---|---|
| `MiniCplCode` | abbrev | T Def `defreg`; WAVE-B §3.1 | — | — |
| `MiniCplCode.partner` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `MiniCplCode` | — |
| `MiniTreeCode` | structure | T Def `defreg`; WAVE-B §3.2 | — | — |
| `MiniTreeCode.lone` | def | WAVE-B §3.2 | `MiniTreeCode` | — |
| `MiniTreeCode.red` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `MiniTreeCode` | — |
| `MiniTreeCode.green` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `MiniTreeCode` | — |
| `slotSign` | def | T L627 | — | — |
| `node3` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | — | `TTree` |
| `addrExt` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | — | `TTree.Path` |
| `TTree.setAt` | def | (section) T Def `defreg`, L826–L829 | — | `TTree`, `TTree.Path` |
| `TTree.subtreeAt` | def | (section) T Def `defreg`, L826–L829 | — | `TTree`, `TTree.Path` |
| `RawCpl` | abbrev | (section) T Def `defreg`, L826–L829 | — | `TTree`, `TTree.Path` |
| `RawCpl.tree` | def | (section) T Def `defreg`, L826–L829 | `RawCpl` | `TTree`, `TTree.Path` |
| `RawCpl.mapTree` | def | (section) T Def `defreg`, L826–L829 | `RawCpl` | `TTree`, `TTree.Path` |
| `RawCpl.opA` | def | T Def `defreg`; WAVE-B §3.3 | `MiniCplCode`, `MiniCplCode.partner`, `RawCpl`, `RawCpl.mapTree`, `TTree.setAt`, `addrExt` | `TTree`, `TTree.Path` |
| `RawCpl.relocate` | def | (section) T Def `defreg`, L826–L829 | — | `TTree.Path` |
| `RawCpl.orient` | def | (section) T Def `defreg`, L826–L829 | — | `TTree.Path` |
| `RawCpl.opB` | def | T Def `defreg`; WAVE-B §3.3 | `MiniTreeCode`, `MiniTreeCode.green`, `MiniTreeCode.lone`, `MiniTreeCode.red`, `RawCpl`, `RawCpl.mapTree`, `RawCpl.orient`, `RawCpl.relocate`, `RawCpl.tree`, `TTree.setAt`, `TTree.subtreeAt`, `addrExt`, `node3`, `slotSign` | `TTree`, `TTree.Path`, `nodeSign` |
| `RawRegular` | inductive | T Def `defreg` | `MiniCplCode`, `MiniTreeCode`, `RawCpl`, `RawCpl.opA`, `RawCpl.opB`, `RawCpl.tree` | `TTree`, `TTree.Path`, `TTree.nodes` |
| `symmPairs` | def | (section) T Def `defreg`, L826–L829 | — | — |
| `Garden.MatchesCouple` | def | (section) T Def `defreg`, L826–L829 | `symmPairs` | `GLeaf`, `Garden`, `IsCouple`, `TTree`, `TTree.Path`, `TTree.leaves` |
| `Garden.MatchesTreeCouple` | def | (section) T Def `defreg`, L826–L829 | `RawCpl`, `RawCpl.tree`, `symmPairs` | `GLeaf`, `Garden`, `Garden.IsLone`, `Garden.instDecidableIsLone`, `TTree`, `TTree.Path`, `TTree.leaves` |
| `IsRegularCouple` | def | T Def `defreg` | `Garden.MatchesCouple`, `RawCpl`, `RawRegular` | `Garden`, `TTree`, `TTree.Path` |
| `IsRegularTree` | def | T Def `defreg` | `Garden.MatchesTreeCouple`, `RawCpl`, `RawRegular` | `Garden`, `IsPairedTree` |
| `RegCpl` | inductive | T Prop `propstructure`; WAVE-B §2.7 | `MiniCplCode`, `MiniTreeCode`, `RegChain` | — |
| `RegChain` | inductive | T Def `defregchain`; T L855 | `MiniCplCode`, `MiniTreeCode`, `RegCpl` | — |
| `treeOfSign` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | — | `TTree` |
| `RegCpl.trees` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `MiniCplCode`, `RegChain`, `RegChain.plug`, `RegCpl` | `TTree` |
| `RegChain.plug` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `MiniTreeCode`, `MiniTreeCode.lone`, `MiniTreeCode.red`, `RegChain`, `RegCpl`, `RegCpl.trees`, `node3`, `slotSign`, `treeOfSign` | `TTree` |
| `RegChain.lonePath` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `MiniTreeCode`, `MiniTreeCode.lone`, `RegChain`, `RegCpl` | `TTree.Path` |
| `RegCpl.pairsAt` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `MiniCplCode`, `MiniCplCode.partner`, `RegChain`, `RegChain.lonePath`, `RegChain.pairsAt`, `RegCpl`, `addrExt` | `TTree.Path` |
| `RegChain.pairsAt` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `MiniTreeCode`, `MiniTreeCode.green`, `MiniTreeCode.lone`, `MiniTreeCode.red`, `RegChain`, `RegChain.lonePath`, `RegCpl`, `RegCpl.pairsAt`, `addrExt`, `slotSign` | `TTree.Path` |
| `RegCpl.raw` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `RawCpl`, `RegCpl`, `RegCpl.pairsAt`, `RegCpl.trees` | `TTree`, `TTree.Path` |
| `RegCpl.Decodes` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `Garden.MatchesCouple`, `RegCpl`, `RegCpl.raw`, `RegCpl.trees` | `Garden`, `TTree`, `TTree.Path` |
| `Garden.MatchesPairedTree` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `symmPairs` | `GLeaf`, `Garden`, `MarkTag`, `TTree`, `TTree.Path`, `TTree.leaves` |
| `RegChain.DecodesTree` | def | T Prop `propstructure` | `Garden.MatchesPairedTree`, `RegChain`, `RegChain.lonePath`, `RegChain.pairsAt`, `RegChain.plug` | `Garden`, `TTree`, `TTree.Path` |
| `RegCpl.isType2` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `MiniCplCode`, `MiniTreeCode`, `RegChain`, `RegCpl` | — |
| `RegChain.isNil` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `MiniCplCode`, `MiniTreeCode`, `RegChain`, `RegCpl` | — |
| `RegCpl.wf` | def | T Prop `propstructure` | `MiniCplCode`, `RegChain`, `RegChain.isNil`, `RegChain.wf`, `RegCpl`, `RegCpl.isType2` | — |
| `RegChain.wf` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `MiniTreeCode`, `RegChain`, `RegCpl`, `RegCpl.wf` | — |
| `RegCpl.size` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `MiniCplCode`, `RegChain`, `RegChain.size`, `RegCpl` | — |
| `RegChain.size` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `MiniTreeCode`, `RegChain`, `RegCpl`, `RegCpl.size` | — |
| `RegCpl.exists_decodes` | theorem | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `IsRegularCouple`, `RegCpl`, `RegCpl.Decodes`, `RegCpl.wf` | `Garden` |
| `existsUnique_regCpl_decodes` | theorem | T Prop `propstructure` | `IsRegularCouple`, `RegCpl`, `RegCpl.Decodes`, `RegCpl.wf` | `Garden` |
| `RegChain.exists_decodesTree` | theorem | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `IsRegularTree`, `RegChain`, `RegChain.DecodesTree`, `RegChain.wf` | `Garden` |
| `existsUnique_regChain_decodesTree` | theorem | T Prop `propstructure` | `IsRegularTree`, `RegChain`, `RegChain.DecodesTree`, `RegChain.wf` | `Garden` |
| `RegCpl.size_eq_order` | theorem | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `RegCpl`, `RegCpl.Decodes`, `RegCpl.size` | `Garden`, `Garden.order` |
| `regular_count_le` | theorem | T Prop `propstructure`; L851–L869; DH21 Cor 4.9 | `IsRegularCouple`, `IsRegularTree` | `Garden`, `Garden.order` |
| `RegCpl.linksAt` | def | T Prop `deflink`, L874–L882 | `MiniCplCode`, `MiniCplCode.partner`, `RegChain`, `RegChain.linksAt`, `RegChain.lonePath`, `RegCpl`, `addrExt` | `TTree.Path` |
| `RegChain.linksAt` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `MiniTreeCode`, `MiniTreeCode.green`, `MiniTreeCode.lone`, `MiniTreeCode.red`, `RegChain`, `RegChain.lonePath`, `RegCpl`, `RegCpl.linksAt`, `addrExt`, `slotSign` | `TTree.Path` |
| `RegCpl.links` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `RegCpl`, `RegCpl.linksAt` | `TTree.Path` |
| `RegChain.treeLinks` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `RegChain`, `RegChain.linksAt` | `TTree.Path` |
| `chosenSet` | def | T Prop `deflink`; DH21 Def 4.11 | — | `TTree.Path` |
| `RegCpl.dominant` | def | T Prop `propstructure`, L859–L860; DH21 Def 4.17 | `MiniCplCode`, `RegChain`, `RegChain.dominant`, `RegCpl` | — |
| `RegChain.dominant` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `MiniTreeCode`, `RegChain`, `RegChain.isNil`, `RegCpl`, `RegCpl.dominant` | — |
| `IsSpecialSet` | def | T Def `defencpl`, L1127 | `addrExt` | `TTree.Path` |
| `instDecidableIsSpecialSet` | instance (def) | — (Decidable instance for `IsSpecialSet`; no source object) | `IsSpecialSet`, `addrExt` | `TTree.Path` |
| `specialSets` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `IsSpecialSet`, `chosenSet`, `instDecidableIsSpecialSet` | `TTree.Path` |
| `LayeredGarden.incoherency` | def | T Def `defcoh`, L885–L887 | — | `GBranch`, `GBranch.toNode`, `Garden`, `LayeredGarden`, `TTree.Path`, `TTree.branching`, `instFintypeGBranch` |
| `RegCpl.JB` | def | T Prop `regref2` | `MiniCplCode`, `RegChain`, `RegChain.JBchain`, `RegCpl` | — |
| `RegChain.JBchain` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | `MiniTreeCode`, `RegChain`, `RegCpl`, `RegCpl.JB` | — |
| `RegChain.JBtree` | def | T (regref2-2); T L1185–L1188; T Def `defkg`, L682–L684 | `RegChain`, `RegChain.JBchain` | — |
| `resIntegral` | def | T (regref3-0); WAVE-B §2.8 | — | `Mom` |
| `resSlice` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | — | `Mom` |
| `pvResonantIntegral` | def | T (regref3-3); WAVE-B §2.8 | `resSlice` | `Mom` |
| `RegCpl.Mstar` | def | T Prop `regref3` | `MiniCplCode`, `MiniCplCode.partner`, `RegChain`, `RegChain.Nstar`, `RegChain.lonePath`, `RegCpl`, `addrExt`, `resIntegral` | `Mom`, `TTree.Path` |
| `RegChain.Nstar` | def | T (regref3-2); T (regref3-4) | `MiniTreeCode`, `MiniTreeCode.green`, `MiniTreeCode.lone`, `MiniTreeCode.red`, `RegChain`, `RegChain.lonePath`, `RegCpl`, `RegCpl.Mstar`, `addrExt`, `pvResonantIntegral`, `resIntegral`, `slotSign` | `Mom`, `TTree.Path` |
| `zetaOfTrees` | def | (file) WAVE-B v2 §2.7; L826–L829; L848–L850 | — | `TTree`, `TTree.Path`, `TTree.branching`, `TTree.pathSign` |
| `specialWeight` | def | T (regref1-3); DH21 Lemma 7.3; DH21 Lemma 5.8 | — | `TTree.Path`, `nodeSign` |
| `RegCpl.app` | def | T (regref1-3); WAVE-B §2.7 | `RegCpl`, `RegCpl.JB`, `RegCpl.Mstar`, `RegCpl.dominant`, `RegCpl.links`, `RegCpl.size`, `RegCpl.trees`, `specialSets`, `specialWeight`, `zetaOfTrees` | `Mom`, `TTree`, `TTree.Path` |
| `RegChain.app` | def | T (regref1-3) | `RegChain`, `RegChain.JBtree`, `RegChain.Nstar`, `RegChain.dominant`, `RegChain.plug`, `RegChain.size`, `RegChain.treeLinks`, `specialSets`, `specialWeight`, `zetaOfTrees` | `Mom`, `TTree`, `TTree.Path` |

## `WaveB2-Molecules.lean` (12 declarations)

| declaration | kind | TARGET / DH source | uses (B2) | uses (B1 / Wave A) |
|---|---|---|---|---|
| `Molecule` | structure | T Def `defmol`, L1295 | — | — |
| `Molecule.dartsAt` | def | (file) WAVE-B v2 §2.9; T Def `defmol`; L1297–L1302 | `Molecule` | — |
| `Molecule.deg` | def | (file) WAVE-B v2 §2.9; T Def `defmol`; L1297–L1302 | `Molecule`, `Molecule.dartsAt` | — |
| `Molecule.outdeg` | def | (file) WAVE-B v2 §2.9; T Def `defmol`; L1297–L1302 | `Molecule`, `Molecule.dartsAt` | — |
| `Molecule.indeg` | def | (file) WAVE-B v2 §2.9; T Def `defmol`; L1297–L1302 | `Molecule`, `Molecule.dartsAt` | — |
| `Molecule.Adj` | def | (file) WAVE-B v2 §2.9; T Def `defmol`; L1297–L1302 | `Molecule` | — |
| `Molecule.SameComponent` | def | (file) WAVE-B v2 §2.9; T Def `defmol`; L1297–L1302 | `Molecule`, `Molecule.Adj` | — |
| `Molecule.IsMolecule` | def | T Def `defmol` | `Molecule`, `Molecule.SameComponent`, `Molecule.deg`, `Molecule.indeg`, `Molecule.outdeg` | — |
| `GNode.parent` | def | (section) T Def `defcplmol`, L1297–L1302 | — | `GBranch`, `GNode`, `TTree`, `TTree.Path`, `TTree.branching`, `TTree.nodes`, `TTree.pre` |
| `GardenDart` | abbrev | T L1316 | — | `GBranch`, `GLeaf`, `Garden`, `MarkTag`, `TTree.Path`, `TTree.branching`, `TTree.leaves` |
| `Garden.molecule` | def | T Def `defcplmol` | `GNode.parent`, `GardenDart`, `Molecule` | `GBranch`, `GBranch.toNode`, `GLeaf`, `GLeaf.toNode`, `Garden`, `Garden.sign`, `MarkTag`, `TTree.Path`, `TTree.branching`, `TTree.leaves`, `instFintypeGBranch`, `nodeSign` |
| `Garden.isMolecule_molecule` | theorem | T Prop `propcplmol`, L1303–L1306 | `Garden.molecule`, `GardenDart`, `Molecule.IsMolecule` | `GBranch`, `GLeaf`, `Garden`, `MarkTag`, `TTree.Path`, `TTree.branching`, `TTree.leaves`, `instDecidableEqGBranch`, `instFintypeGBranch`, `instFintypeGLeaf` |

## `WaveB2-Statements.lean` (6 declarations)

| declaration | kind | TARGET / DH source | uses (B2) | uses (B1 / Wave A) |
|---|---|---|---|---|
| `timeBox` | def | (file) WAVE-B v2 §4.11; T Prop `regref1`; L1145–L1232 | — | — |
| `timeBoxGt` | def | (file) WAVE-B v2 §4.11; T Prop `regref1`; L1145–L1232 | `timeBox` | — |
| `InputRemainder` | def | T L1033 | — | `Mom`, `SNormR`, `WTParams`, `WTParams.theta` |
| `regBound` | def | (file) WAVE-B v2 §4.11; T Prop `regref1`; L1145–L1232 | — | `WTParams`, `WTParams.gamma1` |
| `regularAsymptotics` | theorem | L1145–L1232; WAVE-B v2 §4.11; T (regref1-3); DH21 Lemma 7.3 | `InputRemainder`, `RegChain`, `RegChain.DecodesTree`, `RegChain.JBtree`, `RegChain.Nstar`, `RegChain.app`, `RegChain.dominant`, `RegChain.lonePath`, `RegChain.size`, `RegChain.treeLinks`, `RegChain.wf`, `RegCpl`, `RegCpl.Decodes`, `RegCpl.JB`, `RegCpl.Mstar`, `RegCpl.app`, `RegCpl.dominant`, `RegCpl.links`, `RegCpl.size`, `RegCpl.wf`, `regBound`, `specialSets`, `timeBox`, `timeBoxGt` | `GNode`, `Garden`, `KQstar`, `KTstar`, `LayeredGarden`, `Mom`, `SNormR`, `TTree.Path`, `TTree.nodes`, `WTParams`, `WTParams.N`, `WTPrefix`, `XNorm00Restr`, `XNormRestr`, `wkeTaylorTerm` |
| `incoherentDecay` | theorem | T Prop `proplayer1`, L953–L956; L946–L951; WAVE-B v2 §4.12; T Def `defkg` | `InputRemainder`, `LayeredGarden.incoherency`, `RegChain`, `RegChain.DecodesTree`, `RegChain.lonePath`, `RegChain.size`, `RegChain.treeLinks`, `RegChain.wf`, `RegCpl`, `RegCpl.Decodes`, `RegCpl.links`, `RegCpl.size`, `RegCpl.wf`, `regBound`, `timeBox`, `timeBoxGt` | `GNode`, `GNode.root`, `Garden`, `KQstar`, `KTstar`, `LayeredGarden`, `Mom`, `TTree.Path`, `TTree.nodes`, `WTParams`, `WTParams.N`, `WTPrefix`, `XNormRestr`, `inputsF` |

## Held out with B2.3 (76 declarations; not in this freeze)

**The B2.3 section of `WaveB2-Statements.lean`** (13): `AtomLabel.IsAlpha`, `Molecule.ABLinked`, `Molecule.DecorationHyp`, `Molecule.FinalShape`, `Molecule.IsConnected`, `Molecule.IsPerfect`, `Molecule.IsTame`, `Molecule.alphaFactor`, `Molecule.epsDefect`, `Molecule.numBeta`, `Molecule.perfectIndicator`, `Molecule.rigidityRHS`, `rigidity`.

**Used only by B2.3** (43): `AtomLabel`, `Molecule.Directed`, `Molecule.Gamma`, `Molecule.GapKind`, `Molecule.GroupConnected`, `Molecule.InGroup`, `Molecule.IsBlock`, `Molecule.IsBlockGap`, `Molecule.IsDecoration`, `Molecule.IsLadder`, `Molecule.IsLadderGap`, `Molecule.IsLadderSet`, `Molecule.IsRestricted`, `Molecule.IsVine`, `Molecule.bonds`, `Molecule.bondsBetween`, `Molecule.circuitRank`, `Molecule.countA`, `Molecule.countE`, `Molecule.dartSign`, `Molecule.degIn`, `Molecule.ends`, `Molecule.gapAt`, `Molecule.gapKind`, `Molecule.groupBonds`, `Molecule.inIn`, `Molecule.instDecidableInGroup`, `Molecule.kvec`, `Molecule.ladderAtoms`, `Molecule.ladderLength`, `Molecule.ladderWeight`, `Molecule.maximalLadders`, `Molecule.numComponents`, `Molecule.numFree`, `Molecule.numLadders`, `Molecule.outIn`, `Molecule.rho`, `VineTemplate`, `VineType`, `VineType.expand`, `VineType.template`, `insertRungs`, `railBonds`.

**Used by no theorem** (20): `IsDeviation`, `MiniTreeCode.equiv`, `Molecule.IsAlphaCut`, `Molecule.IsCutData`, `Molecule.IsHyperBlock`, `Molecule.cut`, `Molecule.eraseBond`, `Molecule.instDecidableDirected`, `Molecule.instDecidableEqGapKind`, `Molecule.sigma`, `VineType.IsBad`, `deviation`, `instDecidableDecodes`, `instDecidableDecodesTree`, `instDecidableEqMiniTreeCode`, `instDecidableEqVineType`, `instDecidableMatchesCouple`, `instDecidableMatchesPairedTree`, `instDecidableMatchesTreeCouple`, `instFintypeMiniTreeCode`.

