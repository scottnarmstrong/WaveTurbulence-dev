# FREEZE-LIST: Wave B tier B2 (B2-CL-20: closure of B2.1 and B2.2; after CL-13 to CL-19)

Generated from the compiled modules `WaveB2Draft.{Regular, Molecules, Statements}` by the Lean metaprogram
`FreezeList.lean` and `gen_freeze.py` (next to this file), adapted from B1's. Each row is one declaration of
the freeze set: its kind, the TARGET/DH source it cites, the other B2 declarations its type, body and
auxiliary proofs use, and the B1 and Wave A owners they use (which its frozen file must import). The source
comes from the docstring, else the enclosing section header `(section)`, else the module doc `(file)`.

**Scope (B2-CL-20; orchestrator rulings of 2026-11-04: small frozen surface, ~20-anchor budget).** The only
theorem anchors are B2.1 `regularAsymptotics` and B2.2 `incoherentDecay`. The freeze set is these two theorems
and **exactly the B2 declarations they reach** (transitively, through types, bodies and auxiliary proofs).
Everything else is held out (listed at the end, 106 declarations):
- the B2.3 section of `WaveB2-Statements.lean` (13: `rigidity` and its 12 helpers);
- the 7 characterization lemmas of Regular §4 and Molecules (non-frozen, editable targets; CL-20) and the 15 declarations only they reach;
- 51 declarations used only by B2.3;
- 20 declarations used by no theorem at all.

Checked by the generator: the freeze set is closed (no frozen declaration uses a held-out one).

**Counts.**
- **2 theorems**: the anchors B2.1 `regularAsymptotics` and B2.2 `incoherentDecay`.
- **51 definitions**, **2 abbrevs**, **1 structure**, **2 inductives**.
- **1 instance**, a named `@[instance_reducible, instance] def` (B2-CL-16; B1 CL-16 convention). No `deriving` clause (B2-CL-12).

**Closure.** No frozen definition uses a proved theorem of the project: structure projections, constructors
and recursors are folded into their structure or inductive, and auxiliary `proof_n`/`match_n` constants into
their definition. The frozen declarations lie in `WaveB2-Regular.lean` and `WaveB2-Statements.lean`, which
import only `WaveBDraft.System` (B1), `Mathlib.Analysis.Calculus.DSlope` and each other.

## `WaveB2-Regular.lean` (53 declarations)

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
| `RawCpl` | abbrev | (section) T Def `defreg`, L826–L829 | — | `TTree`, `TTree.Path` |
| `symmPairs` | def | (section) T Def `defreg`, L826–L829 | — | — |
| `Garden.MatchesCouple` | def | (section) T Def `defreg`, L826–L829 | `symmPairs` | `GLeaf`, `Garden`, `IsCouple`, `TTree`, `TTree.Path`, `TTree.leaves` |
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

## `WaveB2-Molecules.lean` (no frozen declarations)

## `WaveB2-Statements.lean` (6 declarations)

| declaration | kind | TARGET / DH source | uses (B2) | uses (B1 / Wave A) |
|---|---|---|---|---|
| `timeBox` | def | (file) WAVE-B v2 §4.11; T Prop `regref1`; L1145–L1232 | — | — |
| `timeBoxGt` | def | (file) WAVE-B v2 §4.11; T Prop `regref1`; L1145–L1232 | `timeBox` | — |
| `InputRemainder` | def | T L1033 | — | `Mom`, `SNormR`, `WTParams`, `WTParams.theta` |
| `regBound` | def | (file) WAVE-B v2 §4.11; T Prop `regref1`; L1145–L1232 | — | `WTParams`, `WTParams.gamma1` |
| `regularAsymptotics` | theorem | L1145–L1232; WAVE-B v2 §4.11; T (regref1-3); DH21 Lemma 7.3 | `InputRemainder`, `RegChain`, `RegChain.DecodesTree`, `RegChain.JBtree`, `RegChain.Nstar`, `RegChain.app`, `RegChain.dominant`, `RegChain.lonePath`, `RegChain.size`, `RegChain.treeLinks`, `RegChain.wf`, `RegCpl`, `RegCpl.Decodes`, `RegCpl.JB`, `RegCpl.Mstar`, `RegCpl.app`, `RegCpl.dominant`, `RegCpl.links`, `RegCpl.size`, `RegCpl.wf`, `regBound`, `specialSets`, `timeBox`, `timeBoxGt` | `GNode`, `Garden`, `KQstar`, `KTstar`, `LayeredGarden`, `Mom`, `SNormR`, `TTree.Path`, `TTree.nodes`, `WTParams`, `WTParams.N`, `WTPrefix`, `XNorm00Restr`, `XNormRestr`, `wkeTaylorTerm` |
| `incoherentDecay` | theorem | T Prop `proplayer1`, L953–L956; L946–L951; WAVE-B v2 §4.12; T Def `defkg` | `InputRemainder`, `LayeredGarden.incoherency`, `RegChain`, `RegChain.DecodesTree`, `RegChain.lonePath`, `RegChain.size`, `RegChain.treeLinks`, `RegChain.wf`, `RegCpl`, `RegCpl.Decodes`, `RegCpl.links`, `RegCpl.size`, `RegCpl.wf`, `regBound`, `timeBox`, `timeBoxGt` | `GNode`, `GNode.root`, `Garden`, `KQstar`, `KTstar`, `LayeredGarden`, `Mom`, `TTree.Path`, `TTree.nodes`, `WTParams`, `WTParams.N`, `WTPrefix`, `XNormRestr`, `inputsF` |

## Held out (106 declarations; not in this freeze)

**The B2.3 section of `WaveB2-Statements.lean`** (13): `AtomLabel.IsAlpha`, `Molecule.ABLinked`, `Molecule.DecorationHyp`, `Molecule.FinalShape`, `Molecule.IsConnected`, `Molecule.IsPerfect`, `Molecule.IsTame`, `Molecule.alphaFactor`, `Molecule.epsDefect`, `Molecule.numBeta`, `Molecule.perfectIndicator`, `Molecule.rigidityRHS`, `rigidity`.

**Characterization lemmas (non-frozen, CL-20)** (7): `Garden.isMolecule_molecule`, `RegChain.exists_decodesTree`, `RegCpl.exists_decodes`, `RegCpl.size_eq_order`, `existsUnique_regChain_decodesTree`, `existsUnique_regCpl_decodes`, `regular_count_le`.

**Reached only by the characterization lemmas** (15): `GNode.parent`, `Garden.MatchesTreeCouple`, `Garden.molecule`, `GardenDart`, `IsRegularCouple`, `IsRegularTree`, `RawCpl.mapTree`, `RawCpl.opA`, `RawCpl.opB`, `RawCpl.orient`, `RawCpl.relocate`, `RawCpl.tree`, `RawRegular`, `TTree.setAt`, `TTree.subtreeAt`.

**Used only by B2.3** (51): `AtomLabel`, `Molecule`, `Molecule.Adj`, `Molecule.Directed`, `Molecule.Gamma`, `Molecule.GapKind`, `Molecule.GroupConnected`, `Molecule.InGroup`, `Molecule.IsBlock`, `Molecule.IsBlockGap`, `Molecule.IsDecoration`, `Molecule.IsLadder`, `Molecule.IsLadderGap`, `Molecule.IsLadderSet`, `Molecule.IsMolecule`, `Molecule.IsRestricted`, `Molecule.IsVine`, `Molecule.SameComponent`, `Molecule.bonds`, `Molecule.bondsBetween`, `Molecule.circuitRank`, `Molecule.countA`, `Molecule.countE`, `Molecule.dartSign`, `Molecule.dartsAt`, `Molecule.deg`, `Molecule.degIn`, `Molecule.ends`, `Molecule.gapAt`, `Molecule.gapKind`, `Molecule.groupBonds`, `Molecule.inIn`, `Molecule.indeg`, `Molecule.instDecidableInGroup`, `Molecule.kvec`, `Molecule.ladderAtoms`, `Molecule.ladderLength`, `Molecule.ladderWeight`, `Molecule.maximalLadders`, `Molecule.numComponents`, `Molecule.numFree`, `Molecule.numLadders`, `Molecule.outIn`, `Molecule.outdeg`, `Molecule.rho`, `VineTemplate`, `VineType`, `VineType.expand`, `VineType.template`, `insertRungs`, `railBonds`.

**Used by no theorem** (20): `IsDeviation`, `MiniTreeCode.equiv`, `Molecule.IsAlphaCut`, `Molecule.IsCutData`, `Molecule.IsHyperBlock`, `Molecule.cut`, `Molecule.eraseBond`, `Molecule.instDecidableDirected`, `Molecule.instDecidableEqGapKind`, `Molecule.sigma`, `VineType.IsBad`, `deviation`, `instDecidableDecodes`, `instDecidableDecodesTree`, `instDecidableEqMiniTreeCode`, `instDecidableEqVineType`, `instDecidableMatchesCouple`, `instDecidableMatchesPairedTree`, `instDecidableMatchesTreeCouple`, `instFintypeMiniTreeCode`.

