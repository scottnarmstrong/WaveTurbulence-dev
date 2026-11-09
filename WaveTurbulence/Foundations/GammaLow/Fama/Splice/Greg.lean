/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceGreg` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.Clocks
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeCoupleLayering
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceGreg


/-!
# REDSPLICE-DEF (S2a): the regular part of `g_sk` (TARGET L1962, R19 (3))

For an original layered garden `LG` decoded by the reconstruction data `D` of its skeleton `S` (the REGRED
decomposition), `gregOf` is the total incoherency index (TARGET Def `defcoh`) of the regular couples `Q_{(l,l')}`
attached at the source leaf pairs and of the regular trees `T_{(m)}` attached at the branches of `S`.  Each link
list is taken at the literal inflated attachment addresses of `ReconstructionData.attachmentPairs`, and counted
in the layered original garden by `LayeredGarden.incoherency`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open TTree WaveTurbulence WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- `g_reg`: the incoherency index of the regular couples and regular trees attached to the skeleton `S`
inside the layered garden `LG`. -/
@[expose] noncomputable def gregOf {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (LG : LayeredGarden w) : ℕ :=
  (∑ p : SourcePair S, LG.incoherency ((D.couple p).linksAt
      (inflatedPosition S D.tree (p.firstLeaf hS).toNode) (inflatedPosition S D.tree (p.secondLeaf hS).toNode))) +
  ∑ b : GBranch S.tree, LG.incoherency ((D.tree b).linksAt (nodeSign S.sig b.1)
      (inflatedPosition S D.tree b.toNode))

end WaveTurbulence.GammaLow.Fama
