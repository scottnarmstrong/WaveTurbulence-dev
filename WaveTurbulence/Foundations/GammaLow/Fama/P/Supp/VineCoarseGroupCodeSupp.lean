/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineCoarseGroupCode` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VinePrescriptionSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VinePrimeStateSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import Mathlib.Logic.Equiv.Set
public import WaveTurbulence.Foundations.Vine.A.VineCoarseGroupCode
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Amend7
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Deg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Gap
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Greg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.IP
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Pairs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleHinge
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Famb.Molecule.TwistSourceFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
/-! Group names after the actual all-SG splice. The names distinguish every
original maximal group and retain the entire local prescription carrier.
This file does not assert ordered LF invariance of the normalizing garden. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open Finset Stage1 RedSplice Represents WaveTurbulence.GammaLow.FinalCount
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- Splicing never identifies atoms from distinct maximal groups. -/
theorem spliced_group_images_disjoint (σ : Prescription G)
    {S T : Finset (GBranch G.tree)} (hS : S ∈ maximalGroupsG γ G.molecule)
    (hT : T ∈ maximalGroupsG γ G.molecule) (hne : S ≠ T) :
    Disjoint (S.image ((stSt γ G σ).M.pi (stSt γ G σ).hcls))
      (T.image ((stSt γ G σ).M.pi (stSt γ G σ).hcls)) := by
  classical
  rw [Finset.disjoint_left]
  intro c hc hd
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hd
  have hr : repC (stSt γ G σ).cls y = repC (stSt γ G σ).cls x :=
    ((stSt γ G σ).M.ob_pi (stSt γ G σ).hcls y).symm.trans
      ((congrArg (stSt γ G σ).M.ob he).trans ((stSt γ G σ).M.ob_pi (stSt γ G σ).hcls x))
  exact Finset.disjoint_left.mp (groups_disjoint (Mole.garden_isMolecule G) hS hT hne)
    (repC_mem_group (Mole.garden_isMolecule G) σ hS hx)
    (hr ▸ repC_mem_group (Mole.garden_isMolecule G) σ hT hy)

/-- Even a wholly contracted group has a nonempty, distinct quotient support. -/
theorem spliced_group_image_injective (σ : Prescription G) :
    Function.Injective (fun S : {S // S ∈ maximalGroupsG γ G.molecule} =>
      S.1.image ((stSt γ G σ).M.pi (stSt γ G σ).hcls)) := by
  classical
  intro S T he
  apply Subtype.ext
  by_contra hn
  obtain ⟨x, hx⟩ := S.2.1.nonempty
  have hc := Finset.mem_image_of_mem ((stSt γ G σ).M.pi (stSt γ G σ).hcls) hx
  change S.1.image _ = T.1.image _ at he
  have hd := hc
  rw [he] at hd
  exact Finset.disjoint_left.mp (spliced_group_images_disjoint σ S.2 T.2 hn) hc hd


/-- A group's name is its whole image support, not a maximal group of the quotient. -/
noncomputable def coarseGroupCode (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w)
    (S : {S // S ∈ maximalGroupsG γ G.molecule}) : Finset (GBranch (coarseSplice γ G).G.tree) := by
  classical
  exact S.1.image ((coarseSplice γ G).M.pi (coarseSplice γ G).hcls)

/-- No two original maximal groups have the same normalized name. -/
theorem coarseGroupCode_injective (G : Garden w) : Function.Injective (coarseGroupCode γ G) :=
  spliced_group_image_injective (fun _ => .SG)




end WaveTurbulence.GammaLow.Fama.VineA
