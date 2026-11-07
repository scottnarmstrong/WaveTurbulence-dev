/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceEpsilon
/-! Transport of the literal spliced-kernel data along an actual molecular
isomorphism. All amplitude and gap arguments retain their concrete carriers. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.LGSpine
variable {w d : ℕ} {G H : Garden w}

/-- The actual darts incident to the transported hinge set correspond bijectively. -/
noncomputable def hingeDartsEquiv (F : MolIso G.molecule H.molecule)
    (hinges : Finset (GBranch G.tree)) : HingeDarts G hinges ≃ HingeDarts H (F.img hinges) :=
  F.d.subtypeEquiv (fun x => by
    rw [F.atom_comm, F.mate_comm, F.atom_comm]
    exact (or_congr (F.mem_img hinges _) (F.mem_img hinges _)).symm)

/-- A concrete local gap specification keeps its two designated incidences and gap kind. -/
noncomputable def mapLocalGapSpecification (F : MolIso G.molecule H.molecule)
    (v : GBranch H.tree) (q : LocalGapSpecification G (F.e.symm v)) : LocalGapSpecification H v where
  first := F.d q.first
  second := F.d q.second
  at_first := (F.atom_comm q.first).trans ((congrArg F.e q.at_first).trans (F.e.apply_symm_apply v))
  at_second := (F.atom_comm q.second).trans ((congrArg F.e q.at_second).trans (F.e.apply_symm_apply v))
  distinct := by
    intro h
    apply q.distinct
    apply F.d.injective
    exact h.trans (F.mate_comm q.first)
  opposite := by
    rw [F.out_comm, F.out_comm]
    exact q.opposite
  kind := q.kind

/-- Transport all actual data of the normalized spliced kernel. -/
noncomputable def mapSplicedKernelData (F : MolIso G.molecule H.molecule) (D : SplicedKernelData G d) :
    SplicedKernelData H d where
  layer v := D.layer (F.e.symm v)
  hinges := F.img D.hinges
  center x := D.center (F.d.symm x)
  edgeAmplitude x := D.edgeAmplitude (F.d.symm x)
  hingeAmplitude K := D.hingeAmplitude (fun x => K (hingeDartsEquiv F D.hinges x))
  gapSpecification v := (D.gapSpecification (F.e.symm v)).map (mapLocalGapSpecification F v)
  frequency v := D.frequency (F.e.symm v)
  rootTime := D.rootTime

end WaveTurbulence.VineA
