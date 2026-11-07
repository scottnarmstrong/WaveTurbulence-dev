/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Final5

/-! # ZP-SURJ export: `ZpSurj` and `ZpLayers` of the twist class `Zp(A)`

The hypotheses `hcan, hel, htc, hcc` are the operation preconditions of `FamilyOperation` at the member `pstar` of `A`
(canonical start, source layer eligibility, coherence of the exceptional tree and couple).  They are needed: the skip
state `A ∈ Zp(A)` must have a coherent exceptional pair. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
variable {kind : Bool}
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5B WaveTurbulence.Stage1
  WaveTurbulence.LGSpine WaveTurbulence.ConjCoh

variable {w : ℕ} {ι : Type*} {p : ℕ} {pstar : ι} {J : Set ι} [DecidableEq ι] [Fintype ι]
variable (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
    (A.family.atoms pstar) (A.family.upper pstar))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))

include hcan hel htc hcc

/-- **`ZpSurj`** (R51): the twist class `Zp(A)` realizes the whole coherent pair carrier. -/
theorem zpSurj_of_state : ZpSurj p kind pstar J A sp0 hA :=
  ⟨zp_coherent A hcan hel htc hcc hA sp0, zp_twin A hcan hel htc hcc hA sp0, zp_carrier A hcan hel htc hcc hA sp0⟩

/-- **`ZpLayers`**: the layer numerals of the vine. -/
theorem zpLayers_of_state : ZpLayers p kind J A sp0 hA := zpLayers_of_start A hcan hel htc hcc hA sp0

end WaveTurbulence.ZpSurj
