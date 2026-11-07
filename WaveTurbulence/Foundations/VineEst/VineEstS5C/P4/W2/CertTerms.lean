/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxCont2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxCont3
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceAll1

/-! # P4-W2 (session 7, step 3a): the certified terms as `CertTerm`s on the low and the high window

`certC_loCT`, `certC_hiCT`, `certT_loCT`, `certT_hiCT`: the `SepTC`s of `AuxCont2/3` with the identity set `V` of the certified expansion
(`ObjExp.term_of_mem`), in the form `pieceAll_*` consumes. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.LGSpine TTree WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1
  Set WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3

set_option linter.unusedSectionVars false

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]
variable {P : WTParams} {κ : KPar P.d} {Bh : ℕ → ℝ}

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
  (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)

include hcan hel htc hcc E hN in
/-- The lo window `CertTerm` of a certified couple term. -/
noncomputable def certC_loCT (b : ST w ι pstar J) (i : Fin (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).m) :
    CertTerm P (30 * P.d) (winCl A pstar) (cornL A pstar) (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CJ (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CM ((certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).term i) :=
  { certC_loTC A sp0 hA hcan hel htc hcc E hN b i with
    V := (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).V
    hV := fun s t h k => by
      rw [(certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).term_of_mem h i k]
      show sepTerm (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).c ((certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).J i) ((certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).M i) s t k = sepTerm ((certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo i).c (((certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo i).J) (((certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo i).M) s t k
      rw [(certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo_c i, (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo_J i, (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo_M i] }

include hcan hel htc hcc E hN in
/-- The hi window `CertTerm` of a certified couple term. -/
noncomputable def certC_hiCT (b : ST w ι pstar J) (i : Fin (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).m) :
    CertTerm P (30 * P.d) (winCh A pstar) (cornH A pstar) (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CJ (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CM ((certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).term i) :=
  { certC_hiTC A sp0 hA hcan hel htc hcc E hN b i with
    V := (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).V
    hV := fun s t h k => by
      rw [(certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).term_of_mem h i k]
      show sepTerm (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).c ((certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).J i) ((certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).M i) s t k = sepTerm ((certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi i).c (((certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi i).J) (((certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi i).M) s t k
      rw [(certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi_c i, (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi_J i, (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi_M i] }

include hcan hel htc hcc E hN in
/-- The lo window `CertTerm` of a certified tree term. -/
noncomputable def certT_loCT (b : ST w ι pstar J) (i : Fin (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).m) :
    CertTerm P (0) (winTl A pstar) (cornL A pstar) (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CJ (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CM ((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).term i) :=
  { certT_loTC A sp0 hA hcan hel htc hcc E hN b i with
    V := (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).V
    hV := fun s t h k => by
      rw [(certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).term_of_mem h i k]
      show sepTerm (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).c ((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).J i) ((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).M i) s t k = sepTerm ((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo i).c (((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo i).J) (((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo i).M) s t k
      rw [(certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo_c i, (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo_J i, (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo_M i] }

include hcan hel htc hcc E hN in
/-- The hi window `CertTerm` of a certified tree term. -/
noncomputable def certT_hiCT (b : ST w ι pstar J) (i : Fin (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).m) :
    CertTerm P (0) (winTh A pstar) (cornH A pstar) (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CJ (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CM ((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).term i) :=
  { certT_hiTC A sp0 hA hcan hel htc hcc E hN b i with
    V := (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).V
    hV := fun s t h k => by
      rw [(certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).term_of_mem h i k]
      show sepTerm (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).c ((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).J i) ((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).M i) s t k = sepTerm ((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi i).c (((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi i).J) (((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi i).M) s t k
      rw [(certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi_c i, (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi_J i, (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi_M i] }

end WaveTurbulence.VineEstS5C.P4.W2
