/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.BotCont2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.BotCont3
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceAll1

/-! # P4-W2 (session 7, step 3a): the certified terms as `CertTerm`s on the low and the high window

`botCertC_loCT`, `botCertC_hiCT`, `botCertT_loCT`, `botCertT_hiCT`: the `SepTC`s of `AuxCont2/3` with the identity set `V` of the certified expansion
(`ObjExp.term_of_mem`), in the form `pieceAll_*` consumes. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.LGSpine TTree WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1
  Set WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS5C.P4.Bot

set_option linter.unusedSectionVars false

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} [Fintype ι] [DecidableEq ι]
variable {P : WTParams} {κ : KPar P.d} {Bh : ℕ → ℝ}

variable (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family) (hA : IsPrimeGarden A.skeleton)
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
  (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
  (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)

include hcan hel htc hcc hup E hN in
/-- The lo window `CertTerm` of a certified couple term. -/
noncomputable def botCertC_loCT (b : BT w ι) (i : Fin (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).m) :
    CertTerm P (30 * P.d) (winCl A pstar) (cornL A pstar) (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CJ (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CM ((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).term i) :=
  { botCertC_loTC A c0 hA hcan hel htc hcc hup E hN b i with
    V := (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).V
    hV := fun s t h k => by
      rw [(botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).term_of_mem h i k]
      show sepTerm (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).c ((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).J i) ((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).M i) s t k = sepTerm ((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo i).c (((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo i).J) (((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo i).M) s t k
      rw [(botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo_c i, (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo_J i, (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo_M i] }

include hcan hel htc hcc hup E hN in
/-- The hi window `CertTerm` of a certified couple term. -/
noncomputable def botCertC_hiCT (b : BT w ι) (i : Fin (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).m) :
    CertTerm P (30 * P.d) (winCh A pstar) (cornH A pstar) (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CJ (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CM ((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).term i) :=
  { botCertC_hiTC A c0 hA hcan hel htc hcc hup E hN b i with
    V := (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).V
    hV := fun s t h k => by
      rw [(botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).term_of_mem h i k]
      show sepTerm (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).c ((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).J i) ((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).M i) s t k = sepTerm ((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi i).c (((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi i).J) (((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi i).M) s t k
      rw [(botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi_c i, (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi_J i, (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi_M i] }

include hcan hel htc hcc hup E hN in
/-- The lo window `CertTerm` of a certified tree term. -/
noncomputable def botCertT_loCT (b : BT w ι) (i : Fin (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).m) :
    CertTerm P (0) (winTl A pstar) (cornL A pstar) (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CJ (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CM ((botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).term i) :=
  { botCertT_loTC A c0 hA hcan hel htc hcc hup E hN b i with
    V := (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).V
    hV := fun s t h k => by
      rw [(botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).term_of_mem h i k]
      show sepTerm (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).c ((botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).J i) ((botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).M i) s t k = sepTerm ((botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo i).c (((botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo i).J) (((botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo i).M) s t k
      rw [(botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo_c i, (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo_J i, (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo_M i] }

include hcan hel htc hcc hup E hN in
/-- The hi window `CertTerm` of a certified tree term. -/
noncomputable def botCertT_hiCT (b : BT w ι) (i : Fin (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).m) :
    CertTerm P (0) (winTh A pstar) (cornH A pstar) (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CJ (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CM ((botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).term i) :=
  { botCertT_hiTC A c0 hA hcan hel htc hcc hup E hN b i with
    V := (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).V
    hV := fun s t h k => by
      rw [(botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).term_of_mem h i k]
      show sepTerm (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).c ((botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).J i) ((botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).M i) s t k = sepTerm ((botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi i).c (((botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi i).J) (((botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi i).M) s t k
      rw [(botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi_c i, (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi_J i, (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi_M i] }

end WaveTurbulence.VineEstS5C.P4.W2
