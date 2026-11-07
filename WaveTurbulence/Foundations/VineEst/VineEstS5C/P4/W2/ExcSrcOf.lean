/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxCont2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxCont3
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceAll1
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.CertTerms
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcBnd
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.SFFam
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.Mem

/-! # P4-W2 (session 7, step 3i): the certified terms of a level as a `CertSrc`

`certSrcOf`: for the separated family `sepFamOf` of a level (`S.sQ b = (certC b).term`, `S.sT b = (certT b).term`), the `CertSrc` with the low window `winCl/winTl` (selector `false`)
and the high window `winCh/winTh` (selector `true`), `good b := b ∈ bsA ∪ bsB`, `cc b = (certC b).c`, `CJq b = (certC b).CJ`, ..., and the window facts of `ExcWin`. -/

@[expose] public section
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
/-- **The certified terms of a level as a `CertSrc`** (windows `L₄` = `false`, `Lₕ` = `true`). -/
noncomputable def certSrcOf :
    CertSrc P (sepFamOf (κ := κ) A sp0 hA hcan hel htc hcc E hN).S (zpQ2 A pstar : ℝ) (zpQ4 A pstar : ℝ) (zpQh A pstar : ℝ) where
  good b := b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA
  BQ s := cond s (winCh A pstar) (winCl A pstar)
  qQ s := cond s (cornH A pstar) (cornL A pstar)
  BT s := cond s (winTh A pstar) (winTl A pstar)
  qT s := cond s (cornH A pstar) (cornL A pstar)
  cc b := (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).c
  cT b := (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).c
  CJq b := (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CJ
  CMq b := (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CM
  CJt b := (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CJ
  CMt b := (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CM
  cq s b i := match s with
    | false => certC_loCT (κ := κ) A sp0 hA hcan hel htc hcc E hN b i
    | true => certC_hiCT (κ := κ) A sp0 hA hcan hel htc hcc E hN b i
  ct s b j := match s with
    | false => certT_loCT (κ := κ) A sp0 hA hcan hel htc hcc E hN b j
    | true => certT_hiCT (κ := κ) A sp0 hA hcan hel htc hcc E hN b j
  cq_c s b i := by
    cases s
    · exact (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo_c i
    · exact (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi_c i
  ct_c s b j := by
    cases s
    · exact (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo_c j
    · exact (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi_c j
  win_q b hb i := ⟨certC_loCT_win (κ := κ) A sp0 hA hcan hel htc hcc E hN hb i,
    certC_hiCT_win (κ := κ) A sp0 hA hcan hel htc hcc E hN hb i⟩
  win_t b hb j := ⟨certT_loCT_win (κ := κ) A sp0 hA hcan hel htc hcc E hN hb j,
    certT_hiCT_win (κ := κ) A sp0 hA hcan hel htc hcc E hN hb j⟩

end WaveTurbulence.VineEstS5C.P4.W2
