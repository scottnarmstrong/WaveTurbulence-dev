/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.BotSrcOf
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.XSrcDataBot
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.XCrossOf

/-! # P4-W2 (session 20, 6B): the cross fields of `srcOf`

`botSrcOfX`: the `K2.XCross` of `botSrcOf` for `L₄ + 1 ≤ Lₕ`, from the selected-clamp data of the certified terms (`XSrcData`). -/

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

variable (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))

variable (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)

include hcan hel htc hcc hup hA E hN in
theorem botCertC_CJ_nonneg (b : BT w ι) : 0 ≤ (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CJ := by
  classical
  unfold botCertC
  split_ifs
  · unfold botCertC_at; exact (certCJ_pos E.hC E.hη _).le
  · unfold botCertC_at; exact (certCJ_pos E.hC E.hη _).le
  · exact zero_le_one

include hcan hel htc hcc hup hA E hN in
theorem botCertT_CJ_nonneg (b : BT w ι) : 0 ≤ (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CJ := by
  classical
  unfold botCertT
  split_ifs
  · unfold botCertT_at; exact (certCJ_pos E.hC E.hη _).le
  · unfold botCertT_at; exact (certCJ_pos E.hC E.hη _).le
  · exact zero_le_one

variable (R : RemEnv P κ) (CRq CRt : BT w ι → ℝ)
variable (hq0 : ∀ b, 0 < CRq b) (ht0 : ∀ b, 0 < CRt b)
variable (hgq : ∀ b, (b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) →
      P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
        layerCost Bh (zpObjC b.1 pstar) < CRq b)
variable (hgt : ∀ b, (b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) →
      P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
        layerCost Bh (zpObjT b.1 pstar) < CRt b)

include hcan hel htc hcc hup hA E hN in
/-- **The cross fields of `botSrcOf`.** -/
noncomputable def botSrcOfX (hη0 : 0 < P.η) (hη4 : P.η < 1 / 4) (hgap : zpQ4 A pstar + 1 ≤ zpQh A pstar) :
    K2.XCross P (botSrcOf (κ := κ) A c0 hA hcan hel htc hcc hup R CRq CRt hq0 ht0 hgq hgt E hN) :=
  xcrossOfData (botSrcOf (κ := κ) A c0 hA hcan hel htc hcc hup R CRq CRt hq0 ht0 hgq hgt E hN) hη0 hη4
    (L2 := zpQ2 A pstar) (L4 := zpQ4 A pstar) (Lh := zpQh A pstar) rfl rfl rfl (zpQ2_le_zpQ4 A hcan hel htc hcc) hgap
    (fun b _ => botCertC_CJ_nonneg A c0 hA hcan hel htc hcc hup E hN b)
    (fun b _ => botCertT_CJ_nonneg A c0 hA hcan hel htc hcc hup E hN b)
    (fun b hb i => by
      obtain ⟨q, fl, inst, Jc, h1, h2, h3, h4, h5, h6⟩ := botCertC_Jdata A c0 hA hcan hel htc hcc hup E hN hb i
      exact ⟨q, fl, inst, Jc, h1, h2, h3, h4, ((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo_J i).trans h5,
        ((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi_J i).trans ((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo_J i).symm,
        ((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi_M i).trans ((botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo_M i).symm, h6⟩)
    (fun b hb j => by
      obtain ⟨q, fl, inst, Jc, h1, h2, h3, h4, h5, h6⟩ := botCertT_Jdata A c0 hA hcan hel htc hcc hup E hN hb j
      exact ⟨q, fl, inst, Jc, h1, h2, h3, h4, ((botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo_J j).trans h5,
        ((botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi_J j).trans ((botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo_J j).symm,
        ((botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi_M j).trans ((botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo_M j).symm, h6⟩)

end WaveTurbulence.VineEstS5C.P4.W2
