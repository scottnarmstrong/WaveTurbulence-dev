/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RemSrcOf
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.XSrcData
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.XCrossOf

/-! # P4-W2 (session 20, 6B): the cross fields of `srcOf`

`srcOfX`: the `K2.XCross` of `srcOf` for `L₄ + 1 ≤ Lₕ`, from the selected-clamp data of the certified terms (`XSrcData`). -/

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

variable (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)

include hcan hel htc hcc E hN in
theorem certC_CJ_nonneg (b : ST w ι pstar J) : 0 ≤ (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CJ := by
  classical
  unfold certC
  split_ifs
  · unfold certC_at; exact (certCJ_pos E.hC E.hη _).le
  · unfold certC_at; exact (certCJ_pos E.hC E.hη _).le
  · exact zero_le_one

include hcan hel htc hcc E hN in
theorem certT_CJ_nonneg (b : ST w ι pstar J) : 0 ≤ (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CJ := by
  classical
  unfold certT
  split_ifs
  · unfold certT_at; exact (certCJ_pos E.hC E.hη _).le
  · unfold certT_at; exact (certCJ_pos E.hC E.hη _).le
  · exact zero_le_one

variable (R : RemEnv P κ) (CRq CRt : ST w ι pstar J → ℝ)
variable (hq0 : ∀ b, 0 < CRq b) (ht0 : ∀ b, 0 < CRt b)
variable (hgq : ∀ b, (b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) →
      P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
        layerCost Bh (zpObjC b.1 pstar) < CRq b)
variable (hgt : ∀ b, (b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) →
      P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
        layerCost Bh (zpObjT b.1 pstar) < CRt b)

include hcan hel htc hcc E hN in
/-- **The cross fields of `srcOf`.** -/
noncomputable def srcOfX (hη0 : 0 < P.η) (hη4 : P.η < 1 / 4) (hgap : zpQ4 A pstar + 1 ≤ zpQh A pstar) :
    K2.XCross P (srcOf (κ := κ) A sp0 hA hcan hel htc hcc R CRq CRt hq0 ht0 hgq hgt E hN) :=
  xcrossOfData (srcOf (κ := κ) A sp0 hA hcan hel htc hcc R CRq CRt hq0 ht0 hgq hgt E hN) hη0 hη4
    (L2 := zpQ2 A pstar) (L4 := zpQ4 A pstar) (Lh := zpQh A pstar) rfl rfl rfl (zpQ2_le_zpQ4 A hcan hel htc hcc) hgap
    (fun b _ => certC_CJ_nonneg A sp0 hA hcan hel htc hcc E hN b)
    (fun b _ => certT_CJ_nonneg A sp0 hA hcan hel htc hcc E hN b)
    (fun b hb i => by
      obtain ⟨q, fl, inst, Jc, h1, h2, h3, h4, h5, h6⟩ := certC_Jdata A sp0 hA hcan hel htc hcc E hN hb i
      exact ⟨q, fl, inst, Jc, h1, h2, h3, h4, ((certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo_J i).trans h5,
        ((certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi_J i).trans ((certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo_J i).symm,
        ((certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi_M i).trans ((certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo_M i).symm, h6⟩)
    (fun b hb j => by
      obtain ⟨q, fl, inst, Jc, h1, h2, h3, h4, h5, h6⟩ := certT_Jdata A sp0 hA hcan hel htc hcc E hN hb j
      exact ⟨q, fl, inst, Jc, h1, h2, h3, h4, ((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo_J j).trans h5,
        ((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi_J j).trans ((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo_J j).symm,
        ((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).hi_M j).trans ((certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).lo_M j).symm, h6⟩)

end WaveTurbulence.VineEstS5C.P4.W2
