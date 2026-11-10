/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RemSrcOf

/-! # P4-W2 (session 18, step 4c-1): the size of a good bundle member

`certC_good_vals`, `certT_good_vals`: for a good index the certified couple/tree has `c = δ^n`, `CJ = certCJ P n`, `CM = certCM P n cost` with `n = size/2` and `cost = layerCost Bh (zpObj..)`.
`sz_good`: `szQ b · szT b = 4 TR² C₁⁴ (C₁² δ)^{zpN} · (cost_C cost_T)` (`zp_half_sizes`).
-/

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
open Classical in
theorem certC_good_vals {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) :
    (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).c = P.δ ^ ((zpCodeC b.1 pstar).size / 2) ∧
    (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CJ = certCJ P ((zpCodeC b.1 pstar).size / 2) ∧
    (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CM = certCM P ((zpCodeC b.1 pstar).size / 2) (layerCost Bh (zpObjC b.1 pstar)) := by
  unfold certC
  rw [dif_pos hb]
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩


include hcan hel htc hcc E hN in
open Classical in
theorem certT_good_vals {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) :
    (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).c = P.δ ^ ((zpCodeT b.1 pstar).size / 2) ∧
    (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CJ = certCJ P ((zpCodeT b.1 pstar).size / 2) ∧
    (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CM = certCM P ((zpCodeT b.1 pstar).size / 2) (layerCost Bh (zpObjT b.1 pstar)) := by
  unfold certT
  rw [dif_pos hb]
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

end WaveTurbulence.VineEstS5C.P4.W2
