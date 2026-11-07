/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz1
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz3

/-! # P4-W2 (session 18, step 4c-4): the sizes of a good bundle member against the native row-bound product

`szQ_good`, `szT_good`: `szQ b = 2 TR C₁² (C₁²δ)^{n_C} cost_C` (and trees).  `sz_idx`: with `CRq b = trc · 2 (C₁ (C₁δ)^{n_C} L^{-w} cost_C)` (`CRt` likewise, `trc = trC (6η⁶) ≥ 1`) the four products
`szQ szT`, `szQ CRt`, `CRq szT`, `CRq CRt` are at most `KZ N0`, `KZ L^{-w} N0` (resp.), `N0 = cb² C₁⁴ (2C₁²δ)^{zpN} cost_C cost_T`, `KZ = 4 TR² trc² / cb²`.
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
theorem szQ_good (hδ : 0 ≤ P.δ) {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) :
    (certSrcOf (κ := κ) A sp0 hA hcan hel htc hcc E hN).szQ b =
      2 * TR P.η * P.C₁ ^ 2 * (P.C₁ ^ 2 * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * layerCost Bh (zpObjC b.1 pstar) := by
  obtain ⟨c1, c2, c3⟩ := certC_good_vals (κ := κ) A sp0 hA hcan hel htc hcc E hN hb
  show |(certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).c| * (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CJ *
      (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CM = _
  rw [c1, c2, c3, abs_of_nonneg (pow_nonneg hδ _)]
  unfold certCJ certCM
  ring

include hcan hel htc hcc E hN in
open Classical in
theorem szT_good (hδ : 0 ≤ P.δ) {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) :
    (certSrcOf (κ := κ) A sp0 hA hcan hel htc hcc E hN).szT b =
      2 * TR P.η * P.C₁ ^ 2 * (P.C₁ ^ 2 * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * layerCost Bh (zpObjT b.1 pstar) := by
  obtain ⟨c1, c2, c3⟩ := certT_good_vals (κ := κ) A sp0 hA hcan hel htc hcc E hN hb
  show |(certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).c| * (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CJ *
      (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CM = _
  rw [c1, c2, c3, abs_of_nonneg (pow_nonneg hδ _)]
  unfold certCJ certCM
  ring

include hcan hel htc hcc E hN in
open Classical in
/-- **The four size products of a good bundle member** against the native row-bound product `N0 = cb² C₁⁴ (2C₁²δ)^{zpN} cost_C cost_T`:
`CRq b = trc · 2 (C₁ (C₁δ)^{n_C} L^{-w} cost_C)` and `CRt b` likewise. -/
theorem sz_idx (hδ : 0 < P.δ) (hC1 : 1 ≤ P.C₁) (hη : P.η ≤ 1) (hcb : 0 < rowCb P) {b : ST w ι pstar J}
    (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) (Lw trc CRqb CRtb : ℝ) (htrc : 1 ≤ trc) (hLw0 : 0 ≤ Lw) (hLw1 : Lw ≤ 1)
    (hcC : 0 ≤ layerCost Bh (zpObjC b.1 pstar)) (hcT : 0 ≤ layerCost Bh (zpObjT b.1 pstar))
    (hq : CRqb = trc * (2 * (P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * Lw * layerCost Bh (zpObjC b.1 pstar))))
    (ht : CRtb = trc * (2 * (P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * Lw * layerCost Bh (zpObjT b.1 pstar)))) :
    let SQ := (certSrcOf (κ := κ) A sp0 hA hcan hel htc hcc E hN).szQ b
    let ST := (certSrcOf (κ := κ) A sp0 hA hcan hel htc hcc E hN).szT b
    let N0 := rowCb P ^ 2 * P.C₁ ^ 4 * (2 * (P.C₁ ^ 2 * P.δ)) ^ zpN A pstar *
      (layerCost Bh (zpObjC b.1 pstar) * layerCost Bh (zpObjT b.1 pstar))
    let KZ := 4 * TR P.η ^ 2 * trc ^ 2 / rowCb P ^ 2
    SQ * ST ≤ KZ * N0 ∧ SQ * CRtb ≤ KZ * (Lw * N0) ∧ CRqb * ST ≤ KZ * (Lw * N0) ∧ CRqb * CRtb ≤ KZ * (Lw * N0) := by
  intro SQ ST N0 KZ
  have hs := zp_half_sizes A sp0 hA hcan hel htc hcc b (mem_zpFinset_of_bs A sp0 hA hb)
  have hq1 : SQ = 2 * TR P.η * P.C₁ ^ 2 * (P.C₁ ^ 2 * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * layerCost Bh (zpObjC b.1 pstar) :=
    szQ_good (κ := κ) A sp0 hA hcan hel htc hcc E hN hδ.le hb
  have ht1 : ST = 2 * TR P.η * P.C₁ ^ 2 * (P.C₁ ^ 2 * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * layerCost Bh (zpObjT b.1 pstar) :=
    szT_good (κ := κ) A sp0 hA hcan hel htc hcc E hN hδ.le hb
  obtain ⟨h1, h2, h3, h4⟩ := sz_idx_alg (TR P.η) trc P.C₁ P.δ (rowCb P) Lw (layerCost Bh (zpObjC b.1 pstar)) (layerCost Bh (zpObjT b.1 pstar))
    ((zpCodeC b.1 pstar).size / 2) ((zpCodeT b.1 pstar).size / 2) (zpN A pstar) hs (one_le_TR hη) htrc hC1 hδ hcb hLw0 hLw1 hcC hcT
  have eq1 : CRqb = 2 * trc * P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * Lw * layerCost Bh (zpObjC b.1 pstar) := by
    rw [hq]; ring
  have eq2 : CRtb = 2 * trc * P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * Lw * layerCost Bh (zpObjT b.1 pstar) := by
    rw [ht]; ring
  rw [hq1, ht1, eq1, eq2]
  exact ⟨h1, h2, h3, h4⟩

end WaveTurbulence.VineEstS5C.P4.W2
