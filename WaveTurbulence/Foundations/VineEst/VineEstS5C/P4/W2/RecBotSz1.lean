/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSrcStep
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.BotSrcOf
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxLeaf2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.BotGeo
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz4

/-! # P4-W2 (session 19, step 2): the bottom bundle, sizes and constants (copy of RecSz1, RecSz4, RecSrcChoice for `botSrcOf`)

`bot_half_sizes`, `bot_leafCost_eq_native`, `botCertC_good_vals`, `botCertT_good_vals`, `botSzQ_good`, `botSzT_good`, `bot_sz_idx`, `crqChoiceB`, `crtChoiceB`, `botSrcOfC`, `botSrcOfC_idx`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.LGSpine TTree WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1
  Set WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4


variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} [Fintype ι] [DecidableEq ι]
variable {P : WTParams} {κ : KPar P.d} {B0 : ℝ}

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

include hA hup hcan hel htc hcc in
theorem bot_half_sizes (b : BT w ι) (hb : b ∈ canonFinsetK p kind A c0) :
    (zpCodeC b.1 pstar).size / 2 + (zpCodeT b.1 pstar).size / 2 = zpN A pstar := by
  have h := botg_sizes A c0 hA hcan hel htc hcc hup b hb
  have h1 := size_half_cpl (zpCodeC b.1 pstar)
  have h2 := size_half_chain (zpCodeT b.1 pstar)
  omega

include hA hup hcan hel htc hcc in
theorem bot_leafCard (b : BT w ι) (hb : b ∈ canonFinsetK p kind A c0) :
    (inputLeaves (zpObjC b.1 pstar).garden).card + (inputLeaves (zpObjT b.1 pstar).garden).card = 2 * zpN A pstar + 1 := by
  have hc := botg_nat_cohC A c0 hA hcan hel htc hcc hup b hb
  have ht := botg_nat_cohT A c0 hA hcan hel htc hcc hup b hb
  rw [card_inputLeaves_plain_couple _ hc.2.1.1.1, card_inputLeaves_paired_tree _ (isPairedTree_of_decodesTree ht.2.1)]
  have h1 := RegCpl.size_eq_order _ hc.2.1
  have h2 := decodesTree_order' ht.2.1
  have := botg_sizes A c0 hA hcan hel htc hcc hup b hb
  omega

section Native
variable {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

include hA hup hcan hel htc hcc in
theorem bot_leafCost_eq_native (i : (assemblySourceFamily B).CoreIndex) (hN : zpN A pstar = zpN (startState B RD hG layer hLayer) i)
    (b' : BT w ι) (hb : b' ∈ canonFinsetK p kind A c0) (B0 : ℝ) :
    layerCost (fun _ => B0) (zpObjC b'.1 pstar) * layerCost (fun _ => B0) (zpObjT b'.1 pstar) =
      layerCost (fun _ => B0) (nativeCoupleLayered RD hG layer hLayer
          (pairOfLeaf G hG ((startState B RD hG layer hLayer).family.placement i).retained)) *
        layerCost (fun _ => B0) (nativeChainLayered RD hG layer hLayer
          ((startState B RD hG layer hLayer).family.placement i).lower) := by
  rw [layerCost_const, layerCost_const, layerCost_const, layerCost_const, ← pow_add, ← pow_add,
    bot_leafCard A c0 hA hcan hel htc hcc hup b' hb, native_leafCard_start B RD hG layer hLayer i, hN]

end Native

section Cert
variable {Bh : ℕ → ℝ} (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)

include hcan hel htc hcc hA hup E hN in
open Classical in
theorem botCertC_good_vals {b : BT w ι} (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) :
    (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).c = P.δ ^ ((zpCodeC b.1 pstar).size / 2) ∧
    (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CJ = certCJ P ((zpCodeC b.1 pstar).size / 2) ∧
    (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CM = certCM P ((zpCodeC b.1 pstar).size / 2) (layerCost Bh (zpObjC b.1 pstar)) := by
  unfold botCertC
  rw [dif_pos hb]
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

include hcan hel htc hcc hA hup E hN in
open Classical in
theorem botCertT_good_vals {b : BT w ι} (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) :
    (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).c = P.δ ^ ((zpCodeT b.1 pstar).size / 2) ∧
    (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CJ = certCJ P ((zpCodeT b.1 pstar).size / 2) ∧
    (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CM = certCM P ((zpCodeT b.1 pstar).size / 2) (layerCost Bh (zpObjT b.1 pstar)) := by
  unfold botCertT
  rw [dif_pos hb]
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

include hcan hel htc hcc hA hup E hN in
open Classical in
theorem botSzQ_good (hδ : 0 ≤ P.δ) {b : BT w ι} (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) :
    (botCertSrcOf (κ := κ) A c0 hA hcan hel htc hcc hup E hN).szQ b =
      2 * TR P.η * P.C₁ ^ 2 * (P.C₁ ^ 2 * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * layerCost Bh (zpObjC b.1 pstar) := by
  obtain ⟨c1, c2, c3⟩ := botCertC_good_vals (κ := κ) A c0 hA hcan hel htc hcc hup E hN hb
  show |(botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).c| * (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CJ *
      (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CM = _
  rw [c1, c2, c3, abs_of_nonneg (pow_nonneg hδ _)]
  unfold certCJ certCM
  ring

include hcan hel htc hcc hA hup E hN in
open Classical in
theorem botSzT_good (hδ : 0 ≤ P.δ) {b : BT w ι} (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) :
    (botCertSrcOf (κ := κ) A c0 hA hcan hel htc hcc hup E hN).szT b =
      2 * TR P.η * P.C₁ ^ 2 * (P.C₁ ^ 2 * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * layerCost Bh (zpObjT b.1 pstar) := by
  obtain ⟨c1, c2, c3⟩ := botCertT_good_vals (κ := κ) A c0 hA hcan hel htc hcc hup E hN hb
  show |(botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).c| * (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CJ *
      (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CM = _
  rw [c1, c2, c3, abs_of_nonneg (pow_nonneg hδ _)]
  unfold certCJ certCM
  ring

include hcan hel htc hcc hA hup E hN in
open Classical in
theorem bot_sz_idx (hδ : 0 < P.δ) (hC1 : 1 ≤ P.C₁) (hη : P.η ≤ 1) (hcb : 0 < rowCb P) {b : BT w ι}
    (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) (Lw trc CRqb CRtb : ℝ) (htrc : 1 ≤ trc) (hLw0 : 0 ≤ Lw) (hLw1 : Lw ≤ 1)
    (hcC : 0 ≤ layerCost Bh (zpObjC b.1 pstar)) (hcT : 0 ≤ layerCost Bh (zpObjT b.1 pstar))
    (hq : CRqb = trc * (2 * (P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * Lw * layerCost Bh (zpObjC b.1 pstar))))
    (ht : CRtb = trc * (2 * (P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * Lw * layerCost Bh (zpObjT b.1 pstar)))) :
    let SQ := (botCertSrcOf (κ := κ) A c0 hA hcan hel htc hcc hup E hN).szQ b
    let ST := (botCertSrcOf (κ := κ) A c0 hA hcan hel htc hcc hup E hN).szT b
    let N0 := rowCb P ^ 2 * P.C₁ ^ 4 * (2 * (P.C₁ ^ 2 * P.δ)) ^ zpN A pstar *
      (layerCost Bh (zpObjC b.1 pstar) * layerCost Bh (zpObjT b.1 pstar))
    let KZ := 4 * TR P.η ^ 2 * trc ^ 2 / rowCb P ^ 2
    SQ * ST ≤ KZ * N0 ∧ SQ * CRtb ≤ KZ * (Lw * N0) ∧ CRqb * ST ≤ KZ * (Lw * N0) ∧ CRqb * CRtb ≤ KZ * (Lw * N0) := by
  intro SQ ST N0 KZ
  have hs := bot_half_sizes A c0 hA hcan hel htc hcc hup b (mem_canon_of_botbs A c0 hb)
  have hq1 : SQ = 2 * TR P.η * P.C₁ ^ 2 * (P.C₁ ^ 2 * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * layerCost Bh (zpObjC b.1 pstar) :=
    botSzQ_good (κ := κ) A c0 hA hcan hel htc hcc hup E hN hδ.le hb
  have ht1 : ST = 2 * TR P.η * P.C₁ ^ 2 * (P.C₁ ^ 2 * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * layerCost Bh (zpObjT b.1 pstar) :=
    botSzT_good (κ := κ) A c0 hA hcan hel htc hcc hup E hN hδ.le hb
  obtain ⟨h1, h2, h3, h4⟩ := sz_idx_alg (TR P.η) trc P.C₁ P.δ (rowCb P) Lw (layerCost Bh (zpObjC b.1 pstar)) (layerCost Bh (zpObjT b.1 pstar))
    ((zpCodeC b.1 pstar).size / 2) ((zpCodeT b.1 pstar).size / 2) (zpN A pstar) hs (one_le_TR hη) htrc hC1 hδ hcb hLw0 hLw1 hcC hcT
  have eq1 : CRqb = 2 * trc * P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * Lw * layerCost Bh (zpObjC b.1 pstar) := by
    rw [hq]; ring
  have eq2 : CRtb = 2 * trc * P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * Lw * layerCost Bh (zpObjT b.1 pstar) := by
    rw [ht]; ring
  rw [hq1, ht1, eq1, eq2]
  exact ⟨h1, h2, h3, h4⟩

end Cert

end WaveTurbulence.VineEstS5C.P4.W2
