/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.XSrcOfXBot
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecBotSz1

/-! # P4-W2 (session 19, step 2): the bottom certified source with the chosen remainder constants (copy of RecSrcChoice, RecSrcStep for `botSrcOf`) -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.LGSpine TTree WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1
  Set WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4


variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} [Fintype ι] [DecidableEq ι]

open Classical in
/-- The bottom couple remainder constant: twice the gate bound on the bundle, `1` elsewhere. -/
noncomputable def crqChoiceB (P : WTParams) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family) (B0 : ℝ) (b : BT w ι) : ℝ :=
  if b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0 then
    2 * (P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) *
      layerCost (fun _ => B0) (zpObjC b.1 pstar))
  else 1

open Classical in
/-- The bottom tree remainder constant. -/
noncomputable def crtChoiceB (P : WTParams) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family) (B0 : ℝ) (b : BT w ι) : ℝ :=
  if b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0 then
    2 * (P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) *
      layerCost (fun _ => B0) (zpObjT b.1 pstar))
  else 1

section
variable {P : WTParams} (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family) {B0 : ℝ}

theorem crqChoiceB_pos (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 0 < P.L) (hB0 : 0 < B0) (b : BT w ι) :
    0 < crqChoiceB (p := p) (kind := kind) (pstar := pstar) P A c0 B0 b := by
  unfold crqChoiceB
  split_ifs
  · rw [layerCost_const]
    have : 0 < P.C₁ := by linarith
    positivity
  · exact one_pos

theorem crtChoiceB_pos (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 0 < P.L) (hB0 : 0 < B0) (b : BT w ι) :
    0 < crtChoiceB (p := p) (kind := kind) (pstar := pstar) P A c0 B0 b := by
  unfold crtChoiceB
  split_ifs
  · rw [layerCost_const]
    have : 0 < P.C₁ := by linarith
    positivity
  · exact one_pos

theorem crqChoiceB_gate (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 0 < P.L) (hB0 : 0 < B0) (b : BT w ι)
    (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) :
    P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((1 : ℕ) : ℝ)) *
      layerCost (fun _ => B0) (zpObjC b.1 pstar) < crqChoiceB (p := p) (kind := kind) (pstar := pstar) P A c0 B0 b := by
  unfold crqChoiceB
  rw [if_pos hb, Nat.cast_one, mul_one]
  have : 0 < P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) *
      layerCost (fun _ => B0) (zpObjC b.1 pstar) := by
    rw [layerCost_const]
    have : 0 < P.C₁ := by linarith
    positivity
  linarith

theorem crtChoiceB_gate (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 0 < P.L) (hB0 : 0 < B0) (b : BT w ι)
    (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) :
    P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((1 : ℕ) : ℝ)) *
      layerCost (fun _ => B0) (zpObjT b.1 pstar) < crtChoiceB (p := p) (kind := kind) (pstar := pstar) P A c0 B0 b := by
  unfold crtChoiceB
  rw [if_pos hb, Nat.cast_one, mul_one]
  have : 0 < P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) *
      layerCost (fun _ => B0) (zpObjT b.1 pstar) := by
    rw [layerCost_const]
    have : 0 < P.C₁ := by linarith
    positivity
  linarith

theorem crqChoiceB_eq (b : BT w ι) (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) :
    crqChoiceB (p := p) (kind := kind) (pstar := pstar) P A c0 B0 b = 2 * (P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) *
      layerCost (fun _ => B0) (zpObjC b.1 pstar)) := by
  unfold crqChoiceB; rw [if_pos hb]

theorem crtChoiceB_eq (b : BT w ι) (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) :
    crtChoiceB (p := p) (kind := kind) (pstar := pstar) P A c0 B0 b = 2 * (P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) *
      layerCost (fun _ => B0) (zpObjT b.1 pstar)) := by
  unfold crtChoiceB; rw [if_pos hb]

end

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
  (R : RemEnv P κ) (E : GateEnv P κ p (fun _ => B0)) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)
  (hC1 : 1 ≤ P.C₁) (hB0 : 0 < B0)

include hcan hel htc hcc hup hA R E hN hC1 hB0 in
/-- **The certified source of a bottom level with the chosen remainder constants.** -/
noncomputable def botSrcOfC : Src P (botSepFamOf (κ := κ) A c0 hA hcan hel htc hcc hup E hN).S (botRemQ pstar κ (botQfam pstar κ A))
    (botRemT pstar κ (botTfam pstar κ A)) (zpQ2 A pstar : ℝ) (zpQ4 A pstar : ℝ) (zpQh A pstar : ℝ) :=
  botSrcOf (κ := κ) A c0 hA hcan hel htc hcc hup R (crqChoiceB (p := p) (kind := kind) (pstar := pstar) P A c0 B0) (crtChoiceB (p := p) (kind := kind) (pstar := pstar) P A c0 B0)
    (crqChoiceB_pos A c0 hC1 R.hδ0 (by linarith [R.hL1]) hB0) (crtChoiceB_pos A c0 hC1 R.hδ0 (by linarith [R.hL1]) hB0)
    (fun b hb => crqChoiceB_gate A c0 hC1 R.hδ0 (by linarith [R.hL1]) hB0 b hb)
    (fun b hb => crtChoiceB_gate A c0 hC1 R.hδ0 (by linarith [R.hL1]) hB0 b hb) E hN

include hcan hel htc hcc hup hA R E hN hC1 hB0 in
/-- **The cross fields of `botSrcOfC`.** -/
noncomputable def botSrcOfCX (hη0 : 0 < P.η) (hη4 : P.η < 1 / 4) (hgap : zpQ4 A pstar + 1 ≤ zpQh A pstar) :
    K2.XCross P (botSrcOfC (κ := κ) A c0 hA hcan hel htc hcc hup R E hN hC1 hB0) :=
  botSrcOfX (κ := κ) A c0 hA hcan hel htc hcc hup E hN R (crqChoiceB (p := p) (kind := kind) (pstar := pstar) P A c0 B0)
    (crtChoiceB (p := p) (kind := kind) (pstar := pstar) P A c0 B0)
    (crqChoiceB_pos A c0 hC1 R.hδ0 (by linarith [R.hL1]) hB0) (crtChoiceB_pos A c0 hC1 R.hδ0 (by linarith [R.hL1]) hB0)
    (fun b hb => crqChoiceB_gate A c0 hC1 R.hδ0 (by linarith [R.hL1]) hB0 b hb)
    (fun b hb => crtChoiceB_gate A c0 hC1 R.hδ0 (by linarith [R.hL1]) hB0 b hb) hη0 hη4 hgap

include hcan hel htc hcc hup hA R E hN hC1 hB0 in
open Classical in
theorem botSrcOfC_idx (hη0 : 0 < P.η) (hη : P.η ≤ 1) (hcb : 0 < rowCb P) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) (Nn : ℝ)
    (hNn : ∀ b : BT w ι, (b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) →
      rowCb P ^ 2 * P.C₁ ^ 4 * (2 * (P.C₁ ^ 2 * P.δ)) ^ zpN A pstar *
        (layerCost (fun _ => B0) (zpObjC b.1 pstar) * layerCost (fun _ => B0) (zpObjT b.1 pstar)) = Nn) :
    ∀ b, (botSrcOfC (κ := κ) A c0 hA hcan hel htc hcc hup R E hN hC1 hB0).good b →
      (botSrcOfC (κ := κ) A c0 hA hcan hel htc hcc hup R E hN hC1 hB0).szQ b * (botSrcOfC (κ := κ) A c0 hA hcan hel htc hcc hup R E hN hC1 hB0).szT b ≤
          (4 * TR P.η ^ 2 * trC (6 * P.η ^ 6) ^ 2 / rowCb P ^ 2) * Nn ∧
        (botSrcOfC (κ := κ) A c0 hA hcan hel htc hcc hup R E hN hC1 hB0).szQ b * (botSrcOfC (κ := κ) A c0 hA hcan hel htc hcc hup R E hN hC1 hB0).CRt b ≤
          (4 * TR P.η ^ 2 * trC (6 * P.η ^ 6) ^ 2 / rowCb P ^ 2) * (P.L ^ (-(P.gamma1 - Real.sqrt P.η)) * Nn) ∧
        (botSrcOfC (κ := κ) A c0 hA hcan hel htc hcc hup R E hN hC1 hB0).CRq b * (botSrcOfC (κ := κ) A c0 hA hcan hel htc hcc hup R E hN hC1 hB0).szT b ≤
          (4 * TR P.η ^ 2 * trC (6 * P.η ^ 6) ^ 2 / rowCb P ^ 2) * (P.L ^ (-(P.gamma1 - Real.sqrt P.η)) * Nn) ∧
        (botSrcOfC (κ := κ) A c0 hA hcan hel htc hcc hup R E hN hC1 hB0).CRq b * (botSrcOfC (κ := κ) A c0 hA hcan hel htc hcc hup R E hN hC1 hB0).CRt b ≤
          (4 * TR P.η ^ 2 * trC (6 * P.η ^ 6) ^ 2 / rowCb P ^ 2) * (P.L ^ (-(P.gamma1 - Real.sqrt P.η)) * Nn) := by
  intro b hb
  have hb' : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0 := hb
  have hL0 : 0 < P.L := by linarith [R.hL1]
  have hLw0 : 0 ≤ P.L ^ (-(P.gamma1 - Real.sqrt P.η)) := Real.rpow_nonneg hL0.le _
  have hLw1 : P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos R.hL1 (by linarith)
  have hcC : 0 ≤ layerCost (fun _ => B0) (zpObjC b.1 pstar) := by rw [layerCost_const]; exact pow_nonneg hB0.le _
  have hcT : 0 ≤ layerCost (fun _ => B0) (zpObjT b.1 pstar) := by rw [layerCost_const]; exact pow_nonneg hB0.le _
  have htrc : 1 ≤ trC (6 * P.η ^ 6) := one_le_trC (by positivity)
  have key := bot_sz_idx (κ := κ) A c0 hA hcan hel htc hcc hup E hN R.hδ0 hC1 hη hcb hb' (P.L ^ (-(P.gamma1 - Real.sqrt P.η))) (trC (6 * P.η ^ 6))
    ((botSrcOfC (κ := κ) A c0 hA hcan hel htc hcc hup R E hN hC1 hB0).CRq b) ((botSrcOfC (κ := κ) A c0 hA hcan hel htc hcc hup R E hN hC1 hB0).CRt b)
    htrc hLw0 hLw1 hcC hcT
    (by show trC (6 * P.η ^ 6) * crqChoiceB (p := p) (kind := kind) (pstar := pstar) P A c0 B0 b = _
        rw [crqChoiceB_eq A c0 b hb'])
    (by show trC (6 * P.η ^ 6) * crtChoiceB (p := p) (kind := kind) (pstar := pstar) P A c0 B0 b = _
        rw [crtChoiceB_eq A c0 b hb'])
  have hN' := hNn b hb'
  simp only at key
  rw [hN'] at key
  exact key

end WaveTurbulence.VineEstS5C.P4.W2
