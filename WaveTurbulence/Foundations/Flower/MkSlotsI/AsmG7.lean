/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.AsmG6

/-! # B3s-HELPER7 AsmG (3): the slot data of the engine in `classRepGen_at`

At a prescribed point `a` and a marked set `Mk` (B3's unit marking `mkU a.prime`), the per-slot data of HELPER9's engine
`MkSlotsE.representsIntMKSel_of_centreModes` for the general piece:
* `SelAdjO`: `SelAdj` of the skeleton slot of an outer slot;
* `θsGen`: the moment exponent `1/4` on `SelAdj` slots, `η` elsewhere;
* `μsGen`: the slot masses of `GenSlotObligationAt` (`Kg · genSlotMass`, times `L^{47d+2}` on `SelAdj` slots);
* `lfGen`: the leaf factor of a slot (`c_F^{nr}`, `genLeaf`, the protected loss, the selected-native gains, the
  `SelAdj` loss);
and the engine hypotheses `hcθ_gen`, `hμ_gen`, `hlf_gen`, `hμb_gen`, and `centreForm_inter_pinSet` (the class
identity on the domain `domOf ∩ pinSet`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Flower.MkSlotsI
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.PL2330
  WaveTurbulence.VineEstS5C VineParamContract WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Represents WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.Flower.Stage1WVine
  WaveTurbulence.Flower.MkUnits WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1MKGate
  WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Flower.MkSlots (withC₁ recLG outerValMμD fixMeasure)
open WaveTurbulence.Flower.FinalMKDefs (RepresentsIntMKSel)
open scoped ENNReal Classical

section Slots

variable (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (a : PrescribedPrimeGarden (2 * R))
  (Mk : Set (Stage1.CLVine a.prime.skeleton))

/-- `SelAdj` of the skeleton slot of an outer slot. -/
abbrev SelAdjO (sl : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G) : Prop :=
  SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel (iotaAt a Mk sl)

/-- The moment exponent of an outer slot: `1/4` on `SelAdj` slots, `η` elsewhere. -/
def θsGen (sl : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G) : ℝ :=
  if SelAdjO J kSel a Mk sl then 1 / 4 else P.η

/-- The slot mass of the general obligation at an outer slot. -/
def μsGen (Kg : ℕ → ℝ → ℝ) (b : ℝ) (sl : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G) : ℝ≥0∞ :=
  if SelAdjO J kSel a Mk sl then
    ENNReal.ofReal (Kg P.d P.η * P.L ^ (47 * (P.d : ℝ) + 2) * genSlotMass P P.C₁ b a J pat t s kSel Rs (iotaAt a Mk sl))
  else ENNReal.ofReal (Kg P.d P.η * genSlotMass P P.C₁ b a J pat t s kSel Rs (iotaAt a Mk sl))

/-- The leaf factor of an outer slot. -/
def lfGen (b : ℝ) (sl : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G) : ℝ :=
  frontierConst P.d ^ Stage1WNoVine.slotNr a.prime.data a.prime.prime.1 (iotaAt a Mk sl) *
    genLeaf a J b (iotaAt a Mk sl) *
    P.L ^ (if HasProtNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      (protI (recLG a) J pat t s kSel) (iotaAt a Mk sl) then genLossExp P.d else 0) *
    (∏ v ∈ MkSlotsS.selNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel
      (iotaAt a Mk sl), Rs v.1.1 ^ (-(1 / 18 : ℝ))) *
    (if SelAdjO J kSel a Mk sl then P.L ^ (47 * (P.d : ℝ) + 2) else 1)

theorem hlf_gen (hL : 0 ≤ P.L) (hRs : ∀ j, 1 ≤ Rs j) {b : ℝ} (hb : 0 ≤ b)
    (sl : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G) :
    0 ≤ lfGen P J pat t s kSel Rs a Mk b sl := by
  unfold lfGen
  have hc0 : 0 ≤ frontierConst P.d := le_trans zero_le_one (one_le_frontierConst _)
  refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hc0 _) (genLeaf_nonneg _ J hb _))
    (Real.rpow_nonneg hL _)) (Finset.prod_nonneg fun v _ => Real.rpow_nonneg (le_trans zero_le_one (hRs _)) _)) ?_
  split_ifs
  · exact Real.rpow_nonneg hL _
  · exact zero_le_one

/-- **`hμb`**: the slot masses in the engine's form. -/
theorem hμb_gen (Kg : ℕ → ℝ → ℝ) (hC : 0 ≤ P.C₁) (hL : 0 ≤ P.L) (hRs : ∀ j, 1 ≤ Rs j) {b : ℝ} (hb : 0 ≤ b)
    (sl : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G) :
    μsGen P J pat t s kSel Rs a Mk Kg b sl ≤
      ENNReal.ofReal (max 1 (Kg P.d P.η) * (P.C₁ * Real.sqrt P.δ) ^ slotSize a.prime.data (iotaAt a Mk sl) *
        P.L ^ (-(P.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (iotaAt a Mk sl) : ℝ)) * lfGen P J pat t s kSel Rs a Mk b sl) := by
  have hK : Kg P.d P.η ≤ max 1 (Kg P.d P.η) := le_max_right _ _
  have hX : 0 ≤ (P.C₁ * Real.sqrt P.δ) ^ slotSize a.prime.data (iotaAt a Mk sl) :=
    pow_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) _
  have hY : 0 ≤ P.L ^ (-(P.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) (iotaAt a Mk sl) : ℝ)) := Real.rpow_nonneg hL _
  have hZ := hlf_gen P J pat t s kSel Rs a Mk hL hRs hb sl
  refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hX) hY) hZ))
  unfold μsGen lfGen genSlotMass
  split_ifs <;> ring_nf

/-- **`hcθ`**: the per-slot exponent pays the two hinge losses `2·6η⁶` and the selection moments (`η ≤ 1/4`). -/
theorem hcθ_gen (hη : 0 < P.η) (hη4 : P.η ≤ 1 / 4) (sl : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G) :
    2 * (6 * P.η ^ 6) + (MkSlotsS.selE ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk).route
        a.prime.prime.1 ((stSt a.prime.skeleton a.totalSigma Mk).plain a.prime.prime.1)) (selRAt J kSel a Mk) sl 0 +
      MkSlotsS.selE ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk).route
        a.prime.prime.1 ((stSt a.prime.skeleton a.totalSigma Mk).plain a.prime.prime.1)) (selRAt J kSel a Mk) sl 1)
      ≤ θsGen P J kSel a Mk sl := by
  unfold θsGen
  by_cases hsa : SelAdjO J kSel a Mk sl
  · rw [if_pos hsa]
    have he0 := MkSlotsS.selE_le ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk).route
      a.prime.prime.1 ((stSt a.prime.skeleton a.totalSigma Mk).plain a.prime.prime.1)) (selRAt J kSel a Mk) sl 0
    have he1 := MkSlotsS.selE_le ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk).route
      a.prime.prime.1 ((stSt a.prime.skeleton a.totalSigma Mk).plain a.prime.prime.1)) (selRAt J kSel a Mk) sl 1
    have h6 : P.η ^ 6 ≤ (1 / 4 : ℝ) ^ 6 := pow_le_pow_left₀ hη.le hη4 6
    norm_num at h6
    linarith
  · rw [if_neg hsa]
    have hna : ¬ MkSlotsS.AdjS ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk).route
        a.prime.prime.1 ((stSt a.prime.skeleton a.totalSigma Mk).plain a.prime.prime.1)) (selRAt J kSel a Mk) sl :=
      fun h' => hsa (selAdj_iota_of_adjS J kSel a Mk sl h')
    rw [MkSlotsS.selE_eq_zero_of_not_adj _ _ sl hna 0, MkSlotsS.selE_eq_zero_of_not_adj _ _ sl hna 1]
    have h5 : P.η ^ 5 ≤ (1 / 4 : ℝ) ^ 5 := pow_le_pow_left₀ hη.le hη4 5
    have e : P.η ^ 6 = P.η ^ 5 * P.η := by ring
    norm_num at h5
    nlinarith

/-- **`hμ`**: the moment masses of the centre-indexed families of the slot data. -/
theorem hμ_gen (Kg : ℕ → ℝ → ℝ) (p : ℕ) (σ : Fin (2 * R) → Option ℕ) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (Rf : Fin (2 * R) → Option ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (sd : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G → (Fin P.d → ℤ) → SlotDatum P.d)
    (hsd : SlotDataOK Kg P P.C₁ p a J pat t s kSel σ Rs roots h b Rf dag Mk sd)
    (X : CentredSlot (stSt a.prime.skeleton a.totalSigma Mk).G → (Fin P.d → ℤ))
    (sl : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G) :
    ∑' l, maxBracketPow (θsGen P J kSel a Mk sl) (half ((famX (fam₀Of sd hsd.supp) (famCOfData sd) X).m sl l)) *
      ENNReal.ofReal ((famX (fam₀Of sd hsd.supp) (famCOfData sd) X).w sl l) ≤
      μsGen P J pat t s kSel Rs a Mk Kg b sl := by
  refine tsum_famX_le (fam₀Of sd hsd.supp) (famCOfData sd) X sl _ _ (fun _ => ?_) (fun c hc => ?_)
  · unfold θsGen μsGen
    by_cases hsa : SelAdjO J kSel a Mk sl
    · rw [if_pos hsa, if_pos hsa]
      exact hsd.massSel sl 0 hsa
    · rw [if_neg hsa, if_neg hsa]
      exact hsd.massEta sl 0 hsa
  · subst hc
    unfold θsGen μsGen
    by_cases hsa : SelAdjO J kSel a Mk (Sum.inr c.1)
    · rw [if_pos hsa, if_pos hsa]
      exact hsd.massSel (Sum.inr c.1) (X c) hsa
    · rw [if_neg hsa, if_neg hsa]
      exact hsd.massEta (Sum.inr c.1) (X c) hsa

end Slots

/-! ## The class identity on the pinned slice -/

/-- **The centre-indexed form on `Dom ∩ pinSet π.fix`** is the one on `Dom`. -/
theorem centreForm_inter_pinSet {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (hS : π.Gsb.IsPlain)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration π.Gsb P.d roots 0 → Prop) (Dom : Set (GBranch π.Gsb.tree → ℝ)) {Jt : Type} [Fintype Jt]
    [DecidableEq Jt] (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ Jt) (hclk : Jt → Fin 3 → ClkSrc π.Gsb)
    (hmom : Jt → Fin 4 → GNode π.Gsb.tree) {I : Type} [Fintype I] (sgn : I → ℂ) (fam₀ : I → SlotFam π.Gsb P.d)
    (famC : I → CentredSlot π.Gsb → (Fin P.d → ℤ) → ChainPiece P.d)
    (HkM : I → Jt → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) :
    centreForm π hS tt base roots selSk Dom route hclk hmom sgn fam₀ famC HkM =
      ∑ i, sgn i * ∑' X : CentredSlot π.Gsb → (Fin P.d → ℤ),
        ∑' ξ : ∀ t, (famX (fam₀ i) (famC i) X).Λ t, (((∏ t, (famX (fam₀ i) (famC i) X).w t (ξ t) : ℝ)) : ℂ) *
          outerValMμD π.Gsb P.L P.γ P.δ base roots tt (Dom ∩ MkSlotsB.pinSet π.fix) π.Cs.hinges
            (fun z => MkSlotsS.pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0) *
              chiX P.L base X z) hS
            (fixMeasure π.fix)
            (fun t => (famX (fam₀ i) (famC i) X).a t (ξ t)) (fun t => (famX (fam₀ i) (famC i) X).m t (ξ t))
            route hclk hmom (HkM i) := by
  unfold centreForm
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine tsum_congr fun X => tsum_congr fun ξ => ?_
  congr 1
  exact (outerValMμD_inter_pinSet _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).symm

end WaveTurbulence.Flower.MkSlotsI
