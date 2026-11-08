/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.AsmG5
public import WaveTurbulence.Foundations.Flower.MkSlotsI.AsmG1
public import WaveTurbulence.Foundations.Flower.MkSlots.IntAsm4
public import WaveTurbulence.Foundations.Flower.MkUnitsL.AssemblyL
public import WaveTurbulence.Foundations.Flower.V5WB.Final

/-! # B3s-HELPER7 AsmG (2): constants and mass lemmas of `classRepGen_at`

* `Cgen d η c₁ Kg`: the large constant (`max 1 c₁` and the engine's `Cchi·nodeBallCard·(9K)²·Ch ≤ C₁` at the slot
  constant `K = max 1 (Kg d η)` and B3-2's hinge constant `ChFWL`);
* `liftGen d = c_F^{16}·topFilterMass²·81·chiDNorm`: the `C₁`-lift constant (it absorbs `c_F^{16N}`,
  `topFilterMass^{Σ|SU|} ≤ topFilterMass^{2N}`, `3^{4#sel} ≤ 81^N`, `chiDNorm^{#sel} ≤ chiDNorm^N`);
* `SelNativeBound`: the statement of the absorbed-selection bound (`prod_selNative_le`, W:MkSlotsI/AsmG3.lean);
* `genLeaf_nonneg`, `selMassMK_le`, `selMassMK_nonneg`, `hs_arith` (the arithmetic of the engine's `hs`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineAlign
open WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.RedSplice (stSt unitBlocks)

namespace WaveTurbulence.Flower.MkSlotsI

/-- **The large constant of the general assembly.** -/
def Cgen (d : ℕ) (η c₁ : ℝ) (Kg : ℕ → ℝ → ℝ) : ℝ :=
  max (max 1 c₁) (Represents.Cchi d * (RepAnalytic.nodeBallCard d : ℝ) * (9 * max 1 (Kg d η)) ^ 2 *
    MkUnitsL.ChFWL d η)

/-- **The `C₁`-lift constant of the general assembly.** -/
def liftGen (d : ℕ) : ℝ :=
  Stage1W.frontierConst d ^ 16 * (V5W.topFilterMass ^ 2 * (81 * chiDNorm))

theorem one_le_liftGen (d : ℕ) : 1 ≤ liftGen d := by
  unfold liftGen
  have h1 : 1 ≤ Stage1W.frontierConst d ^ 16 := one_le_pow₀ (Stage1W.one_le_frontierConst d)
  have h2 : 1 ≤ V5W.topFilterMass ^ 2 := one_le_pow₀ V5WB.one_le_topFilterMass
  have h3 : 1 ≤ 81 * chiDNorm := by have := one_le_chiDNorm; linarith
  exact one_le_mul_of_one_le_of_one_le h1 (one_le_mul_of_one_le_of_one_le h2 h3)

/-- **The absorbed-selection bound** (proved as `prod_selNative_le`, W:MkSlotsI/AsmG3.lean): over the outer slots, the
gains `Rs^{-1/18}` of the selected native vertices dominate those of the absorbed selected trees. -/
def SelNativeBound : Prop :=
  ∀ {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (mkF : Stage1Mk.MarkFn (2 * R)),
    (∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B) →
    ∀ (a : PrescribedPrimeGarden (2 * R)) (Mk : Set (Stage1.CLVine a.prime.skeleton)), Mk = classMk mkF a →
    (∀ j, 1 ≤ Rs j) → (∀ j, (kSel j).isSome → (selCap (MkSlots.recLG a) J kSel j).isSome) →
    ∏ s' : ReplacementSlot (stSt a.prime.skeleton a.totalSigma Mk).G,
      ∏ v ∈ MkSlotsS.selNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel
        (iotaAt a Mk s'), Rs v.1.1 ^ (-(1 / 18 : ℝ)) ≤
      ∏ j : Fin (2 * R), (if (kSel j).isSome ∧ j ∉ (selRAt J kSel a Mk).image (fun v => v.1.1) then
        Rs j ^ (-(1 / 18 : ℝ)) else 1)

theorem slotLeaf_nonneg {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (B : (Fin w × TTree.Path) → NNReal)
    (sl : ReplacementSlot S) : 0 ≤ Represents.slotLeaf D hS layer hLayer B sl := by
  unfold Represents.slotLeaf
  rcases sl with p' | b'
  · exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  · exact Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _

theorem genLeaf_nonneg {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) {b : ℝ} (hb : 0 ≤ b)
    (sl : ReplacementSlot a.prime.skeleton) : 0 ≤ genLeaf a J b sl := by
  rcases sl with q | β
  · refine mul_nonneg ?_ (slotLeaf_nonneg _ _ _ _ _ _)
    split_ifs
    · exact inv_nonneg.2 hb
    · exact zero_le_one
  · simp only [genLeaf]
    exact slotLeaf_nonneg _ _ _ _ _ _

theorem selMassMK_le {R : ℕ} (N : ℕ) {b : ℝ} (hb : 0 ≤ b) (Rs : Fin (2 * R) → ℝ) (hRs : ∀ j, 1 ≤ Rs j)
    (kSel : Fin (2 * R) → Option ℕ) (U : Finset (Fin (2 * R))) :
    0 ≤ selMassMK N b Rs kSel U ∧ selMassMK N b Rs kSel U ≤ b ^ N := by
  have hf : ∀ j, 0 ≤ (if (kSel j).isSome then (Rs j)⁻¹ * (if j ∈ U then 1 else Rs j ^ (-(1 / 18 : ℝ))) else 1) ∧
      (if (kSel j).isSome then (Rs j)⁻¹ * (if j ∈ U then 1 else Rs j ^ (-(1 / 18 : ℝ))) else 1) ≤ 1 := by
    intro j
    have hR0 : 0 < Rs j := lt_of_lt_of_le one_pos (hRs j)
    have hi0 : 0 ≤ (Rs j)⁻¹ := (inv_pos.2 hR0).le
    have hi1 : (Rs j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hRs j)
    have hp0 : 0 ≤ Rs j ^ (-(1 / 18 : ℝ)) := Real.rpow_nonneg hR0.le _
    have hp1 : Rs j ^ (-(1 / 18 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hRs j) (by norm_num)
    split_ifs
    · simp only [mul_one]; exact ⟨hi0, hi1⟩
    · exact ⟨mul_nonneg hi0 hp0, by nlinarith⟩
    · exact ⟨zero_le_one, le_rfl⟩
  unfold selMassMK
  have hP0 := Finset.prod_nonneg fun j (_ : j ∈ (Finset.univ : Finset (Fin (2 * R)))) => (hf j).1
  have hP1 := Finset.prod_le_one₀ (s := (Finset.univ : Finset (Fin (2 * R)))) (fun j _ => (hf j).1)
    (fun j _ => (hf j).2)
  exact ⟨mul_nonneg (pow_nonneg hb _) hP0, mul_le_of_le_one_right (pow_nonneg hb _) hP1⟩

/-- **The arithmetic of the engine's mass hypothesis `hs`.** -/
theorem hs_arith {sg Q1 χ A1 T A2 A3 U1 M bN A4 Lπ A5 Q2 A6 Λ4 Λ7 lift : ℝ}
    (hsg0 : 0 ≤ sg) (hsg : sg ≤ Q1 * χ) (hQ1 : 0 ≤ Q1) (hχ : 0 ≤ χ)
    (hA1 : 0 ≤ A1) (h1 : A1 ≤ T) (hT : 0 ≤ T)
    (hA : 0 ≤ A2 * A3 * U1) (h23 : A2 * A3 * U1 ≤ M * bN) (hM : 0 ≤ M) (hbN : 0 ≤ bN)
    (hA4 : 0 ≤ A4) (h4 : A4 ≤ Lπ) (hA5 : 0 ≤ A5) (h5 : A5 ≤ Q2) (hA6 : 0 ≤ A6) (h6 : A6 ≤ Λ4) (h67 : Λ4 ≤ Λ7)
    (hL : 0 ≤ Lπ) (hQ2 : 0 ≤ Q2) (hΛ4 : 0 ≤ Λ4) (hlift : χ * T * M ≤ lift) :
    sg * ((A1 * (A2 * A3 * A4 * A5 * A6)) * U1) ≤ Λ7 * (lift * (Lπ * (bN * (Q1 * Q2)))) := by
  have e : sg * ((A1 * (A2 * A3 * A4 * A5 * A6)) * U1) = sg * (A1 * ((A2 * A3 * U1) * A4 * A5 * A6)) := by ring
  rw [e]
  have hB : (A2 * A3 * U1) * A4 * A5 * A6 ≤ (M * bN) * Lπ * Q2 * Λ4 :=
    mul_le_mul (mul_le_mul (mul_le_mul h23 h4 hA4 (mul_nonneg hM hbN)) h5 hA5 (mul_nonneg (mul_nonneg hM hbN) hL))
      h6 hA6 (mul_nonneg (mul_nonneg (mul_nonneg hM hbN) hL) hQ2)
  have hB0 : 0 ≤ (A2 * A3 * U1) * A4 * A5 * A6 := mul_nonneg (mul_nonneg (mul_nonneg hA hA4) hA5) hA6
  have hC : A1 * ((A2 * A3 * U1) * A4 * A5 * A6) ≤ T * ((M * bN) * Lπ * Q2 * Λ4) :=
    mul_le_mul h1 hB hB0 hT
  have hC0 : 0 ≤ A1 * ((A2 * A3 * U1) * A4 * A5 * A6) := mul_nonneg hA1 hB0
  calc sg * (A1 * ((A2 * A3 * U1) * A4 * A5 * A6)) ≤ (Q1 * χ) * (T * ((M * bN) * Lπ * Q2 * Λ4)) :=
        mul_le_mul hsg hC hC0 (mul_nonneg hQ1 hχ)
    _ = Λ4 * ((χ * T * M) * (Lπ * (bN * (Q1 * Q2)))) := by ring
    _ ≤ Λ7 * (lift * (Lπ * (bN * (Q1 * Q2)))) := by
        have h0 : 0 ≤ Lπ * (bN * (Q1 * Q2)) := mul_nonneg hL (mul_nonneg hbN (mul_nonneg hQ1 hQ2))
        have hm0 : 0 ≤ χ * T * M := mul_nonneg (mul_nonneg hχ hT) hM
        exact mul_le_mul h67 (mul_le_mul_of_nonneg_right hlift h0) (mul_nonneg hm0 h0) (hΛ4.trans h67)

end WaveTurbulence.Flower.MkSlotsI
