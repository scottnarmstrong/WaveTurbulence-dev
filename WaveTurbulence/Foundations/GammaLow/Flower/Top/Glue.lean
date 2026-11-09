/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Top.Caps
public import WaveTurbulence.Foundations.GammaLow.Flower.Reg
public import WaveTurbulence.Foundations.Flower.CompMK.Glue

/-! # FLOWER-LOW (packet L8), item B (6/6): marked = non-regular + regular, and FL-low from its parts

Main's `Flower.CompMK.Glue` γ-carrying declarations copied by source, `1 / 2 < P.γ` ↦ `P.γ ≤ 1 / 2`, names suffixed
`Low`. **`flowerest1_low_of_parts`**: `LayergardenFlowerLowGate` from the non-regular part `NonregLowTarget`
(PLAN-L8 item F) and the named input `CoupleClauseLowInput` (item D); the regular part is item C's
`regularComponentTargetILow` (no hypotheses). -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CompMK
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs Reg Reg.Skeleton LFTwist
open WaveTurbulence.Flower.ProtWhole

/-- **The glue at fixed parameters.** -/
theorem marked_atLow {Pm : ℕ} {P : WTParams} (hL : 2 ≤ P.L) (hd : 1 ≤ P.d) (hδ : 0 < P.δ) {B₁ B : ℝ} (hB : B₁ + 1 ≤ B)
    (hNR : NonregComponentBoundAtILow B₁ Pm P) (hReg : RegularComponentBoundAtILow B₁ Pm P) :
    MarkedComponentBoundAtILow B Pm P := by
  intro hγ p hp R hR1 hR2 n hn1 hn2 t ht s hs J roots hJ pat kSel A hA hplain hTC h b hb hh Rf σ Rs dag hRf hRs
    hhigh
  have hL0 : 0 < P.L := by linarith
  set Qp : ℝ := ∏ j : Fin (2 * R), (if (kSel j).isSome then (Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ)) else 1) with hQp
  have hRs0 : ∀ j, 0 < Rs j := fun j => lt_of_lt_of_le hL0 (hRs j)
  have hQp0 : 0 ≤ Qp := Finset.prod_nonneg fun j _ => by
    split_ifs
    · exact mul_nonneg (inv_nonneg.2 (hRs0 j).le) (Real.rpow_nonneg (hRs0 j).le _)
    · exact zero_le_one
  have hrest : 0 ≤ P.δ ^ (7 * P.ν * n) * b ^ n * Qp :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hδ.le _) (pow_nonneg (by linarith) _)) hQp0
  have h2 := two_rpow_le (B₁ := B₁) (B := B) (d := P.d) hL hd hR1 hB
  have hpos1 : 0 ≤ P.L ^ (B₁ * P.d * ((2 * R : ℕ) : ℝ)) := Real.rpow_nonneg hL0.le _
  have hone : P.L ^ (B₁ * P.d * ((2 * R : ℕ) : ℝ)) ≤ P.L ^ (B * P.d * ((2 * R : ℕ) : ℝ)) := by linarith
  by_cases hR : R = 1
  · subst hR
    set reg : LayeredGarden (2 * 1) → Prop := fun LG => ∀ hw : 2 * 1 = 2, IsRegularCouple (hw ▸ LG.garden : Garden 2)
      with hreg
    rw [← Finset.sum_filter_add_sum_filter_not A reg]
    have hreg_le := hReg hγ p hp 1 rfl hR2 n hn1 hn2 t ht s hs J roots hJ pat kSel (A.filter reg)
      (fun LG hLG => ⟨(hA LG (Finset.mem_filter.1 hLG).1).1, (hA LG (Finset.mem_filter.1 hLG).1).2.1,
        (hA LG (Finset.mem_filter.1 hLG).1).2.2.1, (hA LG (Finset.mem_filter.1 hLG).1).2.2.2.1,
        (hA LG (Finset.mem_filter.1 hLG).1).2.2.2.2, (Finset.mem_filter.1 hLG).2⟩) hplain h b hb hh Rf σ Rs dag
      hRf hRs hhigh
    have hnr_le := hNR hγ p hp 1 hR1 hR2 n hn1 hn2 t ht s hs J roots hJ pat kSel (A.filter fun LG => ¬ reg LG)
      (fun LG hLG => ⟨(hA LG (Finset.mem_filter.1 hLG).1).1, (hA LG (Finset.mem_filter.1 hLG).1).2.1,
        (hA LG (Finset.mem_filter.1 hLG).1).2.2.1, (hA LG (Finset.mem_filter.1 hLG).1).2.2.2.1,
        (hA LG (Finset.mem_filter.1 hLG).1).2.2.2.2, fun hw hr => (Finset.mem_filter.1 hLG).2 fun _ => hr⟩)
      hplain (markedTwistClosed_filter_nonreg A _ (fun LG hLG => (hA LG hLG).1.1) hTC (fun LG => ¬ reg LG)
        fun LG => ⟨fun h1 hw hr => h1 fun _ => hr, fun h1 h2 => h1 rfl (h2 rfl)⟩) h b hb hh Rf σ Rs dag hRf hRs hhigh
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ P.L ^ (B₁ * P.d * ((2 * 1 : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * n) * b ^ n * Qp +
          P.L ^ (B₁ * P.d * ((2 * 1 : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * n) * b ^ n * Qp := add_le_add hreg_le hnr_le
      _ = (2 * P.L ^ (B₁ * P.d * ((2 * 1 : ℕ) : ℝ))) * (P.δ ^ (7 * P.ν * n) * b ^ n * Qp) := by ring
      _ ≤ P.L ^ (B * P.d * ((2 * 1 : ℕ) : ℝ)) * (P.δ ^ (7 * P.ν * n) * b ^ n * Qp) :=
          mul_le_mul_of_nonneg_right h2 hrest
      _ = _ := by ring
  · have hnr_le := hNR hγ p hp R hR1 hR2 n hn1 hn2 t ht s hs J roots hJ pat kSel A
      (fun LG hLG => ⟨(hA LG hLG).1, (hA LG hLG).2.1, (hA LG hLG).2.2.1, (hA LG hLG).2.2.2.1,
        (hA LG hLG).2.2.2.2, fun hw => absurd (by omega : R = 1) hR⟩) hplain hTC h b hb hh Rf σ Rs dag hRf hRs hhigh
    refine hnr_le.trans ?_
    calc P.L ^ (B₁ * P.d * ((2 * R : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * n) * b ^ n * Qp
        = P.L ^ (B₁ * P.d * ((2 * R : ℕ) : ℝ)) * (P.δ ^ (7 * P.ν * n) * b ^ n * Qp) := by ring
      _ ≤ P.L ^ (B * P.d * ((2 * R : ℕ) : ℝ)) * (P.δ ^ (7 * P.ν * n) * b ^ n * Qp) :=
          mul_le_mul_of_nonneg_right hone hrest
      _ = _ := by ring

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CompMK
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs Reg Reg.Skeleton LFTwist
open WaveTurbulence.Flower.ProtWhole

theorem nonregComponentBoundAtI_indepLow (B : ℝ) (Pm : ℕ) (P : WTParams) (c₁ c₂ : ℝ)
    (h : NonregComponentBoundAtILow B Pm {P with C₁ := c₁, C₂ := c₂}) : NonregComponentBoundAtILow B Pm P := by
  simpa only [NonregComponentBoundAtILow, MkCarries, compValue, N_largeConstants] using h

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CompMK
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs Reg Reg.Skeleton LFTwist
open WaveTurbulence.Flower.ProtWhole

theorem regularComponentBoundAtI_indepLow (B : ℝ) (Pm : ℕ) (P : WTParams) (c₁ c₂ : ℝ)
    (h : RegularComponentBoundAtILow B Pm {P with C₁ := c₁, C₂ := c₂}) : RegularComponentBoundAtILow B Pm P := by
  simpa only [RegularComponentBoundAtILow, MkCarries, compValue, N_largeConstants] using h

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.CompMK
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs Reg Reg.Skeleton LFTwist
open WaveTurbulence.Flower.ProtWhole

/-- **The glue** (brief item 2): the non-regular part and D6b's regular part give the per-component bound at
`B = 18000` (each at `17999`). -/
theorem markedComponentBoundAtI_ofLow (hNR : WTPrefixP (NonregComponentBoundAtILow 17999))
    (hReg : WTPrefixP (RegularComponentBoundAtILow 17999)) : WTPrefixP (MarkedComponentBoundAtILow 18000) :=
  prefixP_and_indep hNR hReg (nonregComponentBoundAtI_indepLow 17999) (regularComponentBoundAtI_indepLow 17999)
    fun _ _ hd hL hδ h1 h2 => marked_atLow hL (by omega) hδ (by norm_num) h1 h2

end

/-- **FL-low from its two remaining parts** (conditional helper; PLAN-L8 items F and D): the non-regular part
`NonregLowTarget` and the named input `CoupleClauseLowInput`. The regular part is `regularComponentTargetILow`
(item C, proved), the twist stability is main's `capsTwistStable`, and the chain above the per-component bound is
main's with the carrier `P.γ ≤ 1 / 2` (`flower_low_of_marked_stable`, at `B = 18000 ≤ 24000`). -/
theorem flowerest1_low_of_parts (hN : NonregLowTarget) (hCouple : CoupleClauseLowInput) :
    LayergardenFlowerLowGate :=
  flower_low_of_marked_stable 18000 (by norm_num) (by norm_num)
    (markedComponentBoundAtI_ofLow hN (regularComponentTargetILow 17999 (by norm_num))) hCouple

end WaveTurbulence.GammaLow.Flower
