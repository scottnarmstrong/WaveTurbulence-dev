/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKFine.Assembly
public import WaveTurbulence.Foundations.Flower.FinalMKPin.Prefix
public import WaveTurbulence.Foundations.Flower.FinalMKGarden.MainMK
public import WaveTurbulence.Foundations.Flower.FinalMKChain.Top
public import WaveTurbulence.Foundations.Spine.PrefixPieceSmall
public import WaveTurbulence.Foundations.Spine.SpliceGateMonotone
public import WaveTurbulence.Foundations.Spine.FinalCountMonotone
import Mathlib.Tactic

/-! # C4b FINE-PIN: the gate `FineSplicedGateHalfMK`

- `ladderFourierAtMK_largeConstantMonotone`, `finalCountAtMK_largeConstantMonotone`: main's monotonicity in the
  large constants, for the marked statements;
- `prefix_with_L_ge`: a lower bound on `L` can be added to any prefix;
- `fineSplicedGateHalfMK_of_count`: the gate from C4a's `WTPrefix LadderFourierAtMK` and the C1 gate, through
  main's `prefix_and` and `prefix_with_piece_small` (the conditions of main's fine bound);
- **`fineSplicedGateHalfMK : FineSplicedGateHalfMK`**: unconditional, with C1b2's `lowLoopClassBoundMKAll` and
  C1c's `finalCountGateHalfMK_of_classBound`. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs
  WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine
open Set Finset
open scoped Classical ENNReal

theorem ladderFourierAtMK_largeConstantMonotone : LargeConstantMonotone LadderFourierAtMK := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h p hp R hR hRmax G hplain hirr hbal hn hnmax D fix E scales hlayer hD
    hfixE hfixT base roots β
  rw [N_largeConstants] at hnmax
  rw [R_largeConstants] at hRmax
  have h0 := h p hp R hR hRmax G hplain hirr hbal hn hnmax D fix E scales hlayer hD hfixE hfixT base roots β
  refine h0.trans ?_
  have hc1 : 0 ≤ P.C₁ := by linarith
  have hL0 : 0 ≤ P.L := by linarith
  have hδ0 : 0 ≤ P.δ ^ (-1 / 2 - 5 * P.ν) := Real.rpow_nonneg hδ.le _
  have hpow := Real.rpow_nonneg hL0 (P.δ ^ (5 * P.ν) * (G.molecule.rho : ℝ))
  have hQ : 0 ≤ (((G.order : ℝ) + 1) * P.L) ^ (4 * E.card) := by positivity
  simp only [← mul_assoc]
  apply ofReal_mul_mono_any (by positivity)
  apply mul_le_mul_of_nonneg_right _ hpow
  rw [mul_assoc _ P.C₁, mul_assoc _ c₁]
  apply mul_le_mul_of_nonneg_left _ hQ
  exact mul_le_mul h₁ (pow_le_pow_left₀ (mul_nonneg hc1 hδ0) (mul_le_mul_of_nonneg_right h₁ hδ0) _)
    (pow_nonneg (mul_nonneg hc1 hδ0) _) (by linarith)

theorem finalCountAtMK_largeConstantMonotone : LargeConstantMonotone FinalCountAtMK := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h p hp R hR hRmax G hplain hirred hbal hn hnmax D C S hD hgeom hS hch base
    roots Adm hAdm
  rw [N_largeConstants] at hnmax
  rw [R_largeConstants] at hRmax
  have h0 := h p hp R hR hRmax G hplain hirred hbal hn hnmax D C S hD hgeom hS hch base roots Adm hAdm
  refine le_trans ?_ h0
  exact countA_mono_C₁ G.molecule P.L P.γ P.δ P.C₁ c₁ hδ.le (by linarith) h₁ base Adm C.ladderScale

theorem finalCountHalfMK_largeConstantMonotone :
    LargeConstantMonotone (fun P => 1 / 2 < P.γ → FinalCountAtMK P) := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h hγ
  exact finalCountAtMK_largeConstantMonotone P c₁ c₂ hC hC₂ hδ hL h₁ h₂ (h hγ)

/-- A lower bound on `L` can be added to any prefix (the last quantifier is eventual). -/
theorem prefix_with_L_ge {Q : WTParams → Prop} (h : WTPrefix Q) (K : ℝ) :
    WTPrefix (fun P => Q P ∧ K ≤ P.L) := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
  exact ⟨C₂, hC₂, max L₀ K, hL₀.trans (le_max_left _ _),
    fun L hL => ⟨H L ((le_max_left _ _).trans hL), (le_max_right _ _).trans hL⟩⟩

/-- **The gate from the two marked inputs** (C4a's pinned ladder Fourier gate and the C1 gate). -/
theorem fineSplicedGateHalfMK_of_count (hFC : FinalCountGateHalfMK) : FineSplicedGateHalfMK := by
  have hQ : WTPrefix (fun P => LadderFourierAtMK P ∧ (1 / 2 < P.γ → FinalCountAtMK P)) :=
    prefix_and FinalMKPin.ladderFourierMK_prefix hFC ladderFourierAtMK_largeConstantMonotone
      finalCountHalfMK_largeConstantMonotone
  have hm : LargeConstantMonotone (fun P => LadderFourierAtMK P ∧ (1 / 2 < P.γ → FinalCountAtMK P)) :=
    ladderFourierAtMK_largeConstantMonotone.and finalCountHalfMK_largeConstantMonotone
  have h3 := prefix_with_L_ge (prefix_with_piece_small hQ hm) 81
  exact FinalMKPin.wtPrefix_mono h3 fun P hP hγ =>
    fineSplicedAtMK_of_gates P hP.1.1.1 (hP.1.1.2 hγ) hP.2 hP.1.2.1.delta_pos hP.1.2.1.c1_ge
      hP.1.2.1.delta_le hP.1.2.1.cap hP.1.2.1.cap_le hP.1.2.1.delta_exp hP.1.2.1.scale_log
      hP.1.2.1.count_const

/-- **C4b deliverable `FineSplicedGateHalfMK`** (unconditional: C1b2's `lowLoopClassBoundMKAll` and C1c's
`finalCountGateHalfMK_of_classBound` give the C1 gate). -/
theorem fineSplicedGateHalfMK : FineSplicedGateHalfMK :=
  fineSplicedGateHalfMK_of_count
    (FinalMKGarden.finalCountGateHalfMK_of_classBound FinalMKChain.lowLoopClassBoundMKAll)

end WaveTurbulence.Flower.FinalMKFine
