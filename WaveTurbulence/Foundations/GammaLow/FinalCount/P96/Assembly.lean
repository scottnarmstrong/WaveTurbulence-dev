/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Assembly96
public import WaveTurbulence.Foundations.GammaLow.FinalCount.P96.Statement
public import WaveTurbulence.Foundations.GammaLow.FinalCount.P96.Cycle
public import WaveTurbulence.Foundations.GammaLow.FinalCount.P96.Case5
import Mathlib.Tactic

/-! # Prop 9.6 at `0 < γ ≤ 1/2`: assembly of the case analysis (DH23 L1854–L1897; M2 §4)

Port of main's `prop96_of_cases46` (`FinalCount/Assembly96.lean`): the cycles, the odd component and cases (2), (3), (5)
at `γ ≤ 1/2` (this packet), the degenerate `V_α = 0, V_β = 1` (main's `caseV`, all `γ`), and the two remaining even
cases as hypotheses: case (4)′ in the shape `EvenCaseLowAt` (it reads `vineLG` over `𝒱_γ`) and case (6) in the shape
`EvenCaseAt`. Hypotheses on `η`: `hsm`, `hηs` only (no `hsm2`, no `η ≤ (2γ − 1)/100`). -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount
universe u v
open WaveTurbulence.FinalCountG8 WaveTurbulence.MoleProp

/-- **Prop 9.6 at `γ ≤ 1/2`, conditional on case (4)′ and case (6)** (conditional helper, distinct name). Cases (1), (2),
(3), (5), the cycles and the degenerate `V_α = 0, V_β = 1` are proved; `FinalDecLow → FinalDec` by N2 Lemma 5.2. -/
theorem prop96_low_of_cases46 (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1) (hDT : DrawnTVineInput.{u, v})
    (h4 : EvenCaseLowAt.{u, v} d γ η (fun a b => a = 0 ∧ b = 2))
    (h6 : EvenCaseAt.{u, v} d γ η (fun a b => a = 2 ∧ b = 1)) :
    Prop96LowAt.{u, v} d γ η := by
  classical
  have hγ0 : min γ (1 - γ) = γ := min_gamma_low hγ.2
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hη1 : η ≤ min γ (1 - γ) / 200 := by rw [hγ0] at hsm ⊢; nlinarith
  have hηd : (d : ℝ) * η ≤ min γ (1 - γ) / 4 := by rw [hγ0] at hsm ⊢; linarith
  obtain ⟨Co, hCo, hodd⟩ := case_odd_low.{u, v} d hd γ hγ η hη hη1 hηd hηs
  obtain ⟨C2, hC2, hcase2⟩ := case_two_low.{u, v} d hd γ hγ η hη hsm hηs
  obtain ⟨C3, hC3, hcase3⟩ := case_three_low.{u, v} d hd γ hγ η hη hsm hηs
  obtain ⟨C4, hC4, hcase4⟩ := h4
  obtain ⟨C5, hC5, hcase5⟩ := case_five_low_even.{u, v} d hd γ hγ η hη hsm hηs
  obtain ⟨C6, hC6, hcase6⟩ := h6
  obtain ⟨CV, hCV, hcaseV⟩ := caseV.{u, v} d γ η
  set Cm := max (max (max Co C2) (max C3 C4)) (max (max C5 C6) CV) with hCm
  have hCo' : Co ≤ Cm := by simp [hCm]
  have hC2' : C2 ≤ Cm := by simp [hCm]
  have hC3' : C3 ≤ Cm := by simp [hCm]
  have hC4' : C4 ≤ Cm := by simp [hCm]
  have hC5' : C5 ≤ Cm := by simp [hCm]
  have hC6' : C6 ≤ Cm := by simp [hCm]
  have hCV' : CV ≤ Cm := by simp [hCm]
  refine ⟨Cm, le_trans hCo hCo', fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨Ro, hRo1, hRo⟩ := hodd m C1 (hCo'.trans hC1) δ hδ
  obtain ⟨R2, hR21, hR2⟩ := hcase2 m C1 (hC2'.trans hC1) δ hδ
  obtain ⟨R3, hR31, hR3⟩ := hcase3 m C1 (hC3'.trans hC1) δ hδ
  obtain ⟨R4, hR41, hR4⟩ := hcase4 m C1 (hC4'.trans hC1) δ hδ
  obtain ⟨R5, hR51, hR5⟩ := hcase5 m C1 (hC5'.trans hC1) δ hδ
  obtain ⟨R6, hR61, hR6⟩ := hcase6 m C1 (hC6'.trans hC1) δ hδ
  obtain ⟨RV, hRV1, hRV⟩ := hcaseV m C1 (hCV'.trans hC1) δ hδ
  obtain ⟨Rc, hRc1, hRc⟩ := cycle_case_low.{u, v} d hd γ hγ η hη (by rw [hγ0] at hsm ⊢; nlinarith) δ hδ
  set R := max (max (max Ro R2) (max R3 R4)) (max (max R5 R6) (max RV Rc)) with hR
  refine ⟨R, fun L hL V D _ _ _ M cls odd Adm P hS hFL hsz hP hMA hfr => ?_⟩
  have hF : FinalDec M cls L γ η Adm := finalDec_of_low hDT hγ.2 hFL
  have hLo : Ro ≤ L := le_trans (by simp [hR]) hL
  have hL2 : R2 ≤ L := le_trans (by simp [hR]) hL
  have hL3 : R3 ≤ L := le_trans (by simp [hR]) hL
  have hL4 : R4 ≤ L := le_trans (by simp [hR]) hL
  have hL5 : R5 ≤ L := le_trans (by simp [hR]) hL
  have hL6 : R6 ≤ L := le_trans (by simp [hR]) hL
  have hLV : RV ≤ L := le_trans (by simp [hR]) hL
  have hLc : Rc ≤ L := le_trans (by simp [hR]) hL
  have hC11 : 1 ≤ C1 := le_trans (le_trans hCo hCo') hC1
  by_cases hcyc : ∀ a ∈ M.atoms, M.deg a = 2
  · exact hRc L hLc C1 hC11 M cls odd Adm P hS hF hcyc hMA
  by_cases hodd' : odd
  · exact hRo L hLo M cls odd Adm P hS hF hsz hP hMA hodd'
  -- even, non-cycle
  obtain ⟨b, hb, hbβ⟩ := hS.evenBeta hodd'
  have hVb : 1 ≤ (betaAtoms M.atoms cls).card := card_pos.mpr ⟨b, mem_filter.mpr ⟨hb, hbβ⟩⟩
  by_cases h3 : 3 ≤ (betaAtoms M.atoms cls).card
  · exact hR2 L hL2 M cls odd Adm P hS hF hsz hP hMA hodd' hcyc h3
  have hb12 : (betaAtoms M.atoms cls).card = 1 ∨ (betaAtoms M.atoms cls).card = 2 := by omega
  rcases hb12 with hb1 | hb2
  · by_cases ha3 : 3 ≤ (alphaAtoms M.atoms cls).card
    · exact hR3 L hL3 M cls odd Adm P hS hF hsz hP hMA hodd' hcyc (Or.inr ⟨hb1, ha3⟩)
    have ha012 : (alphaAtoms M.atoms cls).card = 0 ∨ (alphaAtoms M.atoms cls).card = 1 ∨
        (alphaAtoms M.atoms cls).card = 2 := by omega
    rcases ha012 with ha | ha | ha
    · exact hRV L hLV M cls odd Adm P hS hF hsz hP hMA hfr hodd' hcyc ⟨ha, hb1⟩
    · exact hR5 L hL5 M cls odd Adm P hS hF hsz hP hMA hfr hodd' hcyc ⟨ha, hb1⟩
    · exact hR6 L hL6 M cls odd Adm P hS hF hsz hP hMA hfr hodd' hcyc ⟨ha, hb1⟩
  · by_cases ha1 : 1 ≤ (alphaAtoms M.atoms cls).card
    · exact hR3 L hL3 M cls odd Adm P hS hF hsz hP hMA hodd' hcyc (Or.inl ⟨hb2, ha1⟩)
    · exact hR4 L hL4 M cls odd Adm P hS hFL hsz hP hMA hfr hodd' hcyc ⟨by omega, hb2⟩

end WaveTurbulence.GammaLow.FinalCount
