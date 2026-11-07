/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Case23_96
public import WaveTurbulence.Foundations.FinalCount.CaseV96
public import WaveTurbulence.Foundations.FinalCount.CycleCase96
public import WaveTurbulence.Foundations.FinalCount.Odd96
public import WaveTurbulence.Foundations.FinalCount.Case5Final
import Mathlib.Tactic

/-! # Prop 9.6: assembly of the case analysis (DH23 L1854-L1897)

`prop96_of_cases` combines the proved cases (cycles, odd component, cases (2), (3)) with the four remaining even cases
(4) `V_α = 0, V_β = 2`, (5) `V_α = V_β = 1`, (6) `V_α = 2, V_β = 1` and the degenerate `V_α = 0, V_β = 1` (no admissible
decoration, now proved in `CaseV96`). Those three are the named hypotheses `EvenCaseAt` of this CONDITIONAL helper (distinct name; not a source result).
Each has exactly the shape of `case_two` / `case_three`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp

/-- The assembly, conditional on the four remaining even cases. -/
theorem prop96_of_cases (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hsm2 : (d : ℝ) * η ≤ (2 * γ - 1) / 1000)
    (hηs : 4 * 1440061 * η ≤ 1)
    (h4 : EvenCaseAt.{u, v} d γ η (fun a b => a = 0 ∧ b = 2))
    (h5 : EvenCaseAt.{u, v} d γ η (fun a b => a = 1 ∧ b = 1))
    (h6 : EvenCaseAt.{u, v} d γ η (fun a b => a = 2 ∧ b = 1)) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, ∀ L ≥ R₀,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
        FinalShape M cls odd → FinalDec M cls L γ η Adm → (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
        (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm → (∃ v₂ : V, v₂ ∉ M.atoms) →
        M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (finalRHS M cls odd L γ η) := by
  classical
  have hγ0 : min γ (1 - γ) = 1 - γ := min_eq_right (by linarith [hγ.1])
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hη1 : η ≤ min γ (1 - γ) / 200 := by rw [hγ0] at hsm ⊢; nlinarith
  have hη2 : η ≤ (2 * γ - 1) / 100 := by nlinarith
  have hηd : (d : ℝ) * η ≤ min γ (1 - γ) / 4 := by rw [hγ0] at hsm ⊢; linarith
  obtain ⟨Co, hCo, hodd⟩ := case_odd.{u, v} d hd γ hγ η hη hη1 hηd hηs
  obtain ⟨C2, hC2, hcase2⟩ := case_two.{u, v} d hd γ hγ η hη hsm hηs
  obtain ⟨C3, hC3, hcase3⟩ := case_three.{u, v} d hd γ hγ η hη hsm hηs
  obtain ⟨C4, hC4, hcase4⟩ := h4
  obtain ⟨C5, hC5, hcase5⟩ := h5
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
  obtain ⟨Rc, hRc1, hRc⟩ := cycle_case.{u, v} d hd γ hγ η hη (by rw [hγ0] at hsm ⊢; nlinarith) hη2 δ hδ
  set R := max (max (max Ro R2) (max R3 R4)) (max (max R5 R6) (max RV Rc)) with hR
  refine ⟨R, fun L hL V D _ _ _ M cls odd Adm P hS hF hsz hP hMA hfr => ?_⟩
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
    · exact hR4 L hL4 M cls odd Adm P hS hF hsz hP hMA hfr hodd' hcyc ⟨by omega, hb2⟩

/-- The assembly, conditional on the two remaining even cases (4) and (6); case (5) is proved (`case_five`). -/
theorem prop96_of_cases46 (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hsm2 : (d : ℝ) * η ≤ (2 * γ - 1) / 1000)
    (hηs : 4 * 1440061 * η ≤ 1)
    (h4 : EvenCaseAt.{u, v} d γ η (fun a b => a = 0 ∧ b = 2))
    (h6 : EvenCaseAt.{u, v} d γ η (fun a b => a = 2 ∧ b = 1)) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, ∀ L ≥ R₀,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
        FinalShape M cls odd → FinalDec M cls L γ η Adm → (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
        (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm → (∃ v₂ : V, v₂ ∉ M.atoms) →
        M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (finalRHS M cls odd L γ η) := by
  classical
  have hγ0 : min γ (1 - γ) = 1 - γ := min_eq_right (by linarith [hγ.1])
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hη1 : η ≤ min γ (1 - γ) / 200 := by rw [hγ0] at hsm ⊢; nlinarith
  have hη2 : η ≤ (2 * γ - 1) / 100 := by nlinarith
  have hηd : (d : ℝ) * η ≤ min γ (1 - γ) / 4 := by rw [hγ0] at hsm ⊢; linarith
  obtain ⟨Co, hCo, hodd⟩ := case_odd.{u, v} d hd γ hγ η hη hη1 hηd hηs
  obtain ⟨C2, hC2, hcase2⟩ := case_two.{u, v} d hd γ hγ η hη hsm hηs
  obtain ⟨C3, hC3, hcase3⟩ := case_three.{u, v} d hd γ hγ η hη hsm hηs
  obtain ⟨C4, hC4, hcase4⟩ := h4
  obtain ⟨C5, hC5, hcase5⟩ := case_five.{u, v} d hd γ hγ η hη hsm hηs
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
  obtain ⟨Rc, hRc1, hRc⟩ := cycle_case.{u, v} d hd γ hγ η hη (by rw [hγ0] at hsm ⊢; nlinarith) hη2 δ hδ
  set R := max (max (max Ro R2) (max R3 R4)) (max (max R5 R6) (max RV Rc)) with hR
  refine ⟨R, fun L hL V D _ _ _ M cls odd Adm P hS hF hsz hP hMA hfr => ?_⟩
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
    · exact hR4 L hL4 M cls odd Adm P hS hF hsz hP hMA hfr hodd' hcyc ⟨by omega, hb2⟩

end WaveTurbulence.FinalCountG8
