/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickFreeLatticeCount

/-! # Exact amplitude factorization on the Wick coordinate planes -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Finset Incoh

/-- The original modulated source factor at one independent link. -/
def wickLinkAmplitude {d n : ℕ} (L : ℝ) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : Fin n → Mom d) (j : Fin n) (p : (Fin d → ℤ) × (Fin d → ℤ)) : ℂ :=
  (Real.fourierChar (inner ℝ (β j) (latticePoint L p.1)) • halfLinkCell (z (j,0)) (latticePoint L p.1)) *
    (Real.fourierChar (inner ℝ (γ j) (latticePoint L p.2)) • halfLinkCell (z (j,1)) (latticePoint L p.2))

theorem halfCellAmplitude_eq_prod_wickLinkAmplitude {d n : ℕ} (L : ℝ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d)
    (θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :
    halfCellAmplitude z β γ (fun j => latticePoint L (θ j).1)
      (fun j => latticePoint L (θ j).2) = ∏ j, wickLinkAmplitude L z β γ j (θ j) := by
  exact (prod_mul_distrib).symm

/-- The removed links depend only on their remaining free vectors. -/
def wickTracedAmplitude {d n : ℕ} (L : ℝ) (σ : Fin n → Fin 4)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d)
    (v : {j : Fin n // σ j = 1 ∨ σ j = 2} → Fin d → ℤ) : ℂ :=
  ∏ j : {j : Fin n // σ j ≠ 0},
    wickLinkAmplitude L z β γ j.val (wickPatternInsert σ (0,v) j.val)

/-- Exact factorization retains all surviving oscillatory variables.
The trace amplitude contains only finite-box free variables. -/
theorem halfCellAmplitude_wickPatternInsert {d n : ℕ} (L : ℝ) (σ : Fin n → Fin 4)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d)
    (u : WickPatternCoordinates d σ) :
    halfCellAmplitude z β γ (fun j => latticePoint L (wickPatternInsert σ u j).1)
      (fun j => latticePoint L (wickPatternInsert σ u j).2) =
      (∏ j : {j : Fin n // σ j = 0}, wickLinkAmplitude L z β γ j.val (u.1 j)) *
        wickTracedAmplitude L σ z β γ u.2 := by
  classical
  rw [halfCellAmplitude_eq_prod_wickLinkAmplitude]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun j : Fin n => σ j = 0)]
  apply congrArg₂ (fun a b : ℂ => a*b)
  · apply prod_congr rfl
    intro j _
    simp only [wickPatternInsert,dite_eq_left j.property]
  · unfold wickTracedAmplitude
    apply prod_congr rfl
    intro j _
    simp only [wickPatternInsert,dite_eq_right j.property]

/-- All removed smooth factors have norm at most one, regardless of
modulation and without taking absolute values in the surviving sum. -/
theorem norm_wickTracedAmplitude_le_one {d n : ℕ} (L : ℝ) (σ : Fin n → Fin 4)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ : Fin n → Mom d)
    (v : {j : Fin n // σ j = 1 ∨ σ j = 2} → Fin d → ℤ) :
    ‖wickTracedAmplitude L σ z β γ v‖ ≤ 1 := by
  unfold wickTracedAmplitude
  apply (Finset.norm_prod_le _ _).trans
  apply prod_le_one₀
  · intro j _
    exact norm_nonneg _
  · intro j _
    unfold wickLinkAmplitude
    simp only [Circle.smul_def,smul_eq_mul,norm_mul,Circle.norm_coe,one_mul]
    simpa only [one_mul] using mul_le_mul (norm_halfLinkCell_le_one _ _)
      (norm_halfLinkCell_le_one _ _) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)

/-- All counted factors belong to removed links; the NT sum remains intact. -/
theorem norm_sum_wickTracedAmplitude_le {d n : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (σ : Fin n → Fin 4) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : Fin n → Mom d) :
    ‖∑ v ∈ wickFreeLatticeBox L σ z, wickTracedAmplitude L σ z β γ v‖ ≤
      (2^d*L^d)^(wickTracedLinks σ).card := by
  calc
    _ ≤ ∑ v ∈ wickFreeLatticeBox L σ z, ‖wickTracedAmplitude L σ z β γ v‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ wickFreeLatticeBox L σ z, (1:ℝ) :=
      sum_le_sum (fun v _ => norm_wickTracedAmplitude_le_one L σ z β γ v)
    _ = ((wickFreeLatticeBox L σ z).card:ℝ) := by simp
    _ ≤ _ := card_wickFreeLatticeBox_le hL σ z

end WaveTurbulence.RegAsymp
