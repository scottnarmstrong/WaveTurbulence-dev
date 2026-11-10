/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalErrorScalar

/-! # A single actual scalar envelope for the finite original physical error -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links ApproxNT

/-- The original source weights and physical normalization cost at most
one; the combined scalar envelope pays only the finite original powerset. -/
theorem norm_physicalErrorScalar_le {d : ℕ} (L δ γ : ℝ) (Q : RegCpl) (ζ : ℂ)
    (hζ : ‖ζ‖ ≤ 1)
    (C : (Z : (chosenSet Q.links).powerset) →
      ({j : Fin Q.links.length // j ∉ markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ)
    (lam : ℝ × ℝ) (β γ' : Fin Q.links.length → Mom d)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ)
    {rN rW r : ℝ} (hNr : rN ≤ r) (hWr : rW ≤ r)
    (BN BW : (chosenSet Q.links).powerset → ℝ) (hBN : ∀ Z, 0 ≤ BN Z) (hBW : ∀ Z, 0 ≤ BW Z)
    (hN : ∀ Z : (chosenSet Q.links).powerset,
      ‖localRemainder L (2*δ) γ (markedLinkIndices Q Z.val) (C Z) β γ' lam z‖ ≤
        ((1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*rN)*BN Z)
    (hW : ∀ Z : (chosenSet Q.links).powerset,
      ‖normalizedWickCorrection L (2*δ) γ z β γ' (markedLinkIndices Q Z.val) (C Z) lam‖ ≤
        ((1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*rW)*BW Z) :
    ‖physicalErrorScalar L δ γ Q ζ C lam β γ' z‖ ≤
      ((1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*r)*∑ Z, (BN Z+BW Z) := by
  classical
  let H := (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  unfold physicalErrorScalar
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_right hζ (norm_nonneg _)).trans
  rw [one_mul]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Z _
  have hv : ‖(∏ a ∈ Z.val, ((Cancel.zetaA a:ℂ)*Real.pi*Complex.I)⁻¹)*((4:ℂ)^Q.links.length)⁻¹‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (norm_original_source_weight_le_one Z.val)
      (norm_inverse_four_pow_le_one Q.links.length) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  calc
    _ ≤ 1*‖localRemainder L (2*δ) γ (markedLinkIndices Q Z.val) (C Z) β γ' lam z +
        normalizedWickCorrection L (2*δ) γ z β γ' (markedLinkIndices Q Z.val) (C Z) lam‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hv (norm_nonneg _)
    _ ≤ H*rN*BN Z+H*rW*BW Z := by
      rw [one_mul]
      exact (norm_add_le _ _).trans (add_le_add (hN Z) (hW Z))
    _ ≤ H*r*BN Z+H*r*BW Z := add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNr hH) (hBN Z))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWr hH) (hBW Z))
    _ = _ := by dsimp only [H]; ring

end WaveTurbulence.RA1Leafwise
