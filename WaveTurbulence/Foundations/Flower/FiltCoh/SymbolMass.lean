/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.CoupleEnvelope
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeWickRemainderIdentity

/-! # FILT-COH: one physical cell symbol at weight `θ`, and its tree form

`physical_symbol_envelope_theta` is the single-coefficient envelope (geometric mass, no `L` loss). The tree kernel
identity of main (`RA1Leafwise.KTstar_classified_leaf_profile_mixtures`) carries the symbol as
`N(δ) · treeProfileArrayScalar` (`physicalWeightedCellSymbol_eq_tree`). -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh
open scoped ENNReal

variable {d : ℕ}

/-- The tree scalar with the physical normalization is the physical cell symbol. -/
theorem physicalWeightedCellSymbol_eq_tree {n : ℕ} {L : ℝ} (hL : 0 < L) (δ γ : ℝ)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d) (lam : ℝ × ℝ) :
    physicalWeightedCellSymbol L δ γ z β γ' J C lam =
      (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
        treeProfileArrayScalar L (2*δ*L^(2*γ)) RA1Leafwise.treeWickArrayWeight z β γ' J C lam := by
  have hs := RA1Leafwise.tree_normalized_profile_eq_remainders_add_leading hL (2*δ) γ J C z β γ' lam
  have harg : L^(2*γ)*(2*δ) = 2*δ*L^(2*γ) := by ring
  rw [harg, doubled_coupling_prefactor] at hs
  rw [physicalWeightedCellSymbol_decomposition hL]
  unfold localRemainder at hs ⊢
  rw [doubled_coupling_prefactor] at hs ⊢
  have h4 : (4:ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hq : (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
      treeProfileArrayScalar L (2*δ*L^(2*γ)) RA1Leafwise.treeWickArrayWeight z β γ' J C lam =
      ((4:ℂ)^n)⁻¹ * ((4:ℂ)^n * (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
        treeProfileArrayScalar L (2*δ*L^(2*γ)) RA1Leafwise.treeWickArrayWeight z β γ' J C lam) := by
    field_simp
  rw [hq, hs]
  field_simp
  ring

end WaveTurbulence.Flower.FiltCoh
