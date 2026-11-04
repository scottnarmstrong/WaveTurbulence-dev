/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ApproxNT.AppRep
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! # Exact scalar transport through the actual NT sum and approximation -/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT
variable {d n : ℕ}

/-- The singular factors in resProfile do not affect scalar linearity. -/
theorem resProfile_const_smul (J : Finset (Fin n))
    (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (c : ℝ) :
    resProfile J (fun Ω => c • Ψ Ω) = fun Ω => c • resProfile J Ψ Ω := by
  funext Ω
  simp only [resProfile,mul_smul_comm]

/-- The actual lattice sum is scalar linear in its temporal symbol. -/
theorem approxSum_const_smul_symbol (L μ : ℝ)
    (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ)
    (J : Finset (Fin n)) (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ) (c : ℝ) :
    approxSum L μ W (resProfile J (fun Ω => c • Ψ Ω)) =
      c • approxSum L μ W (resProfile J Ψ) := by
  simp only [approxSum,resProfile_const_smul,mul_smul_comm]
  exact tsum_const_smul'' c

/-- The actual singular-integral approximation is scalar linear in its symbol. -/
theorem approxApp_const_smul_symbol (L δ γ : ℝ) (J : Finset (Fin n))
    (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ)
    (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) (c : ℝ) :
    approxApp L δ γ J (fun Ω => c • Ψ Ω) W = c • approxApp L δ γ J Ψ W := by
  simp only [approxApp,integral_smul,mul_smul_comm,Algebra.smul_mul_assoc]

/-- Scalar normalization is removed in the literal NT remainder. -/
theorem remainder_const_smul_symbol (L δ γ : ℝ) (J : Finset (Fin n))
    (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ)
    (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) (c : ℝ) :
    approxSum L (L^(2*γ)*δ) W (resProfile J (fun Ω => c • Ψ Ω)) -
        approxApp L δ γ J (fun Ω => c • Ψ Ω) W =
      c • (approxSum L (L^(2*γ)*δ) W (resProfile J Ψ) - approxApp L δ γ J Ψ W) := by
  rw [approxSum_const_smul_symbol,approxApp_const_smul_symbol,smul_sub]

end WaveTurbulence.RegAsymp
