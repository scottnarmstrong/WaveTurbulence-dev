/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickSliceEnvelope
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellFiniteSupport

/-! # Exact actual Wick correction as a finite sum of source slices -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Finset ApproxNT WithLp Links

/-- The original squared Wick factor minus the unmasked source term. -/
def normalizedWickCorrection {d n : ℕ} (L δ γ : ℝ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (lam : ℝ × ℝ) : ℂ :=
  (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
    ∑' θ, (((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ)-1) *
      (halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1)
        (fun j => latticePoint L (θ j).2) *
        resProfile J (fun Ω => C (ofLp Ω) lam) (wickLatticeEnergy L (L^(2*γ)*δ) θ))

/-- A pattern meeting a special energy contributes identically zero. -/
theorem normalizedWickSlice_eq_zero_of_not_disjoint {d n : ℕ} (L δ γ : ℝ)
    (σ : Fin n → Fin 4) (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (lam : ℝ × ℝ) (h : ¬Disjoint (wickTracedLinks σ) J) :
    normalizedWickSlice L δ γ σ z β γ' J C lam = 0 := by
  unfold normalizedWickSlice
  rw [tsum_wickPatternTerm_mul]
  have he (u : WickPatternCoordinates d σ) :
      halfCellAmplitude z β γ' (fun j => latticePoint L (wickPatternInsert σ u j).1)
        (fun j => latticePoint L (wickPatternInsert σ u j).2) *
        resProfile J (fun Ω => C (ofLp Ω) lam)
          (wickLatticeEnergy L (L^(2*γ)*δ) (wickPatternInsert σ u)) = 0 := by
    rw [resProfile_wickPatternInsert_eq_zero L (L^(2*γ)*δ) σ u J _ h,mul_zero]
  simp_rw [he]
  rw [tsum_zero,mul_zero,mul_zero]

/-- Finite-support Fubini preserves the exact inclusion-exclusion
coefficients, including the doubled both-zero intersections. -/
theorem normalizedWickCorrection_eq_sum {d n : ℕ} {L : ℝ} (hL : 0 < L) (δ γ : ℝ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (lam : ℝ × ℝ) :
    normalizedWickCorrection L δ γ z β γ' J C lam =
      ∑ σ ∈ ((univ : Finset (Fin n → Fin 4)).erase 0), normalizedWickSlice L δ γ σ z β γ' J C lam := by
  classical
  let E := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin d → ℤ) (fun _ => Fin d → ℤ)
  have hs (σ : Fin n → Fin 4) : Summable (fun θ => (∏ j, wickPatternTerm θ j (σ j)) *
      (halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1)
        (fun j => latticePoint L (θ j).2) *
        resProfile J (fun Ω => C (ofLp Ω) lam) (wickLatticeEnergy L (L^(2*γ)*δ) θ))) := by
    convert summable_halfCell_lattice_pullback hL z β γ' E E.injective
      (fun θ => (∏ j, wickPatternTerm θ j (σ j))*
        resProfile J (fun Ω => C (ofLp Ω) lam) (wickLatticeEnergy L (L^(2*γ)*δ) θ)) using 1
    funext θ
    change (∏ j, wickPatternTerm θ j (σ j)) *
      (halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2)*
        resProfile J (fun Ω => C (ofLp Ω) lam) (wickLatticeEnergy L (L^(2*γ)*δ) θ)) =
      halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2)*
        ((∏ j, wickPatternTerm θ j (σ j))*resProfile J (fun Ω => C (ofLp Ω) lam)
          (wickLatticeEnergy L (L^(2*γ)*δ) θ))
    ring
  unfold normalizedWickCorrection normalizedWickSlice
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [wick_difference_inclusion_exclusion,Finset.sum_mul]
  exact Summable.tsum_finsetSum (fun σ _ => hs σ)

end WaveTurbulence.RegAsymp
