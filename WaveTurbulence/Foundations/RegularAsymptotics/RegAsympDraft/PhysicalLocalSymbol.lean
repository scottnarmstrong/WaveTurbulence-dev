/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickCorrectionExpansion
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LocalTimeRestriction
import Mathlib.Logic.Equiv.Prod

/-! # Exact physical2delta decomposition into NT remainder, leading term and Wick correction -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open ApproxNT Links WithLp

/-- The actual normalized squared-Wick local NT sum at physical energy2delta. -/
def physicalWeightedCellSymbol {d n : ℕ} (L δ γ : ℝ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (lam : ℝ × ℝ) : ℂ :=
  (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)*
    ∑' θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ),
      ((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ)*
        (halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1)
          (fun j => latticePoint L (θ j).2)*
          resProfile J (fun Ω => C (ofLp Ω) lam) (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ))

/-- Doubling delta multiplies the original order2n prefactor by4^n,
including zero delta and the total-division convention at zero lattice scale. -/
theorem doubled_coupling_prefactor (n d : ℕ) (L δ γ : ℝ) :
    ((((2*δ)/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) =
      (4:ℂ)^n*((((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)) := by
  have he : (2*δ)/(2*L^((d:ℝ)-γ)) = 2*(δ/(2*L^((d:ℝ)-γ))) := by ring
  have hr : ((2*δ)/(2*L^((d:ℝ)-γ)))^(2*n) =
      (4:ℝ)^n*(δ/(2*L^((d:ℝ)-γ)))^(2*n) := by
    rw [he,mul_pow,pow_mul]
    norm_num
  simpa only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat] using
    congrArg Complex.ofReal hr

/-- Exact physical-symbol decomposition. Both previously estimated
remainders are evaluated at2delta and multiplied by4^-n; the leading
approxApp retains the original physical coupling prefactor. Finite actual
half-cell support justifies the squared-Wick subtraction. -/
theorem physicalWeightedCellSymbol_decomposition {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (δ γ : ℝ) (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (lam : ℝ × ℝ) :
    physicalWeightedCellSymbol L δ γ z β γ' J C lam =
      ((4:ℂ)^n)⁻¹*localRemainder L (2*δ) γ J C β γ' lam z +
      (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)*
        approxApp L (2*δ) γ J (fun Ω => C (ofLp Ω) lam) (halfCellAmplitude z β γ') +
      ((4:ℂ)^n)⁻¹*normalizedWickCorrection L (2*δ) γ z β γ' J C lam := by
  let E := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin d → ℤ) (fun _ => Fin d → ℤ)
  let W := fun θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ) =>
    halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2)*
      resProfile J (fun Ω => C (ofLp Ω) lam) (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ)
  let p := fun θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ) =>
    ((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ)
  have hs : Summable W := summable_halfCell_lattice_pullback hL z β γ' E E.injective
    (fun θ => resProfile J (fun Ω => C (ofLp Ω) lam) (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ))
  have hp : Summable (fun θ => p θ*W θ) := by
    apply (summable_halfCell_lattice_pullback hL z β γ' E E.injective
      (fun θ => p θ*resProfile J (fun Ω => C (ofLp Ω) lam)
        (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ))).congr
    intro θ
    rw [show E θ = ((fun j => (θ j).1),(fun j => (θ j).2)) from rfl]
    dsimp only [W]
    ring
  have hc : (∑' θ, (p θ-1)*W θ) = (∑' θ, p θ*W θ)-(∑' θ, W θ) := by
    rw [← hp.tsum_sub hs]
    apply tsum_congr
    intro θ
    ring
  have ha : (∑' θ, W θ) = approxSum L (L^(2*γ)*(2*δ)) (halfCellAmplitude z β γ')
      (resProfile J (fun Ω => C (ofLp Ω) lam)) := by
    exact E.tsum_eq (fun g => halfCellAmplitude z β γ'
      (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j))*
        resProfile J (fun Ω => C (ofLp Ω) lam)
          (fun j => (L^(2*γ)*(2*δ))*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j))))
  have halg (q A B T : ℂ) : q*B =
      ((4:ℂ)^n)⁻¹*((4:ℂ)^n*q*(A-T))+q*T+
      ((4:ℂ)^n)⁻¹*((4:ℂ)^n*q*(B-A)) := by
    have hn : (4:ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp [hn]
    ring
  unfold physicalWeightedCellSymbol localRemainder normalizedWickCorrection
  change _ = ((4:ℂ)^n)⁻¹*(_*(_-_))+_*_+((4:ℂ)^n)⁻¹*(_*(∑' θ, (p θ-1)*W θ))
  rw [hc,← ha]
  simp only [doubled_coupling_prefactor]
  exact halg _ _ _ _

end WaveTurbulence.RegAsymp
