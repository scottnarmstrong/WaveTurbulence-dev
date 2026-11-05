/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhysicalLeadingFactor

/-! # Exact finite source profile summation on the original half-cell lattice support -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Links ClassJR WithLp

/-- A finite family of actual regular time profiles commutes with the
squared-Wick half-cell sum. The physical normalization and its original
energy2delta are retained in every resulting frequency density. -/
theorem halfCell_finite_profiles_eq_physicalSymbols {d n : ℕ} {I : Type*} [Fintype I]
    {L : ℝ} (hL : 0 < L) (δ γ : ℝ) (t : Fin 2 → ℝ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : I → Finset (Fin n))
    (C : (i : I) → ({j : Fin n // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ i, SymReg (C i)) (v : I → ℂ) :
    (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)*
      (∑' θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ),
        halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2)*
        (((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ)*
          ∑ i, v i*∫ lam, resProfile (J i) (fun Ω => C i (ofLp Ω) lam)
            (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ)*e2 lam (t 0) (t 1))) =
    ∑ i, v i*pairedInverseProfile
      (fun lam => physicalWeightedCellSymbol L δ γ z β γ' (J i) (C i) lam) t := by
  classical
  let E := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin d → ℤ) (fun _ => Fin d → ℤ)
  let A := fun θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ) =>
    halfCellAmplitude z β γ' (fun j => latticePoint L (θ j).1) (fun j => latticePoint L (θ j).2)
  let p := fun θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ) =>
    ((∏ j, epsXY (θ j).1 (θ j).2^2:ℝ):ℂ)
  let T := fun (i : I) (θ : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) =>
    ∫ lam, resProfile (J i) (fun Ω => C i (ofLp Ω) lam)
      (wickLatticeEnergy L (L^(2*γ)*(2*δ)) θ)*e2 lam (t 0) (t 1)
  let R := fun (i : I) θ => (p θ*A θ)*T i θ
  let q : ℂ := (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)
  have hs (i : I) : Summable (fun θ => v i*R i θ) := by
    apply (summable_halfCell_lattice_pullback hL z β γ' E E.injective
      (fun θ => v i*p θ*T i θ)).congr
    intro θ
    rw [show E θ = ((fun j => (θ j).1),(fun j => (θ j).2)) from rfl]
    change A θ*(v i*p θ*T i θ) = v i*((p θ*A θ)*T i θ)
    ring
  have he (θ) : A θ*(p θ*∑ i, v i*T i θ) = ∑ i, v i*R i θ := by
    rw [← mul_assoc,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (A θ*p θ)*(v i*T i θ) = v i*((p θ*A θ)*T i θ)
    ring
  change q*(∑' θ, A θ*(p θ*∑ i, v i*T i θ)) = _
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun i _ => hs i),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [tsum_mul_left]
  have ht := physicalWeightedCellSymbol_temporal_interchange hL δ γ (t 0) (t 1)
    z β γ' (J i) (hC i)
  change q*(∑' θ, R i θ) = pairedInverseProfile
    (fun lam => physicalWeightedCellSymbol L δ γ z β γ' (J i) (C i) lam) t at ht
  calc
    q*(v i*(∑' θ, R i θ)) = v i*(q*(∑' θ, R i θ)) := by ring
    _ = _ := by rw [ht]

end WaveTurbulence.RegAsymp
