/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.TreeWickRemainderIdentity
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhysicalLocalSymbol

/-! # The original tree physical error density at the exact physical NT scale -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open ApproxNT WithLp

/-- The actual NT and Wick error densities with the physical2delta and original coupling. -/
def treePhysicalErrorScalar {d n : ℕ} (L δ γ : ℝ) (J : Finset (Fin n))
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ)
    (β γ' : Fin n → Mom d) (z : (Fin n × Fin 2) → Fin d → ℤ) : ℂ :=
  ((4:ℂ)^n)⁻¹*(localRemainder L (2*δ) γ J C β γ' lam z +
    normalizedWickCorrection L (2*δ) γ z β γ' J C lam)

/-- The ORIGINAL normalized scalar minus its leading term is exactly the actual
physical NT/Wick error density, retaining4^-n and2delta, including n0 and delta0. -/
theorem tree_physical_profile_sub_leading {d n : ℕ} {L : ℝ} (hL : 0 < L) (δ γ : ℝ)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d) (lam : ℝ × ℝ) :
    (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)*
      (treeProfileArrayScalar L (2*δ*L^(2*γ)) treeWickArrayWeight z β γ' J C lam -
        approxApp L (2*δ) γ J (fun Ω => C (ofLp Ω) lam) (halfCellAmplitude z β γ')) =
      treePhysicalErrorScalar L δ γ J C lam β γ' z := by
  have hs := tree_normalized_profile_eq_remainders_add_leading hL (2*δ) γ J C z β γ' lam
  have hq := doubled_coupling_prefactor n d L δ γ
  have hp : (4:ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have harg : L^(2*γ)*(2*δ)=2*δ*L^(2*γ) := by ring
  rw [harg] at hs
  unfold treePhysicalErrorScalar
  calc
    _ = ((4:ℂ)^n)⁻¹*(
        ((((2*δ)/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)*
          treeProfileArrayScalar L (2*δ*L^(2*γ)) treeWickArrayWeight z β γ' J C lam -
        ((((2*δ)/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)*
          approxApp L (2*δ) γ J (fun Ω => C (ofLp Ω) lam) (halfCellAmplitude z β γ')) := by
      rw [hq]
      field_simp [hp]
    _ = _ := by rw [hs]; ring

end WaveTurbulence.RA1Leafwise
