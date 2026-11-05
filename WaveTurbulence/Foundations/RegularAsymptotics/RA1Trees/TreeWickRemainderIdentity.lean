/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeKernelProfileMixtures
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickCorrectionExpansion
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LocalTimeRestriction

/-! # Exact actual tree Wick profile splits into NT remainder, Wick correction and leading term -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh IncohInst Links ClassJR ApproxNT WithLp

/-- The literal source squared Wick product agrees with the checked correction's product. -/
theorem treeWickArrayWeight_eq_epsXY {d n : ℕ}
    (g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) :
    treeWickArrayWeight g = ((∏ j, epsXY (g.1 j) (g.2 j)^2:ℝ):ℂ) := by
  unfold treeWickArrayWeight
  apply congrArg Complex.ofReal
  apply Finset.prod_congr rfl
  intro j _
  rw [epsXY_eq_linkEpsilon]
  rfl

/-- The original normalized local Wick scalar is exactly the NT error plus the actual
exceptional Wick correction plus the literal leading approximation. No asymptotic premise,
nonempty order or nonzero delta is needed for this identity. -/
theorem tree_normalized_profile_eq_remainders_add_leading {d n : ℕ} {L : ℝ}
    (hL : 0 < L) (δ γ : ℝ) (J : Finset (Fin n))
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d) (lam : ℝ × ℝ) :
    (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
      treeProfileArrayScalar L (L^(2*γ)*δ) treeWickArrayWeight z β γ' J C lam =
      localRemainder L δ γ J C β γ' lam z +
        normalizedWickCorrection L δ γ z β γ' J C lam +
          (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
            approxApp L δ γ J (fun Ω => C (ofLp Ω) lam) (halfCellAmplitude z β γ') := by
  classical
  let q : ℂ := (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)
  let A := fun g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ) =>
    halfCellAmplitude z β γ' (fun j => latticePoint L (g.1 j)) (fun j => latticePoint L (g.2 j))
  let Ψ := fun g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ) =>
    resProfile J (fun Ω => C (ofLp Ω) lam)
      (fun j => (L^(2*γ)*δ)*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))
  let E := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin d → ℤ) (fun _ => Fin d → ℤ)
  have hWick : normalizedWickCorrection L δ γ z β γ' J C lam =
      q * ∑' g, (treeWickArrayWeight g-1)*(A g*Ψ g) := by
    unfold normalizedWickCorrection
    apply congrArg (fun v : ℂ => q*v)
    rw [← E.symm.tsum_eq]
    apply tsum_congr
    intro g
    rw [treeWickArrayWeight_eq_epsXY]
    rfl
  have hz (g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ))
      (hg : g ∉ halfCellArrayLatticeBox L z) : A g = 0 := by
    by_contra hn
    exact hg (mem_halfCellArrayLatticeBox hL z β γ' g hn)
  have hraw : treeProfileArrayScalar L (L^(2*γ)*δ) treeWickArrayWeight z β γ' J C lam =
      approxSum L (L^(2*γ)*δ) (halfCellAmplitude z β γ') (resProfile J (fun Ω => C (ofLp Ω) lam)) +
        ∑' g, (treeWickArrayWeight g-1)*(A g*Ψ g) := by
    change (∑' g, A g*(treeWickArrayWeight g*Ψ g)) =
      (∑' g, A g*Ψ g) + ∑' g, (treeWickArrayWeight g-1)*(A g*Ψ g)
    rw [tsum_eq_sum (s := halfCellArrayLatticeBox L z) (fun g hg => by rw [hz g hg,zero_mul]),
      tsum_eq_sum (s := halfCellArrayLatticeBox L z) (fun g hg => by rw [hz g hg,zero_mul]),
      tsum_eq_sum (s := halfCellArrayLatticeBox L z) (fun g hg => by rw [hz g hg,zero_mul,mul_zero]),
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro g _
    ring
  rw [hraw,hWick]
  unfold localRemainder
  dsimp only [q]
  ring

end WaveTurbulence.RegAsymp
