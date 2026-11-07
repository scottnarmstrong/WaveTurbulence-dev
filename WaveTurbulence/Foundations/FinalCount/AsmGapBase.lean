/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmCountBase
/-! **FINALCOUNT-ASSEMBLY: base independence of gaps.**  `gapAt L w κ x₁ x₂ = kvec w κ x₁ - kvec w κ x₂` does not depend on the base `w`
(ruling 4: the terminal bounds of G3/G8 are stated at base `0`/`w`; gaps and hence `gapKind`, `GapSim`, `NoBetaCut` agree). -/
@[expose] public section
set_option autoImplicit false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount

variable {D : Type*} [Fintype D] {d : ℕ}

theorem gapAt_base_indep (L : ℝ) (w w' : Mom d) (κ : D → (Fin d → ℤ)) (x₁ x₂ : D) :
    Molecule.gapAt L w' κ x₁ x₂ = Molecule.gapAt L w κ x₁ x₂ := by
  unfold Molecule.gapAt; rw [kvec_shift L w w' κ x₁, kvec_shift L w w' κ x₂]; abel

theorem gapKind_base_indep (L γ η : ℝ) (w w' : Mom d) (κ : D → (Fin d → ℤ)) (x₁ x₂ : D) :
    Molecule.gapKind L γ η (Molecule.gapAt L w' κ x₁ x₂) = Molecule.gapKind L γ η (Molecule.gapAt L w κ x₁ x₂) := by
  rw [gapAt_base_indep L w w' κ x₁ x₂]

end WaveTurbulence.FinalCountAsm
