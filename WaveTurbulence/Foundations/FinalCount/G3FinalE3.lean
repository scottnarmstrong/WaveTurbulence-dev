/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3FinalE2
/-! **FINALCOUNT-G3: `Prop95ConclE`**, the corrected conclusions of Prop 9.5 / TARGET `finalmol` for runs with
tame-atom erasures, and its proof (`HRunE.prop95E`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R R' : ℕ} {M₀ : Molecule V D₀}

/-- TARGET `subpro` (3), L2044: every atom of `M_sub` with a zero-gap triple is SG (hinge) or tame (`Tm`). -/
def DegenSGT (M₀ : Molecule V D₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (Tm : V → Prop) : Prop :=
  ∀ a ∈ M₀.atoms, ∀ x y, M₀.atom x = a → M₀.atom y = a → M₀.out x = false →
    M₀.out y = true → y ≠ M₀.mate x → Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = .ZG →
    SGat M₀ L γ η w κ a ∨ Tm a

theorem InvE.noloop {t : ℕ} {h : HSt V D₀} (hI : InvE M₀ R t L γ η w κ h) :
    ∀ x, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x) := by
  obtain ⟨R', -, hg⟩ := hI.good
  exact hg.1.noloop

end WaveTurbulence.FinalCountG3
