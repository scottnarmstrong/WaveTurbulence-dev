/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Case23_96
import Mathlib.Tactic

/-! # Prop 9.6: the shape of a case theorem for an even, non-cycle component -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp

/-- The shape of a case theorem for an even, non-cycle component with `V_α = a`, `V_β = b` satisfying `Cnd a b`. -/
def EvenCaseAt.{u', v'} (d : ℕ) (γ η : ℝ) (Cnd : ℕ → ℕ → Prop) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {V : Type u'} {D : Type v'} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      FinalShape M cls odd → FinalDec M cls L γ η Adm → (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
      (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm →
      (∃ v₂ : V, v₂ ∉ M.atoms) → ¬ odd →
      (¬ ∀ a ∈ M.atoms, M.deg a = 2) → Cnd (alphaAtoms M.atoms cls).card (betaAtoms M.atoms cls).card →
      M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (finalRHS M cls odd L γ η)

end WaveTurbulence.FinalCountG8
