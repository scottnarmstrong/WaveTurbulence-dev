/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountAlgebra

/-! # The literal canonical six-label K4 local counting set

The three momentum equations have been eliminated by an exact integer
affine bijection. All six unit-ball restrictions and all three actual
signed energies are retained. No counting estimate is built into the set.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp
open CountLemmas

/-- The exact canonical K4 fiber after eliminating only the three fixed
momentum equations. The free label order is source labels 2,4,3. -/
def k4CanonicalSet {d : ℕ} (L : ℝ) (A : Fin 6 → Mom d)
    (a b c : Fin d → ℤ) (β : Fin 3 → ℝ) (τ : ℝ) :
    Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) :=
  {q | let k := k4Labels a b c q.1 q.2.1 q.2.2
    (∀ i : Fin 6, NearLattice L (A i) (k i)) ∧
    |-‖latticePoint L (k 0)‖^2+‖latticePoint L (k 1)‖^2+‖latticePoint L (k 3)‖^2-β 0| ≤ τ ∧
    |-‖latticePoint L (k 1)‖^2+‖latticePoint L (k 2)‖^2+‖latticePoint L (k 4)‖^2-β 1| ≤ τ ∧
    |-‖latticePoint L (k 2)‖^2-‖latticePoint L (k 3)‖^2+‖latticePoint L (k 5)‖^2-β 2| ≤ τ}

/-- Finiteness follows from three actual unit-ball restrictions and is
independent of the energy parameters. -/
theorem finite_k4CanonicalSet {d : ℕ} {L : ℝ} (hL : 0 < L)
    (A : Fin 6 → Mom d) (a b c : Fin d → ℤ) (β : Fin 3 → ℝ) (τ : ℝ) :
    (k4CanonicalSet L A a b c β τ).Finite := by
  apply ((finite_nearLattice hL (A 1)).prod
    ((finite_nearLattice hL (A 3)).prod (finite_nearLattice hL (A 2)))).subset
  intro q hq
  exact ⟨hq.1 1,hq.1 3,hq.1 2⟩

end WaveTurbulence.MoleProp
