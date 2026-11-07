/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
import Mathlib.Tactic

/-! # The inherited admissibility predicate for actual bond reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- Existential projection through the actual copied-boundary-label map.
All inherited label tests are retained; no new independent label is chosen. -/
def reinsertedPostAdmissibility {d : ℕ} (Adm : (D → (Fin d → ℤ)) → Prop)
    (i : Fin P.edges.length)
    (κ' : Degen.RetainedDart M r.removedAtoms ⊕ Bool → (Fin d → ℤ)) : Prop :=
  ∃ κ : D → (Fin d → ℤ), Adm κ ∧ (∀ x,κ (M.mate x) = κ x) ∧ r.reinsertedLabels κ i = κ'

theorem reinsertedPostAdmissibility_map {d : ℕ} (Adm : (D → (Fin d → ℤ)) → Prop)
    (i : Fin P.edges.length) (κ : D → (Fin d → ℤ)) (hκ : Adm κ)
    (hmate : ∀ x,κ (M.mate x) = κ x) :
    r.reinsertedPostAdmissibility Adm i (r.reinsertedLabels κ i) := ⟨κ,hκ,hmate,rfl⟩

end AppbRealization
end WaveTurbulence.Mole
