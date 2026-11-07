/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineHVCGroupGap
public import WaveTurbulence.Foundations.Molecule.VineHyperGapAmbiguity
/-! Diagnostic for the unsuccessful universal-choice route. The source's actual
hyper-object gap can depend on its designated bond. This is not a prime-garden
or LF-batch counterexample and makes no claim that A4 is false. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset LGSpine.SourceVine Vine.HyperGapAudit

/-- Both actual source objects on the audit triple have the same atoms and joints,
but different gap kinds on a conserving decoration. -/
theorem single_hyper_choice_example (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) :
    triple.IsMolecule ∧ triple.IsDecoration 16 0 defects labels ∧
    (∀ v ∈ triple.atoms, triple.deg v = 4 → defects v = 0) ∧
    ∃ P Q : Object triple,
      P.atoms = Q.atoms ∧ P.upper = Q.upper ∧ P.lower = Q.lower ∧
      P.HasGapKind 16 (1 / 2) η 0 labels .LG ∧ Q.HasGapKind 16 (1 / 2) η 0 labels .SG := by
  let P : Object triple := ⟨univ, 0, 1, .hyper ⟨0, by decide,
    ⟨(triple_adjoint_I 0 (Or.inl rfl)).1, 1, Chain.single ⟨.I, triple_adjoint_I 0 (Or.inl rfl)⟩⟩⟩⟩
  let Q : Object triple := ⟨univ, 0, 1, .hyper ⟨2, by decide,
    ⟨(triple_adjoint_I 2 (Or.inr rfl)).1, 1, Chain.single ⟨.I, triple_adjoint_I 2 (Or.inr rfl)⟩⟩⟩⟩
  exact ⟨triple_isMolecule, decorated, defects_at_full, P, Q, rfl, rfl, rfl, ⟨vector 2, outer_gap, (different_gap_kinds η hη0 hη1).1⟩,
    ⟨vector (1 / 16), inner_gap, (different_gap_kinds η hη0 hη1).2⟩⟩

end WaveTurbulence.VineA
