/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.CombinedPostTransport
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DartRelabelingEquality
import Mathlib.Tactic

/-! # The flattened and sequential combined post counts are exactly equal -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable {M : Molecule V D} {P Q : AppbPattern}

theorem combinedPost_countA_eq_sequential (r : AppbRealization M P) (s : AppbRealization r.post Q)
    (v0 : M.atoms) {d : ℕ} (L γ δ C1 : ℝ) (w : Mom d) (A : (D → (Fin d → ℤ)) → Prop)
    (q : Fin (r.combinedPattern s).edges.length → (Fin d → ℤ)) (scales : Finset V → ℝ) :
    appbLinkCountA (r.combinedRemoval s v0).post L γ δ C1 w
      ((r.combinedRemoval s v0).conditionedPostAdmissibility A q) scales =
    appbLinkCountA s.post L γ δ C1 w (combinedSequentialAdmissibility r s v0 A q) scales :=
  linkCountA_relabel_eq (r.combinedRemoval s v0).post s.post (combinedPostDartEquiv r s v0)
    (combinedPost_atoms_eq r s v0) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    L γ δ C1 w scales ((r.combinedRemoval s v0).conditionedPostAdmissibility A q)

end WaveTurbulence.Mole.AppbAlgorithm
