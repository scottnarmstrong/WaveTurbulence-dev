/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib
/-! **FINALCOUNT-ASSEMBLY, B/C: the abstract cover induction.**  States `St` with a well-founded order `lt`, classes `A : Set Dec`
(of decorations), a quantity `Q h A ∈ [0,∞]` that is monotone in `A`, subadditive over unions and zero on `∅`, and a potential `W`.
If at every non-final `(h, A)` the class is covered by `≤ N` subclasses `A' j`, each reached by a step `h → h' j` with
`Q h (A' j) ≤ I j * Q (h' j) (A' j)` and `N * (I j * W (h' j)) ≤ W h`, and the final classes satisfy `Q h A ≤ W h`, then `Q h A ≤ W h`
everywhere.  This is the class decomposition + chain induction of the assembly (PLAN §B/C); the concrete content is in the hypotheses. -/
@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm

theorem Q_iUnion_le {St Dec ι : Type*} (Q : St → Set Dec → ℝ≥0∞) (hunion : ∀ h A B, Q h (A ∪ B) ≤ Q h A + Q h B)
    (hempty : ∀ h, Q h ∅ = 0) (h : St) (S : Finset ι) (A : ι → Set Dec) :
    Q h (⋃ j ∈ S, A j) ≤ ∑ j ∈ S, Q h (A j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [hempty]
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (hunion _ _ _).trans (add_le_add_right ih _)

end WaveTurbulence.FinalCountAsm
