/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.BondDartReindex
import Mathlib.Tactic

/-! # Empty erasure is an actual relabeling of the original source problem -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def eraseEmptyDartEquiv (M : Molecule V D) : D ≃ Degen.RetainedDart M ∅ where
  toFun x := ⟨x,by simp,by simp⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

theorem countAFree_le_erase_empty (M : Molecule V D) {d : ℕ}
    (L γ δ C1 : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    countAFree M L γ δ C1 w Adm P ≤
      countAFree (Degen.eraseAtoms M ∅) L γ δ C1 w (erasedFreeAdmissibility M ∅ Adm) P := by
  apply countAFree_le_of_bond_preserving_dart_equiv M _ (eraseEmptyDartEquiv M)
  · change M.atoms = M.atoms \ ∅
    simp
  · intro x; rfl
  · intro x; exact Subtype.ext rfl
  · intro x; rfl
  · intro κ hκ hb
    exact ⟨κ,hκ,hb,by funext x; rfl⟩

end WaveTurbulence.MoleProp
