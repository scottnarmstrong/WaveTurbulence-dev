/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.JointChildSlots

/-!
# Ordered child signs in the actual garden carrier

The two outer positions preserve the parent's sign; the middle position
reverses it. These signs determine the exclusive type-I source cases.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree
variable {w : ℕ} (G : Garden w)

/-- Ordered children of an actual garden branch are positionally distinct. -/
theorem child_injective (v : GBranch G.tree) : Function.Injective v.child := by
  intro i j h
  have he := congrArg (fun n : GNode G.tree => n.1.2) h
  change v.1.2++[i] = v.1.2++[j] at he
  exact List.singleton_injective (List.append_cancel_left he)

/-- The three child signs, in the source left/middle/right convention. -/
theorem child_signs (v : GBranch G.tree) :
    G.sign (v.child 0) = G.sign v.toNode ∧
      G.sign (v.child 1) = -G.sign v.toNode ∧ G.sign (v.child 2) = G.sign v.toNode := by
  simp [Garden.sign,nodeSign,TTree.pathSign,GBranch.child,List.count_append,pow_succ,GBranch.toNode]

/-- Opposite signs of two children force exactly one of their slots to be middle. -/
theorem opposite_child_sign_iff (v : GBranch G.tree) (i j : Fin 3) :
    G.sign (v.child j) = -G.sign (v.child i) ↔
      (i ≠ 1 ∧ j = 1) ∨ (i = 1 ∧ j ≠ 1) := by
  have hs := child_signs G v
  rcases Int.units_eq_one_or (G.sign v.toNode) with h | h
  all_goals fin_cases i <;> fin_cases j <;> simp [hs.1,hs.2.1,hs.2.2,h]

end WaveTurbulence.Molecpl
