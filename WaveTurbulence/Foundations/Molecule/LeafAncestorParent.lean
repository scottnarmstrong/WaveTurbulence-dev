/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.CollapsedTwistForest

/-! # Ancestors of actual child leaves

TARGET twist: the leaf paired with u23 is outside the lower subtree.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w)

/-- An ancestor branch of a child leaf is already an ancestor of its parent. -/
theorem branch_desc_leaf_parent {b c : GBranch G.tree} {l : GLeaf G.tree} {j : Fin 3}
    (hl : l.toNode = c.child j) (hd : b.toNode.IsDesc l.toNode) : b.toNode.IsDesc c.toNode := by
  rw [hl] at hd
  change b.1.1 = c.1.1 ∧ b.1.2 <+: c.1.2 ++ [j] at hd
  have hne : b.1.2 ≠ c.1.2 ++ [j] := by
    intro he
    have hn : b.toNode = l.toNode := by
      rw [hl]
      exact Subtype.ext (Prod.ext hd.1 he)
    exact Mole.branch_toNode_ne_leaf b l hn
  have hlen := hd.2.length_le
  have hlt : b.1.2.length < (c.1.2 ++ [j]).length := by
    have hnot : b.1.2.length ≠ (c.1.2 ++ [j]).length := fun he => hne (hd.2.eq_of_length he)
    omega
  refine ⟨hd.1,?_⟩
  change b.1.2 <+: c.1.2
  exact List.prefix_of_prefix_length_le hd.2 (List.prefix_append c.1.2 [j]) (by
    simp only [List.length_append,List.length_singleton] at hlt
    omega)

/-- A paired child leaf whose selected parent is excluded below b lies outside the lower subtree. -/
theorem child_leaf_outside_of_terminal {S : Finset (GBranch G.tree)} {b c : GBranch G.tree}
    (hc : c ∈ S) (hne : c ≠ b)
    (hterminal : ∀ z ∈ S, b.toNode.IsDesc z.toNode → z = b)
    {l : GLeaf G.tree} {j : Fin 3} (hl : l.toNode = c.child j) : ¬ b.toNode.IsDesc l.toNode := by
  intro hd
  exact hne (hterminal c hc (branch_desc_leaf_parent G hl hd))

end WaveTurbulence.Twist
