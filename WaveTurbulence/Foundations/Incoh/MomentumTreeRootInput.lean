/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RootInputCoordinates

/-! # Appending a temporary root input to a tree's actual momentum rows

The lone leaf becomes one genuine input for localization. Its temporary
smooth cutoff will be removed by a root partition of unity in the tree
spatial assembly. Every field below is a finite source identity.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- Append the actual root row as one additional input, leaving all original source rows intact. -/
@[expose] def MomentumTreeData.withRootInput {n m w : ℕ} (P : MomentumTreeData n m w) :
    MomentumTreeData n (m + 1) w where
  tree := P.tree
  order_eq := P.order_eq
  nodeRow := P.nodeRow
  inputRow := Fin.lastCases (momentumUnitRow none) P.inputRow
  input_root_column := by
    intro a
    refine Fin.lastCases ?_ (fun b => ?_) a
    · simp [momentumUnitRow]
    · simpa only [Fin.lastCases_castSucc] using P.input_root_column b
  leafInput := fun i p => some ((P.leafInput i p).elim (Fin.last m) Fin.castSucc)
  root_row := P.root_row
  parent_row := P.parent_row
  leaf_row := by
    intro i p hp
    have h := P.leaf_row i p hp
    cases he : P.leafInput i p with
    | none => simpa [he] using h
    | some a => simpa [he] using h
  chosenTree := P.chosenTree
  chosenPath := P.chosenPath
  chosen_mem_nodes := P.chosen_mem_nodes
  child0_mem_nodes := P.child0_mem_nodes
  child2_mem_nodes := P.child2_mem_nodes
  link_x_row := P.link_x_row
  link_y_row := P.link_y_row

/-- All source leaves, including the lone root-valued leaf, now have an actual input index. -/
theorem MomentumTreeData.withRootInput_all_leaves {n m w : ℕ} (P : MomentumTreeData n m w) :
    ∀ i p, p ∈ (P.withRootInput.tree i).leaves → P.withRootInput.leafInput i p ≠ none := by
  intro i p _
  simp only [withRootInput, ne_eq, reduceCtorEq, not_false_eq_true]

/-- Original source inputs evaluate to exactly their original momenta. -/
theorem MomentumTreeData.withRootInput_inputMomentum_castSucc {d n m w : ℕ}
    (P : MomentumTreeData n m w) (k : Mom d) (x : Fin n → Fin 2 → Mom d) (a : Fin m) :
    P.withRootInput.inputMomentum k x a.castSucc = P.inputMomentum k x a := by
  simp only [MomentumTreeData.inputMomentum, withRootInput, Fin.lastCases_castSucc]

/-- The appended input evaluates to the actual root momentum. -/
theorem MomentumTreeData.withRootInput_inputMomentum_last {d n m w : ℕ}
    (P : MomentumTreeData n m w) (k : Mom d) (x : Fin n → Fin 2 → Mom d) :
    P.withRootInput.inputMomentum k x (Fin.last m) = k := by
  simp only [MomentumTreeData.inputMomentum, withRootInput, Fin.lastCases_last,
    momentumRowEval_unit, rootLinkMomenta]

/-- A root-row certificate for the augmented data is the finite unit row at the appended input. -/
@[expose] def MomentumTreeData.withRootInputCoordinates {n m w : ℕ} (P : MomentumTreeData n m w) :
    RootInputCoordinates P.withRootInput where
  sigma := Pi.single (Fin.last m) 1
  abs_sigma_le := by
    intro a
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  root_row := by
    classical
    simp only [Pi.single_apply]
    simp [withRootInput]

end WaveTurbulence.Incoh
