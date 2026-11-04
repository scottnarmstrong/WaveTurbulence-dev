/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreeForestLocalization

/-!
# Finite momentum-tree coordinates for source localization

C2's integer node expansions supply these structural rows. The actual
momentum decoration and link differences are computed, not fields carrying
analytic bounds. The two root/link momentum coordinates of a link remain
free; source leaves may be paired inputs or the lone root-valued leaf.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- One root coordinate and the two free momentum coordinates of each link. -/
abbrev MomentumCoordinate (n : ℕ) := Option (Fin n × Fin 2)

/-- The integer row selecting one actual root/link momentum coordinate. -/
@[expose] def momentumUnitRow {n : ℕ} (i : MomentumCoordinate n) : MomentumCoordinate n → ℤ :=
  fun j => if j = i then 1 else 0

/-- Structural integer momentum data for a finite forest of total order `2n`. -/
structure MomentumTreeData (n m w : ℕ) where
  tree : Fin w → LocalizationTree
  order_eq : (∑ i, (tree i).order) = 2 * n
  nodeRow : Fin w → LocalizationTree.Path → MomentumCoordinate n → ℤ
  inputRow : Fin m → MomentumCoordinate n → ℤ
  input_root_column : ∀ a, inputRow a none = 1
  leafInput : Fin w → LocalizationTree.Path → Option (Fin m)
  root_row : ∀ i, nodeRow i [] = momentumUnitRow none
  parent_row : ∀ i p, p ∈ (tree i).branching →
    nodeRow i p = nodeRow i (p ++ [0]) - nodeRow i (p ++ [1]) + nodeRow i (p ++ [2])
  leaf_row : ∀ i p, p ∈ (tree i).leaves → nodeRow i p =
    match leafInput i p with
    | none => momentumUnitRow none
    | some a => inputRow a
  chosenTree : Fin n → Fin w
  chosenPath : Fin n → LocalizationTree.Path
  chosen_mem_nodes : ∀ i, chosenPath i ∈ (tree (chosenTree i)).nodes
  child0_mem_nodes : ∀ i, chosenPath i ++ [0] ∈ (tree (chosenTree i)).nodes
  child2_mem_nodes : ∀ i, chosenPath i ++ [2] ∈ (tree (chosenTree i)).nodes
  link_x_row : ∀ i,
    nodeRow (chosenTree i) (chosenPath i ++ [0]) - nodeRow (chosenTree i) (chosenPath i) =
      momentumUnitRow (some (i, 0))
  link_y_row : ∀ i,
    nodeRow (chosenTree i) (chosenPath i) - nodeRow (chosenTree i) (chosenPath i ++ [2]) =
      momentumUnitRow (some (i, 1))

/-- Evaluate an actual integer coefficient row on vector momenta. -/
@[expose] def momentumRowEval {n : ℕ} {V : Type*} [AddCommGroup V]
    (u : MomentumCoordinate n → V) : (MomentumCoordinate n → ℤ) →+ V where
  toFun a := ∑ j, a j • u j
  map_zero' := by simp
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- A coordinate row evaluates to the actual coordinate it selects. -/
theorem momentumRowEval_unit {n : ℕ} {V : Type*} [AddCommGroup V]
    (u : MomentumCoordinate n → V) (i : MomentumCoordinate n) :
    momentumRowEval u (momentumUnitRow i) = u i := by
  classical
  cases i <;> simp [momentumRowEval, momentumUnitRow]

/-- The actual node momentum obtained from the source integer expansion. -/
@[expose] def MomentumTreeData.nodeMomentum {n m w : ℕ} (P : MomentumTreeData n m w)
    {V : Type*} [AddCommGroup V] (u : MomentumCoordinate n → V)
    (i : Fin w) (p : LocalizationTree.Path) : V := momentumRowEval u (P.nodeRow i p)

/-- The structural parent rows prove the literal source decoration relation. -/
theorem MomentumTreeData.isDecoration_nodeMomentum {n m w : ℕ} (P : MomentumTreeData n m w)
    {V : Type*} [AddCommGroup V] (u : MomentumCoordinate n → V) (i : Fin w) :
    LocalizationTree.IsDecoration (P.tree i) (P.nodeMomentum u i) := by
  intro p hp
  change momentumRowEval u (P.nodeRow i p) = _
  rw [P.parent_row i p hp, map_add, map_sub]
  rfl

/-- The free link `x` is exactly the chosen child/root momentum difference. -/
theorem MomentumTreeData.nodeMomentum_link_x {n m w : ℕ} (P : MomentumTreeData n m w)
    {V : Type*} [AddCommGroup V] (u : MomentumCoordinate n → V) (i : Fin n) :
    P.nodeMomentum u (P.chosenTree i) (P.chosenPath i ++ [0]) -
      P.nodeMomentum u (P.chosenTree i) (P.chosenPath i) = u (some (i, 0)) := by
  change momentumRowEval u _ - momentumRowEval u _ = _
  rw [← map_sub, P.link_x_row i, momentumRowEval_unit]

/-- The free link `y` is exactly the chosen root/third-child momentum difference. -/
theorem MomentumTreeData.nodeMomentum_link_y {n m w : ℕ} (P : MomentumTreeData n m w)
    {V : Type*} [AddCommGroup V] (u : MomentumCoordinate n → V) (i : Fin n) :
    P.nodeMomentum u (P.chosenTree i) (P.chosenPath i) -
      P.nodeMomentum u (P.chosenTree i) (P.chosenPath i ++ [2]) = u (some (i, 1)) := by
  change momentumRowEval u _ - momentumRowEval u _ = _
  rw [← map_sub, P.link_y_row i, momentumRowEval_unit]

end WaveTurbulence.Incoh
