/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LadderBridge
public import WaveTurbulence.Foundations.Spine.GardenPos
/-! # Locality of the node labels at an atom (S3b LADDER-DECAY)

Two decorations with the same bond labels at all darts at an atom have the same node labels at
the four slot nodes of that atom (the other slot nodes are root boundary values). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine

variable {w d : ℕ} {G : Garden w}

lemma parent_child_self (a : GBranch G.tree) (j : Fin 3) (h : (a.child j).1.2 ≠ []) :
    GNode.parent (a.child j) h = a := by
  apply Subtype.ext
  show ((a.child j).1.1, (a.child j).1.2.dropLast) = a.1
  show (a.1.1, (a.1.2 ++ [j]).dropLast) = a.1
  rw [List.dropLast_concat]

lemma extendLabels_slot_eq {E : Type*} (hP : G.IsPlain) (n : Fin w → E) (K K' : GardenDart G → E)
    (hK : ∀ x, K (G.molecule.mate x) = K x) (hK' : ∀ x, K' (G.molecule.mate x) = K' x)
    (a : GBranch G.tree) (i : Fin 4)
    (h : ∀ x, G.molecule.atom x = a → K x = K' x) :
    Mole.extendLabels G hP n K (Mole.slotNode G a i) = Mole.extendLabels G hP n K' (Mole.slotNode G a i) := by
  induction i using Fin.cases with
  | zero =>
    show Mole.extendLabels G hP n K a.toNode = Mole.extendLabels G hP n K' a.toNode
    by_cases hr : a.1.2 = []
    · simp [Mole.extendLabels, GBranch.toNode, hr]
    · rw [Mole.extendLabels_branch G hP n K a hr, Mole.extendLabels_branch G hP n K' a hr]
      exact h _ rfl
  | succ j =>
    show Mole.extendLabels G hP n K (a.child j) = Mole.extendLabels G hP n K' (a.child j)
    have hr : (a.child j).1.2 ≠ [] := Mole.child_nonroot G a j
    by_cases hb : (a.child j).1.2 ∈ (G.tree (a.child j).1.1).branching
    · let b : GBranch G.tree := ⟨(a.child j).1, hb⟩
      have e : a.child j = b.toNode := rfl
      rw [e, Mole.extendLabels_branch G hP n K b hr, Mole.extendLabels_branch G hP n K' b hr]
      have hm := h (.inl (⟨b, hr⟩, true)) (parent_child_self a j hr)
      calc K (.inl (⟨b, hr⟩, false)) = K (.inl (⟨b, hr⟩, true)) := (hK (.inl (⟨b, hr⟩, true)))
        _ = K' (.inl (⟨b, hr⟩, true)) := hm
        _ = K' (.inl (⟨b, hr⟩, false)) := (hK' (.inl (⟨b, hr⟩, true))).symm
    · let l : GLeaf G.tree := ⟨(a.child j).1, ((TTree.mem_nodes_iff _ _).mp (a.child j).2).resolve_right hb⟩
      have e : a.child j = l.toNode := rfl
      rw [e]
      by_cases hp : (G.pair l).1.2 = []
      · rw [Mole.extendLabels_leaf_paired_root G hP n K l hr hp,
          Mole.extendLabels_leaf_paired_root G hP n K' l hr hp]
      · rw [Mole.extendLabels_leaf G hP n K l hr hp, Mole.extendLabels_leaf G hP n K' l hr hp]
        exact h _ (parent_child_self a j hr)

/-- **Locality of node labels.** -/
theorem node_label_local (hP : G.IsPlain) (roots : Fin w → (Fin d → ℤ))
    (z z' : GenDecoration G d roots 0) (a : GBranch G.tree)
    (h : ∀ x, G.molecule.atom x = a → bondIndex G z.1 x = bondIndex G z'.1 x) (i : Fin 4) :
    z.1 (Mole.slotNode G a i) = z'.1 (Mole.slotNode G a i) := by
  have ext : ∀ y : GenDecoration G d roots 0,
      y.1 = Mole.extendLabels G hP roots (bondIndex G y.1) := by
    intro y
    rw [bondIndex_eq_restrict]
    exact (Mole.extend_restrictLabels G hP roots y.1 (fun i => y.2.2.1 i) (fun l => y.2.1.2 l)).symm
  have hsym : ∀ y : GenDecoration G d roots 0, ∀ x, bondIndex G y.1 (G.molecule.mate x) = bondIndex G y.1 x := by
    intro y x
    rw [bondIndex_eq_restrict]
    exact Mole.restrictLabels_mate G y.1 (fun l => y.2.1.2 l) x
  have e1 := congrFun (ext z) (Mole.slotNode G a i)
  have e2 := congrFun (ext z') (Mole.slotNode G a i)
  rw [e1, e2]
  exact extendLabels_slot_eq hP roots _ _ (hsym z) (hsym z') a i h

end WaveTurbulence.LadderDecay
