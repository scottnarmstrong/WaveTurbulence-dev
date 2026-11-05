/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistDecorationRoots

/-! # Identifying the twist placement with the specified core vine

TARGET twist: the leaf u23 is the unique internal lower child of that
vine, not an arbitrary outer leaf paired outside. This source-facing
producer retains the slot identification forgotten by the generic helper.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w)

/-- A placement uses precisely the designated lower internal child of the given vine. -/
@[expose] def IsPlacementAt (S : Finset (GBranch G.tree)) (b : GBranch G.tree) (P : CorePlacement G) : Prop :=
  P.lower = b ∧ ∀ i : Fin 3, i.succ ∈ Mole.internalPositions G S b ↔ i = P.keep

/-- An actual paired child with selected paired parent occupies the unique retained slot. -/
theorem retained_slot_of_leaf_pair {S : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b) (hc : c ∈ S)
    {l : GLeaf G.tree} {i j : Fin 3} (hm : G.mark l = none)
    (hl : l.toNode = b.child i) (hr : (G.pair l).toNode = c.child j) :
    ∀ t : Fin 3, t.succ ∈ Mole.internalPositions G S b ↔ t = i := by
  have hn : l.1.2 ≠ [] := by
    change l.toNode.1.2 ≠ []
    rw [hl]
    exact Mole.child_nonroot G b i
  have hp : (G.pair l).1.2 ≠ [] := by
    change (G.pair l).toNode.1.2 ≠ []
    rw [hr]
    exact Mole.child_nonroot G c j
  let x : GardenDart G := .inr ⟨l,hm,hn,hp⟩
  have ha : G.molecule.atom x = b := parent_eq_of_child hn hl
  have hb : G.molecule.atom (G.molecule.mate x) = c := parent_eq_of_child hp hr
  have hpos : Mole.dartPosition G x = i.succ := by
    apply Fin.ext
    change (l.1.2.getLast hn).val+1 = i.val+1
    have hh : l.1.2 = b.1.2 ++ [i] := congrArg (fun n : GNode G.tree => n.1.2) hl
    simp [hh]
  have hin : i.succ ∈ Mole.internalPositions G S b :=
    (Mole.mem_internalPositions G).mpr ⟨x,ha,by
      change G.molecule.atom x ∈ S ∧ G.molecule.atom (G.molecule.mate x) ∈ S
      rw [ha,hb]; exact ⟨hB.2.2.1,hc⟩,hpos⟩
  obtain ⟨k,_hk,hslots⟩ := Mole.with_parent_joint_retained_child G hB.2.2.1
    hB.2.2.2.2.2.2.1 hB.2.2.2.2.2.2.2.1 hCL.2
  have hi := (hslots i).mp hin
  subst k
  exact hslots

/-- Conditional leaf-data helper; source producers below derive all its inputs. -/
theorem placementAt_of_leaf_pair {S : Finset (GBranch G.tree)} {a b c : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : Mole.CLParentPattern G S a b) (hc : c ∈ S)
    {l : GLeaf G.tree} {i j : Fin 3} (hm : G.mark l = none)
    (hl : l.toNode = b.child i) (hr : (G.pair l).toNode = c.child j)
    (hout : ¬ b.toNode.IsDesc (G.pair l).toNode) : ∃ P : CorePlacement G, IsPlacementAt G S b P := by
  have hp : (G.pair l).1.2 ≠ [] := by
    change (G.pair l).toNode.1.2 ≠ []
    rw [hr]
    exact Mole.child_nonroot G c j
  exact ⟨⟨b,l,hCL.2.choose,hp,i,hm,hl,Molecpl.lower_leaf_outer G hB hCL hc hm hl hr,hout⟩,
    rfl,retained_slot_of_leaf_pair G hB hCL hc hm hl hr⟩

/-- Type-I source vines produce their designated internal u23 placement. -/
theorem typeI_placementAt {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hV : G.molecule.IsVine .I S a b) (hCL : Mole.CLParentPattern G S a b) :
    ∃ P : CorePlacement G, IsPlacementAt G S b P := by
  obtain ⟨l,i,j,hm,hl,hr,_hi⟩ := Molecpl.typeI_leaf_pair G hV hCL
  apply placementAt_of_leaf_pair G hV.1 hCL hV.1.2.1 hm hl hr
  intro hd
  have hba := branch_desc_leaf_parent G hr hd
  have hlen := hba.2.length_le
  have hab := Mole.cl_parent_strict_descendant G hV.1 hCL
  dsimp [GBranch.toNode] at hlen
  omega

/-- Core type-II source vines produce their designated internal u23 placement. -/
theorem typeII_placementAt {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hV : G.molecule.IsVine .II S a b) (hCL : Mole.CLParentPattern G S a b)
    (hcore : ¬ ∃ p ∈ S, ∃ q ∈ S, Molecpl.IsTypeIIE G a b p q) :
    ∃ P : CorePlacement G, IsPlacementAt G S b P := by
  obtain ⟨R,hn,hp,hcases⟩ := Molecpl.garden_typeII_local_cases G hV hCL
  have hLP : Molecpl.LowerLP G R := by
    rcases hcases with ⟨_hall,hlp⟩ | ⟨_hparent,hlp,_hpc⟩ | ⟨_hparent,hlp,_hpc⟩ | ⟨hparent,hall⟩
    · exact hlp
    · exact hlp
    · exact hlp
    · obtain ⟨hqn,hqp⟩ := hparent
      obtain ⟨i,hi,hio,_⟩ := Molecpl.lower_child_retained G hV.1 hCL R.right_mem hqn hqp
      have hd : Molecpl.DoubleLeafPairAt G R.left R.right :=
        Molecpl.double_leaf_pair_positions G (Molecpl.FourIncidences.doublePair R.left_row) hall
      have ha := Mole.block_one_root_descendants G hV.1 hCL.1 hCL.2 R.left_mem
      exact (hcore ⟨R.left,R.left_mem,R.right,R.right_mem,⟨hn,hp⟩,⟨hqn,hqp⟩,hd,⟨i,hi,hio⟩,ha⟩).elim
  obtain ⟨l,i,j,hm,hl,hr,_hi,_hs⟩ := Molecpl.lower_LP_retained G hV.1 hCL R hLP
  exact placementAt_of_leaf_pair G hV.1 hCL R.right_mem hm hl hr
    (child_leaf_outside_of_terminal G R.right_mem R.right_ne_lower
      (Molecpl.lower_LP_terminal G hV.1 hCL R hLP) hr)

/-- Every specified core CL vine produces its actual designated unit-twist placement. -/
theorem corePlacement_at_vine {X : VineType} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (h : IsCoreCLVine G X S a b) : ∃ P : CorePlacement G, IsPlacementAt G S b P := by
  obtain ⟨hV,hCL,hcore⟩ := h
  rcases hcore with rfl | ⟨rfl,hcore⟩
  · exact typeI_placementAt G hV hCL
  · exact typeII_placementAt G hV hCL hcore

end WaveTurbulence.Twist
