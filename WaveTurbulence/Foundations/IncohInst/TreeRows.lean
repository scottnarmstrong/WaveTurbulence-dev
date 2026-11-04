/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleRows
public import WaveTurbulence.Foundations.IncohInst.Enhanced.TreeIncoh2

/-! # Integer momentum rows of the actual C2 paired tree -/

public section
noncomputable section
open scoped BigOperators
namespace WaveTurbulence.IncohInst
open Incoh Links

variable {G : Garden 1} {X : RegChain}

/-- The integer node expansion supplied by ENHANCED, with its root column retained. -/
@[expose] def treeNodeRow (hX : X.DecodesTree G) (a : GNode G.tree) :
    MomentumCoordinate (X.treeLinks (G.sig 0)).length → ℤ :=
  fun j => match j with
    | none => 1
    | some (i, b) => if b = 0 then (tree_node_linear hX a).choose i
      else (tree_node_linear hX a).choose_spec.choose i

/-- Integer row evaluation equals the actual C2 tree decoration in every coefficient group. -/
theorem treeNodeRow_eval (hX : X.DecodesTree G) (a : GNode G.tree)
    {V : Type} [AddCommGroup V] (u : MomentumCoordinate (X.treeLinks (G.sig 0)).length → V) :
    momentumRowEval u (treeNodeRow hX a) =
      (treeDecOfParams hX (u none) (fun j => (u (some (j, 0)), u (some (j, 1))))).1 a := by
  rw [(tree_node_linear hX a).choose_spec.choose_spec]
  change (∑ j, treeNodeRow hX a j • u j) = _
  simp only [treeNodeRow, Fintype.sum_option, one_smul, Fintype.sum_prod_type,
    Fin.sum_univ_two, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide]

/-- The actual source root row is the distinguished root coordinate. -/
theorem treeNodeRow_root (hX : X.DecodesTree G) :
    treeNodeRow hX (GNode.root G.tree 0) = momentumUnitRow none := by
  apply momentumRow_eq_of_eval
  intro u
  rw [treeNodeRow_eval, momentumRowEval_unit]
  exact (treeDecOfParams hX (u none) (fun j => (u (some (j, 0)), u (some (j, 1))))).2.2

/-- The source alternating parent identity holds as an exact integer row identity. -/
theorem treeNodeRow_parent (hX : X.DecodesTree G) (b : GBranch G.tree) :
    treeNodeRow hX b.toNode = treeNodeRow hX (b.child 0) -
      treeNodeRow hX (b.child 1) + treeNodeRow hX (b.child 2) := by
  apply momentumRow_eq_of_eval
  intro u
  rw [map_add, map_sub]
  simp only [treeNodeRow_eval]
  exact (treeDecOfParams hX (u none) (fun j => (u (some (j, 0)), u (some (j, 1))))).2.1.1 b

/-- Paired leaves have the same actual integer row. -/
theorem treeNodeRow_pair (hX : X.DecodesTree G) (a : GLeaf G.tree) :
    treeNodeRow hX a.toNode = treeNodeRow hX (G.pair a).toNode := by
  apply momentumRow_eq_of_eval
  intro u
  simp only [treeNodeRow_eval]
  exact (treeDecOfParams hX (u none) (fun j => (u (some (j, 0)), u (some (j, 1))))).2.1.2 a

/-- The chosen endpoint of a source tree link. -/
@[expose] def treeChosenBranch (hX : X.DecodesTree G) (j : Fin (X.treeLinks (G.sig 0)).length) :
    GBranch G.tree :=
  ⟨treeChosen X (G.sig 0) j,
    (tree_mem_pairEndpoints_links_iff hX _).1 (by
      rw [← flatPairs_toFinset]
      exact List.mem_toFinset.mpr (mem_flatPairs (List.get_mem (X.treeLinks (G.sig 0)) j) (Or.inl rfl)))⟩

/-- The first free tree coordinate is precisely the chosen first-child difference. -/
theorem treeNodeRow_link_x (hX : X.DecodesTree G) (j : Fin (X.treeLinks (G.sig 0)).length) :
    treeNodeRow hX ((treeChosenBranch hX j).child 0) - treeNodeRow hX (treeChosenBranch hX j).toNode =
      momentumUnitRow (some (j, 0)) := by
  apply momentumRow_eq_of_eval
  intro u
  rw [map_sub, treeNodeRow_eval, treeNodeRow_eval, momentumRowEval_unit]
  have he := congrArg (fun θ => (θ j).1) (treeDecParams_treeDecOfParams hX (u none)
    (fun j => (u (some (j, 0)), u (some (j, 1)))))
  change xv (extend _) (treeChosenBranch hX j).1 = _ at he
  rw [xv_extend] at he
  exact he

/-- The second free tree coordinate is precisely the chosen third-child difference. -/
theorem treeNodeRow_link_y (hX : X.DecodesTree G) (j : Fin (X.treeLinks (G.sig 0)).length) :
    treeNodeRow hX (treeChosenBranch hX j).toNode - treeNodeRow hX ((treeChosenBranch hX j).child 2) =
      momentumUnitRow (some (j, 1)) := by
  apply momentumRow_eq_of_eval
  intro u
  rw [map_sub, treeNodeRow_eval, treeNodeRow_eval, momentumRowEval_unit]
  have he := congrArg (fun θ => (θ j).2) (treeDecParams_treeDecOfParams hX (u none)
    (fun j => (u (some (j, 0)), u (some (j, 1)))))
  change yv (extend _) (treeChosenBranch hX j).1 = _ at he
  rw [yv_extend] at he
  exact he

end WaveTurbulence.IncohInst
