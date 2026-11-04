/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeRows

/-! # Exact input and lone-leaf rows for source paired trees -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst
open Incoh Links

variable {G : Garden 1} {X : RegChain}

/-- Positive representative of a nontrivially paired source leaf. -/
@[expose] def treePositiveLeaf (a : GLeaf G.tree) (hp : G.pair a ≠ a) : TPlus G :=
  if hs : G.sign a.toNode = 1 then ⟨a, hs, hp⟩ else
    ⟨G.pair a, by
      have hsign : G.sign (G.pair a).toNode = -G.sign a.toNode := G.pair_sign a hp
      rw [hsign, (Int.units_eq_one_or _).resolve_left hs]
      decide, by
      rw [G.pair_pair]
      exact Ne.symm hp⟩

/-- Integer rows agree with the chosen positive representative of each source pair. -/
theorem treeNodeRow_positive (hX : X.DecodesTree G) (a : GLeaf G.tree) (hp : G.pair a ≠ a) :
    treeNodeRow hX (treePositiveLeaf a hp).1.toNode = treeNodeRow hX a.toNode := by
  unfold treePositiveLeaf
  split_ifs
  · rfl
  · exact (treeNodeRow_pair hX a).symm

/-- The source lone leaf's row is exactly the root row. -/
theorem treeNodeRow_lone (hX : X.DecodesTree G) (a : GLeaf G.tree) (hp : G.pair a = a) :
    treeNodeRow hX a.toNode = momentumUnitRow none := by
  apply momentumRow_eq_of_eval
  intro u
  rw [treeNodeRow_eval, momentumRowEval_unit]
  have ha : a = loneLeaf hX := by
    apply Subtype.ext
    exact Prod.ext (Subsingleton.elim _ _) ((tree_pair_eq_iff hX a).1 hp)
  rw [ha, ← tree_root_eq_lone hX (treeDecOfParams hX (u none)
    (fun j => (u (some (j, 0)), u (some (j, 1))))).2.1]
  exact (treeDecOfParams hX (u none) (fun j => (u (some (j, 0)), u (some (j, 1))))).2.2

/-- Enumerate exactly the paired positive source leaves, omitting the lone leaf. -/
@[expose] def treeInputEquiv (G : Garden 1) : TPlus G ≃ Fin (Fintype.card (TPlus G)) :=
  Fintype.equivFin _

/-- The exact source assignment of leaf inputs; only the lone leaf has no input. -/
@[expose] def treeLeafInput (G : Garden 1) (a : GLeaf G.tree) : Option (Fin (Fintype.card (TPlus G))) :=
  if hp : G.pair a = a then none else some (treeInputEquiv G (treePositiveLeaf a hp))

/-- Every source leaf row has precisely the form required by the analytic carrier. -/
theorem treeNodeRow_leaf (hX : X.DecodesTree G) (a : GLeaf G.tree) :
    treeNodeRow hX a.toNode = match treeLeafInput G a with
      | none => momentumUnitRow none
      | some i => treeNodeRow hX ((treeInputEquiv G).symm i).1.toNode := by
  unfold treeLeafInput
  split_ifs with hp
  · exact treeNodeRow_lone hX a hp
  · simp only [Equiv.symm_apply_apply]
    exact (treeNodeRow_positive hX a hp).symm

/-- Exactly `2n` input factors remain in the paired tree source kernel. -/
theorem tree_input_count (hX : X.DecodesTree G) :
    Fintype.card (TPlus G) = 2 * (X.treeLinks (G.sig 0)).length := by
  have h := card_tLeafCoord hX
  simp only [TLeafCoord, TLinkCoord, Fintype.card_option, Fintype.card_prod, Fintype.card_fin] at h
  omega

end WaveTurbulence.IncohInst
