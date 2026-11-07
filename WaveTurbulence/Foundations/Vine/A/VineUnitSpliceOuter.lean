/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSpliceChildRange
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceChildren
public import WaveTurbulence.Foundations.Vine.A.VinePortRigidity
public import WaveTurbulence.Foundations.Molecule.CoreBranchAddresses
/-! An outer slot is fixed by the actual selected LF quotient map. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Mole WaveTurbulence.Twist WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w}

/-- A retained original child of a retained original parent follows its original slot under LF. -/
theorem unitSplice_old_child (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (b : GBranch (stSt G σ).G.tree) (n : GNode (stSt G σ).G.tree) (i : Fin 3)
    (hc : spliceOldNode (unitBlocks G σ) n = ((stSt G σ).M.ob b).child i) :
    spliceOldNode (unitBlocks Z.target (transportPrescription Z.iso σ))
      (unitSpliceNodeEquiv Z σ hsel n) =
      ((stSt Z.target (transportPrescription Z.iso σ)).M.ob ((unitSpliceMolIso Z σ hsel).e b)).child i := by
  have hb : (stSt G σ).M.ob b ≠ Z.P.lower :=
    fun h => active_lower_not_surviving Z σ hsel ⟨b, h⟩
  have hslot : exchangeChildSlot Z.P.lower.1 Z.P.keep ((stSt G σ).M.ob b).1 i = i := by
    unfold exchangeChildSlot
    exact ite_eq_right (fun h => hb (Subtype.ext h))
  rw [unitSpliceMolIso_branch_names]
  obtain ⟨p, rfl⟩ := (nodePieceEquiv (stSt G σ).G.tree).surjective n
  cases p with
  | inl c =>
    have hc' := (spliceOldNode_branch (unitBlocks G σ) c).symm.trans hc
    have he := branch_child_transport G Z.P hc'
      (fun h => active_lower_not_surviving Z σ hsel ⟨c, h⟩)
    rw [hslot] at he
    exact (congrArg (spliceOldNode _) (unitSpliceNodeEquiv_branch Z σ hsel c)).trans
      ((spliceOldNode_branch _ _).trans
        ((congrArg GBranch.toNode (unitSpliceMolIso_branch_names Z σ hsel c)).trans he))
  | inr q =>
    have hc' := (spliceOldNode_leaf (unitBlocks G σ) q).symm.trans hc
    have he := leaf_child_transport G Z.P hc'
      (fun h => active_pair_not_surviving Z σ hsel ⟨q, h⟩)
    rw [hslot] at he
    exact (congrArg (spliceOldNode _) (unitSpliceNodeEquiv_leaf Z σ hsel q)).trans
      ((spliceOldNode_leaf _ _).trans
        ((congrArg GLeaf.toNode (unitSpliceLeafEquiv_names Z σ hsel q)).trans he))

/-- An original port external to every actual unit is fixed by the actual quotient map. -/
theorem unitSpliceChildSlot_of_external (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (b : GBranch (stSt G σ).G.tree) (i : Fin 3)
    (hext : ∀ u ∈ unitBlocks G σ, i.succ ∉ internalPositions G u.atoms ((stSt G σ).M.ob b)) :
    unitSpliceChildSlot Z σ hsel b i = i := by
  let l := unitBlocks Z.target (transportPrescription Z.iso σ)
  let n := unitSpliceNodeEquiv Z σ hsel (b.child i)
  let v := (stSt Z.target (transportPrescription Z.iso σ)).M.ob ((unitSpliceMolIso Z σ hsel).e b)
  have he : spliceOldNode l n = v.child i := unitSplice_old_child Z σ hsel b (b.child i) i
    (spliceOldNode_child_external _ (unitBlocks_pairwise (garden_isMolecule G) σ) b i hext)
  have hn : n.1.2 ≠ [] := fun h => child_nonroot (stSt G σ).G b i
    ((unitSpliceNodeEquiv_root Z σ hsel (b.child i)).mp h)
  have ho : (spliceOldNode l n).1.2 ≠ [] := fun h => child_nonroot Z.target v i
    ((congrArg (fun n : GNode Z.target.tree => n.1.2) he).symm.trans h)
  have hp : GNode.parent (spliceOldNode l n) ho = v :=
    (spliceNodeParent_congr ho (child_nonroot Z.target v i) he).trans (parent_child_branch_eq Z.target v i _)
  have hf : repC (spliceFold Z.target l).cls (GNode.parent (spliceOldNode l n) ho) =
      GNode.parent (spliceOldNode l n) ho := by
    rw [hp]
    exact splice_old_branch_fixed _ ((unitSpliceMolIso Z σ hsel).e b)
  change n.1.2.getLast hn = i
  exact (spliceOldNode_port l n hn ho hf).trans (node_last_of_eq_child _ ho v i he)

/-- Ordered normalization: every child slot of the actual selected LF quotient is fixed. -/
theorem unitSpliceChildSlot_eq (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (b : GBranch (stSt G σ).G.tree) (i : Fin 3) : unitSpliceChildSlot Z σ hsel b i = i := by
  obtain ⟨j, hj, hext⟩ := spliceFold_outer_slot (unitBlocks G σ)
    (unitBlocks_pairwise (garden_isMolecule G) σ) b
  have he := child_equiv_eq_refl (unitSpliceChildEquiv Z σ hsel b)
    (unitSpliceChildSlot_middle Z σ hsel b) j hj (unitSpliceChildSlot_of_external Z σ hsel b j hext)
  exact congrArg (fun e : Fin 3 ≃ Fin 3 => e i) he

end WaveTurbulence.VineA
