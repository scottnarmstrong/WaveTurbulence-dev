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

/-- B1b-2 (Mk-general form of `unitSplice_old_child`). -/
theorem unitSplice_old_childMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0)
    (b : GBranch (stSt G σ Mk).G.tree) (n : GNode (stSt G σ Mk).G.tree) (i : Fin 3)
    (hc : spliceOldNode (unitBlocks G σ Mk) n = ((stSt G σ Mk).M.ob b).child i) :
    spliceOldNode (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')
      (unitSpliceNodeEquivMk Z σ hT hsel n) =
      ((stSt Z.target (transportPrescription Z.iso σ) Mk').M.ob ((unitSpliceMolIsoMk Z σ hT hsel).e b)).child i := by
  have hb : (stSt G σ Mk).M.ob b ≠ Z.P.lower :=
    fun h => active_lower_not_survivingMk Z σ hsel ⟨b, h⟩
  have hslot : exchangeChildSlot Z.P.lower.1 Z.P.keep ((stSt G σ Mk).M.ob b).1 i = i := by
    unfold exchangeChildSlot
    exact ite_eq_right (fun h => hb (Subtype.ext h))
  rw [unitSpliceMolIso_branch_namesMk]
  obtain ⟨p, rfl⟩ := (nodePieceEquiv (stSt G σ Mk).G.tree).surjective n
  cases p with
  | inl c =>
    have hc' := (spliceOldNode_branch (unitBlocks G σ Mk) c).symm.trans hc
    have he := branch_child_transport G Z.P hc'
      (fun h => active_lower_not_survivingMk Z σ hsel ⟨c, h⟩)
    rw [hslot] at he
    exact (congrArg (spliceOldNode _) (unitSpliceNodeEquiv_branchMk Z σ hT hsel c)).trans
      ((spliceOldNode_branch _ _).trans
        ((congrArg GBranch.toNode (unitSpliceMolIso_branch_namesMk Z σ hT hsel c)).trans he))
  | inr q =>
    have hc' := (spliceOldNode_leaf (unitBlocks G σ Mk) q).symm.trans hc
    have he := leaf_child_transport G Z.P hc'
      (fun h => active_pair_not_survivingMk Z σ hsel ⟨q, h⟩)
    rw [hslot] at he
    exact (congrArg (spliceOldNode _) (unitSpliceNodeEquiv_leafMk Z σ hT hsel q)).trans
      ((spliceOldNode_leaf _ _).trans
        ((congrArg GLeaf.toNode (unitSpliceLeafEquiv_namesMk Z σ hT hsel q)).trans he))

/-- B1b-2 (Mk-general form of `unitSpliceChildSlot_of_external`). -/
theorem unitSpliceChildSlot_of_externalMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0)
    (b : GBranch (stSt G σ Mk).G.tree) (i : Fin 3)
    (hext : ∀ u ∈ unitBlocks G σ Mk, i.succ ∉ internalPositions G u.atoms ((stSt G σ Mk).M.ob b)) :
    unitSpliceChildSlotMk Z σ hT hsel b i = i := by
  let l := unitBlocks Z.target (transportPrescription Z.iso σ) Mk'
  let n := unitSpliceNodeEquivMk Z σ hT hsel (b.child i)
  let v := (stSt Z.target (transportPrescription Z.iso σ) Mk').M.ob ((unitSpliceMolIsoMk Z σ hT hsel).e b)
  have he : spliceOldNode l n = v.child i := unitSplice_old_childMk Z σ hT hsel b (b.child i) i
    (spliceOldNode_child_external _ (unitBlocks_pairwiseMk (garden_isMolecule G) σ Mk) b i hext)
  have hn : n.1.2 ≠ [] := fun h => child_nonroot (stSt G σ Mk).G b i
    ((unitSpliceNodeEquiv_rootMk Z σ hT hsel (b.child i)).mp h)
  have ho : (spliceOldNode l n).1.2 ≠ [] := fun h => child_nonroot Z.target v i
    ((congrArg (fun n : GNode Z.target.tree => n.1.2) he).symm.trans h)
  have hp : GNode.parent (spliceOldNode l n) ho = v :=
    (spliceNodeParent_congr ho (child_nonroot Z.target v i) he).trans (parent_child_branch_eq Z.target v i _)
  have hf : repC (spliceFold Z.target l).cls (GNode.parent (spliceOldNode l n) ho) =
      GNode.parent (spliceOldNode l n) ho := by
    rw [hp]
    exact splice_old_branch_fixed _ ((unitSpliceMolIsoMk Z σ hT hsel).e b)
  change n.1.2.getLast hn = i
  exact (spliceOldNode_port l n hn ho hf).trans (node_last_of_eq_child _ ho v i he)

/-- B1b-2 (Mk-general form of `unitSpliceChildSlot_eq`). -/
theorem unitSpliceChildSlot_eqMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0)
    (b : GBranch (stSt G σ Mk).G.tree) (i : Fin 3) : unitSpliceChildSlotMk Z σ hT hsel b i = i := by
  obtain ⟨j, hj, hext⟩ := spliceFold_outer_slot (unitBlocks G σ Mk)
    (unitBlocks_pairwiseMk (garden_isMolecule G) σ Mk) b
  have he := child_equiv_eq_refl (unitSpliceChildEquivMk Z σ hT hsel b)
    (unitSpliceChildSlot_middleMk Z σ hT hsel b) j hj (unitSpliceChildSlot_of_externalMk Z σ hT hsel b j hext)
  exact congrArg (fun e : Fin 3 ≃ Fin 3 => e i) he

end WaveTurbulence.VineA
