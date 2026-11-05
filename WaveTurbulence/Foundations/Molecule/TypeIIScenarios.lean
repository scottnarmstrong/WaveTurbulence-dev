/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.ScenarioRelations

/-! # The five actual-garden type-II scenarios

TARGET Proposition molecpl (2), L1405--L1415. All parent relations,
paired leaves, ordered outer slots, and ancestor relations refer to the
actual Garden. The one-rung Q-block is included by the end-rung producer.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree Vine
variable {w : ℕ} (G : Garden w)

/-- TARGET scenario (II-a). -/
@[expose] def IsTypeIIA (a b p q : GBranch G.tree) : Prop :=
  IsParent G q b ∧ OuterLeafPairAt G b p ∧ DoubleLeafPairAt G p q ∧
    ¬ p.toNode.IsDesc q.toNode ∧ ¬ q.toNode.IsDesc p.toNode ∧
    a.toNode.IsDesc p.toNode ∧ a.toNode.IsDesc q.toNode

/-- TARGET scenario (II-b). -/
@[expose] def IsTypeIIB (a b p q : GBranch G.tree) : Prop :=
  IsParent G p b ∧ OuterLeafPairAt G b q ∧ DoubleLeafPairAt G p q ∧
    ¬ p.toNode.IsDesc q.toNode ∧ ¬ q.toNode.IsDesc p.toNode ∧
    a.toNode.IsDesc p.toNode ∧ a.toNode.IsDesc q.toNode

/-- TARGET scenario (II-c). -/
@[expose] def IsTypeIIC (a b p q : GBranch G.tree) : Prop :=
  IsParent G p q ∧ IsParent G q b ∧ LeafPairAt G p q ∧
    OuterLeafPairAt G b p ∧ a.toNode.IsDesc p.toNode

/-- TARGET scenario (II-d). -/
@[expose] def IsTypeIID (a b p q : GBranch G.tree) : Prop :=
  IsParent G p b ∧ IsParent G p q ∧ LeafPairAt G p q ∧
    OuterLeafPairAt G b q ∧ a.toNode.IsDesc p.toNode

/-- TARGET scenario (II-e), including the identity q=u23 in its retained outer slot. -/
@[expose] def IsTypeIIE (a b p q : GBranch G.tree) : Prop :=
  IsParent G p b ∧ IsParent G b q ∧ DoubleLeafPairAt G p q ∧
    (∃ i : Fin 3, q.toNode = b.child i ∧ i ≠ 1) ∧ a.toNode.IsDesc p.toNode

/-- Every CL type-II vine has the source's five-scenario garden geometry,
up to interchanging the two adjacent rung atoms. No local geometry is assumed. -/
theorem typeII_scenarios {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hV : G.molecule.IsVine .II S a b) (hCL : Mole.CLParentPattern G S a b) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ p ≠ a ∧ p ≠ b ∧ q ≠ a ∧ q ≠ b ∧
      G.molecule.bondsBetween b p = 1 ∧ G.molecule.bondsBetween b q = 1 ∧
      G.molecule.bondsBetween p q = 2 ∧
      (IsTypeIIA G a b p q ∨ IsTypeIIB G a b p q ∨ IsTypeIIC G a b p q ∨
        IsTypeIID G a b p q ∨ IsTypeIIE G a b p q) := by
  obtain ⟨R,hn,hp,hcases⟩ := garden_typeII_local_cases G hV hCL
  have hdesc (v : GBranch G.tree) (hv : v ∈ S) : a.toNode.IsDesc v.toNode :=
    Mole.block_one_root_descendants G hV.1 hCL.1 hCL.2 hv
  have hcounts := R.lower_single_counts hV.1
  have hdoub := R.double_count (Mole.garden_isMolecule G)
  have finish (p q : GBranch G.tree) (hpS : p ∈ S) (hqS : q ∈ S)
      (hne : p ≠ q) (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b)
      (hbp : G.molecule.bondsBetween b p = 1) (hbq : G.molecule.bondsBetween b q = 1)
      (hpq : G.molecule.bondsBetween p q = 2)
      (h : IsTypeIIA G a b p q ∨ IsTypeIIB G a b p q ∨ IsTypeIIC G a b p q ∨
        IsTypeIID G a b p q ∨ IsTypeIIE G a b p q) :
      ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ p ≠ a ∧ p ≠ b ∧ q ≠ a ∧ q ≠ b ∧
        G.molecule.bondsBetween b p = 1 ∧ G.molecule.bondsBetween b q = 1 ∧
        G.molecule.bondsBetween p q = 2 ∧
        (IsTypeIIA G a b p q ∨ IsTypeIIB G a b p q ∨ IsTypeIIC G a b p q ∨
          IsTypeIID G a b p q ∨ IsTypeIIE G a b p q) :=
    ⟨p,hpS,q,hqS,hne,hpa,hpb,hqa,hqb,hbp,hbq,hpq,h⟩
  have hdLP : LeafPairAt G R.left R.right := by
    obtain ⟨i,hi⟩ := doubled_has_lp G (FourIncidences.doublePair R.left_row)
    exact dart_leaf_pair G hi ((FourIncidences.doublePair R.left_row).atom_eq i)
      ((FourIncidences.doublePair R.left_row).neighbor_eq i)
  rcases hcases with ⟨hall,hlp⟩ | ⟨hparent,hlp,_hpc⟩ | ⟨hparent,hlp,_hpc⟩ | ⟨hparent,hall⟩
  · have hdouble : DoubleLeafPairAt G R.left R.right :=
      double_leaf_pair_positions G (FourIncidences.doublePair R.left_row) hall
    have hinc := two_LP_rungs_incomparable G hV.1 hCL R hn hp hall hlp
    exact finish R.left R.right R.left_mem R.right_mem R.distinct R.left_ne_upper R.left_ne_lower
      R.right_ne_upper R.right_ne_lower hcounts.1 hcounts.2 hdoub
      (Or.inr (Or.inl ⟨⟨hn,hp⟩,lower_outerLeafPairAt G hV.1 hCL R hlp,hdouble,
        hinc.1,hinc.2,hdesc _ R.left_mem,hdesc _ R.right_mem⟩))
  · have hdLP' : LeafPairAt G R.right R.left := by
      obtain ⟨i,hi⟩ := doubled_has_lp G (FourIncidences.doublePair R.left_row).mates
      exact dart_leaf_pair G hi ((FourIncidences.doublePair R.left_row).mates.atom_eq i)
        ((FourIncidences.doublePair R.left_row).mates.neighbor_eq i)
    exact finish R.right R.left R.right_mem R.left_mem R.distinct.symm R.right_ne_upper R.right_ne_lower
      R.left_ne_upper R.left_ne_lower hcounts.2 hcounts.1
      (by rw [Mole.bondsBetween_symm]; exact hdoub)
      (Or.inr (Or.inr (Or.inl ⟨hparent,⟨hn,hp⟩,hdLP',
        lower_outerLeafPairAt G hV.1 hCL R hlp,hdesc _ R.right_mem⟩)))
  · exact finish R.left R.right R.left_mem R.right_mem R.distinct R.left_ne_upper R.left_ne_lower
      R.right_ne_upper R.right_ne_lower hcounts.1 hcounts.2 hdoub
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨hn,hp⟩,hparent,hdLP,
        lower_outerLeafPairAt G hV.1 hCL R hlp,hdesc _ R.left_mem⟩))))
  · have hdouble : DoubleLeafPairAt G R.left R.right :=
      double_leaf_pair_positions G (FourIncidences.doublePair R.left_row) hall
    obtain ⟨hqn,hqp⟩ := hparent
    obtain ⟨i,hi,hio,_⟩ := lower_child_retained G hV.1 hCL R.right_mem hqn hqp
    exact finish R.left R.right R.left_mem R.right_mem R.distinct R.left_ne_upper R.left_ne_lower
      R.right_ne_upper R.right_ne_lower hcounts.1 hcounts.2 hdoub
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨hn,hp⟩,⟨hqn,hqp⟩,hdouble,⟨i,hi,hio⟩,
        hdesc _ R.left_mem⟩))))

end WaveTurbulence.Molecpl
