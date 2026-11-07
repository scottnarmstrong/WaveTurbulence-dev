/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw11Data

/-! # Rigid relocation of the upper block under a unit twist (V5 Step 4b, step 4, WP-B part 1)

For a unit twist `(G, P)` at a member BELOW the split joint `b` and the upper block `S` (joints `a`, `b`), the block `S` is
moved rigidly: `RigidAt P S b` says `P.lower ∉ S` and that no child of an atom of `S.erase b` is the lower joint or the
partner of the retained leaf.  Then the naive node bijection preserves the structure of `S`: children (`child_naive`), the
realization nodes (`real_iff_rigid`), the regional pairs and their leaves (`tp_first_rigid`), with NO exchange of labels.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {G : Garden w} (P : CorePlacement G)

/-- The block `S` (with lower joint `b`) is rigid for the unit twist `P`. -/
structure RigidAt (S : Finset (GBranch G.tree)) (b : GBranch G.tree) : Prop where
  lower_notMem : P.lower ∉ S
  child_lower : ∀ v ∈ S.erase b, ∀ i : Fin 3, v.child i ≠ P.lower.toNode
  child_partner : ∀ v ∈ S.erase b, ∀ i : Fin 3, v.child i ≠ (G.pair P.retained).toNode

theorem not_internal_retained_of {S : Finset (GBranch G.tree)} (h : P.lower ∉ S) :
    ¬ Mole.IsInternalLeaf G S P.retained := by
  rintro ⟨hm, hn, hp, hg⟩
  have ha : G.molecule.atom (retainedLP G P) = P.lower := retained_parent G P
  exact h (ha ▸ hg.1)

theorem not_internal_pair_of {S : Finset (GBranch G.tree)} (h : P.lower ∉ S) :
    ¬ Mole.IsInternalLeaf G S (G.pair P.retained) := fun hh =>
  not_internal_retained_of P h ((Mole.internal_leaf_pair_iff G S P.retained).mp hh)

namespace RigidAt
variable {P} {S : Finset (GBranch G.tree)} {b : GBranch G.tree} (hR : RigidAt P S b)
include hR

theorem ne_lower {v : GBranch G.tree} (hv : v ∈ S) : v ≠ P.lower := fun h => hR.lower_notMem (h ▸ hv)

theorem child_naive {v : GBranch G.tree} (hv : v ∈ S.erase b) (i : Fin 3) :
    naiveNodeEquiv G P (v.child i) = (coreBranchEquiv G P v).child i := by
  have hne := hR.ne_lower (Finset.mem_of_mem_erase hv)
  have hpv : v.1 ≠ P.lower.1 := fun he => hne (Subtype.ext he)
  have := naiveNodeEquiv_child G P (p := v) (n := v.child i) (i := i) rfl (hR.child_lower v hv i)
    (hR.child_partner v hv i)
  simpa only [exchangeChildSlot, hpv, ite_false] using this

/-- A realization node of `S` that is a child of an atom `v ∈ S` is moved like a child (the lower joint `b` included). -/
theorem child_naive_real {v : GBranch G.tree} (hv : v ∈ S) {i : Fin 3} (hx : v.child i ∈ clRealizationNodes G S) :
    naiveNodeEquiv G P (v.child i) = (coreBranchEquiv G P v).child i := by
  have hne := hR.ne_lower hv
  have hpv : v.1 ≠ P.lower.1 := fun he => hne (Subtype.ext he)
  have h1 : v.child i ≠ P.lower.toNode := fun h => by
    rw [h] at hx
    exact hR.lower_notMem ((branch_mem_clRealizationNodes _).mp hx)
  have h2 : v.child i ≠ (G.pair P.retained).toNode := fun h => by
    rw [h] at hx
    exact not_internal_pair_of P hR.lower_notMem ((leaf_mem_clRealizationNodes _).mp hx)
  have := naiveNodeEquiv_child G P (p := v) (n := v.child i) (i := i) rfl h1 h2
  simpa only [exchangeChildSlot, hpv, ite_false] using this

end RigidAt

/-- The realization nodes of a block and of its twisted image correspond under the naive node bijection, provided the
retained leaf and its partner are internal to neither (the hypotheses are the rigid ones for both gardens). -/
theorem real_iff_of {S : Finset (GBranch G.tree)} (h1 : ¬ Mole.IsInternalLeaf G S P.retained)
    (h2 : ¬ Mole.IsInternalLeaf G S (G.pair P.retained))
    (h1' : ¬ Mole.IsInternalLeaf (unitTwistGarden G P) (twistedAtoms G P S) (coreLeafEquiv G P P.retained))
    (h2' : ¬ Mole.IsInternalLeaf (unitTwistGarden G P) (twistedAtoms G P S)
      ((unitTwistGarden G P).pair (coreLeafEquiv G P P.retained))) (x : GNode G.tree) :
    Mole.InIncidenceRealization G S x ↔
      Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P S) (naiveNodeEquiv G P x) := by
  obtain ⟨q, rfl⟩ := (nodePieceEquiv G.tree).surjective x
  cases q with
  | inl b =>
    change Mole.InIncidenceRealization G S b.toNode ↔ Mole.InIncidenceRealization _ _ (naiveNodeEquiv G P b.toNode)
    have e1 := Mole.branch_incidence_realization_iff G S b
    have e2 := Mole.branch_incidence_realization_iff (unitTwistGarden G P) (twistedAtoms G P S) (coreBranchEquiv G P b)
    have hn : naiveNodeEquiv G P b.toNode = (coreBranchEquiv G P b).toNode := naiveNodeEquiv_branch G P b
    have e3 : Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P S) (naiveNodeEquiv G P b.toNode) ↔
        Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P S) (coreBranchEquiv G P b).toNode :=
      Iff.of_eq (congrArg (fun n : GNode (unitTwistGarden G P).tree =>
        Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P S) n) hn)
    exact e1.trans ((mem_twistedAtoms G P S b).symm.trans (e2.symm.trans e3.symm))
  | inr l =>
    change Mole.InIncidenceRealization G S l.toNode ↔ Mole.InIncidenceRealization _ _ (naiveNodeEquiv G P l.toNode)
    have e1 := Mole.leaf_incidence_realization_iff G S l
    have e2 := Mole.leaf_incidence_realization_iff (unitTwistGarden G P) (twistedAtoms G P S) (coreLeafEquiv G P l)
    have hn : naiveNodeEquiv G P l.toNode = (coreLeafEquiv G P l).toNode := naiveNodeEquiv_leaf G P l
    have e3 : Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P S) (naiveNodeEquiv G P l.toNode) ↔
        Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P S) (coreLeafEquiv G P l).toNode :=
      Iff.of_eq (congrArg (fun n : GNode (unitTwistGarden G P).tree =>
        Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P S) n) hn)
    refine e1.trans (Iff.trans ?_ (e2.symm.trans e3.symm))
    by_cases hr1 : l = P.retained
    · subst hr1
      exact iff_of_false h1 h1'
    by_cases hr2 : l = G.pair P.retained
    · subst hr2
      refine iff_of_false h2 ?_
      have := h2'
      rw [unitTwistGarden_pair] at this
      exact this
    · exact (ordinary_internal_iff G P l hr1 hr2).symm

theorem RigidAt.real_iff {S : Finset (GBranch G.tree)} {b : GBranch G.tree} (hR : RigidAt P S b) (x : GNode G.tree) :
    Mole.InIncidenceRealization G S x ↔
      Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P S) (naiveNodeEquiv G P x) := by
  have hl' : (reversePlacement G P).lower ∉ twistedAtoms G P S := fun h =>
    hR.lower_notMem ((mem_twistedAtoms G P S P.lower).mp h)
  refine real_iff_of P (not_internal_retained_of P hR.lower_notMem) (not_internal_pair_of P hR.lower_notMem)
    (not_internal_retained_of (reversePlacement G P) hl') ?_ x
  have := not_internal_pair_of (reversePlacement G P) hl'
  change ¬ Mole.IsInternalLeaf _ _ ((unitTwistGarden G P).pair (coreLeafEquiv G P P.retained)) at this
  exact this

end WaveTurbulence.VineEstS4
