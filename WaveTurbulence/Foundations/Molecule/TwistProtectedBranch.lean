/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistFamilyAction

/-! # Branches outside active lower subtrees stay protected

This geometric fact supplies a witness that different subsets give
different actual gardens, not merely different marked family states.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} {G : Garden w}

/-- A branch outside the exchanged lower subtree stays outside every branch
that was not its ancestor before the surgery. -/
theorem coreBranchEquiv_not_desc (P : CorePlacement G) (u v : GBranch G.tree)
    (hv : ¬ P.lower.toNode.IsDesc v.toNode) (hu : ¬ u.toNode.IsDesc v.toNode) :
    ¬ (coreBranchEquiv G P u).toNode.IsDesc (coreBranchEquiv G P v).toNode := by
  have hfv := coreBranchEquiv_fixed_val G P v hv
  by_cases hd : P.lower.toNode.IsDesc u.toNode
  · intro hn
    have huaddr := coreBranchEquiv_address G P u
    obtain ⟨q,hq⟩ := hd.2
    have hvu : u.1 = (P.lower.1.1,P.lower.1.2 ++ q) := Prod.ext hd.1.symm hq.symm
    have hfu : (coreBranchEquiv G P u).1 =
        ((G.pair P.retained).1.1,(G.pair P.retained).1.2 ++ switchPath P.keep q) := by
      exact huaddr.trans (by rw [hvu]; simp [exchangeAddress])
    change (coreBranchEquiv G P u).1.1 = (coreBranchEquiv G P v).1.1 ∧
      (coreBranchEquiv G P u).1.2 <+: (coreBranchEquiv G P v).1.2 at hn
    rw [hfu,hfv] at hn
    have hp := (List.prefix_append (G.pair P.retained).1.2 (switchPath P.keep q)).trans hn.2
    exact leaf_not_prefix_branch (G.pair P.retained).2 (hn.1 ▸ v.2) hp
  · have hfu := coreBranchEquiv_fixed_val G P u hd
    exact fun hn => hu ((fixed_branch_desc_iff G P hfu hfv).mp hn)

/-- Actual ancestor relations depend only on the two raw node addresses. -/
theorem branchDesc_iff_of_vals {F H : Fin w → TTree} {a b : GBranch F} {c d : GBranch H}
    (ha : a.1 = c.1) (hb : b.1 = d.1) : a.toNode.IsDesc b.toNode ↔ c.toNode.IsDesc d.toNode := by
  change a.1.1 = b.1.1 ∧ a.1.2 <+: b.1.2 ↔ c.1.1 = d.1.1 ∧ c.1.2 <+: d.1.2
  rw [ha,hb]

/-- A protected family's lower address does not move at this active site. -/
theorem CoreFamily.protected_lower {ι : Type*} (F : CoreFamily G ι) (i j : ι)
    (hv : ¬ (F.placement i).lower.toNode.IsDesc (F.placement j).lower.toNode) :
    ((F.twist i).placement j).lower.1 = (F.placement j).lower.1 :=
  (congrArg Subtype.val (F.nextPlacement_lower i j)).trans
    (coreBranchEquiv_fixed_val G (F.placement i) (F.placement j).lower hv)

/-- An outside family member stays outside the protected lower site after this surgery. -/
theorem CoreFamily.protected_outside {ι : Type*} (F : CoreFamily G ι) (i j k : ι)
    (hi : ¬ (F.placement i).lower.toNode.IsDesc (F.placement j).lower.toNode)
    (hk : ¬ (F.placement k).lower.toNode.IsDesc (F.placement j).lower.toNode) :
    ¬ ((F.twist i).placement k).lower.toNode.IsDesc ((F.twist i).placement j).lower.toNode := by
  have h := coreBranchEquiv_not_desc (F.placement i) (F.placement k).lower (F.placement j).lower hi hk
  exact fun hn => h ((branchDesc_iff_of_vals
    (congrArg Subtype.val (F.nextPlacement_lower i k)) (congrArg Subtype.val (F.nextPlacement_lower i j))).mp hn)

/-- A unit twist leaves a literal leaf at the old lower branching address. -/
theorem unitTwist_leaf_at_lower (P : CorePlacement G) :
    P.lower.1.2 ∈ ((unitTwistGarden G P).tree P.lower.1.1).leaves := by
  have hm := (coreLeafEquiv G P (G.pair P.retained)).2
  change (coreLeafEquiv G P (G.pair P.retained)).1.2 ∈
    ((unitTwistGarden G P).tree (coreLeafEquiv G P (G.pair P.retained)).1.1).leaves at hm
  simpa only [coreLeafEquiv_paired_val] using hm

end WaveTurbulence.Twist
