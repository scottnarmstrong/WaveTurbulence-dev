/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistTypeIISwitches

/-! # Actual source type-I scenario switches under a designated unit twist -/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- Moving the lower root to u0 gives the old u0 child position. -/
theorem new_lower_child_from_pair {p : GBranch G.tree} {j : Fin 3}
    (fp : (coreBranchEquiv G P p).1 = p.1) (hr : (G.pair P.retained).toNode = p.child j) :
    (coreBranchEquiv G P p).child j = (coreBranchEquiv G P P.lower).toNode := by
  apply Subtype.ext
  change ((coreBranchEquiv G P p).1.1,(coreBranchEquiv G P p).1.2 ++ [j]) = (coreBranchEquiv G P P.lower).1
  rw [fp,coreBranchEquiv_lower_val]
  exact (congrArg (fun n : GNode G.tree => n.1) hr).symm

/-- Moving u0 to the lower root gives the old lower child position. -/
theorem new_paired_child_from_lower {p : GBranch G.tree} {i : Fin 3}
    (fp : (coreBranchEquiv G P p).1 = p.1) (hb : p.child i = P.lower.toNode) :
    ((unitTwistGarden G P).pair (coreLeafEquiv G P P.retained)).toNode = (coreBranchEquiv G P p).child i := by
  rw [unitTwistGarden_pair]
  apply Subtype.ext
  change (coreLeafEquiv G P (G.pair P.retained)).1 =
    ((coreBranchEquiv G P p).1.1,(coreBranchEquiv G P p).1.2 ++ [i])
  rw [coreLeafEquiv_paired_val,fp]
  exact (congrArg (fun n : GNode G.tree => n.1) hb).symm

/-- The designated unit twist exchanges source type (I-a) with type (I-b). -/
theorem typeI_A_to_B {S : Finset (GBranch G.tree)} {a : GBranch G.tree}
    (hB : G.molecule.IsBlock S a P.lower) (hCL : Mole.CLParentPattern G S a P.lower)
    (hP : IsPlacementAt G S P.lower P) (h : Molecpl.IsTypeIA G a P.lower) :
    Molecpl.IsTypeIB (unitTwistGarden G P) (coreBranchEquiv G P a) (coreBranchEquiv G P P.lower) := by
  obtain ⟨i,hi,hbi,k,l,_hk,hm,hl,hr⟩ := h
  have he := placement_retained_of_pair G P hB hCL hP hB.2.1 hm hl hr
  subst l
  have fa := selected_branch_fixed G P hB hCL hP hB.2.1 hB.2.2.2.1
  exact ⟨new_lower_child_from_pair G P fa hr,i,hi,P.keep,coreLeafEquiv G P P.retained,
    P.outer,(unitTwistGarden_mark G P P.retained).trans P.unmarked,(reversePlacement G P).child,
    new_paired_child_from_lower G P fa hbi⟩

/-- The designated unit twist exchanges source type (I-b) with type (I-a). -/
theorem typeI_B_to_A {S : Finset (GBranch G.tree)} {a : GBranch G.tree}
    (hB : G.molecule.IsBlock S a P.lower) (hCL : Mole.CLParentPattern G S a P.lower)
    (hP : IsPlacementAt G S P.lower P) (h : Molecpl.IsTypeIB G a P.lower) :
    Molecpl.IsTypeIA (unitTwistGarden G P) (coreBranchEquiv G P a) (coreBranchEquiv G P P.lower) := by
  obtain ⟨hbi,j,hj,k,l,_hk,hm,hl,hr⟩ := h
  have he := placement_retained_of_pair G P hB hCL hP hB.2.1 hm hl hr
  subst l
  have fa := selected_branch_fixed G P hB hCL hP hB.2.1 hB.2.2.2.1
  exact ⟨j,hj,new_lower_child_from_pair G P fa hr,P.keep,coreLeafEquiv G P P.retained,
    P.outer,(unitTwistGarden_mark G P P.retained).trans P.unmarked,(reversePlacement G P).child,
    new_paired_child_from_lower G P fa hbi⟩

end WaveTurbulence.Twist
