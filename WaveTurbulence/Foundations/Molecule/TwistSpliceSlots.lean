/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistCLTransport

/-! # The actual CL splice slots after the designated unit twist

TARGET twistexplain (c): the upper excluded position and lower retained
position are unchanged; the two free subtrees exchange positions by sign.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)
variable {S : Finset (GBranch G.tree)} {a : GBranch G.tree}

/-- The designated old lower retained slot is still internally occupied after the twist. -/
theorem twisted_kept_internal (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) :
    P.keep.succ ∈ Mole.internalPositions (unitTwistGarden G P) (twistedAtoms G P S) (coreBranchEquiv G P P.lower) := by
  have hm : GNode.parent P.lower.toNode P.nonroot ∈ S := hCL.2.choose_spec
  have hg : G.molecule.InGroup S (lowerPC G P false) := ⟨hB.2.2.1,hm⟩
  exact (Mole.mem_internalPositions (unitTwistGarden G P)).mpr
    ⟨twistDartEquiv G P (lowerPC G P false),twistDartEquiv_atom G P (lowerPC G P false),
      (inGroup_twistedAtoms G P S _).mpr hg,lowerPC_twisted_position G P⟩

/-- The new lower internal child is exactly the original retained outer slot. -/
theorem twisted_lower_slots (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P) :
    ∀ i : Fin 3, i.succ ∈ Mole.internalPositions (unitTwistGarden G P) (twistedAtoms G P S)
      (coreBranchEquiv G P P.lower) ↔ i = P.keep := by
  have hb := isBlock_twistedAtoms G P hB
  have hc := clParentPattern_twistedAtoms G P hB hCL hP
  obtain ⟨k,_hk,hslots⟩ := Mole.with_parent_joint_retained_child (unitTwistGarden G P) hb.2.2.1
    hb.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.1 hc.2
  have hi := (hslots P.keep).mp (twisted_kept_internal G P hB hCL)
  subst k
  exact hslots

/-- The reverse placement is precisely the designated placement of the transported CL block. -/
theorem reversePlacement_at_twistedAtoms (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P) :
    IsPlacementAt (unitTwistGarden G P) (twistedAtoms G P S) (coreBranchEquiv G P P.lower) (reversePlacement G P) :=
  ⟨rfl,twisted_lower_slots G P hB hCL hP⟩

/-- The exact old upper excluded and lower retained positions give valid new CL splice slots. -/
@[expose] noncomputable def twistedSpliceSlots (hB : G.molecule.IsBlock S a P.lower)
    (hCL : Mole.CLParentPattern G S a P.lower) (hP : IsPlacementAt G S P.lower P)
    (D : Mole.CLSpliceSlots G S a P.lower) :
    Mole.CLSpliceSlots (unitTwistGarden G P) (twistedAtoms G P S)
      (coreBranchEquiv G P a) (coreBranchEquiv G P P.lower) where
  excluded := D.excluded
  kept := P.keep
  excluded_ne_middle := D.excluded_ne_middle
  kept_ne_middle := P.outer
  upper i := (internalPositions_twist_other G P S a hB.2.2.2.1 i.succ).trans (D.upper i)
  lower := twisted_lower_slots G P hB hCL hP

/-- The old splice's kept index equals the designated u23 index. -/
theorem spliceSlots_kept (hP : IsPlacementAt G S P.lower P) (D : Mole.CLSpliceSlots G S a P.lower) :
    D.kept = P.keep := ((D.lower P.keep).mp ((hP.2 P.keep).mpr rfl)).symm

end WaveTurbulence.Twist
