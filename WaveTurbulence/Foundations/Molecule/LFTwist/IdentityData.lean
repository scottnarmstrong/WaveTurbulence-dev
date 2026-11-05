/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.LFReinsertData
public import WaveTurbulence.Foundations.Molecule.LFTwist.DecodedLayered

/-! # Unchanged exceptional codes recover the original actual reconstruction -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist

private theorem sourcePairEquiv_refl {w : ℕ} (G : Garden w) (hG : G.IsPlain) (q : SourcePair G) :
    sourcePairEquiv hG hG (Equiv.refl _) (fun _ => rfl) q = q := pairOfLeaf_firstLeaf G hG q

theorem transportReconstruction_refl {w : ℕ} {G : Garden w} (D : ReconstructionData G) (hG : G.IsPlain) :
    transportReconstruction hG hG (Equiv.refl _) (Equiv.refl _) (fun _ => rfl) D = D := by
  apply ReconstructionData.ext_tree_couple
  · rfl
  · funext q
    apply congrArg D.couple
    apply (sourcePairEquiv hG hG (Equiv.refl _) (fun _ => rfl)).injective
    exact ((sourcePairEquiv hG hG (Equiv.refl _) (fun _ => rfl)).apply_symm_apply q).trans
      (sourcePairEquiv_refl G hG q).symm

namespace LFSource
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG)

theorem pairs_false (q : SourcePair s.skeleton) : s.pairs false q = q :=
  sourcePairEquiv_refl s.skeleton s.plain q

theorem baseData_false : s.baseData false = normalizedData s.data s.placement.lower s.exceptional :=
  transportReconstruction_refl _ s.plain

/-- Restoring the old couple leaves exactly the original lower-tree erasure. -/
theorem midData_identity : s.midData false (s.data.couple s.exceptional) (s.data.couple_wf s.exceptional) =
    s.data.eraseTree s.placement.lower := by
  change (s.baseData false).withCouple (s.pairs false s.exceptional) _ _ = _
  rw [s.pairs_false,s.baseData_false]
  apply ReconstructionData.ext_tree_couple
  · rfl
  · funext q
    by_cases hq : q = s.exceptional
    · subst q
      exact Function.update_self _ _ _
    · exact (Function.update_of_ne hq _ _).trans
        ((s.data.eraseTree s.placement.lower).eraseCouple_other s.exceptional q hq)

/-- False skeleton choice and unchanged exceptional attachments recover the
entire original code datum, including every ordinary slot. -/
theorem finalData_identity :
    s.finalData false (s.data.tree s.placement.lower) (s.data.couple s.exceptional)
      (s.data.tree_wf s.placement.lower) (s.data.couple_wf s.exceptional) = s.data := by
  change (s.midData false _ _).withTree _ _ _ = _
  rw [s.midData_identity]
  apply ReconstructionData.ext_tree_couple
  · funext b
    by_cases hb : b = s.placement.lower
    · subst b
      exact Function.update_self _ _ _
    · exact (Function.update_of_ne hb _ _).trans (s.data.eraseTree_other s.placement.lower b hb)
  · rfl

/-- The old layered garden is an actual output on the unchanged-choice carrier. -/
theorem identity_output_decodes :
    (s.finalData false (s.data.tree s.placement.lower) (s.data.couple s.exceptional)
      (s.data.tree_wf s.placement.lower) (s.data.couple_wf s.exceptional)).Decodes (s.chosen_plain false) LG.garden :=
  s.finalData_identity.symm ▸ s.decodes

end LFSource
end WaveTurbulence.LFTwist
