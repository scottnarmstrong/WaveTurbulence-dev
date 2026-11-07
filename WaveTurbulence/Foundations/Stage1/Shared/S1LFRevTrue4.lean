/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1LFRevTrue3
public import WaveTurbulence.Foundations.Stage1.Shared.S1LayerTwistInv
import Mathlib.Tactic

/-!
# Reversal of a true-choice LF operation: the normalized base of the reverse source
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

theorem unitLayerTwist_eq_of_eq {LG1 LG2 : LayeredGarden w} (e : LG1 = LG2)
    {P1 : CorePlacement LG1.garden} {P2 : CorePlacement LG2.garden}
    (hP : (congrArg LayeredGarden.garden e ▸ P1 : CorePlacement LG2.garden) = P2)
    (h1 : SameLowerLayer LG1 P1) :
    ∃ h2 : SameLowerLayer LG2 P2, unitLayerTwist LG1 P1 h1 = unitLayerTwist LG2 P2 h2 := by
  subst e
  have : P1 = P2 := hP
  subst this
  exact ⟨h1, rfl⟩

theorem unitLayerTwist_involutive_of_eq {LG1 normA : LayeredGarden w} {PA : CorePlacement normA.garden}
    {hA : SameLowerLayer normA PA} (e : LG1 = unitLayerTwist normA PA hA) {P1 : CorePlacement LG1.garden}
    (hP : (congrArg LayeredGarden.garden e ▸ P1 : CorePlacement (unitLayerTwist normA PA hA).garden) =
      reversePlacement normA.garden PA) (h1 : SameLowerLayer LG1 P1) :
    unitLayerTwist LG1 P1 h1 = normA := by
  subst e
  have : P1 = reversePlacement normA.garden PA := hP
  subst this
  exact unitLayerTwist_involutive normA PA hA h1

theorem nil_lonePath : RegChain.nil.lonePath = [] := rfl

section Base
variable {s : LFSource p kind LG} (h : LFConstruction s true)

theorem revSourceT_base_true : (revSourceT s h).base true = s.base false := by
  have K := normalized_output h
  rw [pairs_true_exc s] at K
  let N := normalizedData s.data s.placement.lower s.exceptional
  have hqN : N.couple (pairOfLeaf s.skeleton s.plain s.placement.retained) = .triv :=
    (s.data.eraseTree s.placement.lower).eraseCouple_at s.exceptional
  let hdN := normalized_decodes LG s.data s.plain s.decodes s.placement.lower s.exceptional p
  let normA := normalizedLayered LG s.data s.plain s.decodes s.placement.lower s.exceptional p
  let PA := expandedPlacement N s.plain hdN s.placement hqN
  have hP : (congrArg LayeredGarden.garden K ▸
      expandedPlacement (normalizedData h.data (revSourceT s h).placement.lower (revSourceT s h).exceptional)
        (revSourceT s h).plain
        (normalized_decodes h.output h.data (revSourceT s h).plain h.decodes (revSourceT s h).placement.lower
          (revSourceT s h).exceptional p) (revSourceT s h).placement
        ((h.data.eraseTree (revSourceT s h).placement.lower).eraseCouple_at (revSourceT s h).exceptional) :
      CorePlacement (s.base true).garden) = reversePlacement normA.garden PA := by
    apply corePlacement_cast_eq
    · show (normalizedData h.data (revSourceT s h).placement.lower (revSourceT s h).exceptional).corePosition
        (revSourceT s h).placement.lower = (reversePlacement normA.garden PA).lower.1
      rw [normalizedData_output_true h, reverse_expanded_lower_val]
      have e1 : (s.baseData true).corePosition (s.branches true s.placement.lower) =
          inflatedPosition (s.chosen true) (s.baseData true).tree (s.branches true s.placement.lower).toNode := by
        unfold ReconstructionData.corePosition
        rw [baseData_tree_lower s true, nil_lonePath]
        exact Prod.ext rfl (List.append_nil _)
      refine e1.trans ?_
      exact twist_lower_inflated N s.plain s.placement
    · rfl
  have hA := normalization_sameLower LG s.data s.plain s.decodes s.placement s.canonical s.treeCoherent
    s.coupleCoherent s.core s.selected s.eligible
  have hbase : (revSourceT s h).base true = unitLayerTwist _ _ (normalization_sameLower h.output h.data
      (revSourceT s h).plain h.decodes (revSourceT s h).placement (revSourceT s h).canonical
      (revSourceT s h).treeCoherent (revSourceT s h).coupleCoherent (revSourceT s h).core
      (revSourceT s h).selected (revSourceT s h).eligible) := rfl
  rw [hbase]
  exact unitLayerTwist_involutive_of_eq (hA := hA) K hP _

end Base

end WaveTurbulence.Stage1
