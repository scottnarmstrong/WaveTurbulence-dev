/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1LFRevTrue0
import Mathlib.Tactic

/-!
# Reversal of a true-choice LF operation: the source at the output

Transport of end-rung data along the twist isomorphism, choice-generic coherence of the output, and the
source `revSourceT` seen from the output of a true-choice construction.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

/-! ### End rungs along a directed isomorphism -/

def fourIncidences_iso {G H : Garden w} (f : GardenDirectedIso G H) {v : GBranch G.tree}
    {nb : Fin 4 → GBranch G.tree} (R : Vine.FourIncidences G.molecule v nb) :
    Vine.FourIncidences H.molecule (f.branches v) (fun i => f.branches (nb i)) where
  dart := fun i => f.darts (R.dart i)
  injective := fun i j h => R.injective (f.darts.injective h)
  atom_eq := fun i => by rw [f.atom_comm, R.atom_eq]
  neighbor_eq := fun i => by rw [f.mate_comm, f.atom_comm, R.neighbor_eq]

def endRungData_iso {G H : Garden w} (f : GardenDirectedIso G H) {B : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (R : Molecpl.EndRungData G.molecule B a b) :
    Molecpl.EndRungData H.molecule (isoAtoms G H f B) (f.branches a) (f.branches b) where
  left := f.branches R.left
  right := f.branches R.right
  nextLeft := f.branches R.nextLeft
  nextRight := f.branches R.nextRight
  left_mem := (mem_isoAtoms G H f B _).mpr R.left_mem
  right_mem := (mem_isoAtoms G H f B _).mpr R.right_mem
  nextLeft_mem := (mem_isoAtoms G H f B _).mpr R.nextLeft_mem
  nextRight_mem := (mem_isoAtoms G H f B _).mpr R.nextRight_mem
  distinct := f.branches.injective.ne R.distinct
  left_ne_upper := f.branches.injective.ne R.left_ne_upper
  left_ne_lower := f.branches.injective.ne R.left_ne_lower
  right_ne_upper := f.branches.injective.ne R.right_ne_upper
  right_ne_lower := f.branches.injective.ne R.right_ne_lower
  nextLeft_ne_left := f.branches.injective.ne R.nextLeft_ne_left
  nextLeft_ne_right := f.branches.injective.ne R.nextLeft_ne_right
  nextRight_ne_left := f.branches.injective.ne R.nextRight_ne_left
  nextRight_ne_right := f.branches.injective.ne R.nextRight_ne_right
  left_row := by
    have := fourIncidences_iso f R.left_row
    convert this using 2
    rename_i i; fin_cases i <;> rfl
  right_row := by
    have := fourIncidences_iso f R.right_row
    convert this using 2
    rename_i i; fin_cases i <;> rfl


/-! ### Choice-generic coherence and eligibility at the output -/

section Output
variable {s : LFSource p kind LG} {ε : Bool}

theorem inducedPrelayer_output (h : LFConstruction s ε) (b : GBranch s.skeleton.tree) :
    inducedPrelayer h.output h.data (s.chosen_plain ε) h.decodes (s.branches ε b) =
      inducedPrelayer LG s.data s.plain s.decodes b :=
  (coreLayer_eq_layerAt h.output h.data (s.chosen_plain ε) h.decodes _).trans
    ((h.coreLayers b).symm.trans (coreLayer_eq_layerAt LG s.data s.plain s.decodes b).symm)

theorem treeCoherent_output_gen (h : LFConstruction s ε) :
    CohOn h.output ((h.data.tree (s.branches ε s.placement.lower)).linksAt
      (nodeSign (s.chosen ε).sig (s.branches ε s.placement.lower).1)
      (inflatedPosition (s.chosen ε) h.data.tree (s.branches ε s.placement.lower).toNode)) := by
  have e1 : h.data.tree (s.branches ε s.placement.lower) = h.newTree := Function.update_self _ _ _
  have e2 : inflatedPosition (s.chosen ε) h.data.tree (s.branches ε s.placement.lower).toNode =
      inflatedPosition (s.chosen ε) (s.midData ε h.newCouple h.couple_wf).tree
        (s.branches ε s.placement.lower).toNode := by
    have hED : h.data.eraseTree (s.branches ε s.placement.lower) = s.midData ε h.newCouple h.couple_wf :=
      eraseTree_final _ _ _ _
    rw [← hED]
    exact (h.data.eraseTree_position_at (s.branches ε s.placement.lower)).symm
  rw [e1, e2]
  exact h.treeInsertion.pattern.1

theorem coupleCoherent_output_gen (h : LFConstruction s ε) :
    CohOn h.output ((h.data.couple (s.pairs ε s.exceptional)).linksAt
      (inflatedPosition (s.chosen ε) h.data.tree
        ((s.pairs ε s.exceptional).firstLeaf (s.chosen_plain ε)).toNode)
      (inflatedPosition (s.chosen ε) h.data.tree
        ((s.pairs ε s.exceptional).secondLeaf (s.chosen_plain ε)).toNode)) := by
  rw [eraseTree_couple_links h.data (s.chosen_plain ε) (s.branches ε s.placement.lower)
    (s.pairs ε s.exceptional)]
  refine (cohOn_map_iff _ _ _ (eraseTree_native_layerAt h.output h.data (s.chosen_plain ε) h.decodes
    (s.branches ε s.placement.lower)) _).mpr ?_
  rw [collapse_output_eq_mid h]
  have hED' : h.data.eraseTree (s.branches ε s.placement.lower) =
      s.midData ε h.newCouple h.couple_wf := eraseTree_final _ _ _ _
  rw [hED']
  have e : (s.midData ε h.newCouple h.couple_wf).couple (s.pairs ε s.exceptional) = h.newCouple :=
    Function.update_self _ _ _
  rw [e]
  exact h.coupleInsertion.pattern.1

theorem eligible_output_true (h : LFConstruction s true) :
    SourceLayerEligible h.output h.data (s.chosen_plain true) h.decodes
      (reversePlacement s.skeleton s.placement) s.vineType
      (twistedAtoms s.skeleton s.placement s.support) (coreBranchEquiv s.skeleton s.placement s.upper) := by
  have hel := s.eligible
  unfold SourceLayerEligible at hel ⊢
  rcases hel with hI | ⟨hII, R, hR⟩
  · exact Or.inl hI
  · refine Or.inr ⟨hII, endRungData_iso (unitTwistDirectedIso s.skeleton s.placement) R, ?_⟩
    have e : ∀ b, inducedPrelayer h.output h.data (s.chosen_plain true) h.decodes (coreBranchEquiv s.skeleton s.placement b) =
        inducedPrelayer LG s.data s.plain s.decodes b := fun b => inducedPrelayer_output h b
    change inducedPrelayer h.output h.data (s.chosen_plain true) h.decodes (coreBranchEquiv s.skeleton s.placement s.placement.lower) ≤
      min (inducedPrelayer h.output h.data (s.chosen_plain true) h.decodes (coreBranchEquiv s.skeleton s.placement R.left))
        (inducedPrelayer h.output h.data (s.chosen_plain true) h.decodes (coreBranchEquiv s.skeleton s.placement R.right))
    rw [e, e, e]
    exact hR


theorem pairs_true_exc (s : LFSource p kind LG) :
    s.pairs true s.exceptional = pairOfLeaf (unitTwistGarden s.skeleton s.placement)
      (unitTwistGarden_plain s.skeleton s.placement s.plain)
      (coreLeafEquiv s.skeleton s.placement s.placement.retained) :=
  sourcePairEquiv_pairOfLeaf s.plain (s.chosen_plain true) (chosenLeafEquiv s.skeleton s.placement true)
    (chosenLeafEquiv_pair s.skeleton s.placement true) s.placement.retained

theorem treeCoherent_output_true (h : LFConstruction s true) :
    CohOn h.output ((h.data.tree (reversePlacement s.skeleton s.placement).lower).linksAt
      (nodeSign (unitTwistGarden s.skeleton s.placement).sig (reversePlacement s.skeleton s.placement).lower.1)
      (inflatedPosition (unitTwistGarden s.skeleton s.placement) h.data.tree
        (reversePlacement s.skeleton s.placement).lower.toNode)) :=
  treeCoherent_output_gen h

theorem coupleCoherent_output_true (h : LFConstruction s true) :
    CohOn h.output ((h.data.couple (pairOfLeaf (unitTwistGarden s.skeleton s.placement)
        (unitTwistGarden_plain s.skeleton s.placement s.plain)
        (reversePlacement s.skeleton s.placement).retained)).linksAt
      (inflatedPosition (unitTwistGarden s.skeleton s.placement) h.data.tree
        ((pairOfLeaf (unitTwistGarden s.skeleton s.placement)
          (unitTwistGarden_plain s.skeleton s.placement s.plain)
          (reversePlacement s.skeleton s.placement).retained).firstLeaf
            (unitTwistGarden_plain s.skeleton s.placement s.plain)).toNode)
      (inflatedPosition (unitTwistGarden s.skeleton s.placement) h.data.tree
        ((pairOfLeaf (unitTwistGarden s.skeleton s.placement)
          (unitTwistGarden_plain s.skeleton s.placement s.plain)
          (reversePlacement s.skeleton s.placement).retained).secondLeaf
            (unitTwistGarden_plain s.skeleton s.placement s.plain)).toNode)) := by
  have := coupleCoherent_output_gen h
  rw [pairs_true_exc] at this
  exact this

/-- The source seen from the output of a true-choice construction (reverse placement). -/
@[expose] noncomputable def revSourceT (s : LFSource p kind LG) (h : LFConstruction s true) :
    LFSource p kind h.output where
  skeleton := unitTwistGarden s.skeleton s.placement
  plain := unitTwistGarden_plain s.skeleton s.placement s.plain
  data := h.data
  decodes := h.decodes
  placement := reversePlacement s.skeleton s.placement
  canonical := h.canonical
  vineType := s.vineType
  support := twistedAtoms s.skeleton s.placement s.support
  upper := coreBranchEquiv s.skeleton s.placement s.upper
  core := isCoreCLVine_twistedAtoms s.skeleton s.placement s.core s.selected
  selected := reversePlacement_at_twistedAtoms s.skeleton s.placement s.core.1.1 s.core.2.1 s.selected
  eligible := eligible_output_true h
  treeCoherent := treeCoherent_output_true h
  coupleCoherent := coupleCoherent_output_true h

end Output

end WaveTurbulence.Stage1
