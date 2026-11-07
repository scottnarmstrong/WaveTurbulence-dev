/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Dia3
public import WaveTurbulence.Foundations.Stage1.Shared.S1LFRevTrue6
import Mathlib.Tactic

/-!
# Transport across a `true`-choice operation: eligibility and data of another member
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

@[expose] def fourIncidences_iso' {G H : Garden w} (f : GardenDirectedIso G H) {v : GBranch G.tree}
    {nb : Fin 4 → GBranch G.tree} (R : Vine.FourIncidences G.molecule v nb) :
    Vine.FourIncidences H.molecule (f.branches v) (fun i => f.branches (nb i)) where
  dart := fun i => f.darts (R.dart i)
  injective := fun i j h => R.injective (f.darts.injective h)
  atom_eq := fun i => by rw [f.atom_comm, R.atom_eq]
  neighbor_eq := fun i => by rw [f.mate_comm, f.atom_comm, R.neighbor_eq]

@[expose] def endRungData_iso' {G H : Garden w} (f : GardenDirectedIso G H) {B : Finset (GBranch G.tree)}
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
    have := fourIncidences_iso' f R.left_row
    convert this using 2
    rename_i i; fin_cases i <;> rfl
  right_row := by
    have := fourIncidences_iso' f R.right_row
    convert this using 2
    rename_i i; fin_cases i <;> rfl

theorem data_tree_other_true {s : LFSource p kind LG} (h : LFConstruction s true) (b : GBranch s.skeleton.tree)
    (hb : b ≠ s.placement.lower) : h.data.tree (s.branches true b) = s.data.tree b := by
  have hne : s.branches true b ≠ s.branches true s.placement.lower :=
    fun he => hb ((s.branches true).injective he)
  exact (Function.update_of_ne hne _ _).trans (s.base_tree_other true b hb)

theorem data_couple_other_true {s : LFSource p kind LG} (h : LFConstruction s true) (q : SourcePair s.skeleton)
    (hq : q ≠ s.exceptional) : h.data.couple (s.pairs true q) = s.data.couple q := by
  have hne : s.pairs true q ≠ s.pairs true s.exceptional := fun he => hq ((s.pairs true).injective he)
  exact (Function.update_of_ne hne _ _).trans (s.base_couple_other true q hq)

/-- Eligibility of another member is preserved by a `true`-choice operation (only the induced
prelayer and the end-rung transport matter). -/
theorem eligible_transport_true {s : LFSource p kind LG} (h : LFConstruction s true)
    {P : CorePlacement s.skeleton} {P' : CorePlacement (unitTwistGarden s.skeleton s.placement)}
    (hP' : P'.lower = coreBranchEquiv s.skeleton s.placement P.lower)
    {X : VineType} {B : Finset (GBranch s.skeleton.tree)} {a : GBranch s.skeleton.tree}
    (el : SourceLayerEligible LG s.data s.plain s.decodes P X B a) :
    SourceLayerEligible h.output h.data (s.chosen_plain true) h.decodes P' X
      (twistedAtoms s.skeleton s.placement B) (coreBranchEquiv s.skeleton s.placement a) := by
  unfold SourceLayerEligible at el ⊢
  rcases el with hI | ⟨hII, R, hR⟩
  · exact Or.inl hI
  · refine Or.inr ⟨hII, ?_⟩
    rw [hP']
    refine ⟨endRungData_iso' (unitTwistDirectedIso s.skeleton s.placement) R, ?_⟩
    have e : ∀ b, inducedPrelayer h.output h.data (s.chosen_plain true) h.decodes
        (coreBranchEquiv s.skeleton s.placement b) = inducedPrelayer LG s.data s.plain s.decodes b :=
      fun b => inducedPrelayer_output h b
    change inducedPrelayer h.output h.data (s.chosen_plain true) h.decodes (coreBranchEquiv s.skeleton s.placement P.lower) ≤
      min (inducedPrelayer h.output h.data (s.chosen_plain true) h.decodes (coreBranchEquiv s.skeleton s.placement R.left))
        (inducedPrelayer h.output h.data (s.chosen_plain true) h.decodes (coreBranchEquiv s.skeleton s.placement R.right))
    rw [e, e, e]
    exact hR

variable {ι : Type*}

theorem transT_treeCoherent (A : FamilyReconstruction w ι) (i j : ι) (hij : i ≠ j)
    (c : CanonicalObject p kind A.layered)
    (el : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement i)
      (A.family.kind i) (A.family.atoms i) (A.family.upper i))
    (tc : CohOn A.layered ((A.data.tree (A.family.placement i).lower).linksAt
      (nodeSign A.skeleton.sig (A.family.placement i).lower.1)
      (inflatedPosition A.skeleton A.data.tree (A.family.placement i).lower.toNode)))
    (cc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).linksAt
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).firstLeaf A.plain).toNode)
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).secondLeaf A.plain).toNode)))
    (con : LFConstruction (A.source i c el tc cc) true)
    (tcJ : CohOn A.layered ((A.data.tree (A.family.placement j).lower).linksAt
      (nodeSign A.skeleton.sig (A.family.placement j).lower.1)
      (inflatedPosition A.skeleton A.data.tree (A.family.placement j).lower.toNode))) :
    CohOn con.output ((con.data.tree (A.family.nextPlacement i j).lower).linksAt
      (nodeSign (unitTwistGarden A.skeleton (A.family.placement i)).sig (A.family.nextPlacement i j).lower.1)
      (inflatedPosition (unitTwistGarden A.skeleton (A.family.placement i)) con.data.tree
        (A.family.nextPlacement i j).lower.toNode)) := by
  have hb : (A.family.placement j).lower ≠ (A.source i c el tc cc).placement.lower :=
    fun he => hij ((A.family.lower_injective he).symm)
  rw [CoreFamily.nextPlacement_lower]
  have ht : con.data.tree (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement j).lower) =
      A.data.tree (A.family.placement j).lower := data_tree_other_true con _ hb
  have hs := coreBranchEquiv_sign A.skeleton (A.family.placement i) (A.family.placement j).lower
  have hb' : (A.family.placement j).lower ≠ (A.family.placement i).lower :=
    CoreFamily.lower_ne_of_ne A.family hij.symm
  rw [if_neg hb'] at hs
  have hs' : nodeSign (unitTwistGarden A.skeleton (A.family.placement i)).sig
      (coreBranchEquiv A.skeleton (A.family.placement i) (A.family.placement j).lower).1 =
      nodeSign A.skeleton.sig (A.family.placement j).lower.1 := hs
  rw [ht, hs']
  refine cohOn_chain_transport _ _ _ _ (fun r hr => ?_) tcJ
  exact (con.ordinaryTreeLayers _ hb r hr).symm

theorem transT_coupleCoherent (A : FamilyReconstruction w ι) (i j : ι) (hij : i ≠ j)
    (c : CanonicalObject p kind A.layered)
    (el : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement i)
      (A.family.kind i) (A.family.atoms i) (A.family.upper i))
    (tc : CohOn A.layered ((A.data.tree (A.family.placement i).lower).linksAt
      (nodeSign A.skeleton.sig (A.family.placement i).lower.1)
      (inflatedPosition A.skeleton A.data.tree (A.family.placement i).lower.toNode)))
    (cc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).linksAt
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).firstLeaf A.plain).toNode)
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).secondLeaf A.plain).toNode)))
    (con : LFConstruction (A.source i c el tc cc) true)
    (ccJ : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement j).retained)).linksAt
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement j).retained).firstLeaf A.plain).toNode)
      (inflatedPosition A.skeleton A.data.tree
        ((pairOfLeaf A.skeleton A.plain (A.family.placement j).retained).secondLeaf A.plain).toNode))) :
    CohOn con.output ((con.data.couple (pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement i))
        (unitTwistGarden_plain A.skeleton (A.family.placement i) A.plain)
        (A.family.nextPlacement i j).retained)).linksAt
      (inflatedPosition (unitTwistGarden A.skeleton (A.family.placement i)) con.data.tree
        ((pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement i))
          (unitTwistGarden_plain A.skeleton (A.family.placement i) A.plain)
          (A.family.nextPlacement i j).retained).firstLeaf
          (unitTwistGarden_plain A.skeleton (A.family.placement i) A.plain)).toNode)
      (inflatedPosition (unitTwistGarden A.skeleton (A.family.placement i)) con.data.tree
        ((pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement i))
          (unitTwistGarden_plain A.skeleton (A.family.placement i) A.plain)
          (A.family.nextPlacement i j).retained).secondLeaf
          (unitTwistGarden_plain A.skeleton (A.family.placement i) A.plain)).toNode)) := by
  set q := pairOfLeaf A.skeleton A.plain (A.family.placement j).retained with hq
  have hne : q ≠ (A.source i c el tc cc).exceptional :=
    fun he => CoreFamily.exceptional_ne A.family A.plain hij.symm he
  have hpe : (A.source i c el tc cc).pairs true q =
      pairOfLeaf (unitTwistGarden A.skeleton (A.family.placement i))
        (unitTwistGarden_plain A.skeleton (A.family.placement i) A.plain)
        (coreLeafEquiv A.skeleton (A.family.placement i) (A.family.placement j).retained) :=
    sourcePairEquiv_pairOfLeaf (A.source i c el tc cc).plain ((A.source i c el tc cc).chosen_plain true)
      (chosenLeafEquiv _ _ true) (chosenLeafEquiv_pair _ _ true) _
  rw [CoreFamily.nextPlacement_retained, ← hpe]
  have hco : con.data.couple ((A.source i c el tc cc).pairs true q) = A.data.couple q :=
    data_couple_other_true con q hne
  rw [hco]
  have hemb := reconstruction_coupleEmb A.data A.plain A.decodes q
  refine cohOn_couple_transport _ _ _ _ _ hemb.indep (fun r hr => ?_) (fun r hr => ?_) ccJ
  · have := con.ordinaryCoupleLayers q hne 0 r hr
    exact this.symm
  · have := con.ordinaryCoupleLayers q hne 1 r hr
    exact this.symm

end WaveTurbulence.Stage1
