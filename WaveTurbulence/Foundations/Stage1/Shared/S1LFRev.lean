/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1LFNorm
public import WaveTurbulence.Foundations.Molecule.LFTwist.FamilyOutputs
public import WaveTurbulence.Foundations.Molecule.LFTwist.IdentityConstruction
import Mathlib.Tactic

/-!
# Reversing an LF operation (skeleton choice `false`)

First pieces of the reverse operation: the induced prelayer of the output equals the one of the source
(from the `coreLayers` field), so source layer eligibility is preserved.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

theorem coreLayer_eq_layerAt {S : Garden w} (LG : LayeredGarden w) (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS LG.garden) (b : GBranch S.tree) :
    coreLayer LG D hS hd b = layerAt LG (D.corePosition b) :=
  (layerAt_node LG (D.decodedCoreBranch hS hd b).toNode).symm

theorem inducedPrelayer_output_false {s : LFSource p kind LG} (h : LFConstruction s false)
    (b : GBranch s.skeleton.tree) :
    inducedPrelayer h.output h.data (s.chosen_plain false) h.decodes b =
      inducedPrelayer LG s.data s.plain s.decodes b := by
  exact (coreLayer_eq_layerAt h.output h.data (s.chosen_plain false) h.decodes b).trans
    ((h.coreLayers b).symm.trans (coreLayer_eq_layerAt LG s.data s.plain s.decodes b).symm)

variable {s : LFSource p kind LG}

theorem eligible_output (h : LFConstruction s false) :
    SourceLayerEligible h.output h.data s.plain h.decodes s.placement s.vineType s.support s.upper := by
  have hP : inducedPrelayer h.output h.data s.plain h.decodes =
      inducedPrelayer LG s.data s.plain s.decodes := funext (inducedPrelayer_output_false h)
  have := s.eligible
  unfold SourceLayerEligible at this ⊢
  rw [hP]
  exact this

theorem treeCoherent_output (h : LFConstruction s false) :
    CohOn h.output ((h.data.tree s.placement.lower).linksAt (nodeSign s.skeleton.sig s.placement.lower.1)
      (inflatedPosition s.skeleton h.data.tree s.placement.lower.toNode)) := by
  have e1 : h.data.tree s.placement.lower = h.newTree := Function.update_self _ _ _
  have e2 : inflatedPosition s.skeleton h.data.tree s.placement.lower.toNode =
      inflatedPosition (s.chosen false) (s.midData false h.newCouple h.couple_wf).tree
        (s.branches false s.placement.lower).toNode := by
    have hED : h.data.eraseTree s.placement.lower = s.midData false h.newCouple h.couple_wf :=
      eraseTree_final _ _ _ _
    rw [← hED]
    exact (h.data.eraseTree_position_at s.placement.lower).symm
  rw [e1, e2]
  exact h.treeInsertion.pattern.1

/-- The source seen from the output of a false-choice construction (same skeleton and placement). -/
@[expose] noncomputable def revSource (h : LFConstruction s false)
    (hel : SourceLayerEligible h.output h.data s.plain h.decodes s.placement s.vineType s.support s.upper)
    (htc : CohOn h.output ((h.data.tree s.placement.lower).linksAt (nodeSign s.skeleton.sig s.placement.lower.1)
      (inflatedPosition s.skeleton h.data.tree s.placement.lower.toNode)))
    (hcc : CohOn h.output ((h.data.couple (pairOfLeaf s.skeleton s.plain s.placement.retained)).linksAt
      (inflatedPosition s.skeleton h.data.tree
        ((pairOfLeaf s.skeleton s.plain s.placement.retained).firstLeaf s.plain).toNode)
      (inflatedPosition s.skeleton h.data.tree
        ((pairOfLeaf s.skeleton s.plain s.placement.retained).secondLeaf s.plain).toNode))) :
    LFSource p kind h.output where
  skeleton := s.skeleton
  plain := s.plain
  data := h.data
  decodes := h.decodes
  placement := s.placement
  canonical := h.canonical
  vineType := s.vineType
  support := s.support
  upper := s.upper
  core := s.core
  selected := s.selected
  eligible := hel
  treeCoherent := htc
  coupleCoherent := hcc

theorem coupleCoherent_output (h : LFConstruction s false) :
    CohOn h.output ((h.data.couple (pairOfLeaf s.skeleton s.plain s.placement.retained)).linksAt
      (inflatedPosition s.skeleton h.data.tree
        ((pairOfLeaf s.skeleton s.plain s.placement.retained).firstLeaf s.plain).toNode)
      (inflatedPosition s.skeleton h.data.tree
        ((pairOfLeaf s.skeleton s.plain s.placement.retained).secondLeaf s.plain).toNode)) := by
  have hED : h.data.eraseTree s.placement.lower = s.midData false h.newCouple h.couple_wf :=
    eraseTree_final _ _ _ _
  have hq : s.pairs false s.exceptional = s.exceptional := LFSource.pairs_false s _
  have hmain : CohOn h.output ((h.data.couple (s.pairs false s.exceptional)).linksAt
      (inflatedPosition (s.chosen false) h.data.tree
        ((s.pairs false s.exceptional).firstLeaf (s.chosen_plain false)).toNode)
      (inflatedPosition (s.chosen false) h.data.tree
        ((s.pairs false s.exceptional).secondLeaf (s.chosen_plain false)).toNode)) := by
    rw [eraseTree_couple_links h.data (s.chosen_plain false) (s.branches false s.placement.lower)
      (s.pairs false s.exceptional)]
    refine (cohOn_map_iff _ _ _ (eraseTree_native_layerAt h.output h.data (s.chosen_plain false) h.decodes
      (s.branches false s.placement.lower)) _).mpr ?_
    rw [collapse_output_eq_mid h]
    have hED' : h.data.eraseTree (s.branches false s.placement.lower) =
        s.midData false h.newCouple h.couple_wf := eraseTree_final _ _ _ _
    rw [hED']
    have e : (s.midData false h.newCouple h.couple_wf).couple (s.pairs false s.exceptional) = h.newCouple :=
      Function.update_self _ _ _
    rw [e]
    exact h.coupleInsertion.pattern.1
  change CohOn h.output ((h.data.couple s.exceptional).linksAt
      (inflatedPosition s.skeleton h.data.tree (s.exceptional.firstLeaf s.plain).toNode)
      (inflatedPosition s.skeleton h.data.tree (s.exceptional.secondLeaf s.plain).toNode))
  exact hq ▸ hmain

variable (h : LFConstruction s false)
  (hel : SourceLayerEligible h.output h.data s.plain h.decodes s.placement s.vineType s.support s.upper)
  (htc : CohOn h.output ((h.data.tree s.placement.lower).linksAt (nodeSign s.skeleton.sig s.placement.lower.1)
      (inflatedPosition s.skeleton h.data.tree s.placement.lower.toNode)))
  (hcc : CohOn h.output ((h.data.couple (pairOfLeaf s.skeleton s.plain s.placement.retained)).linksAt
      (inflatedPosition s.skeleton h.data.tree
        ((pairOfLeaf s.skeleton s.plain s.placement.retained).firstLeaf s.plain).toNode)
      (inflatedPosition s.skeleton h.data.tree
        ((pairOfLeaf s.skeleton s.plain s.placement.retained).secondLeaf s.plain).toNode)))

theorem revSource_baseData : (revSource h hel htc hcc).baseData false = s.baseData false := by
  have e1 : (revSource h hel htc hcc).baseData false =
      normalizedData h.data s.placement.lower s.exceptional := LFSource.baseData_false _
  rw [e1]
  have e2 := eraseCouple_mid (s := s) (ε := false) h.newCouple h.couple_wf
  have e3 : h.data.eraseTree s.placement.lower = s.midData false h.newCouple h.couple_wf :=
    eraseTree_final _ _ _ _
  unfold normalizedData
  rw [e3]
  rw [LFSource.pairs_false] at e2
  exact e2

theorem revSource_base : (revSource h hel htc hcc).base false = s.base false := by
  have e1 : (revSource h hel htc hcc).base false =
      normalizedLayered h.output h.data (s.chosen_plain false) h.decodes s.placement.lower s.exceptional p := rfl
  rw [e1]
  have := normalized_output h
  rw [LFSource.pairs_false] at this
  exact this

theorem revSource_midData :
    (revSource h hel htc hcc).midData false (s.data.couple s.exceptional) (s.data.couple_wf s.exceptional) =
      s.data.eraseTree s.placement.lower := by
  have hm : (revSource h hel htc hcc).midData false (s.data.couple s.exceptional)
      (s.data.couple_wf s.exceptional) = s.midData false (s.data.couple s.exceptional)
      (s.data.couple_wf s.exceptional) := by
    unfold LFSource.midData
    rw [revSource_baseData h hel htc hcc]
    rfl
  exact hm.trans s.midData_identity

theorem revSource_finalData :
    (revSource h hel htc hcc).finalData false (s.data.tree s.placement.lower) (s.data.couple s.exceptional)
      (s.data.tree_wf s.placement.lower) (s.data.couple_wf s.exceptional) = s.data := by
  have hm : (revSource h hel htc hcc).finalData false (s.data.tree s.placement.lower)
      (s.data.couple s.exceptional) (s.data.tree_wf s.placement.lower) (s.data.couple_wf s.exceptional) =
      s.finalData false (s.data.tree s.placement.lower) (s.data.couple s.exceptional)
      (s.data.tree_wf s.placement.lower) (s.data.couple_wf s.exceptional) := by
    unfold LFSource.finalData
    have := revSource_midData h hel htc hcc
    have h2 : (revSource h hel htc hcc).midData false (s.data.couple s.exceptional)
        (s.data.couple_wf s.exceptional) = s.midData false (s.data.couple s.exceptional)
        (s.data.couple_wf s.exceptional) := this.trans s.midData_identity.symm
    rw [h2]
    rfl
  exact hm.trans s.finalData_identity

theorem data_tree_other (h : LFConstruction s false) (b : GBranch s.skeleton.tree)
    (hb : b ≠ s.placement.lower) : h.data.tree b = s.data.tree b :=
  (Function.update_of_ne hb _ _).trans (s.base_tree_other false b hb)

theorem data_couple_other (h : LFConstruction s false) (q : SourcePair s.skeleton)
    (hq : q ≠ s.exceptional) : h.data.couple q = s.data.couple q := by
  have e : h.data.couple (s.pairs false q) = s.data.couple q :=
    (Function.update_of_ne (fun he => hq ((s.pairs false).injective he)) _ _).trans
      (s.base_couple_other false q hq)
  rwa [LFSource.pairs_false] at e

/-- **Reverse construction (choice `false`).** From the output of an LF construction one returns to the
source layered garden by an LF construction at the output. -/
theorem exists_reverse_construction :
    ∃ h' : LFConstruction (revSource h hel htc hcc) false, h'.output = LG ∧ h'.data = s.data := by
  classical
  let s' := revSource h hel htc hcc
  let X := s.data.tree s.placement.lower
  let Q := s.data.couple s.exceptional
  let hX := s.data.tree_wf s.placement.lower
  let hQ := s.data.couple_wf s.exceptional
  have hmid := revSource_midData h hel htc hcc
  have hfin := revSource_finalData h hel htc hcc
  have hbase := revSource_base h hel htc hcc
  have hbd := revSource_baseData h hel htc hcc
  have hmD : (s'.midData false Q hQ).Decodes (s'.chosen_plain false) s.identityMid.garden := by
    rw [hmid]
    exact eraseTree_collapse_decodes s.data s.plain s.decodes s.placement.lower
  have heD : (s'.finalData false X Q hX hQ).Decodes (s'.chosen_plain false) LG.garden := by
    rw [hfin]
    exact s.decodes
  let midLayer := decodedLayer (s'.midData false Q hQ) (s'.chosen_plain false) s.identityMid hmD
  let outLayer := decodedLayer (s'.finalData false X Q hX hQ) (s'.chosen_plain false) LG heD
  have hmL := decodedLayer_isLayering (s'.midData false Q hQ) (s'.chosen_plain false) s.identityMid hmD
  have heL := decodedLayer_isLayering (s'.finalData false X Q hX hQ) (s'.chosen_plain false) LG heD
  have hmidL : layeredReconstruction (s'.midData false Q hQ) (s'.chosen_plain false) midLayer hmL = s.identityMid :=
    decodedLayered_eq _ _ _ hmD
  have houtL : layeredReconstruction (s'.finalData false X Q hX hQ) (s'.chosen_plain false) outLayer heL = LG :=
    decodedLayered_eq _ _ _ heD
  obtain ⟨t, ht⟩ := s.identity_tree_insertion
  have hcoup := s.identity_couple_insertion
  refine ⟨{
    newTree := X
    newCouple := Q
    tree_wf := hX
    couple_wf := hQ
    midLayer := midLayer
    mid_isLayering := hmL
    outLayer := outLayer
    out_isLayering := heL
    tail := t
    coupleInsertion := ?_
    treeInsertion := ?_
    coreLayers := ?_
    ordinaryTreeLayers := ?_
    ordinaryCoupleLayers := ?_
    combinedOrder := ?_
    combinedTopCount := ?_ }, houtL, hfin⟩
  · rw [hmidL, hbase, hbd]
    exact hcoup
  · rw [hmidL, houtL, hmid]
    rw [s.midData_identity] at ht
    exact ht
  · intro b
    rw [houtL, hfin]
    exact (h.coreLayers b).symm
  · intro b hb q hq
    rw [houtL, hfin]
    have htb : h.data.tree b = s.data.tree b := data_tree_other h b hb
    change q ∈ ((h.data.tree b).plug _ _).nodes at hq
    rw [htb] at hq
    exact (h.ordinaryTreeLayers b hb q hq).symm
  · intro q hq i r hr
    rw [houtL, hfin]
    have htq : h.data.couple q = s.data.couple q := data_couple_other h q hq
    change r ∈ ((decodedCouple (h.data.couple q)).tree i).nodes at hr
    rw [htq] at hr
    have key := h.ordinaryCoupleLayers q hq i r hr
    rw [LFSource.pairs_false s q] at key
    rw [LFSource.pairs_false (revSource h hel htc hcc) q]
    exact key.symm
  · have e1 : (revSource h hel htc hcc).data.tree (revSource h hel htc hcc).placement.lower = h.newTree :=
      Function.update_self _ _ _
    have e2 : (revSource h hel htc hcc).data.couple (revSource h hel htc hcc).exceptional = h.newCouple := by
      have := data_couple_exc h
      rwa [LFSource.pairs_false] at this
    rw [e1, e2]
    exact h.combinedOrder.symm
  · rw [houtL, hfin]
    have key := h.combinedTopCount
    have hb' : s.branches false s.placement.lower = s.placement.lower := rfl
    have hp' : s.pairs false s.exceptional = s.exceptional := LFSource.pairs_false s s.exceptional
    rw [hb', hp'] at key
    have k2 : (revSource h hel htc hcc).branches false (revSource h hel htc hcc).placement.lower =
        s.placement.lower := rfl
    have k3 : (revSource h hel htc hcc).pairs false (revSource h hel htc hcc).exceptional = s.exceptional :=
      LFSource.pairs_false _ _
    rw [k2, k3]
    exact key.symm

end WaveTurbulence.Stage1

namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {ι : Type*}

theorem familyReconstruction_ext {A B : FamilyReconstruction w ι} (hs : A.skeleton = B.skeleton)
    (hf : HEq A.family B.family) (hd : HEq A.data B.data) (hl : A.layered = B.layered) : A = B := by
  obtain ⟨S, F, pl, D, L, dec⟩ := A
  obtain ⟨S', F', pl', D', L', dec'⟩ := B
  change S = S' at hs
  subst hs
  change HEq F F' at hf
  change HEq D D' at hd
  change L = L' at hl
  subst hl
  have hf' := eq_of_heq hf
  have hd' := eq_of_heq hd
  subst hf'
  subst hd'
  rfl

/-- **Reverse of an LF operation with skeleton choice `false`** (GAP.congEquiv (b)): at the output
there is an LF operation returning exactly the original state. -/
theorem exists_reverse_op_false (A : FamilyReconstruction w ι) (i : ι)
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
    (con : LFConstruction (A.source i c el tc cc) false) :
    ∃ op' : FamilyOperation (p := p) (kind := kind)
        (FamilyOperation.output (⟨c, el, tc, cc, false, con⟩ : FamilyOperation (p := p) (kind := kind) A i)) i,
      op'.output = A := by
  obtain ⟨h', hh', hd'⟩ := exists_reverse_construction (s := A.source i c el tc cc) con
    (eligible_output con) (treeCoherent_output con) (coupleCoherent_output con)
  refine ⟨⟨con.canonical, eligible_output con, treeCoherent_output con, coupleCoherent_output con, false, h'⟩, ?_⟩
  apply familyReconstruction_ext
  · rfl
  · exact HEq.rfl
  · exact heq_of_eq hd'
  · exact hh'

end WaveTurbulence.Stage1
