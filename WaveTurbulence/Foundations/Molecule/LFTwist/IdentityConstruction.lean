/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.IdentityStages

/-! # The unchanged source object is realized by an actual LF construction -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links RegRed
namespace LFSource
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG)

/-- False skeleton choice and the old coherent exceptional attachments realize
the identity, including all literal source layer and combined-count clauses. -/
theorem identity_construction : ∃ h : LFConstruction s false, h.output = LG := by
  let X := s.data.tree s.placement.lower
  let Q := s.data.couple s.exceptional
  let hX := s.data.tree_wf s.placement.lower
  let hQ := s.data.couple_wf s.exceptional
  let M := s.midData false Q hQ
  let E := s.finalData false X Q hX hQ
  have hm : M.Decodes (s.chosen_plain false) s.identityMid.garden := s.identityMid_decodes
  have he : E.Decodes (s.chosen_plain false) LG.garden := s.identity_output_decodes
  let midLayer := decodedLayer M (s.chosen_plain false) s.identityMid hm
  let outLayer := decodedLayer E (s.chosen_plain false) LG he
  have hmL := decodedLayer_isLayering M (s.chosen_plain false) s.identityMid hm
  have heL := decodedLayer_isLayering E (s.chosen_plain false) LG he
  have hmid : layeredReconstruction M (s.chosen_plain false) midLayer hmL = s.identityMid :=
    decodedLayered_eq M (s.chosen_plain false) s.identityMid hm
  have hout : layeredReconstruction E (s.chosen_plain false) outLayer heL = LG :=
    decodedLayered_eq E (s.chosen_plain false) LG he
  obtain ⟨t,ht⟩ := s.identity_tree_insertion
  have hcouple := s.identity_couple_insertion
  let h : LFConstruction s false := {
    newTree := X
    newCouple := Q
    tree_wf := hX
    couple_wf := hQ
    midLayer := midLayer
    mid_isLayering := hmL
    outLayer := outLayer
    out_isLayering := heL
    tail := t
    coupleInsertion := by rw [hmid]; exact hcouple
    treeInsertion := by rw [hmid,hout]; exact ht
    coreLayers := by
      intro b
      rw [hout,s.finalData_identity]
      rfl
    ordinaryTreeLayers := by
      intro b hb q hq
      rw [hout,s.finalData_identity]
      rfl
    ordinaryCoupleLayers := by
      intro q hq i r hr
      rw [hout,s.finalData_identity,s.pairs_false]
      rfl
    combinedOrder := rfl
    combinedTopCount := by
      rw [hout,s.finalData_identity,s.pairs_false]
      rfl }
  exact ⟨h,hout⟩

end LFSource
end WaveTurbulence.LFTwist
