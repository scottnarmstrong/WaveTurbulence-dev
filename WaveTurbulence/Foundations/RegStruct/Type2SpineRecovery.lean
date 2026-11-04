/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ExternalSpineStopping

/-! # Recovering both maximal chain spines from a type-2 carrier -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Both outer chains follow the unique-L-child algorithm in the actual decoded carrier. -/
theorem type2_externalSegments (p n : RegChain) (q : RegCpl) :
    ExternalSegment (decodedCouple (.type2 p n q)) (0,[]) p.lonePath ∧
      ExternalSegment (decodedCouple (.type2 p n q)) (1,[]) n.lonePath := by
  constructor
  · apply chain_externalSegment p (.type2 p n q) _ (decodedCouple_decodes _) (0,[]) 1 q.trees.1
    · change Comb.subtree (p.plug 1 q.trees.1) [] = _
      simp [Comb.subtree]
    · intro z hz
      exact List.mem_append_left _ (List.mem_append_left _ hz)
    · exact (type2_terminal_external p n q).1
  · apply chain_externalSegment n (.type2 p n q) _ (decodedCouple_decodes _) (1,[]) (-1) q.trees.2
    · change Comb.subtree (n.plug (-1) q.trees.2) [] = _
      simp [Comb.subtree]
    · intro z hz
      exact List.mem_append_left _ (List.mem_append_right _ hz)
    · exact (type2_terminal_external p n q).2

/-- The terminal restriction of well-formed data makes both spines source-maximal. -/
theorem type2_maximalSpines (p n : RegChain) (q : RegCpl) (hq : q.isType2 = false) :
    MaximalExternalSpine (decodedCouple (.type2 p n q)) (0,[]) p.lonePath ∧
      MaximalExternalSpine (decodedCouple (.type2 p n q)) (1,[]) n.lonePath := by
  have hseg := type2_externalSegments p n q
  have hstop : ExternalStop (decodedCouple (.type2 p n q)) (0,p.lonePath) ∧
      ExternalStop (decodedCouple (.type2 p n q)) (1,n.lonePath) := by
    apply framed_terminal_stops (.type2 p n q) q _ (decodedCouple_decodes _)
    · exact plug_subtree_lonePath p 1 q.trees.1
    · exact plug_subtree_lonePath n (-1) q.trees.2
    · intro z hz
      exact List.mem_append_right _ hz
    · exact (by decide : (1 : Fin 2) ≠ 0)
    · exact hq
  exact ⟨⟨hseg.1,hstop.1⟩,⟨hseg.2,hstop.2⟩⟩

/-- Equal carriers with the terminal stopping restriction have identical two literal spines. -/
theorem type2_lonePaths_unique (p n p' n' : RegChain) (q q' : RegCpl)
    (hq : q.isType2 = false) (hq' : q'.isType2 = false)
    (he : decodedCouple (.type2 p n q) = decodedCouple (.type2 p' n' q')) :
    p.lonePath = p'.lonePath ∧ n.lonePath = n'.lonePath := by
  have h := type2_maximalSpines p n q hq
  have h' := type2_maximalSpines p' n' q' hq'
  rw [he] at h
  exact ⟨maximalExternalSpine_unique _ _ _ _ h.1 h'.1,
    maximalExternalSpine_unique _ _ _ _ h.2 h'.2⟩

end WaveTurbulence.Reg
