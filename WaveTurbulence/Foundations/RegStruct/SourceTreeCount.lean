/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.TreeCarrierUniqueness

/-! # Exponential counting of actual regular paired trees at fixed root sign -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Removing the auxiliary trivial tree preserves the total branching order. -/
theorem matchingTree_order (Q : RegCpl) (G : Garden 1) (hM : G.MatchesTreeCouple Q.raw) :
    G.order = Q.size := by
  have hord := code_trees_order Q
  have hg : G.order = (G.tree 0).order := by simp [Garden.order]
  rw [hg]
  by_cases hζ : G.sig 0 = 1
  · simp only [Garden.MatchesTreeCouple,hζ,ite_true] at hM
    have h0 := hM.1
    have h1 := hM.2.1
    change Q.trees.1 = G.tree 0 at h0
    change Q.trees.2 = .leaf at h1
    rw [h0,h1,TTree.order,Nat.add_zero] at hord
    exact hord
  · simp only [Garden.MatchesTreeCouple,hζ,ite_false] at hM
    have h0 := hM.1
    have h1 := hM.2.1
    change Q.trees.2 = G.tree 0 at h0
    change Q.trees.1 = .leaf at h1
    rw [h0,h1,TTree.order,Nat.zero_add] at hord
    exact hord

/-- Source-regular trees have well-formed couple data with the correct matching relation. -/
theorem isRegularTree_exists_wf_matching (G : Garden 1) (hG : IsRegularTree G) :
    ∃ Q : RegCpl, Q.wf = true ∧ Q.size = G.order ∧ G.MatchesTreeCouple Q.raw := by
  obtain ⟨R,hR,hM⟩ := hG.2
  obtain ⟨Q,hw,hrep⟩ := RawRegular.exists_wf_rawRep hR
  have hm := (hrep.matchesTreeCouple_iff G).mp hM
  exact ⟨Q,hw,(matchingTree_order Q G hm).symm,hm⟩

end WaveTurbulence.Reg
