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

/-- Actual source-regular trees with fixed sign and branching order. -/
abbrev SourceTrees (ζ : ℤˣ) (m : ℕ) :=
  {G : Garden 1 // IsRegularTree G ∧ G.sig 0 = ζ ∧ G.order = 2*m}

/-- Choose well-formed structure data for an actual regular tree. -/
noncomputable def sourceTreeCode (ζ : ℤˣ) (m : ℕ) (G : SourceTrees ζ m) :
    {Q : RegCpl // Q.wf = true ∧ Q.size = 2*m} := by
  classical
  let h := isRegularTree_exists_wf_matching G.1 G.2.1
  let Q := Classical.choose h
  have hQ := Classical.choose_spec h
  exact ⟨Q,hQ.1,hQ.2.1.trans G.2.2.2⟩

/-- The chosen code retains the source tree-to-couple matching relation. -/
theorem sourceTreeCode_matching (ζ : ℤˣ) (m : ℕ) (G : SourceTrees ζ m) :
    G.1.MatchesTreeCouple (sourceTreeCode ζ m G).1.raw :=
  (Classical.choose_spec (isRegularTree_exists_wf_matching G.1 G.2.1)).2.2

/-- Chosen data distinguish actual regular trees at a fixed sign. -/
theorem sourceTreeCode_injective (ζ : ℤˣ) (m : ℕ) : Function.Injective (sourceTreeCode ζ m) := by
  intro G H he
  apply Subtype.ext
  have hs : G.1.sig = H.1.sig := by
    funext j
    fin_cases j
    exact G.2.2.1.trans H.2.2.1.symm
  have hM := sourceTreeCode_matching ζ m H
  rw [← he] at hM
  exact tree_carrier_unique G.2.1.1 H.2.1.1 hs (sourceTreeCode_matching ζ m G) hM

/-- Finiteness of actual source-regular trees at a fixed sign and order. -/
theorem finite_sourceTrees (ζ : ℤˣ) (m : ℕ) : Finite (SourceTrees ζ m) := by
  let _ := finite_coupleCodes m
  exact Finite.of_injective (sourceTreeCode ζ m) (sourceTreeCode_injective ζ m)

/-- Number of actual source-regular trees with fixed root sign. -/
noncomputable def sourceTreeCount (ζ : ℤˣ) (m : ℕ) : ℕ := Nat.card (SourceTrees ζ m)

/-- TARGET Proposition 4.4: actual regular trees have an absolute exponential bound. -/
theorem sourceTreeCount_le_pow (ζ : ℤˣ) (m : ℕ) : sourceTreeCount ζ m ≤ (12^9)^m := by
  let _ := finite_coupleCodes m
  exact (Nat.card_le_card_of_injective (sourceTreeCode ζ m) (sourceTreeCode_injective ζ m)).trans
    (coupleCodeCount_le_pow m)

end WaveTurbulence.Reg
