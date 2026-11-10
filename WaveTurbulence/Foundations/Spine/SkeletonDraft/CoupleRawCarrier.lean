/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ForwardAMini
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ForwardBMini
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SourcePrimeExistence

/-! # Exact canonical finite-pair carrier for the pinned raw regular-couple histories -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- The source raw couple with its fixed (+,-) signature and canonical finite oriented matching. -/
def rawCplSet (R : RawCpl) : Raw 2 := ⟨![1,-1],R.tree,R.2.toFinset⟩

theorem rawOfGarden_eq_code_raw {Q : RegCpl} {G : Garden 2} (h : Q.Decodes G) :
    rawOfGarden G = rawCplSet Q.raw := by
  classical
  have hsig : G.sig = ![1,-1] := h.1.2
  apply Raw.ext
  · exact hsig
  · exact (decodes_forest h).trans (raw_tree_eq_coupleForest Q).symm
  · change sourcePairs G = Q.raw.2.toFinset
    ext p
    constructor
    · intro hp
      obtain ⟨ℓ,hℓ,rfl⟩ := Finset.mem_image.mp hp
      have hs := (Finset.mem_filter.mp hℓ).2
      have hm := h.2.2.2 ℓ
      rcases (mem_symmPairs_iff _ _).mp hm with hp | hp
      · exact List.mem_toFinset.mpr hp
      · have hn := (rawPair_signs Q _ hp).2
        change nodeSign ![1,-1] ℓ.1 = -1 at hn
        rw [hsig] at hs
        have he : (1 : ℤˣ) = -1 := hs.symm.trans hn
        exact (by decide : (1 : ℤˣ) ≠ -1) he |>.elim
    · intro hp
      have hmem := List.mem_toFinset.mp hp
      have hv : p.1.2 ∈ (G.tree p.1.1).leaves := by
        rw [decodes_forest h]
        exact (decodedCouple_pairs_valid Q p hmem).1
      let ℓ : GLeaf G.tree := ⟨p.1,hv⟩
      have hpair := pair_of_decodes h p ((mem_symmPairs_iff _ _).mpr (Or.inl hmem)) hv
      have hpos : nodeSign G.sig ℓ.1 = 1 := by
        rw [hsig]
        exact (rawPair_signs Q p hmem).1
      apply Finset.mem_image.mpr
      exact ⟨ℓ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpos⟩,Prod.ext rfl hpair⟩

/-- Exact representation transfers the finite raw carrier, including its complete oriented pair set. -/
theorem RawRep.rawCplSet_eq {Q : RegCpl} {R : RawCpl} (h : RawRep Q R) :
    rawCplSet R = rawCplSet Q.raw := by
  apply Raw.ext
  · rfl
  · exact h.forest.trans (raw_tree_eq_coupleForest Q).symm
  · change R.2.toFinset = Q.raw.2.toFinset
    ext p
    simp only [List.mem_toFinset]
    exact h.2.mem_iff

/-- Every source-regular raw couple has the actual perfect-matching typing invariant. -/
theorem rawCplSet_valid_of_regular {R : RawCpl} (hR : RawRegular R) : (rawCplSet R).Valid := by
  obtain ⟨Q,hQ,hrep⟩ := RawRegular.exists_wf_rawRep hR
  have he := rawOfGarden_eq_code_raw (decodedCouple_decodes Q)
  rw [RawRep.rawCplSet_eq hrep,← he]
  exact rawOfGarden_valid _ (decodedCouple_decodes Q).1.1

end WaveTurbulence.Reg.Skeleton
