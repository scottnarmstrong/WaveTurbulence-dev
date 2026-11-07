/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VineEst.LeafCorr2

/-! # Layers, signs, partners and tree indices along `OrdCorr` (LFTWIST-LEAFMAP, step 4) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LFTwist
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree Links
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
  (h : LFConstruction s ε)

theorem LFConstruction.OrdCorr.layer {x : GLeaf (s.data.forest s.plain)}
    {y : GLeaf (h.data.forest (s.chosen_plain ε))} (hc : h.OrdCorr x y) :
    layerAt LG x.1 = layerAt h.output y.1 := by
  rcases hc with ⟨q, hq, ℓ, ℓ', he, rfl, rfl⟩ | ⟨b, hb, ℓ, ℓ', he, rfl, rfl⟩
  · rw [coupleLeaf_addr, coupleLeaf_addr, ← he]
    exact h.ordinaryCoupleLayers q hq ℓ.1.1 ℓ.1.2 (TTree.leaves_subset_nodes _ ℓ.2)
  · rw [chainLeaf_addr, chainLeaf_addr, ← he]
    exact h.ordinaryTreeLayers b hb ℓ.1.1.2 (TTree.leaves_subset_nodes _ ℓ.1.2)

theorem LFConstruction.OrdCorr.sign {x : GLeaf (s.data.forest s.plain)}
    {y : GLeaf (h.data.forest (s.chosen_plain ε))} (hc : h.OrdCorr x y) :
    nodeSign s.skeleton.sig x.1 = nodeSign (s.chosen ε).sig y.1 := by
  rcases hc with ⟨q, hq, ℓ, ℓ', he, rfl, rfl⟩ | ⟨b, hb, ℓ, ℓ', he, rfl, rfl⟩
  · rw [coupleLeaf_sign, coupleLeaf_sign, ← he]
  · rw [chainLeaf_sign, chainLeaf_sign, ← he, s.ordinary_branch_sign ε b hb]

theorem LFConstruction.OrdCorr.index {x : GLeaf (s.data.forest s.plain)}
    {y : GLeaf (h.data.forest (s.chosen_plain ε))} (hc : h.OrdCorr x y) : x.1.1 = y.1.1 := by
  rcases hc with ⟨q, hq, ℓ, ℓ', he, rfl, rfl⟩ | ⟨b, hb, ℓ, ℓ', he, rfl, rfl⟩
  · rw [coupleLeaf_addr, coupleLeaf_addr, ← he]
    exact (h.ordinary_couple_root_index q hq ℓ.1.1).symm
  · rw [chainLeaf_addr, chainLeaf_addr, ← he]
    change (inflatedPosition s.skeleton s.data.tree b.toNode).1 = (inflatedPosition (s.chosen ε) h.data.tree (s.branches ε b).toNode).1
    rw [inflatedPosition_index, inflatedPosition_index]
    exact (s.branches_index ε b).symm


theorem LFConstruction.OrdCorr.pair {x : GLeaf (s.data.forest s.plain)}
    {y : GLeaf (h.data.forest (s.chosen_plain ε))} (hc : h.OrdCorr x y) :
    ∃ (x' : GLeaf (s.data.forest s.plain)) (y' : GLeaf (h.data.forest (s.chosen_plain ε))),
      h.OrdCorr x' y' ∧ (s.data.garden s.plain).pair x = x' ∧
        (h.data.garden (s.chosen_plain ε)).pair y = y' := by
  rcases hc with ⟨q, hq, ℓ, ℓ', he, rfl, rfl⟩ | ⟨b, hb, ℓ, ℓ', he, rfl, rfl⟩
  · have hD : decodedCouple (h.data.couple (s.pairs ε q)) = decodedCouple (s.data.couple q) :=
      congrArg decodedCouple (h.couple_other q hq)
    have hv := pair_val_congr hD.symm ℓ ℓ' he
    refine ⟨_, _, Or.inl ⟨q, hq, (decodedCouple (s.data.couple q)).pair ℓ,
      (decodedCouple (h.data.couple (s.pairs ε q))).pair ℓ', hv, rfl, rfl⟩, ?_, ?_⟩
    · exact coupleLeaf_pair s.data s.plain q ℓ
    · exact coupleLeaf_pair h.data (s.chosen_plain ε) (s.pairs ε q) ℓ'
  · obtain ⟨m, hm, hpm⟩ := chainLeaf_pair s.data s.plain b ℓ
    obtain ⟨m', hm', hpm'⟩ := chainLeaf_pair h.data (s.chosen_plain ε) (s.branches ε b) ℓ'
    have hT : decodedTree (h.data.tree (s.branches ε b)) (nodeSign (s.chosen ε).sig (s.branches ε b).1) =
        decodedTree (s.data.tree b) (nodeSign s.skeleton.sig b.1) := by
      rw [h.tree_other b hb, s.ordinary_branch_sign ε b hb]
    have hv := pair_val_congr hT.symm ℓ.1 ℓ'.1 he
    refine ⟨_, _, Or.inr ⟨b, hb, m, m', ?_, rfl, rfl⟩, hpm, hpm'⟩
    rw [hm, hm']
    exact hv

end WaveTurbulence.LFTwist
