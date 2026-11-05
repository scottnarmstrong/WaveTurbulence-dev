/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Canon.Decomp
/-! Closed leaf pairs regarded as two-root subforests. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem leavesBelowSet_leaf_image {w : ℕ} (LG : LayeredGarden w) (S : Finset (GLeaf LG.garden.tree)) :
    LG.leavesBelowSet (S.image (fun ℓ => ℓ.toNode)) = S := by
  classical
  ext ℓ
  constructor
  · intro h
    obtain ⟨u, hu, hd⟩ := Canon.Rel.mem_leavesBelowSet.mp h
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hu
    exact GLeaf.eq_of_isDesc hd ▸ hl
  · intro h
    exact Canon.Rel.mem_leavesBelowSet.mpr
      ⟨ℓ.toNode, Finset.mem_image_of_mem _ h, GNode.isDesc_refl _⟩

theorem completelyPaired_leaf_pair {w : ℕ} (G : Garden w) (hG : G.IsPlain) (ℓ : GLeaf G.tree) :
    G.CompletelyPaired {ℓ, G.pair ℓ} := by
  classical
  intro x hx
  refine ⟨fun he => ((G.pair_eq_iff x).mp he) (hG x), ?_⟩
  rcases (show x = ℓ ∨ x = G.pair ℓ from by simpa only [mem_insert, mem_singleton] using hx) with rfl | rfl
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
  · exact Finset.mem_insert.mpr (Or.inl (G.pair_pair ℓ))

theorem leavesBelowSet_leaf_pair {w : ℕ} (LG : LayeredGarden w) (ℓ : GLeaf LG.garden.tree) :
    LG.leavesBelowSet {ℓ.toNode, (LG.garden.pair ℓ).toNode} = {ℓ, LG.garden.pair ℓ} := by
  have he := leavesBelowSet_leaf_image LG {ℓ, LG.garden.pair ℓ}
  simpa only [Finset.image_insert, Finset.image_singleton] using he

end WaveTurbulence.Induct
