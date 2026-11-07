/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Sound2

/-! # ZP-SURJ soundness: the native tree of a construction is a pattern datum -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.Stage1

variable {w : ℕ}

theorem chainNodesSet_node (X : RegChain) (ζ : ℤˣ) (a z : Fin w × Path) (hz : z ∈ chainNodesSet X ζ a) :
    ∃ r ∈ (X.plug ζ .leaf).nodes, z = addrExt a r := by
  unfold chainNodesSet at hz
  have h1 := chain_branchAddresses X ζ .leaf a
  have h2 := chain_leafAddresses X ζ .leaf a
  rcases Finset.mem_union.mp hz with hz | hz
  · have : z ∈ branchAddresses (X.plug ζ .leaf) a := by rw [h1]; exact Finset.mem_union_left _ hz
    obtain ⟨q, hq, rfl⟩ := mem_image_addrExt this
    exact ⟨q, TTree.branching_subset_nodes _ hq, rfl⟩
  · have : z ∈ leafAddresses (X.plug ζ .leaf) a := by rw [h2]; exact Finset.mem_union_left _ hz
    obtain ⟨q, hq, rfl⟩ := mem_image_addrExt this
    exact ⟨q, TTree.leaves_subset_nodes _ hq, rfl⟩

theorem lone_mem_nodes (X : RegChain) (ζ : ℤˣ) : X.lonePath ∈ (X.plug ζ .leaf).nodes :=
  TTree.leaves_subset_nodes _ (chain_lone_mem_leaves X ζ)

/-- A tree pattern at an address of `H` is the pattern of the native tree, when the layers agree on the chain nodes. -/
theorem treePatternN_native {H : LayeredGarden w} {a : Fin w × Path} {X : RegChain} {ζ : ℤˣ}
    {LX : LayeredGarden 1} (pa : ℕ)
    (hlay : ∀ r ∈ (X.plug ζ .leaf).nodes, layerAt H (addrExt a r) = layerAt LX ((0 : Fin 1), r)) :
    TreePatternN H pa X ζ a ↔ TreePatternN LX pa X ζ ((0 : Fin 1), ([] : Path)) := by
  have hP : ∀ (x : Fin 1 × Path) (q : Path), Under (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) x →
      Under (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) (addrExt x q) := fun x q hx => under_trans hx (under_ext x q)
  have hρ : ∀ (x : Fin 1 × Path) (q : Path), Under (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) x →
      shiftTo (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) a (addrExt x q) =
        addrExt (shiftTo (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) a x) q := fun x q hx => shiftTo_addrExt a hx q
  let Rg : Fin 1 × Path → Prop := fun z =>
    z ∈ chainNodesSet X ζ ((0 : Fin 1), ([] : Path)) ∨ z = addrExt ((0 : Fin 1), ([] : Path)) X.lonePath
  have hlay' : ∀ z, Under (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) z → Rg z →
      layerAt H (shiftTo (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) a z) = layerAt LX z := by
    intro z hz hR
    obtain ⟨r, rfl⟩ := under_of_addrExt hz
    rw [shiftTo_addrExt_self]
    have hlone' : addrExt ((0 : Fin 1), ([] : Path)) r = ((0 : Fin 1), r) := by simp [addrExt]
    rw [hlone']
    have hr : r ∈ (X.plug ζ .leaf).nodes := by
      rcases hR with hR | hR
      · obtain ⟨r', hr', e⟩ := chainNodesSet_node X ζ _ _ hR
        have : addrExt ((0 : Fin 1), ([] : Path)) r = addrExt ((0 : Fin 1), ([] : Path)) r' := by rw [← e]
        have e2 : r = r' := by simpa [addrExt] using this
        rw [e2]; exact hr'
      · have e2 : r = X.lonePath := by simpa [addrExt] using hR
        rw [e2]; exact lone_mem_nodes X ζ
    exact hlay r hr
  have hmap := treePatternN_mapR (fun x : Fin 1 × Path => Under (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) x)
    (shiftTo (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) a) Rg hP hρ hlay'
    (H1 := LX) (H2 := H) pa X ζ ((0 : Fin 1), ([] : Path)) (under_refl _)
    (fun z hz => Or.inl hz) (Or.inr rfl)
  rw [shiftTo_self] at hmap
  exact hmap

end WaveTurbulence.ZpSurj
