/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.RootImageLeafSets
public import WaveTurbulence.Foundations.XChain.PairedEmbedding
/-! Irreducibility of a garden transfers to its exact embedded root set. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem completelyPaired_univ_of_plain {w : ℕ} (G : Garden w) (h : G.IsPlain) :
    G.CompletelyPaired univ := by
  intro ℓ _
  exact ⟨fun he => ((G.pair_eq_iff ℓ).mp he) (h ℓ), mem_univ _⟩

theorem irreducibleAt_of_root_image {v w : ℕ} (LG : LayeredGarden w) (H : Garden v)
    (r : Fin v ↪ GNode LG.garden.tree) (l : GLeaf H.tree ↪ GLeaf LG.garden.tree)
    (hpair : ∀ ℓ, LG.garden.pair (l ℓ) = l (H.pair ℓ))
    (hleaves : ∀ K : Finset (Fin v), LG.leavesBelowSet (K.map r) = (H.leavesOf K).map l)
    (hirr : H.Irreducible) : LG.IrreducibleAt (univ.map r) := by
  classical
  intro A hA hAn hAu hcp
  have hsub := Finset.mem_powerset.mp hA
  let K := univ.filter (fun k => r k ∈ A)
  have he : K.map r = A := by
    ext u
    constructor
    · intro hu
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hu
      exact (Finset.mem_filter.mp hk).2
    · intro hu
      obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp (hsub hu)
      exact Finset.mem_map.mpr ⟨k, Finset.mem_filter.mpr ⟨mem_univ _, hu⟩, rfl⟩
  have hKn : K.Nonempty := by
    obtain ⟨u, hu⟩ := hAn
    obtain ⟨k, hk, _⟩ := Finset.mem_map.mp ((congrArg (fun S => u ∈ S) he).mpr hu)
    exact ⟨k, hk⟩
  have hKu : K ≠ univ := by
    intro hk
    exact hAu (he.symm.trans (congrArg (Finset.map r) hk))
  have hmap := (congrArg LG.leavesBelowSet he).symm.trans (hleaves K)
  have hp := (congrArg LG.garden.CompletelyPaired hmap).mp hcp
  exact hirr K hKn hKu ((completelyPaired_map_iff H LG.garden l hpair _).mp hp)

end WaveTurbulence.Induct
