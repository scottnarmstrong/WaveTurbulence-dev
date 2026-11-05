/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.CoupleDom

/-!
# Pulling chain-layer statements back along maps that preserve layers on the chain region only

For an embedded regular tree the decoded carrier has a leaf at the lone position, while the ambient garden carries
the inserted subtree there; their layers agree on the chain region, not below the lone position. The statements
`ChainPairLayers` and `SpineMono` only see layers at chain nodes:

* `chainPairLayers_map_on`, `spineMono_map_on`: the pull-backs, assuming agreement on `chainNodesSet` only.
-/

@[expose] public section

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

variable {w v : ℕ}

theorem mem_chainNodesSet_inner {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain} {ζ : ℤˣ}
    {a z : Fin v × Path} (hz : z ∈ chainNodesSet inner (slotSign ζ m.c) (addrExt a [m.c])) :
    z ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ a := by
  unfold chainNodesSet pairEndpoints at hz ⊢
  simp only [RegChain.linksAt, RegChain.pairsAt, List.map_cons, List.map_append, List.toFinset_cons,
    List.toFinset_append, Finset.mem_union, Finset.mem_insert] at hz ⊢
  tauto

theorem mem_chainNodesSet_rest {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain} {ζ : ℤˣ}
    {a z : Fin v × Path}
    (hz : z ∈ chainNodesSet rest (slotSign (slotSign ζ m.c) m.lone) (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))) :
    z ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ a := by
  unfold chainNodesSet pairEndpoints at hz ⊢
  simp only [RegChain.linksAt, RegChain.pairsAt, List.map_cons, List.map_append, List.toFinset_cons,
    List.toFinset_append, Finset.mem_union, Finset.mem_insert] at hz ⊢
  tauto

theorem mem_chainNodesSet_innerLone (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) (ζ : ℤˣ)
    (a : Fin v × Path) : addrExt a ([m.c] ++ inner.lonePath) ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ a := by
  unfold chainNodesSet pairEndpoints
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  rw [List.mem_toFinset]
  simp [RegChain.linksAt]

theorem mem_chainNodesSet_red {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain} {ζ : ℤˣ}
    {a z : Fin v × Path} (hz : z ∈ orientedNodes (slotSign ζ m.red.1 = 1) Qr (addrExt a [m.red.1])
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))) :
    z ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ a := by
  unfold orientedNodes cplNodes at hz
  unfold chainNodesSet
  unfold pairEndpoints at hz ⊢
  split_ifs at hz with hc <;>
  · simp only [RegChain.linksAt, RegChain.pairsAt, hc, ite_true, ite_false, List.map_cons, List.map_append,
      List.toFinset_cons, List.toFinset_append, Finset.mem_union, Finset.mem_insert] at hz ⊢
    tauto

theorem mem_chainNodesSet_green {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain} {ζ : ℤˣ}
    {a z : Fin v × Path} (hz : z ∈ orientedNodes (slotSign ζ m.green.1 = 1) Qg (addrExt a [m.green.1])
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))) :
    z ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ a := by
  unfold orientedNodes cplNodes at hz
  unfold chainNodesSet
  unfold pairEndpoints at hz ⊢
  split_ifs at hz with hc <;>
  · simp only [RegChain.linksAt, RegChain.pairsAt, hc, ite_true, ite_false, List.map_cons, List.map_append,
      List.toFinset_cons, List.toFinset_append, Finset.mem_union, Finset.mem_insert] at hz ⊢
    tauto

section MapOn

variable (LG : LayeredGarden w) (LG' : LayeredGarden v) (f : (Fin v × Path) → (Fin w × Path))
  (hf : ∀ a p, f (addrExt a p) = addrExt (f a) p)
include hf

theorem chainPairLayers_map_on :
    ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin v × Path),
      (∀ z ∈ chainNodesSet X ζ a, layerAt LG' z = layerAt LG (f z)) →
      ChainPairLayers LG X ζ (f a) → ChainPairLayers LG' X ζ a
  | .nil, _, _, _, _ => trivial
  | .pair m Qr Qg inner rest, ζ, a, hlay, ⟨h1, h2, h3, h4, h5⟩ => by
    have ha := hlay a (root_mem_chainNodesSet _ _ _ _ _ _ _)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hlay _ (mem_chainNodesSet_innerLone _ _ _ _ _ _ _), ha, hf]
      exact h1
    · intro z hz
      rw [hlay z (mem_chainNodesSet_red hz), ha]
      apply h2
      rw [← hf, ← hf, orientedNodes_map _ Qr f hf]
      exact Finset.mem_image_of_mem f hz
    · intro z hz
      rw [hlay z (mem_chainNodesSet_green hz), ha]
      apply h3
      rw [← hf, ← hf, orientedNodes_map _ Qg f hf]
      exact Finset.mem_image_of_mem f hz
    · refine chainPairLayers_map_on inner _ _ (fun z hz => hlay z (mem_chainNodesSet_inner hz)) ?_
      rw [hf]
      exact h4
    · refine chainPairLayers_map_on rest _ _ (fun z hz => hlay z (mem_chainNodesSet_rest hz)) ?_
      rw [hf]
      exact h5

theorem spineMono_map_on :
    ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin v × Path),
      (∀ z ∈ chainNodesSet X ζ a, layerAt LG' z = layerAt LG (f z)) →
      SpineMono LG (f a) X → SpineMono LG' a X
  | .nil, _, _, _, _ => trivial
  | .pair m Qr Qg inner rest, ζ, a, hlay, ⟨h1, h2⟩ => by
    have hn : f (nextAddr a m inner) = nextAddr (f a) m inner := hf _ _
    refine ⟨fun m' Qr' Qg' inner' rest' hrest => ?_,
      spineMono_map_on rest (slotSign (slotSign ζ m.c) m.lone) _
        (fun z hz => hlay z (mem_chainNodesSet_rest hz)) (hn ▸ h2)⟩
    have hnr : nextAddr a m inner ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ a := by
      apply mem_chainNodesSet_rest
      rw [hrest]
      exact root_mem_chainNodesSet _ _ _ _ _ _ _
    rw [hlay _ hnr, hlay a (root_mem_chainNodesSet _ _ _ _ _ _ _), hn]
    exact h1 m' Qr' Qg' inner' rest' hrest

end MapOn

end WaveTurbulence.PL234
