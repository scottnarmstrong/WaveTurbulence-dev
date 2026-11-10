/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.PieceCouple
public import WaveTurbulence.Foundations.RegStruct.PairNaturality

/-!
# Chain structure under appending and address transport

For the induction over the same-layer blocks of the `+` chain (TARGET prooflayer1-1):

* `couple_linksAt_map`, `chain_linksAt_map`: link decoding commutes with address maps respecting extension
  (the companion of the spine's `couple_pairsAt_map`);
* `cplNodes_map`, `orientedNodes_map`, `chainNodesSet_map`;
* `chainPairLayers_map`, `spineMono_map`, `takeLayer_map`, `dropLayer_map`, `topAll_map`: layer statements
  pulled back along a layer-preserving address map;
* `chainEmb_append_left`, `chainEmb_append_right`, `chainPairLayers_append_right`, `spineMono_append_right`.
-/

@[expose] public section
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

variable {w v : ℕ}

mutual
theorem couple_linksAt_map (Q : RegCpl) (f : (Fin w × Path) → (Fin v × Path))
    (hf : ∀ a p, f (addrExt a p) = addrExt (f a) p) (a b : Fin w × Path) :
    Q.linksAt (f a) (f b) = (Q.linksAt a b).map (fun p => (f p.1, f p.2)) := by
  cases Q with
  | triv => rfl
  | type1 c r g d =>
    simp only [RegCpl.linksAt, List.map_cons, List.map_append, ← hf,
      couple_linksAt_map r f hf, couple_linksAt_map g f hf, couple_linksAt_map d f hf]
  | type2 p m q =>
    simp only [RegCpl.linksAt, List.map_append, ← hf,
      chain_linksAt_map p f hf, chain_linksAt_map m f hf, couple_linksAt_map q f hf]
termination_by structural Q

theorem chain_linksAt_map (X : RegChain) (f : (Fin w × Path) → (Fin v × Path))
    (hf : ∀ a p, f (addrExt a p) = addrExt (f a) p) (ζ : ℤˣ) (a : Fin w × Path) :
    X.linksAt ζ (f a) = (X.linksAt ζ a).map (fun p => (f p.1, f p.2)) := by
  cases X with
  | nil => rfl
  | pair m r g i s =>
    by_cases hr : slotSign ζ m.red.1 = 1 <;>
      by_cases hg : slotSign ζ m.green.1 = 1 <;>
      simp only [RegChain.linksAt, hr, hg, ite_true, ite_false, List.map_cons, List.map_append, ← hf,
        couple_linksAt_map r f hf, couple_linksAt_map g f hf,
        chain_linksAt_map i f hf, chain_linksAt_map s f hf]
termination_by structural X
end

theorem list_toFinset_map {α β : Type*} [DecidableEq α] [DecidableEq β] (l : List α) (f : α → β) :
    (l.map f).toFinset = l.toFinset.image f := by
  ext x
  simp

theorem pairEndpoints_map {α β : Type*} [DecidableEq α] [DecidableEq β] (P : List (α × α)) (f : α → β) :
    pairEndpoints (P.map fun p => (f p.1, f p.2)) = (pairEndpoints P).image f := by
  unfold pairEndpoints
  rw [Finset.image_union, ← list_toFinset_map, ← list_toFinset_map, List.map_map, List.map_map,
    List.map_map, List.map_map]
  rfl

theorem cplNodes_map (Q : RegCpl) (f : (Fin w × Path) → (Fin v × Path))
    (hf : ∀ a p, f (addrExt a p) = addrExt (f a) p) (a b : Fin w × Path) :
    cplNodes Q (f a) (f b) = (cplNodes Q a b).image f := by
  unfold cplNodes
  rw [couple_linksAt_map Q f hf, couple_pairsAt_map Q f hf, pairEndpoints_map, pairEndpoints_map,
    Finset.image_union]

theorem chainNodesSet_map (X : RegChain) (f : (Fin w × Path) → (Fin v × Path))
    (hf : ∀ a p, f (addrExt a p) = addrExt (f a) p) (ζ : ℤˣ) (a : Fin w × Path) :
    chainNodesSet X ζ (f a) = (chainNodesSet X ζ a).image f := by
  unfold chainNodesSet
  rw [chain_linksAt_map X f hf, chain_pairsAt_map X f hf, pairEndpoints_map, pairEndpoints_map,
    Finset.image_union]

theorem orientedNodes_map (P : Prop) [Decidable P] (Q : RegCpl) (f : (Fin w × Path) → (Fin v × Path))
    (hf : ∀ a p, f (addrExt a p) = addrExt (f a) p) (x y : Fin w × Path) :
    orientedNodes P Q (f x) (f y) = (orientedNodes P Q x y).image f := by
  unfold orientedNodes
  split_ifs <;> exact cplNodes_map Q f hf _ _

/-! ### Pulling layer statements back along address maps -/

section Map

variable (LG : LayeredGarden w) (LG' : LayeredGarden v) (f : (Fin v × Path) → (Fin w × Path))
  (hf : ∀ a p, f (addrExt a p) = addrExt (f a) p) (hlay : ∀ z, layerAt LG' z = layerAt LG (f z))
include hf hlay

theorem chainPairLayers_map :
    ∀ (X : RegChain) (ζ : ℤˣ) (a : Fin v × Path), ChainPairLayers LG X ζ (f a) → ChainPairLayers LG' X ζ a
  | .nil, _, _, _ => trivial
  | .pair m Qr Qg inner rest, ζ, a, ⟨h1, h2, h3, h4, h5⟩ => by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hlay, hlay, hf]
      exact h1
    · intro z hz
      rw [hlay, hlay]
      apply h2
      rw [← hf, ← hf, orientedNodes_map _ Qr f hf]
      exact Finset.mem_image_of_mem f hz
    · intro z hz
      rw [hlay, hlay]
      apply h3
      rw [← hf, ← hf, orientedNodes_map _ Qg f hf]
      exact Finset.mem_image_of_mem f hz
    · refine chainPairLayers_map inner _ _ ?_
      rw [hf]
      exact h4
    · refine chainPairLayers_map rest _ _ ?_
      rw [hf]
      exact h5

theorem spineMono_map : ∀ (X : RegChain) (a : Fin v × Path), SpineMono LG (f a) X → SpineMono LG' a X
  | .nil, _, _ => trivial
  | .pair m Qr Qg inner rest, a, ⟨h1, h2⟩ => by
    have hn : f (nextAddr a m inner) = nextAddr (f a) m inner := hf _ _
    refine ⟨fun m' Qr' Qg' inner' rest' hrest => ?_, spineMono_map rest _ (hn ▸ h2)⟩
    rw [hlay, hlay, hn]
    exact h1 m' Qr' Qg' inner' rest' hrest

end Map

/-! ### Appending -/

theorem chainEmb_append_left {G : Garden w} {B D : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree}
    (hC : ChainEmb G (appendChain B D) ζ a h) : ChainEmb G B ζ a (D.plug ζ h) :=
  ⟨hC.node, by rw [hC.tree, appendChain_plug], fun p hp ℓ hℓ =>
    hC.pairs p (by rw [appendChain_pairsAt]; exact List.mem_append_left _ hp) ℓ hℓ⟩

theorem chainEmb_append_right {G : Garden w} {B D : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree}
    (hC : ChainEmb G (appendChain B D) ζ a h) : ChainEmb G D ζ (addrExt a B.lonePath) h := by
  have ht : (G.tree a.1).subtreeAt a.2 = B.plug ζ (D.plug ζ h) := by rw [hC.tree, appendChain_plug]
  refine ⟨?_, ?_, fun p hp ℓ hℓ =>
    hC.pairs p (by rw [appendChain_pairsAt]; exact List.mem_append_right _ hp) ℓ hℓ⟩
  · refine ((node_iff_of_subtree hC.node ht B.lonePath).1).2 ?_
    exact lonePath_mem_plug B ζ _
  · change (G.tree a.1).subtreeAt (a.2 ++ B.lonePath) = _
    rw [Links.subtreeAt_append, ht, Links.plug_subtreeAt_lonePath]

theorem chainPairLayers_append_right (LG : LayeredGarden w) :
    ∀ (B D : RegChain) (ζ : ℤˣ) (a : Fin w × Path), ChainPairLayers LG (appendChain B D) ζ a →
      ChainPairLayers LG D ζ (addrExt a B.lonePath)
  | .nil, D, ζ, a, h => by simpa [appendChain, RegChain.lonePath, addrExt] using h
  | .pair _ _ _ _ rest, D, _, _, ⟨_, _, _, _, h5⟩ => by
    have ih := chainPairLayers_append_right LG rest D _ _ h5
    rw [slotSign_lone, addrExt_append] at ih
    simpa only [RegChain.lonePath, List.append_assoc] using ih

theorem chainPairLayers_append_left (LG : LayeredGarden w) :
    ∀ (B D : RegChain) (ζ : ℤˣ) (a : Fin w × Path), ChainPairLayers LG (appendChain B D) ζ a →
      ChainPairLayers LG B ζ a
  | .nil, _, _, _, _ => trivial
  | .pair _ _ _ _ rest, D, _, _, ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨h1, h2, h3, h4, chainPairLayers_append_left LG rest D _ _ h5⟩

theorem spineMono_append_right (LG : LayeredGarden w) :
    ∀ (B D : RegChain) (a : Fin w × Path), SpineMono LG a (appendChain B D) →
      SpineMono LG (addrExt a B.lonePath) D
  | .nil, D, a, h => by simpa [appendChain, RegChain.lonePath, addrExt] using h
  | .pair _ _ _ _ rest, D, _, ⟨_, h2⟩ => by
    have ih := spineMono_append_right LG rest D _ h2
    rw [nextAddr, addrExt_append] at ih
    simpa only [RegChain.lonePath, List.append_assoc] using ih

end WaveTurbulence.PL234
