/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Reloc4

/-! # ZP-SURJ: region-aware relocation of the tree pattern

The tree pattern of a chain only reads layers at chain nodes and at the lone position; relocating it between a
layered tree and a layered garden with a tail below the lone position only needs agreement there.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree WaveTurbulence.Reg WaveTurbulence.Links

variable {w w' : ℕ}

theorem chainNodes_inner_sub {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain} {ζ : ℤˣ}
    {a z : Fin w × Path} (h : z ∈ chainNodesSet inner (slotSign ζ m.c) (addrExt a [m.c])) :
    z ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ a := by
  unfold chainNodesSet at h ⊢
  rw [RegChain.linksAt, RegChain.pairsAt, pairEndpoints_cons, pairEndpoints_append, pairEndpoints_append,
    pairEndpoints_append, pairEndpoints_append, pairEndpoints_append, pairEndpoints_append]
  simp only [Finset.mem_union, Finset.mem_singleton] at h ⊢
  tauto

theorem chainNodes_rest_sub {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain} {ζ : ℤˣ}
    {a z : Fin w × Path}
    (h : z ∈ chainNodesSet rest (slotSign (slotSign ζ m.c) m.lone)
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))) :
    z ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ a := by
  unfold chainNodesSet at h ⊢
  rw [RegChain.linksAt, RegChain.pairsAt, pairEndpoints_cons, pairEndpoints_append, pairEndpoints_append,
    pairEndpoints_append, pairEndpoints_append, pairEndpoints_append, pairEndpoints_append]
  simp only [Finset.mem_union, Finset.mem_singleton] at h ⊢
  tauto

theorem chainNodes_nb {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain} {ζ : ℤˣ}
    {a : Fin w × Path} :
    addrExt a ([m.c] ++ inner.lonePath) ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ a := by
  unfold chainNodesSet
  rw [RegChain.linksAt, pairEndpoints_cons]
  simp

theorem chainNodes_oriented_red {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain} {ζ : ℤˣ}
    {a z : Fin w × Path}
    (h : z ∈ orientedNodes (slotSign ζ m.red.1 = 1) Qr (addrExt a [m.red.1])
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))) :
    z ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ a := by
  unfold chainNodesSet
  rw [RegChain.linksAt, RegChain.pairsAt, pairEndpoints_cons, pairEndpoints_append, pairEndpoints_append,
    pairEndpoints_append, pairEndpoints_append, pairEndpoints_append, pairEndpoints_append]
  unfold orientedNodes cplNodes at h
  split_ifs at h with hs
  · simp only [Finset.mem_union, Finset.mem_singleton] at h ⊢
    simp only [hs, ↓reduceIte]
    tauto
  · simp only [Finset.mem_union, Finset.mem_singleton] at h ⊢
    simp only [hs, ↓reduceIte]
    tauto

theorem chainNodes_oriented_green {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain} {ζ : ℤˣ}
    {a z : Fin w × Path}
    (h : z ∈ orientedNodes (slotSign ζ m.green.1 = 1) Qg (addrExt a [m.green.1])
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))) :
    z ∈ chainNodesSet (.pair m Qr Qg inner rest) ζ a := by
  unfold chainNodesSet
  rw [RegChain.linksAt, RegChain.pairsAt, pairEndpoints_cons, pairEndpoints_append, pairEndpoints_append,
    pairEndpoints_append, pairEndpoints_append, pairEndpoints_append, pairEndpoints_append]
  unfold orientedNodes cplNodes at h
  split_ifs at h with hs
  · simp only [Finset.mem_union, Finset.mem_singleton] at h ⊢
    simp only [hs, ↓reduceIte]
    tauto
  · simp only [Finset.mem_union, Finset.mem_singleton] at h ⊢
    simp only [hs, ↓reduceIte]
    tauto

section RegionAware
variable (P : Fin w × Path → Prop) (ρ : Fin w × Path → Fin w' × Path) (Rg : Fin w × Path → Prop)
  (hP : ∀ x q, P x → P (addrExt x q)) (hρ : ∀ x q, P x → ρ (addrExt x q) = addrExt (ρ x) q)
  {H1 : LayeredGarden w} {H2 : LayeredGarden w'}
  (hlay : ∀ z, P z → Rg z → layerAt H2 (ρ z) = layerAt H1 z)

include hP hρ hlay

theorem oriented_layers_mapR (Pr : Prop) [Decidable Pr] (Q : RegCpl) (x y : Fin w × Path) (a : Fin w × Path)
    (hx : P x) (hy : P y) (ha : P a) (hRa : Rg a) (hR : ∀ u ∈ orientedNodes Pr Q x y, Rg u) :
    (∀ z ∈ orientedNodes Pr Q (ρ x) (ρ y), layerAt H2 z = layerAt H2 (ρ a)) ↔
    (∀ z ∈ orientedNodes Pr Q x y, layerAt H1 z = layerAt H1 a) := by
  refine ball_map ρ _ _ (fun z => mem_oriented_map P ρ hP hρ Pr Q x y hx hy z) _ _ ?_
  intro u hu
  rw [hlay u (oriented_P P hP Pr Q x y hx hy hu) (hR u hu), hlay a ha hRa]

theorem chainPairLayers_mapR (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (ha : P a)
    (hR : ∀ z ∈ chainNodesSet X ζ a, Rg z) :
    ChainPairLayers H2 X ζ (ρ a) ↔ ChainPairLayers H1 X ζ a := by
  cases X with
  | nil => simp [ChainPairLayers]
  | pair m Qr Qg inner rest =>
    have hRa : Rg a := hR a (root_mem_chainNodesSet m Qr Qg inner rest ζ a)
    have hRnb : Rg (addrExt a ([m.c] ++ inner.lonePath)) := hR _ chainNodes_nb
    have hl : layerAt H2 (addrExt (ρ a) ([m.c] ++ inner.lonePath)) = layerAt H1 (addrExt a ([m.c] ++ inner.lonePath)) := by
      rw [← hρ a _ ha]; exact hlay _ (hP a _ ha) hRnb
    have e0 : layerAt H2 (ρ a) = layerAt H1 a := hlay a ha hRa
    have hi := chainPairLayers_mapR inner (slotSign ζ m.c) (addrExt a [m.c]) (hP _ _ ha)
      (fun z hz => hR z (chainNodes_inner_sub hz))
    have hr := chainPairLayers_mapR rest (slotSign (slotSign ζ m.c) m.lone)
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) (hP _ _ ha)
      (fun z hz => hR z (chainNodes_rest_sub hz))
    have hor := oriented_layers_mapR P ρ Rg hP hρ hlay (slotSign ζ m.red.1 = 1) Qr (addrExt a [m.red.1])
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) a (hP _ _ ha) (hP _ _ ha) ha hRa
      (fun u hu => hR u (chainNodes_oriented_red hu))
    have hog := oriented_layers_mapR P ρ Rg hP hρ hlay (slotSign ζ m.green.1 = 1) Qg (addrExt a [m.green.1])
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) a (hP _ _ ha) (hP _ _ ha) ha hRa
      (fun u hu => hR u (chainNodes_oriented_green hu))
    simp only [hρ a _ ha] at hi hr hor hog
    rw [e0] at hor hog
    simp only [ChainPairLayers, hi, hr, hl, e0, hor, hog]
termination_by structural X

theorem cohOn_chain_mapR (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (ha : P a)
    (hR : ∀ z ∈ chainNodesSet X ζ a, Rg z) :
    CohOn H2 (X.linksAt ζ (ρ a)) ↔ CohOn H1 (X.linksAt ζ a) := by
  rw [chain_links_map P ρ hP hρ X ζ a ha]
  unfold CohOn
  simp only [List.mem_map, forall_exists_index, and_imp]
  have hP' : ∀ l ∈ X.linksAt ζ a, P l.1 ∧ P l.2 := fun l hl =>
    ⟨chainNodes_P P hP X ζ ha (Finset.mem_union_left _ (mem_pairEndpoints_fst hl)),
     chainNodes_P P hP X ζ ha (Finset.mem_union_left _ (mem_pairEndpoints_snd hl))⟩
  have hR' : ∀ l ∈ X.linksAt ζ a, Rg l.1 ∧ Rg l.2 := fun l hl =>
    ⟨hR _ (Finset.mem_union_left _ (mem_pairEndpoints_fst hl)),
     hR _ (Finset.mem_union_left _ (mem_pairEndpoints_snd hl))⟩
  constructor
  · intro h l hl
    have := h _ l hl rfl
    rwa [hlay _ (hP' l hl).1 (hR' l hl).1, hlay _ (hP' l hl).2 (hR' l hl).2] at this
  · intro h l' l hl e
    subst e
    simp only
    rw [hlay _ (hP' l hl).1 (hR' l hl).1, hlay _ (hP' l hl).2 (hR' l hl).2]
    exact h l hl

theorem treePatternN_mapR (pa : ℕ) (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (ha : P a)
    (hR : ∀ z ∈ chainNodesSet X ζ a, Rg z) (hRl : Rg (addrExt a X.lonePath)) :
    TreePatternN H2 pa X ζ (ρ a) ↔ TreePatternN H1 pa X ζ a := by
  unfold TreePatternN
  have hxp := fun (u : Fin w' × Path) => mem_chainNodesSet_map P ρ hP hρ X ζ a ha u
  have hl : layerAt H2 (addrExt (ρ a) X.lonePath) = layerAt H1 (addrExt a X.lonePath) := by
    rw [← hρ a _ ha]; exact hlay _ (hP a _ ha) hRl
  have h4 : (∀ z ∈ chainNodesSet X ζ (ρ a), layerAt H2 (addrExt (ρ a) X.lonePath) ≤ layerAt H2 z ∧
      layerAt H2 z ≤ pa) ↔
      ∀ z ∈ chainNodesSet X ζ a, layerAt H1 (addrExt a X.lonePath) ≤ layerAt H1 z ∧ layerAt H1 z ≤ pa := by
    rw [hl]
    refine ball_map ρ _ _ hxp _ _ ?_
    intro u hu; rw [hlay u (chainNodes_P P hP X ζ ha hu) (hR u hu)]
  rw [cohOn_chain_mapR P ρ Rg hP hρ hlay X ζ a ha hR, chainPairLayers_mapR P ρ Rg hP hρ hlay X ζ a ha hR, h4]

end RegionAware

end WaveTurbulence.ZpSurj
