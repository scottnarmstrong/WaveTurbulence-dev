/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.Ambient
public import WaveTurbulence.Foundations.Flower.ProtPin.Relayer
public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.LayerReg1
public import WaveTurbulence.Foundations.Spine.PL234Draft.BlockLayers
public import WaveTurbulence.Foundations.Spine.PL234Draft.SameLayer
public import WaveTurbulence.Foundations.Spine.PL234Draft.GlueTree
public import WaveTurbulence.Foundations.IncohInst.Links.Coherence
public import WaveTurbulence.Foundations.RegStruct.DecodedLeaves

/-! # D3 PROT-PIN: coherent protected objects and coherent cut pieces are flat

In a canonical ambient `H` (`IsCanonGC (p + 1) H`), a coherent regular chain has each pair in one layer together with
its couples (main's `chain_coherent`, TARGET `layerreg1`), and a coherent couple whose roots have equal parent layers
lies in that layer (main's `cpl_coherent`). Hence:
* `flat_tree_whole`: a coherent protected paired tree (stem in layer `p`, `ChainIn`) has every node except its lone
  leaf in layer `p` (`chainNodes_layer_of_topAll`), for any layer of the lone position;
* `flat_tree_piece` / `flat_tree_sub`: a coherent tree piece whose root and lone position are in layer `p` lies in
  layer `p` (`chainNodes_layer_of_ends`);
* `flat_couple_piece` / `flat_couple_sub`: a coherent couple piece whose roots hang below layer-`p` nodes lies in
  layer `p`.
Coherence is read in `H` from incoherency `0` of the object (`cohOn_of_tree`, `cohOn_of_couple`, converses of main's
`incoherency_eq_zero_of_isCoherent*At`). The flat relayerings (`flatLeafLayer`, constant leaves) put the lone leaf of
a flat paired tree in the box layer `q'`, the leaves of a flat cap couple in layer `p`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Links WaveTurbulence.Reg Set Finset
open scoped Classical

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs

/-! ### Coherence read in the ambient -/

/-- Coherence of a tree, read in an ambient garden. -/
theorem cohOn_of_tree {w' : ℕ} {H : LayeredGarden w'} {X : RegChain} {LG : LayeredGarden 1}
    (hX : X.DecodesTree LG.garden) {a : Fin w' × TTree.Path}
    (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2))
    (h0 : LG.incoherency (X.treeLinks (LG.garden.sig 0)) = 0) : CohOn H (X.linksAt (LG.garden.sig 0) a) := by
  let f : Fin 1 × TTree.Path → Fin w' × TTree.Path := fun z => addrExt a z.2
  have hf : ∀ x r, f (addrExt x r) = addrExt (f x) r := by
    intro x r
    simp only [f, addrExt, List.append_assoc]
  have hm := PL234.chain_linksAt_map X f hf (LG.garden.sig 0) (0, [])
  have h0' : f (0, []) = a := by simp [f, addrExt]
  rw [h0'] at hm
  intro l' hl'
  rw [hm] at hl'
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hl'
  have hc := (tree_coherent_iff hX).1 h0 l hl
  have hb1 := (tree_mem_pairEndpoints_links_iff hX _).1 ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inl rfl⟩)
  have hb2 := (tree_mem_pairEndpoints_links_iff hX _).1 ((mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inr rfl⟩)
  have e : ∀ (x : Fin 1 × TTree.Path) (hx : x.2 ∈ (LG.garden.tree x.1).nodes), layerAt LG x = layerAt H (f x) :=
    fun x hx => (layerAt_node LG ⟨x, hx⟩).trans (hlay ⟨x, hx⟩)
  exact (e l.1 (TTree.branching_subset_nodes _ hb1)).symm.trans
    (hc.trans (e l.2 (TTree.branching_subset_nodes _ hb2)))

/-- Coherence of a couple, read in an ambient garden. -/
theorem cohOn_of_couple {w' : ℕ} {H : LayeredGarden w'} {Q : RegCpl} {LG : LayeredGarden 2}
    (hQ : Q.Decodes LG.garden) {a b : Fin w' × TTree.Path}
    (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt (if z.1.1 = 0 then a else b) z.1.2))
    (h0 : LG.incoherency Q.links = 0) : CohOn H (Q.linksAt a b) := by
  let f : Fin 2 × TTree.Path → Fin w' × TTree.Path := fun z => addrExt (if z.1 = 0 then a else b) z.2
  have hf : ∀ x r, f (addrExt x r) = addrExt (f x) r := by
    intro x r
    simp only [f, addrExt, List.append_assoc]
  have hm := PL234.couple_linksAt_map Q f hf (0, []) (1, [])
  have h0' : f (0, []) = a := by simp [f, addrExt]
  have h1' : f (1, []) = b := by simp [f, addrExt]
  rw [h0', h1'] at hm
  intro l' hl'
  rw [hm] at hl'
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hl'
  have hc := (coherent_iff hQ).1 h0 l hl
  obtain ⟨hb1, hb2, _⟩ := link_branching hQ hl
  have e : ∀ (x : Fin 2 × TTree.Path) (hx : x.2 ∈ (LG.garden.tree x.1).nodes), layerAt LG x = layerAt H (f x) :=
    fun x hx => (layerAt_node LG ⟨x, hx⟩).trans (hlay ⟨x, hx⟩)
  exact (e l.1 (TTree.branching_subset_nodes _ hb1)).symm.trans
    (hc.trans (e l.2 (TTree.branching_subset_nodes _ hb2)))

/-! ### Nodes of a placed chain; the stem -/

/-- Every node of a plugged chain code, read at `a`, is a node of the placed chain or its lone position (main's
`addrExt_mem_chainNodes`, for any plugged tree). -/
theorem mem_chainNodes_or_lone (X : RegChain) (ζ : ℤˣ) {w : ℕ} (a : Fin w × TTree.Path) {q : TTree.Path}
    (hq : q ∈ (X.plug ζ .leaf).nodes) : addrExt a q ∈ chainNodesSet X ζ a ∨ q = X.lonePath := by
  rcases (TTree.mem_nodes_iff _ _).mp hq with hl | hb
  · have hmem : addrExt a q ∈ leafAddresses (X.plug ζ .leaf) a := mem_image.mpr ⟨q, hl, rfl⟩
    rw [chain_leafAddresses] at hmem
    rcases mem_union.mp hmem with h | h
    · exact Or.inl (mem_union.mpr (Or.inr h))
    · right
      simp only [leafAddresses, TTree.leaves, Finset.image_singleton, Finset.mem_singleton] at h
      have h2 := congrArg Prod.snd h
      simpa [addrExt] using h2
  · have hmem : addrExt a q ∈ branchAddresses (X.plug ζ .leaf) a := mem_image.mpr ⟨q, hb, rfl⟩
    rw [chain_branchAddresses] at hmem
    rcases mem_union.mp hmem with h | h
    · exact Or.inl (mem_union.mpr (Or.inl h))
    · simp [branchAddresses, TTree.branching] at h

/-- Every top-level pair of a chain whose stem is in layer `r` is in layer `r`. -/
theorem topAll_of_stem {w : ℕ} (LG : LayeredGarden w) (r : ℕ) :
    ∀ (X : RegChain) (a : Fin w × TTree.Path),
      (∀ q : TTree.Path, q <+: X.lonePath → q ≠ X.lonePath → layerAt LG (addrExt a q) = r) →
      PL234.TopAll LG r a X
  | .nil, _, _ => trivial
  | .pair m Qr Qg inner rest, a, h => by
    have hlp : (RegChain.pair m Qr Qg inner rest).lonePath =
        ([m.c] ++ inner.lonePath ++ [m.lone]) ++ rest.lonePath := rfl
    refine ⟨?_, topAll_of_stem LG r rest _ fun q hq hne => ?_⟩
    · have h0 := h [] List.nil_prefix (by rw [hlp]; simp)
      simpa [addrExt] using h0
    · have e : addrExt (PL234.nextAddr a m inner) q = addrExt a (([m.c] ++ inner.lonePath ++ [m.lone]) ++ q) := by
        simp only [PL234.nextAddr, addrExt, List.append_assoc]
      rw [e]
      refine h _ ?_ ?_
      · rw [hlp]
        exact (List.prefix_append_right_inj _).2 hq
      · rw [hlp]
        exact fun he => hne (List.append_cancel_left he)

/-- The stem of a protected paired tree (in layer `p`, `ChainIn`) read in the ambient. -/
theorem stem_layer {w' : ℕ} {H : LayeredGarden w'} {p : ℕ} {X : RegChain} {LG : LayeredGarden 1}
    (hX : X.DecodesTree LG.garden) (hch : ChainIn p X LG) {a : Fin w' × TTree.Path}
    (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2)) :
    ∀ q : TTree.Path, q <+: X.lonePath → q ≠ X.lonePath → layerAt H (addrExt a q) = p := by
  intro q hq hne
  have hb : q ∈ (LG.garden.tree 0).branching := by
    rw [hX.1]
    exact ProtGeo.prefix_lone_branching X _ hq hne
  let b : GBranch LG.garden.tree := ⟨((0 : Fin 1), q), hb⟩
  exact (hlay b.toNode).symm.trans (hch b rfl hq hne)

/-! ### Flatness -/

/-- **A coherent protected paired tree is flat**: every node except the lone leaf is in layer `p`. -/
theorem flat_tree_whole {w' : ℕ} {H : LayeredGarden w'} {p : ℕ} (hcan : IsCanonGC (p + 1) H) {X : RegChain}
    {LG : LayeredGarden 1} (hwf : X.wf = true) (hX : X.DecodesTree LG.garden) {a : Fin w' × TTree.Path}
    {h : TTree} (hC : ChainEmb H.garden X (LG.garden.sig 0) a h)
    (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2)) (hch : ChainIn p X LG)
    (h0 : LG.incoherency (X.treeLinks (LG.garden.sig 0)) = 0) :
    ∀ z : GNode LG.garden.tree, z.1.2 ≠ X.lonePath → LG.layer z = p := by
  have hcoh := cohOn_of_tree hX hlay h0
  have hPL := chain_coherent hcan.2.2 hcan.1 X (LG.garden.sig 0) a h hwf hC hcoh
  have hT := topAll_of_stem H p X a (stem_layer hX hch hlay)
  have hall := PL234.chainNodes_layer_of_topAll hC hPL hT
  intro z hz
  have hm : z.1.2 ∈ (X.plug (LG.garden.sig 0) .leaf).nodes := by
    have h2 := z.2
    rw [show z.1.1 = 0 from Subsingleton.elim _ _, hX.1] at h2
    exact h2
  rcases mem_chainNodes_or_lone X (LG.garden.sig 0) a hm with hc | hc
  · rw [hlay z]
    exact hall _ hc
  · exact absurd hc hz

/-- **A coherent tree piece with root and lone position in layer `p` is flat in layer `p`.** -/
theorem flat_tree_piece {w' : ℕ} {H : LayeredGarden w'} {p : ℕ} (hcan : IsCanonGC (p + 1) H) {Y : RegChain}
    {LGt : LayeredGarden 1} (hwf : Y.wf = true) (hdec : Y.DecodesTree LGt.garden) {a : Fin w' × TTree.Path}
    {h : TTree} (hC : ChainEmb H.garden Y (LGt.garden.sig 0) a h)
    (hlay : ∀ z : GNode LGt.garden.tree, LGt.layer z = layerAt H (addrExt a z.1.2))
    (hle : ∀ z, LGt.layer z ≤ p) (hlone : ∀ z : GNode LGt.garden.tree, z.1.2 = Y.lonePath → LGt.layer z = p)
    (h0 : LGt.incoherency (Y.treeLinks (LGt.garden.sig 0)) = 0) : ∀ z, LGt.layer z = p := by
  have hcoh := cohOn_of_tree hdec hlay h0
  have hPL := chain_coherent hcan.2.2 hcan.1 Y (LGt.garden.sig 0) a h hwf hC hcoh
  have hlm : Y.lonePath ∈ (LGt.garden.tree 0).nodes := by
    rw [hdec.1]
    exact lonePath_mem_plug Y _ _
  have hrm : ([] : TTree.Path) ∈ (LGt.garden.tree 0).nodes := TTree.nil_mem_nodes _
  have hzl : LGt.layer ⟨((0 : Fin 1), Y.lonePath), hlm⟩ = p := hlone _ rfl
  have hu := layerAt_le_of_under LGt (x := ((0 : Fin 1), ([] : TTree.Path))) (z := ((0 : Fin 1), Y.lonePath))
    hrm hlm ⟨rfl, List.nil_prefix⟩
  rw [layerAt_of_mem LGt (z := ((0 : Fin 1), Y.lonePath)) hlm,
    layerAt_of_mem LGt (z := ((0 : Fin 1), ([] : TTree.Path))) hrm] at hu
  have hzr : LGt.layer ⟨((0 : Fin 1), []), hrm⟩ = p := le_antisymm (hle _) (hzl.symm.le.trans hu)
  have ha : layerAt H a = p := by
    have h1 := (hlay ⟨((0 : Fin 1), []), hrm⟩).symm.trans hzr
    simpa [addrExt] using h1
  have hl : layerAt H (addrExt a Y.lonePath) = p := (hlay ⟨((0 : Fin 1), Y.lonePath), hlm⟩).symm.trans hzl
  have hall := PL234.chainNodes_layer_of_ends hC hPL ha hl
  intro z
  have hm : z.1.2 ∈ (Y.plug (LGt.garden.sig 0) .leaf).nodes := by
    have h2 := z.2
    rw [show z.1.1 = 0 from Subsingleton.elim _ _, hdec.1] at h2
    exact h2
  rcases mem_chainNodes_or_lone Y (LGt.garden.sig 0) a hm with hc | hc
  · rw [hlay z]
    exact hall _ hc
  · exact hlone z hc

/-- **A coherent couple piece whose roots have parent layer `p` is flat in layer `p`.** -/
theorem flat_couple_piece {w' : ℕ} {H : LayeredGarden w'} {p : ℕ} (hcan : IsCanonGC (p + 1) H) {Q : RegCpl}
    {LGc : LayeredGarden 2} (hwf : Q.wf = true) (hdec : Q.Decodes LGc.garden) {a b : Fin w' × TTree.Path}
    (hE : Embeds H.garden Q a b)
    (hlay : ∀ z : GNode LGc.garden.tree, LGc.layer z = layerAt H (addrExt (if z.1.1 = 0 then a else b) z.1.2))
    (hpa : parAt H p a = p) (hpb : parAt H p b = p) (h0 : LGc.incoherency Q.links = 0) :
    ∀ z, LGc.layer z = p := by
  have hcoh := cohOn_of_couple hdec hlay h0
  have hc := (cpl_coherent hcan.2.2 hcan.1 Q a b hwf hE hcoh).2 (hpa.trans hpb.symm)
  intro z
  rw [hlay z, hc _ (PL234.addrExt_mem_cplNodes hdec a b z), hpa]

/-! ### Pieces placed inside the object -/

/-- An object node below a placed sub-object, read in the ambient. -/
theorem layerAt_sub {w' : ℕ} {H : LayeredGarden w'} {LG : LayeredGarden 1} {a : Fin w' × TTree.Path}
    (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2)) {r : Fin 1 × TTree.Path}
    {T : TTree} (hr : r.2 ∈ (LG.garden.tree r.1).nodes) (ht : (LG.garden.tree r.1).subtreeAt r.2 = T)
    {q : TTree.Path} (hq : q ∈ T.nodes) : layerAt LG (addrExt r q) = layerAt H (addrExt a (r.2 ++ q)) := by
  have hn := (node_iff_of_subtree hr ht q).1.2 hq
  rw [layerAt_of_mem LG hn]
  exact hlay ⟨addrExt r q, hn⟩

/-- Nodes of a chain plugged with a leaf are nodes of the chain plugged with any tree. -/
theorem nodes_plug_leaf_sub (X : RegChain) (ζ : ℤˣ) (t : TTree) {q : TTree.Path}
    (hq : q ∈ (X.plug ζ .leaf).nodes) : q ∈ (X.plug ζ t).nodes := by
  by_cases hpre : X.lonePath <+: q
  · rw [PL234.plug_leaf_prefix X ζ hq hpre]
    exact lonePath_mem_plug X ζ t
  · exact (PL234.plug_mem_off X ζ .leaf t q hpre).1.mp hq

/-- **A coherent tree piece placed in the object (at `r`) is flat**, given its root and lone position in layer `p`. -/
theorem flat_tree_sub {w' : ℕ} {H : LayeredGarden w'} {p : ℕ} (hcan : IsCanonGC (p + 1) H) {LG : LayeredGarden 1}
    {a : Fin w' × TTree.Path} (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2))
    {Y : RegChain} {LGt : LayeredGarden 1} (hwf : Y.wf = true) (hdec : Y.DecodesTree LGt.garden)
    {r : Fin 1 × TTree.Path} {T : TTree} (hCL : ChainEmb LG.garden Y (LGt.garden.sig 0) r T)
    {aH : Fin w' × TTree.Path} {h : TTree} (hCH : ChainEmb H.garden Y (LGt.garden.sig 0) aH h)
    (haH : aH = addrExt a r.2)
    (hlayt : ∀ z : GNode LGt.garden.tree, LGt.layer z = layerAt LG (addrExt r z.1.2))
    (hle : ∀ z, LGt.layer z ≤ p) (hlone : ∀ z : GNode LGt.garden.tree, z.1.2 = Y.lonePath → LGt.layer z = p)
    (h0 : LGt.incoherency (Y.treeLinks (LGt.garden.sig 0)) = 0) : ∀ z, LGt.layer z = p := by
  subst haH
  refine flat_tree_piece hcan hwf hdec hCH (fun z => ?_) hle hlone h0
  have hm : z.1.2 ∈ (Y.plug (LGt.garden.sig 0) T).nodes := by
    have h2 := z.2
    rw [show z.1.1 = 0 from Subsingleton.elim _ _, hdec.1] at h2
    exact nodes_plug_leaf_sub Y _ T h2
  rw [hlayt z, layerAt_sub hlay hCL.node hCL.tree hm]
  simp only [addrExt, List.append_assoc]

/-- **A coherent couple piece placed in the object (at `aL, bL`) is flat.** -/
theorem flat_couple_sub {w' : ℕ} {H : LayeredGarden w'} {p : ℕ} (hcan : IsCanonGC (p + 1) H) {LG : LayeredGarden 1}
    {a : Fin w' × TTree.Path} (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2))
    {Q : RegCpl} {LGc : LayeredGarden 2} (hwf : Q.wf = true) (hdec : Q.Decodes LGc.garden)
    {aL bL : Fin 1 × TTree.Path} (hEL : Embeds LG.garden Q aL bL) {aH bH : Fin w' × TTree.Path}
    (hEH : Embeds H.garden Q aH bH) (haH : aH = addrExt a aL.2) (hbH : bH = addrExt a bL.2)
    (hlayc : ∀ z : GNode LGc.garden.tree,
      LGc.layer z = layerAt LG (addrExt (if z.1.1 = 0 then aL else bL) z.1.2))
    (hpa : parAt H p aH = p) (hpb : parAt H p bH = p)
    (h0 : LGc.incoherency Q.links = 0) : ∀ z, LGc.layer z = p := by
  subst haH hbH
  refine flat_couple_piece hcan hwf hdec hEH (fun z => ?_) hpa hpb h0
  rw [hlayc z]
  rcases Fin.exists_fin_two.mp ⟨z.1.1, rfl⟩ with hz | hz
  · have hm : z.1.2 ∈ Q.trees.1.nodes := by
      have h2 := z.2
      rw [hz, hdec.2.1] at h2
      exact h2
    rw [if_pos hz, if_pos hz, layerAt_sub hlay hEL.nodeA hEL.treeA hm]
    simp only [addrExt, List.append_assoc]
  · have hne : z.1.1 ≠ 0 := by rw [hz]; decide
    have hm : z.1.2 ∈ Q.trees.2.nodes := by
      have h2 := z.2
      rw [hz, hdec.2.2.1] at h2
      exact h2
    rw [if_neg hne, if_neg hne, layerAt_sub hlay hEL.nodeB hEL.treeB hm]
    simp only [addrExt, List.append_assoc]

/-- The parent layer of a child address. -/
theorem parAt_child_eq {w' : ℕ} {H : LayeredGarden w'} {p : ℕ} {x y : Fin w' × TTree.Path} {i : Fin 3}
    (hy : y = addrExt x [i]) (hn : y.2 ∈ (H.garden.tree y.1).nodes) (hx : layerAt H x = p) : parAt H p y = p := by
  subst hy
  exact (parAt_child H p i hn).trans hx

/-- **A coherent side couple of a chain pair is flat**: its two roots hang below the two partner nodes (in layer `p`),
oriented by the slot sign `s`; `base j` is the position of tree `j` below `xp` (D2c's `rBase`/`gBase`). -/
theorem side_flat {w' : ℕ} {H : LayeredGarden w'} {p : ℕ} (hcan : IsCanonGC (p + 1) H) {LG : LayeredGarden 1}
    {a : Fin w' × TTree.Path} (hlay : ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2))
    {Q : RegCpl} {LGc : LayeredGarden 2} (hwf : Q.wf = true) (hdec : Q.Decodes LGc.garden)
    (xp bp : TTree.Path) (i1 i2 : Fin 3) (s : ℤˣ) (base : Fin 2 → TTree.Path)
    (hpos : s = 1 → base 0 = [i1] ∧ base 1 = bp ++ [i2]) (hneg : s ≠ 1 → base 0 = bp ++ [i2] ∧ base 1 = [i1])
    (hEL : if s = 1 then Embeds LG.garden Q (addrExt (addrExt ((0 : Fin 1), []) xp) [i1])
        (addrExt (addrExt ((0 : Fin 1), []) xp) (bp ++ [i2]))
      else Embeds LG.garden Q (addrExt (addrExt ((0 : Fin 1), []) xp) (bp ++ [i2]))
        (addrExt (addrExt ((0 : Fin 1), []) xp) [i1]))
    (hEH : if s = 1 then Embeds H.garden Q (addrExt (addrExt a xp) [i1]) (addrExt (addrExt a xp) (bp ++ [i2]))
      else Embeds H.garden Q (addrExt (addrExt a xp) (bp ++ [i2])) (addrExt (addrExt a xp) [i1]))
    (hlayc : ∀ z : GNode LGc.garden.tree, LGc.layer z = layerAt LG ((0 : Fin 1), xp ++ (base z.1.1 ++ z.1.2)))
    (hxa : layerAt H (addrExt a xp) = p) (hxb : layerAt H (addrExt a (xp ++ bp)) = p)
    (h0 : LGc.incoherency Q.links = 0) : ∀ z, LGc.layer z = p := by
  by_cases hs : s = 1
  · rw [if_pos hs] at hEL hEH
    obtain ⟨hb0, hb1⟩ := hpos hs
    refine flat_couple_sub hcan hlay hwf hdec hEL hEH (by simp [addrExt]) (by simp [addrExt]) (fun z => ?_)
      ((parAt_child H p i1 hEH.nodeA).trans hxa)
      (parAt_child_eq (x := addrExt a (xp ++ bp)) (i := i2) (by simp [addrExt]) hEH.nodeB hxb) h0
    rw [hlayc z]
    rcases Fin.exists_fin_two.mp ⟨z.1.1, rfl⟩ with hz | hz
    · rw [if_pos hz, hz, hb0]
      simp [addrExt]
    · rw [if_neg (show z.1.1 ≠ 0 by rw [hz]; decide), hz, hb1]
      simp [addrExt]
  · rw [if_neg hs] at hEL hEH
    obtain ⟨hb0, hb1⟩ := hneg hs
    refine flat_couple_sub hcan hlay hwf hdec hEL hEH (by simp [addrExt]) (by simp [addrExt]) (fun z => ?_)
      (parAt_child_eq (x := addrExt a (xp ++ bp)) (i := i2) (by simp [addrExt]) hEH.nodeA hxb)
      ((parAt_child H p i1 hEH.nodeB).trans hxa) h0
    rw [hlayc z]
    rcases Fin.exists_fin_two.mp ⟨z.1.1, rfl⟩ with hz | hz
    · rw [if_pos hz, hz, hb0]
      simp [addrExt]
    · rw [if_neg (show z.1.1 ≠ 0 by rw [hz]; decide), hz, hb1]
      simp [addrExt]

/-! ### Flat relayerings -/

/-- Leaf layers of a flat protected paired tree: `q'` at the lone leaf, `p` elsewhere. -/
def flatLeafLayer (LG : LayeredGarden 1) (X : RegChain) (p q' : ℕ) (a : GNode LG.garden.tree) : ℕ :=
  if a.1.2 = X.lonePath then q' else p

theorem isLayering_flat {p q' : ℕ} {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (hflat : ∀ b : GBranch LG.garden.tree, LG.layer b.toNode = p) (hq' : q' ≤ p) :
    IsLayering LG.garden (relayerFun LG (flatLeafLayer LG X p q')) := by
  refine ⟨fun b i => ?_, fun ℓ => ?_⟩
  · have hb : relayerFun LG (flatLeafLayer LG X p q') b.toNode = LG.layer b.toNode := if_pos b.2
    rw [hb, hflat b]
    unfold relayerFun flatLeafLayer
    split_ifs with hc hl
    · exact (LG.isLayering.1 b i).trans (hflat b).le
    · exact hq'
    · exact le_rfl
  · have h1 := not_mem_branching_of_leaf ℓ
    have h2 := not_mem_branching_of_leaf (LG.garden.pair ℓ)
    unfold relayerFun flatLeafLayer
    rw [if_neg h1, if_neg h2]
    have hp := Links.tree_pair_eq_iff hX ℓ
    by_cases hl : ℓ.1.2 = X.lonePath
    · rw [hp.2 hl]
    · have hpl : (LG.garden.pair ℓ).1.2 ≠ X.lonePath := by
        intro h'
        have hfix : LG.garden.pair (LG.garden.pair ℓ) = LG.garden.pair ℓ := (Links.tree_pair_eq_iff hX _).2 h'
        have hfix' : ℓ = LG.garden.pair ℓ := (LG.garden.pair_pair ℓ).symm.trans hfix
        exact hl ((congrArg (fun x : GLeaf LG.garden.tree => x.1.2) hfix').trans h')
      change (if ℓ.1.2 = X.lonePath then q' else p) = (if (LG.garden.pair ℓ).1.2 = X.lonePath then q' else p)
      rw [if_neg hl, if_neg hpl]

theorem relayer_flat_layer {p q' : ℕ} {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (hflat : ∀ b : GBranch LG.garden.tree, LG.layer b.toNode = p)
    (hf : IsLayering LG.garden (relayerFun LG (flatLeafLayer LG X p q'))) (z : GNode LG.garden.tree) :
    (relayer LG (flatLeafLayer LG X p q') hf).layer z = if z.1.2 = X.lonePath then q' else p := by
  change relayerFun LG (flatLeafLayer LG X p q') z = _
  unfold relayerFun flatLeafLayer
  by_cases hb : z.1.2 ∈ (LG.garden.tree z.1.1).branching
  · have hl : z.1.2 ≠ X.lonePath := by
      intro he
      rw [he, show z.1.1 = 0 from Subsingleton.elim _ _] at hb
      exact TTree.not_mem_branching_of_mem_leaves _ (Links.lone_mem_leaves hX) hb
    rw [if_pos hb, if_neg hl]
    exact hflat ⟨z.1, hb⟩
  · rw [if_neg hb]

/-- All leaves in layer `p` (a garden whose branching nodes are in layer `p`). -/
theorem isLayering_const {w p : ℕ} {LG : LayeredGarden w}
    (hflat : ∀ b : GBranch LG.garden.tree, LG.layer b.toNode = p) :
    IsLayering LG.garden (relayerFun LG fun _ => p) := by
  refine ⟨fun b i => ?_, fun ℓ => ?_⟩
  · have hb : relayerFun LG (fun _ => p) b.toNode = LG.layer b.toNode := if_pos b.2
    rw [hb, hflat b]
    unfold relayerFun
    split_ifs
    · exact (LG.isLayering.1 b i).trans (hflat b).le
    · exact le_rfl
  · unfold relayerFun
    rw [if_neg (not_mem_branching_of_leaf ℓ), if_neg (not_mem_branching_of_leaf (LG.garden.pair ℓ))]

theorem relayer_const_layer {w p : ℕ} {LG : LayeredGarden w}
    (hflat : ∀ b : GBranch LG.garden.tree, LG.layer b.toNode = p)
    (hf : IsLayering LG.garden (relayerFun LG fun _ => p)) (z : GNode LG.garden.tree) :
    (relayer LG (fun _ => p) hf).layer z = p := by
  change relayerFun LG (fun _ => p) z = p
  unfold relayerFun
  by_cases hb : z.1.2 ∈ (LG.garden.tree z.1.1).branching
  · rw [if_pos hb]
    exact hflat ⟨z.1, hb⟩
  · rw [if_neg hb]

end WaveTurbulence.Flower.ProtPin
