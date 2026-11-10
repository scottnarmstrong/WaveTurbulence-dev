/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Reloc4

/-! # ZP-SURJ: grafting a layered regular couple into a layered garden (the layering)

`graftLayer LB LQ a b`: the layer function on addresses that is `LB` outside the subtrees at `a`, `b` and the layers
of the layered couple `LQ` inside (the `+` tree below `a`, the `-` tree below `b`). `graftC_isLayering`: if `M`
embeds the code `Q` at `(a, b)`, agrees with `LB` off the region, `LQ` decodes `Q`, and the roots of `LQ` lie below
the parent layers of `a`, `b` in `LB`, then this function is a layering of `M`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree WaveTurbulence.Reg WaveTurbulence.Links

variable {w : ℕ}

/-- The layer function of the graft of `LQ` into `LB` at `(a, b)`. -/
@[expose] noncomputable def graftLayer (LB : LayeredGarden w) (LQ : LayeredGarden 2) (a b : Fin w × Path)
    (z : Fin w × Path) : ℕ :=
  if Under a z then layerAt LQ (0, z.2.drop a.2.length)
  else if Under b z then layerAt LQ (1, z.2.drop b.2.length) else layerAt LB z

theorem graftLayer_a (LB : LayeredGarden w) (LQ : LayeredGarden 2) (a b : Fin w × Path) (r : Path) :
    graftLayer LB LQ a b (addrExt a r) = layerAt LQ ((0 : Fin 2), r) := by
  unfold graftLayer
  rw [if_pos (under_ext a r)]
  simp [addrExt]

theorem graftLayer_b (LB : LayeredGarden w) (LQ : LayeredGarden 2) (a b : Fin w × Path) (hab : Indep a b)
    (r : Path) : graftLayer LB LQ a b (addrExt b r) = layerAt LQ ((1 : Fin 2), r) := by
  have h : ¬ Under a (addrExt b r) := fun h => by
    rcases under_total h (under_ext b r) with h' | h'
    · exact hab.1 h'
    · exact hab.2 h'
  unfold graftLayer
  rw [if_neg h, if_pos (under_ext b r)]
  simp [addrExt]

theorem graftLayer_out (LB : LayeredGarden w) (LQ : LayeredGarden 2) (a b : Fin w × Path) {z : Fin w × Path}
    (ha : ¬ Under a z) (hb : ¬ Under b z) : graftLayer LB LQ a b z = layerAt LB z := by
  simp [graftLayer, ha, hb]

/-- Garden-level agreement off the region of the two roots (nodes, leaves, partners). -/
structure GOut (G0 G1 : Garden w) (a b : Fin w × Path) : Prop where
  node : ∀ z : Fin w × Path, ¬ InRegion a b z → (z.2 ∈ (G0.tree z.1).nodes ↔ z.2 ∈ (G1.tree z.1).nodes)
  leaf : ∀ z : Fin w × Path, ¬ InRegion a b z → (z.2 ∈ (G0.tree z.1).leaves ↔ z.2 ∈ (G1.tree z.1).leaves)
  pair : ∀ (ℓ : GLeaf G0.tree) (ℓ' : GLeaf G1.tree), ¬ InRegion a b ℓ.1 → ℓ.1 = ℓ'.1 →
    (G0.pair ℓ).1 = (G1.pair ℓ').1

section Layering
variable {LB : LayeredGarden w} {M : Garden w} {Q : RegCpl} {LQ : LayeredGarden 2} {a b : Fin w × Path} {p : ℕ}

theorem graftC_nodeA (hEM : Embeds M Q a b) (EQ : Embeds LQ.garden Q ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)))
    (r : Path) :
    ((addrExt a r).2 ∈ (M.tree (addrExt a r).1).nodes ↔ (r ∈ (LQ.garden.tree 0).nodes)) :=
  (node_iff_of_subtree hEM.nodeA hEM.treeA r).1.trans (node_iff_of_subtree EQ.nodeA EQ.treeA r).1.symm

theorem graftC_nodeB (hEM : Embeds M Q a b) (EQ : Embeds LQ.garden Q ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)))
    (r : Path) :
    ((addrExt b r).2 ∈ (M.tree (addrExt b r).1).nodes ↔ (r ∈ (LQ.garden.tree 1).nodes)) :=
  (node_iff_of_subtree hEM.nodeB hEM.treeB r).1.trans (node_iff_of_subtree EQ.nodeB EQ.treeB r).1.symm

/-- Inside the region, the layers of a graft below a node never exceed the layer of that node. -/
theorem graftC_child_region (hEM : Embeds M Q a b)
    (EQ : Embeds LQ.garden Q ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)))
    (hab : Indep a b) {x y : Fin w × Path} (hx : Under a x ∨ Under b x) (hxn : x.2 ∈ (M.tree x.1).nodes)
    (hyn : y.2 ∈ (M.tree y.1).nodes) (hxy : Under x y) :
    graftLayer LB LQ a b y ≤ graftLayer LB LQ a b x := by
  rcases hx with hx | hx
  · have hy : Under a y := under_trans hx hxy
    obtain ⟨r, rfl⟩ := under_of_addrExt hx
    obtain ⟨r', rfl⟩ := under_of_addrExt hy
    rw [graftLayer_a, graftLayer_a]
    have hr : r ∈ (LQ.garden.tree 0).nodes := (graftC_nodeA hEM EQ r).1 hxn
    have hr' : r' ∈ (LQ.garden.tree 0).nodes := (graftC_nodeA hEM EQ r').1 hyn
    have hu : Under (((0 : Fin 2), r) : Fin 2 × Path) ((0 : Fin 2), r') := by
      have := (under_ext_iff a r r').1 hxy
      exact ⟨rfl, this⟩
    exact layerAt_le_of_under LQ hr hr' hu
  · have hy : Under b y := under_trans hx hxy
    obtain ⟨r, rfl⟩ := under_of_addrExt hx
    obtain ⟨r', rfl⟩ := under_of_addrExt hy
    rw [graftLayer_b _ _ _ _ hab, graftLayer_b _ _ _ _ hab]
    have hr : r ∈ (LQ.garden.tree 1).nodes := (graftC_nodeB hEM EQ r).1 hxn
    have hr' : r' ∈ (LQ.garden.tree 1).nodes := (graftC_nodeB hEM EQ r').1 hyn
    have hu : Under (((1 : Fin 2), r) : Fin 2 × Path) ((1 : Fin 2), r') := by
      have := (under_ext_iff b r r').1 hxy
      exact ⟨rfl, this⟩
    exact layerAt_le_of_under LQ hr hr' hu

theorem eq_of_under_child {a x : Fin w × Path} (i : Fin 3) (hy : Under a (addrExt x [i])) (hx : ¬ Under a x) :
    a = addrExt x [i] := by
  obtain ⟨h1, h2⟩ := hy
  simp only [addrExt] at h1 h2
  rcases List.prefix_concat_iff.1 h2 with h | h
  · exact Prod.ext h1 h
  · exact absurd ⟨h1, h⟩ hx

theorem graftC_child_out (hab : Indep a b) (hEB : Embeds LB.garden .triv a b) (hOut : GOut LB.garden M a b)
    (hrA : layerAt LQ ((0 : Fin 2), ([] : Path)) ≤ parAt LB p a)
    (hrB : layerAt LQ ((1 : Fin 2), ([] : Path)) ≤ parAt LB p b)
    {x : Fin w × Path} (i : Fin 3) (hx : ¬ InRegion a b x) (hxn : x.2 ∈ (M.tree x.1).nodes)
    (hyn : (addrExt x [i]).2 ∈ (M.tree (addrExt x [i]).1).nodes) :
    graftLayer LB LQ a b (addrExt x [i]) ≤ graftLayer LB LQ a b x := by
  have hxa : ¬ Under a x := fun h => hx (Or.inl h)
  have hxb : ¬ Under b x := fun h => hx (Or.inr h)
  rw [graftLayer_out _ _ _ _ hxa hxb]
  by_cases hya : Under a (addrExt x [i])
  · have e := eq_of_under_child i hya hxa
    have hn : (addrExt x [i]).2 ∈ (LB.garden.tree (addrExt x [i]).1).nodes := by rw [← e]; exact hEB.nodeA
    have h1 := parAt_child LB p i hn
    rw [← e] at h1 hya ⊢
    have h2 := graftLayer_a LB LQ a b []
    rw [addrExt_nil] at h2
    rw [h2]
    exact hrA.trans (h1.le)
  · by_cases hyb : Under b (addrExt x [i])
    · have e := eq_of_under_child i hyb hxb
      have hn : (addrExt x [i]).2 ∈ (LB.garden.tree (addrExt x [i]).1).nodes := by rw [← e]; exact hEB.nodeB
      have h1 := parAt_child LB p i hn
      rw [← e] at h1 hyb ⊢
      have h2 := graftLayer_b LB LQ a b hab []
      rw [addrExt_nil] at h2
      rw [h2]
      exact hrB.trans (h1.le)
    · rw [graftLayer_out _ _ _ _ hya hyb]
      have hxB := (hOut.node x hx).2 hxn
      have hyB := (hOut.node _ (fun h => h.elim hya hyb)).2 hyn
      exact layerAt_le_of_under LB hxB hyB (under_ext x [i])

theorem indep_root2 : Indep (((0 : Fin 2), ([] : Path)) : Fin 2 × Path) ((1 : Fin 2), ([] : Path)) :=
  ⟨fun h => by simp [Under] at h, fun h => by simp [Under] at h⟩

theorem graftLayer_reloc (hab : Indep a b) {z : Fin 2 × Path}
    (hz : Under (((0 : Fin 2), ([] : Path)) : Fin 2 × Path) z ∨ Under (((1 : Fin 2), ([] : Path)) : Fin 2 × Path) z) :
    graftLayer LB LQ a b (relocMap ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)) a b z) = layerAt LQ z := by
  rcases hz with hz | hz
  · obtain ⟨r, rfl⟩ := under_of_addrExt hz
    rw [relocMap_a, graftLayer_a]
    simp [addrExt]
  · obtain ⟨r, rfl⟩ := under_of_addrExt hz
    rw [relocMap_b indep_root2, graftLayer_b _ _ _ _ hab]
    simp [addrExt]

theorem graftC_pairs_layer (hab : Indep a b) (EQ : Embeds LQ.garden Q ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)))
    {q : (Fin w × Path) × (Fin w × Path)} (hq : q ∈ Q.pairsAt a b) :
    graftLayer LB LQ a b q.1 = graftLayer LB LQ a b q.2 := by
  rw [pairsAt_reloc indep_root2 a b Q, List.mem_map] at hq
  obtain ⟨l, hl, rfl⟩ := hq
  have h1 : Under (((0 : Fin 2), ([] : Path)) : Fin 2 × Path) l.1 ∨ Under (((1 : Fin 2), ([] : Path)) : Fin 2 × Path) l.1 :=
    cpl_endpoints_under Q _ _ l.1 (Finset.mem_union_right _ (mem_pairEndpoints_fst hl))
  have h2 : Under (((0 : Fin 2), ([] : Path)) : Fin 2 × Path) l.2 ∨ Under (((1 : Fin 2), ([] : Path)) : Fin 2 × Path) l.2 :=
    cpl_endpoints_under Q _ _ l.2 (Finset.mem_union_right _ (mem_pairEndpoints_snd hl))
  simp only
  rw [graftLayer_reloc hab h1, graftLayer_reloc hab h2]
  exact EQ.pair_layer LQ hl

/-- **The graft layering.** -/
theorem graftC_isLayering (hab : Indep a b) (hEB : Embeds LB.garden .triv a b) (hEM : Embeds M Q a b)
    (hOut : GOut LB.garden M a b) (hdec : Q.Decodes LQ.garden)
    (hrA : layerAt LQ ((0 : Fin 2), ([] : Path)) ≤ parAt LB p a)
    (hrB : layerAt LQ ((1 : Fin 2), ([] : Path)) ≤ parAt LB p b) :
    IsLayering M (fun n : GNode M.tree => graftLayer LB LQ a b n.1) := by
  have EQ := Embeds.of_decodes hdec
  constructor
  · intro br i
    by_cases hx : InRegion a b br.1
    · exact graftC_child_region hEM EQ hab hx (TTree.branching_subset_nodes _ br.2) (br.child i).2 (under_ext br.1 [i])
    · exact graftC_child_out hab hEB hOut hrA hrB i hx (TTree.branching_subset_nodes _ br.2) (br.child i).2
  · intro ℓ
    by_cases hreg : InRegion a b ℓ.1
    · obtain ⟨q, hq, h⟩ := hEM.partner ℓ hreg
      have hp := graftC_pairs_layer (LB := LB) hab EQ hq
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · change graftLayer LB LQ a b ℓ.1 = graftLayer LB LQ a b (M.pair ℓ).1
        rw [h1, h2]; exact hp
      · change graftLayer LB LQ a b ℓ.1 = graftLayer LB LQ a b (M.pair ℓ).1
        rw [h1, h2]; exact hp.symm
    · have hpo := hEM.pair_out ℓ hreg
      change graftLayer LB LQ a b ℓ.1 = graftLayer LB LQ a b (M.pair ℓ).1
      rw [graftLayer_out _ _ _ _ (fun h => hreg (Or.inl h)) (fun h => hreg (Or.inr h)),
        graftLayer_out _ _ _ _ (fun h => hpo (Or.inl h)) (fun h => hpo (Or.inr h))]
      let ℓB : GLeaf LB.garden.tree := ⟨ℓ.1, (hOut.leaf _ hreg).2 ℓ.2⟩
      have hpair := hOut.pair ℓB ℓ hreg rfl
      have h1 := LB.isLayering.2 ℓB
      rw [← layerAt_node, ← layerAt_node] at h1
      change layerAt LB ℓ.1 = layerAt LB (LB.garden.pair ℓB).1 at h1
      rw [h1, hpair]

variable (hab : Indep a b) (hEB : Embeds LB.garden .triv a b) (hEM : Embeds M Q a b)
  (hOut : GOut LB.garden M a b) (hdec : Q.Decodes LQ.garden)
  (hrA : layerAt LQ ((0 : Fin 2), ([] : Path)) ≤ parAt LB p a)
  (hrB : layerAt LQ ((1 : Fin 2), ([] : Path)) ≤ parAt LB p b)

/-- The layered garden obtained by grafting `LQ` into `LB`. -/
@[expose] noncomputable def graftC : LayeredGarden w :=
  ⟨M, fun n : GNode M.tree => graftLayer LB LQ a b n.1, graftC_isLayering hab hEB hEM hOut hdec hrA hrB⟩

include hab hEB hEM hOut hdec hrA hrB in
theorem graftC_layerAt_node {z : Fin w × Path} (hz : z.2 ∈ (M.tree z.1).nodes) :
    layerAt (graftC hab hEB hEM hOut hdec hrA hrB) z = graftLayer LB LQ a b z :=
  layerAt_of_mem _ hz

include hab hEB hEM hOut hdec hrA hrB in
theorem graftC_layerAt_a (r : Path) :
    layerAt (graftC hab hEB hEM hOut hdec hrA hrB) (addrExt a r) = layerAt LQ ((0 : Fin 2), r) := by
  have EQ := Embeds.of_decodes hdec
  by_cases h : (addrExt a r).2 ∈ (M.tree (addrExt a r).1).nodes
  · rw [graftC_layerAt_node hab hEB hEM hOut hdec hrA hrB h, graftLayer_a]
  · have h' : r ∉ (LQ.garden.tree 0).nodes := fun hh => h ((graftC_nodeA hEM EQ r).2 hh)
    have e1 : layerAt (graftC hab hEB hEM hOut hdec hrA hrB) (addrExt a r) = 0 := by
      unfold layerAt; exact dif_neg h
    have e2 : layerAt LQ ((0 : Fin 2), r) = 0 := by
      unfold layerAt; exact dif_neg h'
    rw [e1, e2]

include hab hEB hEM hOut hdec hrA hrB in
theorem graftC_layerAt_b (r : Path) :
    layerAt (graftC hab hEB hEM hOut hdec hrA hrB) (addrExt b r) = layerAt LQ ((1 : Fin 2), r) := by
  have EQ := Embeds.of_decodes hdec
  by_cases h : (addrExt b r).2 ∈ (M.tree (addrExt b r).1).nodes
  · rw [graftC_layerAt_node hab hEB hEM hOut hdec hrA hrB h, graftLayer_b _ _ _ _ hab]
  · have h' : r ∉ (LQ.garden.tree 1).nodes := fun hh => h ((graftC_nodeB hEM EQ r).2 hh)
    have e1 : layerAt (graftC hab hEB hEM hOut hdec hrA hrB) (addrExt b r) = 0 := by
      unfold layerAt; exact dif_neg h
    have e2 : layerAt LQ ((1 : Fin 2), r) = 0 := by
      unfold layerAt; exact dif_neg h'
    rw [e1, e2]

include hab hEB hEM hOut hdec hrA hrB in
theorem graftC_outAgree : OutAgree LB (graftC hab hEB hEM hOut hdec hrA hrB) a b where
  node := fun z hz => hOut.node z hz
  leaf := fun z hz => hOut.leaf z hz
  layer := by
    intro z hz
    by_cases h : z.2 ∈ (M.tree z.1).nodes
    · rw [graftC_layerAt_node hab hEB hEM hOut hdec hrA hrB h,
        graftLayer_out _ _ _ _ (fun h' => hz (Or.inl h')) (fun h' => hz (Or.inr h'))]
    · have h' : z.2 ∉ (LB.garden.tree z.1).nodes := fun hh => h ((hOut.node z hz).1 hh)
      have e1 : layerAt (graftC hab hEB hEM hOut hdec hrA hrB) z = 0 := by
        unfold layerAt; exact dif_neg h
      have e2 : layerAt LB z = 0 := by
        unfold layerAt; exact dif_neg h'
      rw [e1, e2]
  pair := fun ℓ ℓ' hz he => hOut.pair ℓ ℓ' hz he

include hab hEB hEM hOut hdec hrA hrB in
theorem graftC_pattern_iff :
    LayerPattern (graftC hab hEB hEM hOut hdec hrA hrB) p Q a b ↔
      LayerPatternN LQ (parAt (graftC hab hEB hEM hOut hdec hrA hrB) p a)
        (parAt (graftC hab hEB hEM hOut hdec hrA hrB) p b) Q ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)) := by
  rw [layerPattern_eq_N]
  refine layerPatternN_reloc _ _ Q _ _ indep_root2 a b
    (fun r => by rw [graftC_layerAt_a hab hEB hEM hOut hdec hrA hrB]; simp [addrExt])
    (fun r => by rw [graftC_layerAt_b hab hEB hEM hOut hdec hrA hrB]; simp [addrExt])

include hab hEB hEM hOut hdec hrA hrB in
theorem graftC_parAt_a : parAt (graftC hab hEB hEM hOut hdec hrA hrB) p a = parAt LB p a :=
  (graftC_outAgree hab hEB hEM hOut hdec hrA hrB).symm.parAt_eq_a hab hEM.nodeA hEB.nodeA

include hab hEB hEM hOut hdec hrA hrB in
theorem graftC_parAt_b : parAt (graftC hab hEB hEM hOut hdec hrA hrB) p b = parAt LB p b :=
  (graftC_outAgree hab hEB hEM hOut hdec hrA hrB).symm.parAt_eq_b hab hEM.nodeB hEB.nodeB

end Layering

end WaveTurbulence.ZpSurj
