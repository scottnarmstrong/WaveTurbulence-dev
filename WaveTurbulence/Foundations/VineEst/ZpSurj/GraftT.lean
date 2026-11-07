/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.GraftC
public import WaveTurbulence.Foundations.VineEst.ZpSurj.Reloc5

/-! # ZP-SURJ: grafting a layered regular tree into a layered garden (the layering)

The old garden `LM` has a nil chain at `a` with tail `t` (the subtree at `a`); the new garden has the chain `X`
at `a` and the tail moved to `n' = a ⌢ lonePath X`. `graftTLayer`: `LM` outside, the layers of the tail carried
along, the layers of `LX` on the chain region.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree WaveTurbulence.Reg WaveTurbulence.Links

variable {w : ℕ}

/-- The layer function of the tree graft. -/
@[expose] noncomputable def graftTLayer (LM : LayeredGarden w) (LX : LayeredGarden 1) (a n' : Fin w × Path)
    (y : Fin w × Path) : ℕ :=
  if Under n' y then layerAt LM (addrExt a (y.2.drop n'.2.length))
  else if Under a y then layerAt LX (0, y.2.drop a.2.length) else layerAt LM y

theorem graftTLayer_tail (LM : LayeredGarden w) (LX : LayeredGarden 1) (a n' : Fin w × Path) (s : Path) :
    graftTLayer LM LX a n' (addrExt n' s) = layerAt LM (addrExt a s) := by
  unfold graftTLayer
  rw [if_pos (under_ext n' s)]
  simp [addrExt]

theorem graftTLayer_chain (LM : LayeredGarden w) (LX : LayeredGarden 1) (a n' : Fin w × Path) (r : Path)
    (h : ¬ Under n' (addrExt a r)) :
    graftTLayer LM LX a n' (addrExt a r) = layerAt LX ((0 : Fin 1), r) := by
  unfold graftTLayer
  rw [if_neg h, if_pos (under_ext a r)]
  simp [addrExt]

theorem graftTLayer_out (LM : LayeredGarden w) (LX : LayeredGarden 1) (a n' : Fin w × Path) {y : Fin w × Path}
    (h : ¬ Under a y) (hn : Under a n') : graftTLayer LM LX a n' y = layerAt LM y := by
  unfold graftTLayer
  rw [if_neg (fun h' => h (under_trans hn h')), if_neg h]

/-- The layer of a shifted old address is its old layer. -/
theorem graftTLayer_shift (LM : LayeredGarden w) (LX : LayeredGarden 1) (a n' : Fin w × Path) (hn : Under a n')
    (z : Fin w × Path) : graftTLayer LM LX a n' (shiftAddr a n' z) = layerAt LM z := by
  by_cases h : Under a z
  · obtain ⟨s, rfl⟩ := under_of_addrExt h
    rw [shift_ext, graftTLayer_tail]
  · rw [shift_of_not h, graftTLayer_out LM LX a n' h hn]

section Region
variable {M' : Garden w} {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {t : TTree} {LX : LayeredGarden 1}
  (hEN : ChainEmb M' X ζ a t) (hEX : ChainEmb LX.garden X ζ ((0 : Fin 1), ([] : Path)) .leaf)

include hEN hEX

/-- Nodes of the chain region: those of the new garden at `a ⌢ r` and those of `LX` at `r` agree. -/
theorem chainC_node_iff {r : Path} (hr : ¬ X.lonePath <+: r) :
    ((addrExt a r).2 ∈ (M'.tree (addrExt a r).1).nodes ↔ r ∈ (LX.garden.tree 0).nodes) := by
  have hP : ∀ (x : Fin 1 × Path) (q : Path), Under (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) x →
      Under (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) (addrExt x q) := fun x q hx => under_trans hx (under_ext x q)
  have hρ : ∀ (x : Fin 1 × Path) (q : Path), Under (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) x →
      shiftTo (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) a (addrExt x q) =
        addrExt (shiftTo (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) a x) q := fun x q hx => shiftTo_addrExt a hx q
  have hmap := fun z => mem_chainNodesSet_map (fun x : Fin 1 × Path => Under (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) x)
    (shiftTo (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) a) hP hρ X ζ ((0 : Fin 1), ([] : Path)) (under_refl _) z
  rw [shiftTo_self] at hmap
  have hit : InTree a (addrExt a X.lonePath) (addrExt a r) := ⟨under_ext a r, fun h => hr ((under_ext_iff a _ _).1 h)⟩
  have hit' : InTree (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) (addrExt ((0 : Fin 1), ([] : Path)) X.lonePath)
      ((0 : Fin 1), r) := ⟨under_ext _ r, fun h => hr ((under_ext_iff _ _ _).1 h)⟩
  constructor
  · intro hz
    have h1 := hEN.mem_chainNodesSet hz hit
    obtain ⟨y, hy, e⟩ := (hmap _).1 h1
    have hyr : y = ((0 : Fin 1), r) := by
      have e2 := congrArg Prod.snd e
      simp only [shiftTo, addrExt, List.drop_zero, List.append_cancel_left_eq] at e2
      exact Prod.ext (Subsingleton.elim _ _) e2
    subst hyr
    exact hEX.mem_nodes hy
  · intro hz
    have h1 := hEX.mem_chainNodesSet hz hit'
    have h2 := (hmap (addrExt a r)).2 ⟨((0 : Fin 1), r), h1, by simp [shiftTo, addrExt]⟩
    exact hEN.mem_nodes h2

end Region

/-- Garden-level agreement of a tree insertion at `a` (nil chain, tail moved from `a` to `n'`). -/
structure GOutT (G0 G1 : Garden w) (a n' : Fin w × Path) : Prop where
  node : ∀ z : Fin w × Path, z.2 ∈ (G0.tree z.1).nodes ↔
    (shiftAddr a n' z).2 ∈ (G1.tree (shiftAddr a n' z).1).nodes
  leaf : ∀ z : Fin w × Path, z.2 ∈ (G0.tree z.1).leaves ↔
    (shiftAddr a n' z).2 ∈ (G1.tree (shiftAddr a n' z).1).leaves
  pair : ∀ (ℓ : GLeaf G0.tree) (ℓ' : GLeaf G1.tree), shiftAddr a n' ℓ.1 = ℓ'.1 →
    shiftAddr a n' (G0.pair ℓ).1 = (G1.pair ℓ').1

/-- Paired leaves of an embedded chain have equal layers. -/
theorem chainEmb_pair_layer {LG : LayeredGarden w} {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree}
    (hE : ChainEmb LG.garden X ζ a h) {q : (Fin w × Path) × (Fin w × Path)} (hq : q ∈ X.pairsAt ζ a) :
    layerAt LG q.1 = layerAt LG q.2 := by
  have l1 := hE.leaf_of_mem ((mem_pairEndpoints_iff _ _).2 ⟨q, hq, Or.inl rfl⟩)
  have hp := hE.pairs q hq ⟨q.1, l1⟩ rfl
  have n1 := TTree.leaves_subset_nodes _ l1
  have n2 : q.2.2 ∈ (LG.garden.tree q.2.1).nodes := by
    rw [← hp]; exact TTree.leaves_subset_nodes _ (LG.garden.pair ⟨q.1, l1⟩).2
  rw [layerAt_of_mem LG n1, layerAt_of_mem LG n2]
  let ℓ₁ : GLeaf LG.garden.tree := ⟨q.1, l1⟩
  have e1 : (⟨q.1, n1⟩ : GNode LG.garden.tree) = GLeaf.toNode ℓ₁ := rfl
  have e2 : (⟨q.2, n2⟩ : GNode LG.garden.tree) = GLeaf.toNode (LG.garden.pair ℓ₁) :=
    Subtype.ext hp.symm
  rw [e1, e2]
  exact LG.isLayering.2 _

theorem eq_of_under_antisymm {x y : Fin w × Path} (h1 : Under x y) (h2 : Under y x) : x = y := by
  have := eq_of_under_of_length h1 (under_length h2)
  exact this.symm

/-- The old address whose shift is a given new address outside the chain region. -/
theorem exists_unshift (a n' : Fin w × Path) (hn : Under a n') {y : Fin w × Path} (hy : ¬ InTree a n' y) :
    ∃ z, shiftAddr a n' z = y ∧ (Under n' y → z = addrExt a (y.2.drop n'.2.length)) ∧ (¬ Under n' y → z = y) := by
  by_cases h : Under n' y
  · obtain ⟨s, rfl⟩ := under_of_addrExt h
    refine ⟨addrExt a s, ?_, fun _ => ?_, fun h' => absurd h h'⟩
    · exact shift_ext s
    · simp [addrExt]
  · have ha : ¬ Under a y := fun h' => hy ⟨h', h⟩
    exact ⟨y, shift_of_not ha, fun h' => absurd h' h, fun _ => rfl⟩

section Layering
variable {LM : LayeredGarden w} {M' : Garden w} {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {t : TTree}
  {LX : LayeredGarden 1} {p : ℕ}

theorem graftT_child_tail (hOut : GOutT LM.garden M' a (addrExt a X.lonePath)) {x : Fin w × Path} (i : Fin 3)
    (hx : Under (addrExt a X.lonePath) x) (hxn : x.2 ∈ (M'.tree x.1).nodes)
    (hyn : (addrExt x [i]).2 ∈ (M'.tree (addrExt x [i]).1).nodes) :
    graftTLayer LM LX a (addrExt a X.lonePath) (addrExt x [i]) ≤ graftTLayer LM LX a (addrExt a X.lonePath) x := by
  obtain ⟨s, rfl⟩ := under_of_addrExt hx
  have e : addrExt (addrExt a X.lonePath) s = shiftAddr a (addrExt a X.lonePath) (addrExt a s) := (shift_ext s).symm
  have e2 : addrExt (addrExt (addrExt a X.lonePath) s) [i] =
      shiftAddr a (addrExt a X.lonePath) (addrExt (addrExt a s) [i]) := by
    rw [addrExt_append (addrExt a X.lonePath) s [i], addrExt_append a s [i], shift_ext]
  rw [e2] at hyn ⊢
  rw [e] at hxn ⊢
  rw [graftTLayer_shift _ _ _ _ (under_ext _ _), graftTLayer_shift _ _ _ _ (under_ext _ _)]
  exact layerAt_le_of_under LM ((hOut.node _).2 hxn) ((hOut.node _).2 hyn) (under_ext _ _)

theorem graftT_child_chain (hEN : ChainEmb M' X ζ a t) (hEX : ChainEmb LX.garden X ζ ((0 : Fin 1), ([] : Path)) .leaf)
    (hlone : layerAt LX ((0 : Fin 1), X.lonePath) = layerAt LM a) {x : Fin w × Path} (i : Fin 3)
    (hxa : Under a x) (hxn' : ¬ Under (addrExt a X.lonePath) x) (hxn : x.2 ∈ (M'.tree x.1).nodes)
    (hyn : (addrExt x [i]).2 ∈ (M'.tree (addrExt x [i]).1).nodes) :
    graftTLayer LM LX a (addrExt a X.lonePath) (addrExt x [i]) ≤ graftTLayer LM LX a (addrExt a X.lonePath) x := by
  obtain ⟨r, rfl⟩ := under_of_addrExt hxa
  have hr : ¬ X.lonePath <+: r := fun h => hxn' ((under_ext_iff a _ _).2 h)
  rw [graftTLayer_chain _ _ _ _ _ hxn']
  have hrx : r ∈ (LX.garden.tree 0).nodes := (chainC_node_iff hEN hEX hr).1 hxn
  rw [addrExt_append a r [i]] at hyn ⊢
  by_cases hy : Under (addrExt a X.lonePath) (addrExt a (r ++ [i]))
  · have hl : X.lonePath <+: r ++ [i] := (under_ext_iff a _ _).1 hy
    have hp : X.lonePath = r ++ [i] := by
      rcases List.prefix_concat_iff.1 hl with h | h
      · exact h
      · exact absurd h hr
    have he : addrExt a (r ++ [i]) = addrExt a X.lonePath := by rw [hp]
    rw [he]
    have h1 := graftTLayer_tail LM LX a (addrExt a X.lonePath) []
    rw [addrExt_nil, addrExt_nil] at h1
    rw [h1, ← hlone]
    have hlnode : X.lonePath ∈ (LX.garden.tree 0).nodes := by
      have := nodeOfChainEmb hEX
      simpa [addrExt] using this
    have hu : Under (((0 : Fin 1), r) : Fin 1 × Path) ((0 : Fin 1), X.lonePath) := by
      refine ⟨rfl, ?_⟩
      rw [hp]
      exact List.prefix_append _ _
    exact layerAt_le_of_under LX hrx hlnode hu
  · have hr' : ¬ X.lonePath <+: r ++ [i] := fun h => hy ((under_ext_iff a _ _).2 h)
    rw [graftTLayer_chain _ _ _ _ _ hy]
    have hrx' : r ++ [i] ∈ (LX.garden.tree 0).nodes := (chainC_node_iff hEN hEX hr').1 hyn
    exact layerAt_le_of_under LX hrx hrx' ⟨rfl, List.prefix_append _ _⟩

theorem graftT_child_out (hEO : ChainEmb LM.garden .nil ζ a t)
    (hOut : GOutT LM.garden M' a (addrExt a X.lonePath))
    (hroot : layerAt LX ((0 : Fin 1), ([] : Path)) ≤ parAt LM p a) {x : Fin w × Path} (i : Fin 3)
    (hxa : ¬ Under a x) (hxn : x.2 ∈ (M'.tree x.1).nodes)
    (hyn : (addrExt x [i]).2 ∈ (M'.tree (addrExt x [i]).1).nodes) :
    graftTLayer LM LX a (addrExt a X.lonePath) (addrExt x [i]) ≤ graftTLayer LM LX a (addrExt a X.lonePath) x := by
  have hn : Under a (addrExt a X.lonePath) := under_ext a _
  rw [graftTLayer_out LM LX a _ hxa hn]
  have hxM : x.2 ∈ (LM.garden.tree x.1).nodes := (hOut.node x).2 (by rw [shift_of_not hxa]; exact hxn)
  by_cases hya : Under a (addrExt x [i])
  · have e := eq_of_under_child i hya hxa
    have haM : a.2 ∈ (LM.garden.tree a.1).nodes := hEO.node
    by_cases hna : Under (addrExt a X.lonePath) a
    · have hnaeq : a = addrExt a X.lonePath := eq_of_under_antisymm hn hna
      have h1 := graftTLayer_tail LM LX a (addrExt a X.lonePath) []
      rw [addrExt_nil, addrExt_nil] at h1
      rw [← e]
      have h2 : graftTLayer LM LX a (addrExt a X.lonePath) a = layerAt LM a :=
        (congrArg (graftTLayer LM LX a (addrExt a X.lonePath)) hnaeq).trans h1
      rw [h2]
      have hxy : Under x a := by rw [e]; exact under_ext x [i]
      exact layerAt_le_of_under LM hxM haM hxy
    · rw [← e]
      have hn2 : ¬ Under (addrExt a X.lonePath) (addrExt a []) := by rw [addrExt_nil]; exact hna
      have h1 := graftTLayer_chain LM LX a (addrExt a X.lonePath) [] hn2
      rw [addrExt_nil] at h1
      rw [h1]
      have hpar := parAt_child LM p i (x := x) (by rw [← e]; exact haM)
      rw [← e] at hpar
      exact hroot.trans hpar.le
  · rw [graftTLayer_out LM LX a _ hya hn]
    have hyM : (addrExt x [i]).2 ∈ (LM.garden.tree (addrExt x [i]).1).nodes :=
      (hOut.node _).2 (by rw [shift_of_not hya]; exact hyn)
    exact layerAt_le_of_under LM hxM hyM (under_ext x [i])

theorem graftT_reloc_layer (hEX : ChainEmb LX.garden X ζ ((0 : Fin 1), ([] : Path)) .leaf) {a : Fin w × Path}
    (LM : LayeredGarden w) {z : Fin 1 × Path} (hz : z ∈ pairEndpoints (X.pairsAt ζ ((0 : Fin 1), ([] : Path)))) :
    graftTLayer LM LX a (addrExt a X.lonePath) (shiftTo (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) a z) =
      layerAt LX z := by
  have hn := chain_pairs_not_under_lone X ζ ((0 : Fin 1), ([] : Path)) z hz
  have hz' : z = ((0 : Fin 1), z.2) := Prod.ext (Subsingleton.elim _ _) rfl
  have e : shiftTo (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) a z = addrExt a z.2 := by simp [shiftTo, addrExt]
  rw [e]
  have hn' : ¬ Under (addrExt a X.lonePath) (addrExt a z.2) := fun h => hn (by
    have := (under_ext_iff a _ _).1 h
    refine ⟨Subsingleton.elim _ _, ?_⟩
    simpa [addrExt] using this)
  rw [graftTLayer_chain LM LX a _ _ hn', ← hz']

theorem graftT_pair (hEN : ChainEmb M' X ζ a t) (hEX : ChainEmb LX.garden X ζ ((0 : Fin 1), ([] : Path)) .leaf)
    (hOut : GOutT LM.garden M' a (addrExt a X.lonePath)) (ℓ : GLeaf M'.tree) :
    graftTLayer LM LX a (addrExt a X.lonePath) ℓ.1 =
      graftTLayer LM LX a (addrExt a X.lonePath) (M'.pair ℓ).1 := by
  have hn : Under a (addrExt a X.lonePath) := under_ext a _
  by_cases hC : InTree a (addrExt a X.lonePath) ℓ.1
  · obtain ⟨q, hq, h⟩ := hEN.partner ℓ hC
    have hP : ∀ (x : Fin 1 × Path) (q : Path), Under (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) x →
        Under (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) (addrExt x q) := fun x q hx => under_trans hx (under_ext x q)
    have hρ : ∀ (x : Fin 1 × Path) (q : Path), Under (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) x →
        shiftTo (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) a (addrExt x q) =
          addrExt (shiftTo (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) a x) q := fun x q hx => shiftTo_addrExt a hx q
    have hmap := chain_pairs_map (fun x : Fin 1 × Path => Under (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) x)
      (shiftTo (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) a) hP hρ X ζ ((0 : Fin 1), ([] : Path)) (under_refl _)
    rw [shiftTo_self] at hmap
    rw [hmap, List.mem_map] at hq
    obtain ⟨l, hl, rfl⟩ := hq
    have h1 := graftT_reloc_layer (a := a) hEX LM (mem_pairEndpoints_fst hl)
    have h2 := graftT_reloc_layer (a := a) hEX LM (mem_pairEndpoints_snd hl)
    have h3 := chainEmb_pair_layer hEX hl
    rcases h with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]; simp only; rw [h1, h2]; exact h3
    · rw [e1, e2]; simp only; rw [h1, h2]; exact h3.symm
  · obtain ⟨z, hz, -, -⟩ := exists_unshift a (addrExt a X.lonePath) hn hC
    have hzl : z.2 ∈ (LM.garden.tree z.1).leaves := (hOut.leaf z).2 (by rw [hz]; exact ℓ.2)
    let ℓ0 : GLeaf LM.garden.tree := ⟨z, hzl⟩
    have hp := hOut.pair ℓ0 ℓ hz
    have h1 := LM.isLayering.2 ℓ0
    rw [← layerAt_node, ← layerAt_node] at h1
    change layerAt LM z = layerAt LM (LM.garden.pair ℓ0).1 at h1
    rw [← hz, ← hp, graftTLayer_shift LM LX a _ hn, graftTLayer_shift LM LX a _ hn]
    exact h1

/-- **The tree graft layering.** -/
theorem graftT_isLayering (hEO : ChainEmb LM.garden .nil ζ a t) (hEN : ChainEmb M' X ζ a t)
    (hEX : ChainEmb LX.garden X ζ ((0 : Fin 1), ([] : Path)) .leaf)
    (hOut : GOutT LM.garden M' a (addrExt a X.lonePath))
    (hlone : layerAt LX ((0 : Fin 1), X.lonePath) = layerAt LM a)
    (hroot : layerAt LX ((0 : Fin 1), ([] : Path)) ≤ parAt LM p a) :
    IsLayering M' (fun n : GNode M'.tree => graftTLayer LM LX a (addrExt a X.lonePath) n.1) := by
  constructor
  · intro br i
    have hxn := TTree.branching_subset_nodes _ br.2
    have hyn := (br.child i).2
    by_cases hx : Under (addrExt a X.lonePath) br.1
    · exact graftT_child_tail hOut i hx hxn hyn
    · by_cases hxa : Under a br.1
      · exact graftT_child_chain hEN hEX hlone i hxa hx hxn hyn
      · exact graftT_child_out hEO hOut hroot i hxa hxn hyn
  · intro ℓ
    exact graftT_pair hEN hEX hOut ℓ

section Graft
variable (hEO : ChainEmb LM.garden .nil ζ a t) (hEN : ChainEmb M' X ζ a t)
  (hEX : ChainEmb LX.garden X ζ ((0 : Fin 1), ([] : Path)) .leaf)
  (hOut : GOutT LM.garden M' a (addrExt a X.lonePath))
  (hlone : layerAt LX ((0 : Fin 1), X.lonePath) = layerAt LM a)
  (hroot : layerAt LX ((0 : Fin 1), ([] : Path)) ≤ parAt LM p a)

/-- The layered garden obtained by grafting the layered tree `LX` into `LM`. -/
@[expose] noncomputable def graftT : LayeredGarden w :=
  ⟨M', fun n : GNode M'.tree => graftTLayer LM LX a (addrExt a X.lonePath) n.1,
    graftT_isLayering hEO hEN hEX hOut hlone hroot⟩

include hEO hEN hEX hOut hlone hroot in
theorem graftT_layerAt_node {z : Fin w × Path} (hz : z.2 ∈ (M'.tree z.1).nodes) :
    layerAt (graftT hEO hEN hEX hOut hlone hroot) z = graftTLayer LM LX a (addrExt a X.lonePath) z :=
  layerAt_of_mem _ hz

include hEO hEN hEX hOut hlone hroot in
theorem graftT_layerAt_tail (s : Path) :
    layerAt (graftT hEO hEN hEX hOut hlone hroot) (addrExt (addrExt a X.lonePath) s) =
      layerAt LM (addrExt a s) := by
  have hnode := hOut.node (addrExt a s)
  rw [shift_ext] at hnode
  by_cases h : (addrExt (addrExt a X.lonePath) s).2 ∈ (M'.tree (addrExt (addrExt a X.lonePath) s).1).nodes
  · rw [graftT_layerAt_node hEO hEN hEX hOut hlone hroot h, graftTLayer_tail]
  · have h' : (addrExt a s).2 ∉ (LM.garden.tree (addrExt a s).1).nodes := fun hh => h (hnode.1 hh)
    have e1 : layerAt (graftT hEO hEN hEX hOut hlone hroot) (addrExt (addrExt a X.lonePath) s) = 0 := by
      unfold layerAt; exact dif_neg h
    have e2 : layerAt LM (addrExt a s) = 0 := by
      unfold layerAt; exact dif_neg h'
    rw [e1, e2]

include hEO hEN hEX hOut hlone hroot in
theorem graftT_layerAt_out {z : Fin w × Path} (hz : ¬ Under a z) :
    layerAt (graftT hEO hEN hEX hOut hlone hroot) z = layerAt LM z := by
  have hnode := hOut.node z
  rw [shift_of_not hz] at hnode
  by_cases h : z.2 ∈ (M'.tree z.1).nodes
  · rw [graftT_layerAt_node hEO hEN hEX hOut hlone hroot h, graftTLayer_out _ _ _ _ hz (under_ext a _)]
  · have h' : z.2 ∉ (LM.garden.tree z.1).nodes := fun hh => h (hnode.1 hh)
    have e1 : layerAt (graftT hEO hEN hEX hOut hlone hroot) z = 0 := by
      unfold layerAt; exact dif_neg h
    have e2 : layerAt LM z = 0 := by
      unfold layerAt; exact dif_neg h'
    rw [e1, e2]

include hEO hEN hEX hOut hlone hroot in
theorem graftT_layerAt_chain {r : Path} (hr : ¬ X.lonePath <+: r) :
    layerAt (graftT hEO hEN hEX hOut hlone hroot) (addrExt a r) = layerAt LX ((0 : Fin 1), r) := by
  have hn : ¬ Under (addrExt a X.lonePath) (addrExt a r) := fun h => hr ((under_ext_iff a _ _).1 h)
  by_cases h : (addrExt a r).2 ∈ (M'.tree (addrExt a r).1).nodes
  · rw [graftT_layerAt_node hEO hEN hEX hOut hlone hroot h, graftTLayer_chain _ _ _ _ _ hn]
  · have h' : r ∉ (LX.garden.tree 0).nodes := fun hh => h ((chainC_node_iff hEN hEX hr).2 hh)
    have e1 : layerAt (graftT hEO hEN hEX hOut hlone hroot) (addrExt a r) = 0 := by
      unfold layerAt; exact dif_neg h
    have e2 : layerAt LX ((0 : Fin 1), r) = 0 := by
      unfold layerAt; exact dif_neg h'
    rw [e1, e2]

include hEO hEN hEX hOut hlone hroot in
theorem graftT_outAgree :
    OutAgreeT LM (graftT hEO hEN hEX hOut hlone hroot) a a (addrExt a X.lonePath) where
  node := fun z _ => hOut.node z
  leaf := fun z _ => hOut.leaf z
  layer := by
    intro z _
    by_cases h : Under a z
    · obtain ⟨s, rfl⟩ := under_of_addrExt h
      rw [shift_ext, graftT_layerAt_tail]
    · rw [shift_of_not h, graftT_layerAt_out hEO hEN hEX hOut hlone hroot h]
  pair := fun ℓ ℓ' _ he => hOut.pair ℓ ℓ' he

include hEO hEN hEX hOut hlone hroot in
theorem graftT_parAt : parAt (graftT hEO hEN hEX hOut hlone hroot) p a = parAt LM p a := by
  symm
  refine parAt_eq_of hEO.node (hEN.node) Iff.rfl ?_
  intro x k hk
  refine ⟨x, hk, ?_⟩
  have hx : ¬ Under a x := by
    intro h
    have := under_length h
    rw [hk] at this
    simp [addrExt] at this
  rw [graftT_layerAt_out hEO hEN hEX hOut hlone hroot hx]

include hEO hEN hEX hOut hlone hroot in
theorem graftT_pattern_iff :
    TreePattern (graftT hEO hEN hEX hOut hlone hroot) p X ζ a ↔
      TreePatternN LX (parAt (graftT hEO hEN hEX hOut hlone hroot) p a) X ζ ((0 : Fin 1), ([] : Path)) := by
  rw [treePattern_eq_N]
  have hP : ∀ (x : Fin 1 × Path) (q : Path), Under (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) x →
      Under (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) (addrExt x q) := fun x q hx => under_trans hx (under_ext x q)
  have hρ : ∀ (x : Fin 1 × Path) (q : Path), Under (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) x →
      shiftTo (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) a (addrExt x q) =
        addrExt (shiftTo (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) a x) q := fun x q hx => shiftTo_addrExt a hx q
  let Rg : Fin 1 × Path → Prop := fun z =>
    z ∈ chainNodesSet X ζ ((0 : Fin 1), ([] : Path)) ∨ z = addrExt ((0 : Fin 1), ([] : Path)) X.lonePath
  have hlay : ∀ z, Under (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) z → Rg z →
      layerAt (graftT hEO hEN hEX hOut hlone hroot)
        (shiftTo (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) a z) = layerAt LX z := by
    intro z hz hR
    obtain ⟨r, rfl⟩ := under_of_addrExt hz
    rw [shiftTo_addrExt_self]
    have hlone' : addrExt ((0 : Fin 1), ([] : Path)) r = ((0 : Fin 1), r) := by simp [addrExt]
    rw [hlone']
    by_cases hl : X.lonePath <+: r
    · -- r is the lone path
      have hreg : ¬ SUnder (addrExt ((0 : Fin 1), ([] : Path)) X.lonePath) (addrExt ((0 : Fin 1), ([] : Path)) r) := by
        rcases hR with hR | hR
        · exact (chain_endpoints_region X ζ _ _ hR).2
        · intro h; exact h.2 hR
      have hrl : r = X.lonePath := by
        by_contra hne
        apply hreg
        refine ⟨⟨rfl, ?_⟩, ?_⟩
        · simpa [addrExt] using hl
        · intro h
          apply hne
          have := congrArg Prod.snd h
          simpa [addrExt] using this
      subst hrl
      have h1 := graftT_layerAt_tail hEO hEN hEX hOut hlone hroot []
      rw [addrExt_nil, addrExt_nil] at h1
      rw [h1, hlone]
    · exact graftT_layerAt_chain hEO hEN hEX hOut hlone hroot hl
  have hmap := treePatternN_mapR (fun x : Fin 1 × Path => Under (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) x)
    (shiftTo (((0 : Fin 1), ([] : Path)) : Fin 1 × Path) a) Rg hP hρ hlay
    (parAt (graftT hEO hEN hEX hOut hlone hroot) p a) X ζ ((0 : Fin 1), ([] : Path)) (under_refl _)
    (fun z hz => Or.inl hz) (Or.inr rfl)
  rw [shiftTo_self] at hmap
  exact hmap

end Graft

end Layering

end WaveTurbulence.ZpSurj
