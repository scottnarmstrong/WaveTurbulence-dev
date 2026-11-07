/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.CohCount
public import WaveTurbulence.Foundations.RegStruct.DecodedTreeProperties
public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.LayerReg2Tree

/-! # P4 count bridge (2): coherent embedded regular trees with root parent `q` and lone-leaf layer `q'` (TARGET `layerreg2`)

The tree analogue of `CohCount`: C4's `layerreg2_tree` is relocated from the ambient addresses of `IsCoherentTreeAt` to the standard
address `(0,[])` of the standalone tree.  The lone leaf is not a node of the chain (`chainNodesSet`); its layer is the fixed `q'`.

* `TreeRules`, `tree_determined_of_drops`: C4's `tree_layering_determined` from the rules only.
* `tree_trace_facts`: the standard trace of a coherent tree obeys the rules with drop budget `≤ q - q'`.
* **`ncard_coherentTrees_le`**: the coherent layered trees of root sign `ζ`, order `2m`, parents `(q, q')` number at most
  `(12^9)^m · 2^{2m + (q - q')}`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4
open WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine TTree

set_option linter.unusedSectionVars false

/-- The standard root address of a tree. -/
abbrev t₀ : Fin 1 × Path := ((0 : Fin 1), ([] : Path))

section Reloc
variable {w : ℕ}

/-- The standard addresses of a tree to the address `a` of an ambient garden. -/
def relocT (a : Fin w × Path) (z : Fin 1 × Path) : Fin w × Path := addrExt a z.2

theorem relocT_ext (a : Fin w × Path) (x : Fin 1 × Path) (q : Path) : relocT a (addrExt x q) = addrExt (relocT a x) q := by
  unfold relocT addrExt
  simp [List.append_assoc]

theorem relocT_t₀ (a : Fin w × Path) : relocT a t₀ = a := by simp [relocT, addrExt]

theorem chainLinks_relocT (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    X.linksAt ζ a = (X.linksAt ζ t₀).map (fun l => (relocT a l.1, relocT a l.2)) := by
  have := WaveTurbulence.ZpSurj.chain_links_map (fun _ => True) (relocT a) (fun _ _ _ => trivial)
    (fun x q _ => relocT_ext a x q) X ζ t₀ trivial
  rwa [relocT_t₀] at this

theorem chainPairs_relocT (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    X.pairsAt ζ a = (X.pairsAt ζ t₀).map (fun l => (relocT a l.1, relocT a l.2)) := by
  have := WaveTurbulence.ZpSurj.chain_pairs_map (fun _ => True) (relocT a) (fun _ _ _ => trivial)
    (fun x q _ => relocT_ext a x q) X ζ t₀ trivial
  rwa [relocT_t₀] at this

theorem mem_pairEndpoints_mapT {L : List ((Fin 1 × Path) × (Fin 1 × Path))} (ρ : Fin 1 × Path → Fin w × Path)
    {z : Fin 1 × Path} (hz : z ∈ pairEndpoints L) : ρ z ∈ pairEndpoints (L.map fun l => (ρ l.1, ρ l.2)) := by
  obtain ⟨l, hl, h⟩ := (mem_pairEndpoints_iff _ _).1 hz
  refine (mem_pairEndpoints_iff _ _).2 ⟨(ρ l.1, ρ l.2), List.mem_map.2 ⟨l, hl, rfl⟩, ?_⟩
  rcases h with h | h <;> subst h <;> simp

theorem pairEndpoints_mapT_eq {L : List ((Fin 1 × Path) × (Fin 1 × Path))} (ρ : Fin 1 × Path → Fin w × Path) :
    pairEndpoints (L.map fun l => (ρ l.1, ρ l.2)) = (pairEndpoints L).image ρ := by
  classical
  ext y
  rw [mem_pairEndpoints_iff, Finset.mem_image]
  constructor
  · rintro ⟨l', hl', h⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
    rcases h with h | h
    · exact ⟨l.1, (mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inl rfl⟩, h.symm⟩
    · exact ⟨l.2, (mem_pairEndpoints_iff _ _).2 ⟨l, hl, Or.inr rfl⟩, h.symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact (mem_pairEndpoints_iff _ _).1 (mem_pairEndpoints_mapT ρ hz)

theorem relocT_mem_chainNodes (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) {z : Fin 1 × Path}
    (hz : z ∈ chainNodesSet X ζ t₀) : relocT a z ∈ chainNodesSet X ζ a := by
  unfold chainNodesSet at hz ⊢
  rcases Finset.mem_union.1 hz with h | h
  · exact Finset.mem_union_left _ (by rw [chainLinks_relocT]; exact mem_pairEndpoints_mapT _ h)
  · exact Finset.mem_union_right _ (by rw [chainPairs_relocT]; exact mem_pairEndpoints_mapT _ h)

theorem relocT_injective (a : Fin w × Path) : Function.Injective (relocT a) := by
  rintro ⟨i, r⟩ ⟨i', r'⟩ h
  unfold relocT addrExt at h
  simp only [Prod.mk.injEq, List.append_cancel_left_eq, true_and] at h
  have : i = i' := Subsingleton.elim _ _
  rw [this, h]

end Reloc

section Determined
variable {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (q : ℕ)

/-- The rules of a layering of a placed chain, read off its values. -/
structure TreeRules (f : Fin w × Path → ℕ) : Prop where
  below : ∀ z ∈ pairEndpoints (X.linksAt ζ a), f z ≤ parT a q f z
  leaf : ∀ qq ∈ X.pairsAt ζ a, f qq.1 = min (parT a q f qq.1) (parT a q f qq.2) ∧
    f qq.2 = min (parT a q f qq.1) (parT a q f qq.2)
  off : ∀ z ∉ chainNodesSet X ζ a, f z = 0

/-- **A chain layering is determined by its drops** (C4's `tree_layering_determined`, from the rules only). -/
theorem tree_determined_of_drops {f f' : Fin w × Path → ℕ} (hf : TreeRules X ζ a q f) (hf' : TreeRules X ζ a q f')
    (hd : dropT (pairEndpoints (X.linksAt ζ a)) a q f = dropT (pairEndpoints (X.linksAt ζ a)) a q f') : f = f' := by
  set B := pairEndpoints (X.linksAt ζ a)
  have hpar : ∀ z ∈ chainNodesSet X ζ a, (z ≠ a → f (parentAddr z) = f' (parentAddr z)) →
      parT a q f z = parT a q f' z := by
    intro z _ hh
    unfold parT
    by_cases hza : z = a
    · simp [hza]
    · simp only [hza, ↓reduceIte]; exact hh hza
  have e : ∀ {g : Fin w × Path → ℕ}, TreeRules X ζ a q g → ∀ z ∈ B, g z = parT a q g z - dropT B a q g z := by
    intro g hg z hz
    unfold dropT; rw [if_pos hz]
    have := hg.below z hz; omega
  have hbr : ∀ n, ∀ z ∈ B, z.2.length ≤ n → f z = f' z := by
    intro n
    induction n with
    | zero =>
      intro z hz hl
      have hzn := chain_links_sub_nodes hz
      rw [e hf z hz, e hf' z hz, hd]
      congr 1
      apply hpar z hzn
      intro hza
      exfalso
      obtain ⟨-, i, hzi⟩ := chain_parent_mem .leaf hzn hza
      have := congrArg (fun x : Fin w × Path => x.2.length) hzi
      simp [addrExt] at this; omega
    | succ n ih =>
      intro z hz hl
      have hzn := chain_links_sub_nodes hz
      rw [e hf z hz, e hf' z hz, hd]
      congr 1
      apply hpar z hzn
      intro hza
      obtain ⟨hpm, i, hzi⟩ := chain_parent_mem .leaf hzn hza
      apply ih _ hpm
      have := congrArg (fun x : Fin w × Path => x.2.length) hzi
      simp [addrExt] at this
      simp [parentAddr]; omega
  have hbr' : ∀ z ∈ B, f z = f' z := fun z hz => hbr _ z hz le_rfl
  have hpar' : ∀ z ∈ chainNodesSet X ζ a, parT a q f z = parT a q f' z := fun z hz =>
    hpar z hz fun hza => hbr' _ (chain_parent_mem .leaf hz hza).1
  funext z
  by_cases hz : z ∈ chainNodesSet X ζ a
  · rcases Finset.mem_union.1 hz with hl | hl
    · exact hbr' z hl
    · obtain ⟨qq, hq, hzq⟩ := (mem_pairEndpoints_iff _ _).1 hl
      have m1 : qq.1 ∈ chainNodesSet X ζ a := chain_pairs_sub_nodes ((mem_pairEndpoints_iff _ _).2 ⟨qq, hq, Or.inl rfl⟩)
      have m2 : qq.2 ∈ chainNodesSet X ζ a := chain_pairs_sub_nodes ((mem_pairEndpoints_iff _ _).2 ⟨qq, hq, Or.inr rfl⟩)
      rcases hzq with rfl | rfl
      · rw [(hf.leaf qq hq).1, (hf'.leaf qq hq).1, hpar' _ m1, hpar' _ m2]
      · rw [(hf.leaf qq hq).2, (hf'.leaf qq hq).2, hpar' _ m1, hpar' _ m2]
  · rw [hf.off z hz, hf'.off z hz]

end Determined

section Trace

/-- The standard trace of a layered tree on the nodes of its chain. -/
noncomputable def treeLayerTrace (X : RegChain) (ζ : ℤˣ) (LX : LayeredGarden 1) (z : Fin 1 × Path) : ℕ :=
  if z ∈ chainNodesSet X ζ t₀ then layerAt LX z else 0

/-- **The standard trace of a coherent tree obeys the rules, with drop budget `q - q'`.** -/
theorem tree_trace_facts {p q q' : ℕ} {X : RegChain} {LX : LayeredGarden 1} (h : IsCoherentTreeAt p q q' X LX) :
    TreeRules X (LX.garden.sig 0) t₀ q (treeLayerTrace X (LX.garden.sig 0) LX) ∧
      ∑ z ∈ pairEndpoints (X.linksAt (LX.garden.sig 0) t₀),
          dropT (pairEndpoints (X.linksAt (LX.garden.sig 0) t₀)) t₀ q (treeLayerTrace X (LX.garden.sig 0) LX) z ≤ q - q' := by
  classical
  obtain ⟨hwf, hX, w, H, a, hh, hcan, hC, -, hcoh, hpa, hlone, hlay⟩ := h
  obtain ⟨hplain, -, hcrit⟩ := hcan
  set ζ := LX.garden.sig 0 with hζ
  have hC0 : ChainEmb LX.garden X ζ t₀ .leaf := ChainEmb.of_decodesTree hX
  set f := treeLayerTrace X ζ LX with hfdef
  set ρ := relocT a with hρ
  have hval : ∀ z ∈ chainNodesSet X ζ t₀, f z = layerAt H (ρ z) := by
    intro z hz
    have hn := hC0.mem_nodes hz
    rw [hfdef, treeLayerTrace, if_pos hz, layerAt_of_mem LX hn]
    exact hlay ⟨z, hn⟩
  have hmemH : ∀ z ∈ chainNodesSet X ζ t₀, (ρ z).2 ∈ (H.garden.tree (ρ z).1).nodes := fun z hz =>
    hC.mem_nodes (relocT_mem_chainNodes X ζ a hz)
  have hpar : ∀ z ∈ chainNodesSet X ζ t₀, parT t₀ q f z = parAt H p (ρ z) := by
    intro z hz
    unfold parT
    by_cases hza : z = t₀
    · rw [if_pos hza, hza, hρ, relocT_t₀, hpa]
    · rw [if_neg hza]
      obtain ⟨hpm, i, hzi⟩ := chain_parent_mem .leaf hz hza
      rw [hval _ (chain_links_sub_nodes hpm)]
      have hz' : ρ z = addrExt (ρ (parentAddr z)) [i] := by
        rw [hρ, ← relocT_ext]; exact congrArg _ hzi
      have hn' : (addrExt (ρ (parentAddr z)) [i]).2 ∈ (H.garden.tree (addrExt (ρ (parentAddr z)) [i]).1).nodes := by
        rw [← hz']; exact hmemH z hz
      rw [hz', parAt_child H p i hn']
  refine ⟨⟨fun z hz => ?_, fun qq hq => ?_, fun z hz => ?_⟩, ?_⟩
  · have hzn := chain_links_sub_nodes hz
    rw [hval z hzn, hpar z hzn]
    exact layerAt_le_parAt H p hcrit.1 (hmemH z hzn)
  · have m1 : qq.1 ∈ chainNodesSet X ζ t₀ := chain_pairs_sub_nodes ((mem_pairEndpoints_iff _ _).2 ⟨qq, hq, Or.inl rfl⟩)
    have m2 : qq.2 ∈ chainNodesSet X ζ t₀ := chain_pairs_sub_nodes ((mem_pairEndpoints_iff _ _).2 ⟨qq, hq, Or.inr rfl⟩)
    have hqH : (ρ qq.1, ρ qq.2) ∈ X.pairsAt ζ a := by
      rw [chainPairs_relocT]; exact List.mem_map.2 ⟨qq, hq, rfl⟩
    have T := hC.triv_of_pair hplain hqH
    have L1 := (cpl_coherent hcrit hplain .triv (ρ qq.1) (ρ qq.2) rfl T (by simp [CohOn, RegCpl.linksAt])).1 rfl
    rw [hval _ m1, hval _ m2, hpar _ m1, hpar _ m2]
    exact ⟨L1 _ (mem_cplNodes_triv.2 (Or.inl rfl)), L1 _ (mem_cplNodes_triv.2 (Or.inr rfl))⟩
  · rw [hfdef, treeLayerTrace, if_neg hz]
  · have hB : pairEndpoints (X.linksAt ζ a) = (pairEndpoints (X.linksAt ζ t₀)).image ρ := by
      rw [chainLinks_relocT, pairEndpoints_mapT_eq]
    have hbud := chain_budget hcrit hplain X ζ a hh hwf hC
    have hlone' : q' ≤ parAt H p (addrExt a X.lonePath) := by
      rw [← hlone]; exact layerAt_le_parAt H p hcrit.1 (nodeOfChainEmb hC)
    have hinc := incohCount_chain (LG := H) X ζ a
    rw [incohCount_zero_of_cohOn hcoh] at hinc
    rw [hpa] at hbud
    have hT : budget H p (pairEndpoints (X.linksAt ζ a)) ≤ q - q' := by
      have h1 : headIncoh H X ζ a = 0 := by omega
      have h2 : couplesIncoh H X ζ a = 0 := by omega
      rw [h1, h2] at hbud
      simp only [mul_zero, add_zero] at hbud
      omega
    rw [hB, budget, Finset.sum_image (fun x _ y _ hxy => relocT_injective a hxy)] at hT
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun z hz => ?_)) hT
    have hzn := chain_links_sub_nodes hz
    unfold dropT dropAt
    rw [if_pos hz, hpar z hzn, hval z hzn]

/-- Every node of a decoded tree carrier is a node of its chain, or the lone leaf. -/
theorem chainNodes_or_lone {X : RegChain} {G : Garden 1} (hX : X.DecodesTree G) (z : GNode G.tree) :
    z.1 ∈ chainNodesSet X (G.sig 0) t₀ ∨ z.1 = ((0 : Fin 1), X.lonePath) := by
  rcases z with ⟨⟨i, path⟩, hp⟩
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  have htree : G.tree 0 = X.plug (G.sig 0) .leaf := hX.1
  rcases (TTree.mem_nodes_iff _ _).mp hp with hl | hb
  · have hl' : path ∈ (X.plug (G.sig 0) .leaf).leaves := by rw [← htree]; exact hl
    have hm : ((0 : Fin 1), path) ∈ leafAddresses (X.plug (G.sig 0) .leaf) t₀ :=
      Finset.mem_image.2 ⟨path, hl', by simp [addrExt]⟩
    rw [chain_leafAddresses] at hm
    rcases Finset.mem_union.1 hm with h1 | h1
    · exact Or.inl (chain_pairs_sub_nodes h1)
    · right
      simpa [leafAddresses, TTree.leaves, addrExt] using h1
  · have hb' : path ∈ (X.plug (G.sig 0) .leaf).branching := by rw [← htree]; exact hb
    have hm : ((0 : Fin 1), path) ∈ branchAddresses (X.plug (G.sig 0) .leaf) t₀ :=
      Finset.mem_image.2 ⟨path, hb', by simp [addrExt]⟩
    rw [chain_branchAddresses] at hm
    rcases Finset.mem_union.1 hm with h1 | h1
    · exact Or.inl (chain_links_sub_nodes h1)
    · simp at h1

/-- The lone leaf of a coherent tree is in layer `q'`. -/
theorem lone_layer {p q q' : ℕ} {X : RegChain} {LX : LayeredGarden 1} (h : IsCoherentTreeAt p q q' X LX)
    (z : GNode LX.garden.tree) (hz : z.1 = ((0 : Fin 1), X.lonePath)) : LX.layer z = q' := by
  obtain ⟨-, -, w, H, a, hh, -, -, -, -, -, hlone, hlay⟩ := h
  rw [hlay, ← hlone, hz]

theorem treeLayerTrace_injective {p q q' : ℕ} {X : RegChain} {LX LX' : LayeredGarden 1}
    (h : IsCoherentTreeAt p q q' X LX) (h' : IsCoherentTreeAt p q q' X LX') (hs : LX.garden.sig 0 = LX'.garden.sig 0)
    (he : treeLayerTrace X (LX.garden.sig 0) LX = treeLayerTrace X (LX'.garden.sig 0) LX') : LX = LX' := by
  have hG : LX.garden = LX'.garden := by
    rw [decodedTree_unique X (LX.garden.sig 0) LX.garden h.2.1 rfl,
      decodedTree_unique X (LX.garden.sig 0) LX'.garden h'.2.1 hs.symm]
  have hlone := lone_layer h
  have hlone' := lone_layer h'
  have hX := h.2.1
  rcases LX with ⟨G, l, hl⟩
  rcases LX' with ⟨G', l', hl'⟩
  dsimp only at hG hlone hlone' he hs hX
  subst G'
  have hlayers : l = l' := by
    funext z
    rcases chainNodes_or_lone hX z with hz | hz
    · have := congrFun he z.1
      simpa only [treeLayerTrace, if_pos hz, layerAt_node] using this
    · rw [hlone z hz, hlone' z hz]
  subst l'
  rfl

end Trace

section Count

/-- The coherent layered trees of a code with root sign `ζ` and parents `(q, q')`. -/
def coherentTreesOf (p q q' : ℕ) (ζ : ℤˣ) (X : RegChain) : Set (LayeredGarden 1) :=
  {LX | IsCoherentTreeAt p q q' X LX ∧ LX.garden.sig 0 = ζ}

theorem ncard_coherentTreesOf_le (p q q' : ℕ) (ζ : ℤˣ) (X : RegChain) :
    (coherentTreesOf p q q' ζ X).Finite ∧ (coherentTreesOf p q q' ζ X).ncard ≤ 2 ^ (X.size + (q - q')) := by
  classical
  set B := pairEndpoints (X.linksAt ζ t₀)
  set T := q - q'
  have hmap : ∀ LX ∈ coherentTreesOf p q q' ζ X, dropT B t₀ q (treeLayerTrace X ζ LX) ∈ boundedVecs B T := by
    rintro LX ⟨hLX, hs⟩
    refine ⟨fun z hz => by unfold dropT; rw [if_neg hz], ?_⟩
    have := (tree_trace_facts hLX).2
    rw [hs] at this
    exact this
  have hinj : Set.InjOn (fun LX => dropT B t₀ q (treeLayerTrace X ζ LX)) (coherentTreesOf p q q' ζ X) := by
    rintro LX ⟨hLX, hs⟩ LX' ⟨hLX', hs'⟩ hd
    have r1 := (tree_trace_facts hLX).1
    have r2 := (tree_trace_facts hLX').1
    rw [hs] at r1
    rw [hs'] at r2
    refine treeLayerTrace_injective hLX hLX' (hs.trans hs'.symm) ?_
    rw [hs, hs']
    exact tree_determined_of_drops X ζ t₀ q r1 r2 hd
  have hfin := (boundedVecs_spec B T).1
  refine ⟨Set.Finite.of_injOn hmap hinj hfin, ?_⟩
  have hcard := Set.ncard_le_ncard_of_injOn _ hmap hinj hfin
  have hBc : B.card ≤ X.size := by
    have h1 : B.card ≤ 2 * (X.linksAt ζ t₀).length := pairEndpoints_card_le _
    have h2 := chain_linksAt_length X ζ t₀
    omega
  calc _ ≤ (boundedVecs B T).ncard := hcard
    _ ≤ 2 ^ (B.card + T) := (boundedVecs_spec B T).2
    _ ≤ 2 ^ (X.size + T) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem finite_chainCodes (m : ℕ) : Finite {X : RegChain // X.wf = true ∧ X.size = 2 * m} :=
  Finite.of_injective (fun X => wordSlots (8 * m + 1) (boundedChainWord m X))
    ((wordSlots_injective _).comp (boundedChainWord_injective m))

/-- The coherent layered trees of root sign `ζ`, order `2m`, parents `(q, q')`. -/
def coherentTrees (p q q' : ℕ) (ζ : ℤˣ) (m : ℕ) : Set (LayeredGarden 1) :=
  ⋃ X : {X : RegChain // X.wf = true ∧ X.size = 2 * m}, coherentTreesOf p q q' ζ X.1

/-- **The coherent trees of order `2m`** number at most `(12^9)^m · 2^{2m + (q - q')}`. -/
theorem ncard_coherentTrees_le (p q q' : ℕ) (ζ : ℤˣ) (m : ℕ) :
    (coherentTrees p q q' ζ m).Finite ∧ (coherentTrees p q q' ζ m).ncard ≤ (12 ^ 9) ^ m * 2 ^ (2 * m + (q - q')) := by
  classical
  let _ := finite_chainCodes m
  let _ : Fintype {X : RegChain // X.wf = true ∧ X.size = 2 * m} := Fintype.ofFinite _
  refine ⟨Set.finite_iUnion fun X => (ncard_coherentTreesOf_le p q q' ζ X.1).1, ?_⟩
  have h := Set.ncard_iUnion_le_of_fintype (fun X : {X : RegChain // X.wf = true ∧ X.size = 2 * m} => coherentTreesOf p q q' ζ X.1)
  have hsum : (∑ X : {X : RegChain // X.wf = true ∧ X.size = 2 * m}, (coherentTreesOf p q q' ζ X.1).ncard) ≤
      chainCodeCount m * 2 ^ (2 * m + (q - q')) := by
    calc _ ≤ ∑ _X : {X : RegChain // X.wf = true ∧ X.size = 2 * m}, 2 ^ (2 * m + (q - q')) := by
          apply Finset.sum_le_sum
          intro X _
          simpa only [X.2.2] using (ncard_coherentTreesOf_le p q q' ζ X.1).2
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, chainCodeCount, Nat.card_eq_fintype_card,
          Nat.cast_id]
  exact h.trans (hsum.trans (Nat.mul_le_mul_right _ (chainCodeCount_le_pow m)))

end Count

end WaveTurbulence.VineEstS5C.P4
