/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.Coherent

/-!
# TARGET Prop `layerreg1`, part (1): the statements (packet C4)

Setting of `Coherent.lean`: `LG` satisfies `CanonCriterion p` (T Prop `canonequiv`) and is plain; `𝒬`
(code `Q`, well formed) is embedded at `(a, b)` and coherent; `q = parAt a`, `q' = parAt b` (TARGET's
`𝔏_{(𝔫^±)^pr}`, read as `p` at a root of the garden).

* `layerreg1_type1` (TARGET: "If `𝒬` has type 1 or trivial, then all nodes in `𝒬` must be in layer
  `q'`", with `q ≥ q'`; here without the normalization: layer `min(q, q')`);
* `layerreg1_type2`: the nodes of `𝒬_lp` are in layer `min(q, q')`; for each pair `{a, b}` of either
  chain, `𝔏_{𝔫_a} = 𝔏_{𝔫_b}` and its couples are in this layer; every node of the `+` chain (resp. `-`
  chain) is between `min(q, q')` and `q` (resp. `q'`); the chain nodes `𝔫_1, 𝔫_2, …` are in
  non-increasing layers (`chain_monotone`). For `q ≥ q'` this gives TARGET's statement: the `-` side
  is entirely in layer `q'` (`layerreg1_type2_minus`) and `q ≥ 𝔏_{𝔫_1^+} ≥ ⋯ ≥ 𝔏_{𝔫_{2m}^+} ≥ q'`;
* `layerreg1_tree`: the regular tree statement (`q ≥ 𝔏_{𝔫_1^0} ≥ ⋯ ≥ 𝔏_{𝔫_{2m}^0} ≥ q'`, pairs
  and their couples in one layer);
* `Embeds.of_decodes`, `ChainEmb.of_decodesTree`, `layerreg1_canonCouple`: the decoded carriers
  themselves.
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {w : ℕ}

/-- **The chain nodes `𝔫_1, …, 𝔫_{2m}`, top to bottom.** -/
def chainNodeList : RegChain → (Fin w × Path) → List (Fin w × Path)
  | .nil, _ => []
  | .pair m _ _ inner rest, a =>
    a :: (chainNodeList inner (addrExt a [m.c]) ++ addrExt a ([m.c] ++ inner.lonePath) ::
      chainNodeList rest (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])))

theorem chainNodeList_spec : ∀ (X : RegChain) (a : Fin w × Path),
    (∀ x ∈ chainNodeList X a, Under a x ∧ Under x (addrExt a X.lonePath)) ∧
    (chainNodeList X a).Pairwise Under
  | .nil, _ => by simp [chainNodeList]
  | .pair m Qr Qg inner rest, a => by
    obtain ⟨hI, pI⟩ := chainNodeList_spec inner (addrExt a [m.c])
    obtain ⟨hR, pR⟩ := chainNodeList_spec rest (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))
    have nbE : addrExt (addrExt a [m.c]) inner.lonePath = addrExt a ([m.c] ++ inner.lonePath) := by
      rw [addrExt_append]
    have lone_eq : addrExt a (RegChain.pair m Qr Qg inner rest).lonePath =
        addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) rest.lonePath :=
      chain_lonePath_eq m Qr Qg inner rest a
    have nb_lone : Under (addrExt a ([m.c] ++ inner.lonePath)) (addrExt a
        (RegChain.pair m Qr Qg inner rest).lonePath) :=
      ⟨rfl, ⟨[m.lone] ++ rest.lonePath, by simp [addrExt, RegChain.lonePath]⟩⟩
    have nb_rest : Under (addrExt a ([m.c] ++ inner.lonePath))
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) :=
      ⟨rfl, ⟨[m.lone], by simp [addrExt]⟩⟩
    have a_c : Under a (addrExt a [m.c]) := under_ext _ _
    have a_r : Under a (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) := under_ext _ _
    refine ⟨fun x hx => ?_, ?_⟩
    · simp only [chainNodeList, List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | rfl | hx
      · exact ⟨under_refl _, under_ext _ _⟩
      · obtain ⟨h1, h2⟩ := hI x hx
        rw [nbE] at h2
        exact ⟨under_trans a_c h1, under_trans h2 nb_lone⟩
      · exact ⟨under_ext _ _, nb_lone⟩
      · obtain ⟨h1, h2⟩ := hR x hx
        rw [← lone_eq] at h2
        exact ⟨under_trans a_r h1, h2⟩
    · simp only [chainNodeList, List.pairwise_cons, List.pairwise_append, List.mem_append,
        List.mem_cons]
      refine ⟨?_, pI, ⟨fun y hy => under_trans nb_rest (hR y hy).1, pR⟩, ?_⟩
      · rintro y (hy | rfl | hy)
        · exact under_trans a_c (hI y hy).1
        · exact under_ext _ _
        · exact under_trans a_r (hR y hy).1
      · intro x hx y hy
        have hx2 := (hI x hx).2
        rw [nbE] at hx2
        rcases hy with rfl | hy
        · exact hx2
        · exact under_trans hx2 (under_trans nb_rest (hR y hy).1)

/-- Every node of an embedded chain is a node of the carrier. -/
theorem ChainEmb.mem_nodes {G : Garden w} {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree}
    (hC : ChainEmb G X ζ a h) {z : Fin w × Path} (hz : z ∈ chainNodesSet X ζ a) :
    z.2 ∈ (G.tree z.1).nodes := by
  unfold chainNodesSet at hz
  rcases Finset.mem_union.1 hz with hz | hz
  · have : z ∈ branchAddresses (X.plug ζ h) a := by
      rw [chain_branchAddresses]; exact Finset.mem_union_left _ hz
    exact mem_nodes_of_branchAddresses hC.node hC.tree this
  · have : z ∈ leafAddresses (X.plug ζ h) a := by
      rw [chain_leafAddresses]; exact Finset.mem_union_left _ hz
    exact mem_nodes_of_leafAddresses hC.node hC.tree this

variable {LG : LayeredGarden w} {p : ℕ}

/-- **The chain layers are non-increasing** (`q ≥ 𝔏_{𝔫_1} ≥ ⋯ ≥ 𝔏_{𝔫_{2m}} ≥ 𝔏_{lone}`). -/
theorem chain_monotone (hp : ∀ a, LG.layer a ≤ p) {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path}
    {h : TTree} (hC : ChainEmb LG.garden X ζ a h) :
    (chainNodeList X a).Pairwise (fun x y => layerAt LG y ≤ layerAt LG x) ∧
    ∀ x ∈ chainNodeList X a, layerAt LG (addrExt a X.lonePath) ≤ layerAt LG x ∧
      layerAt LG x ≤ parAt LG p a := by
  obtain ⟨hs, hpw⟩ := chainNodeList_spec X a
  have hl := nodeOfChainEmb hC
  have node : ∀ x ∈ chainNodeList X a, x.2 ∈ (LG.garden.tree x.1).nodes := by
    intro x hx
    obtain ⟨e1, q, hq⟩ := (hs x hx).2
    have hl' := hl
    rw [← e1] at hl'
    exact Comb.TreePath.mem_nodes_of_prefix _ hl' ⟨q, hq⟩
  refine ⟨hpw.imp_of_mem fun {x y} hx hy hu => layerAt_le_of_under LG (node x hx) (node y hy) hu,
    fun x hx => ⟨layerAt_le_of_under LG (node x hx) hl (hs x hx).2, ?_⟩⟩
  exact (layerAt_le_of_under LG hC.node (node x hx) (hs x hx).1).trans
    (layerAt_le_parAt LG p hp hC.node)

variable (hcan : LG.CanonCriterion p) (hplain : LG.garden.IsPlain)
include hcan hplain

/-- **TARGET `layerreg1` (1), trivial and type-1 couples**: all nodes in layer `min(q, q')`. -/
theorem layerreg1_type1 {Q : RegCpl} {a b : Fin w × Path} (hwf : Q.wf = true)
    (hE : Embeds LG.garden Q a b) (hcoh : CohOn LG (Q.linksAt a b)) (ht : Q.isType2 = false) :
    ∀ z ∈ cplNodes Q a b, layerAt LG z = min (parAt LG p a) (parAt LG p b) :=
  (cpl_coherent hcan hplain Q a b hwf hE hcoh).1 ht

/-- **TARGET `layerreg1` (1), type-2 couples.** -/
theorem layerreg1_type2 {Xp Xm : RegChain} {Qlp : RegCpl} {a b : Fin w × Path}
    (hwf : (RegCpl.type2 Xp Xm Qlp).wf = true) (hE : Embeds LG.garden (.type2 Xp Xm Qlp) a b)
    (hcoh : CohOn LG ((RegCpl.type2 Xp Xm Qlp).linksAt a b)) :
    (∀ z ∈ cplNodes Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath),
      layerAt LG z = min (parAt LG p a) (parAt LG p b)) ∧
    ChainPairLayers LG Xp 1 a ∧ ChainPairLayers LG Xm (-1) b ∧
    (∀ z ∈ chainNodesSet Xp 1 a,
      min (parAt LG p a) (parAt LG p b) ≤ layerAt LG z ∧ layerAt LG z ≤ parAt LG p a) ∧
    (∀ z ∈ chainNodesSet Xm (-1) b,
      min (parAt LG p a) (parAt LG p b) ≤ layerAt LG z ∧ layerAt LG z ≤ parAt LG p b) := by
  have hwf' := hwf
  simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_true'] at hwf'
  obtain ⟨⟨⟨⟨wp, wm⟩, wl⟩, wlt⟩, -⟩ := hwf'
  obtain ⟨Cp, Cm, El⟩ := hE.type2
  have cohP : CohOn LG (Xp.linksAt 1 a) := fun l hl =>
    hcoh l (List.mem_append_left _ (List.mem_append_left _ hl))
  have cohM : CohOn LG (Xm.linksAt (-1) b) := fun l hl =>
    hcoh l (List.mem_append_left _ (List.mem_append_right _ hl))
  have cohL : CohOn LG (Qlp.linksAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)) := fun l hl =>
    hcoh l (List.mem_append_right _ hl)
  have LP := chain_coherent hcan hplain Xp 1 a _ wp Cp cohP
  have LM := chain_coherent hcan hplain Xm (-1) b _ wm Cm cohM
  have IL := (cpl_coherent hcan hplain Qlp _ _ wl El cohL).1 wlt
  have hu := IL _ (left_mem_cplNodes _ _ _)
  have hv := IL _ (right_mem_cplNodes _ _ _)
  have upA : min (parAt LG p (addrExt a Xp.lonePath)) (parAt LG p (addrExt b Xm.lonePath)) ≤
      parAt LG p a := by
    rw [← hu]
    exact (layerAt_le_of_under LG hE.nodeA El.nodeA (under_ext a _)).trans
      (layerAt_le_parAt LG p hcan.1 hE.nodeA)
  have upB : min (parAt LG p (addrExt a Xp.lonePath)) (parAt LG p (addrExt b Xm.lonePath)) ≤
      parAt LG p b := by
    rw [← hv]
    exact (layerAt_le_of_under LG hE.nodeB El.nodeB (under_ext b _)).trans
      (layerAt_le_parAt LG p hcan.1 hE.nodeB)
  have heq : min (parAt LG p (addrExt a Xp.lonePath)) (parAt LG p (addrExt b Xm.lonePath)) =
      min (parAt LG p a) (parAt LG p b) := by
    by_contra hne
    have hlt := lt_of_le_of_ne (le_min upA upB) hne
    obtain ⟨sP, hsP, hsP1, hsP2⟩ := spine_cut Xp 1 a _ Cp (fun l hl => cohP l (spineLinks_sub _ _ _ l hl)) _ hu
      (lt_of_lt_of_le hlt (min_le_left _ _))
    obtain ⟨sM, hsM, hsM1, hsM2⟩ := spine_cut Xm (-1) b _ Cm (fun l hl => cohM l (spineLinks_sub _ _ _ l hl)) _ hv
      (lt_of_lt_of_le hlt (min_le_right _ _))
    have uP := spinePos_under Xp a sP hsP
    have uM := spinePos_under Xm b sM hsM
    have hc := crit_apply hcan hplain hE (spinePos_node Cp hsP) (spinePos_node Cm hsM)
      (Or.inl uP.1) (Or.inr uM.1) (indep_of_under hE.indep uP.1 uM.1)
      (type2_pairedUnder Xp Xm Qlp hE.indep hsP hsM)
    rw [hsP1, hsM1, max_self] at hc
    exact absurd hc (not_le.2 (lt_min hsP2 hsM2))
  refine ⟨fun z hz => (IL z hz).trans heq, LP, LM, fun z hz => ⟨?_, ?_⟩, fun z hz => ⟨?_, ?_⟩⟩
  · rw [← heq, ← hu]; exact chain_lower Xp 1 a _ Cp LP z hz
  · have nz := hE.mem_nodes (mem_cplNodes_type2.2 (Or.inl hz))
    have ua := (chain_endpoints_region Xp 1 a z hz).1
    exact (layerAt_le_of_under LG hE.nodeA nz ua).trans (layerAt_le_parAt LG p hcan.1 hE.nodeA)
  · rw [← heq, ← hv]; exact chain_lower Xm (-1) b _ Cm LM z hz
  · have nz := hE.mem_nodes (mem_cplNodes_type2.2 (Or.inr (Or.inl hz)))
    have ub := (chain_endpoints_region Xm (-1) b z hz).1
    exact (layerAt_le_of_under LG hE.nodeB nz ub).trans (layerAt_le_parAt LG p hcan.1 hE.nodeB)

/-- **TARGET's normalized form (`q ≥ q'`)**: the `-` side of a type-2 couple (its chain and its
couples, and `𝒬_lp`) is entirely in layer `q'`. -/
theorem layerreg1_type2_minus {Xp Xm : RegChain} {Qlp : RegCpl} {a b : Fin w × Path}
    (hwf : (RegCpl.type2 Xp Xm Qlp).wf = true) (hE : Embeds LG.garden (.type2 Xp Xm Qlp) a b)
    (hcoh : CohOn LG ((RegCpl.type2 Xp Xm Qlp).linksAt a b))
    (hqq : parAt LG p b ≤ parAt LG p a) :
    (∀ z ∈ chainNodesSet Xm (-1) b, layerAt LG z = parAt LG p b) ∧
    (∀ z ∈ cplNodes Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath),
      layerAt LG z = parAt LG p b) := by
  obtain ⟨hL, -, -, -, hM⟩ := layerreg1_type2 hcan hplain hwf hE hcoh
  rw [min_eq_right hqq] at hL hM
  exact ⟨fun z hz => le_antisymm (hM z hz).2 (hM z hz).1, hL⟩

/-- **TARGET `layerreg1` (1), regular trees**: an embedded coherent regular tree (code `X`, root at
`a`, lone position `addrExt a X.lonePath`): each pair and its couples are in one layer, and all nodes
are between the lone leaf's layer `q'` and the parent layer `q`, non-increasing along the chain. -/
theorem layerreg1_tree {X : RegChain} {ζ : ℤˣ} {a : Fin w × Path} {h : TTree} (hwf : X.wf = true)
    (hC : ChainEmb LG.garden X ζ a h) (hcoh : CohOn LG (X.linksAt ζ a)) :
    ChainPairLayers LG X ζ a ∧
    (∀ z ∈ chainNodesSet X ζ a, layerAt LG (addrExt a X.lonePath) ≤ layerAt LG z ∧
      layerAt LG z ≤ parAt LG p a) ∧
    (chainNodeList X a).Pairwise (fun x y => layerAt LG y ≤ layerAt LG x) := by
  have L := chain_coherent hcan hplain X ζ a h hwf hC hcoh
  refine ⟨L, fun z hz => ⟨chain_lower X ζ a h hC L z hz, ?_⟩, (chain_monotone hcan.1 hC).1⟩
  have nz := hC.mem_nodes hz
  have ua := (chain_endpoints_region X ζ a z hz).1
  exact (layerAt_le_of_under LG hC.node nz ua).trans (layerAt_le_parAt LG p hcan.1 hC.node)

omit hcan hplain

/-- **A decoded couple carrier embeds its code at its roots.** -/
theorem Embeds.of_decodes {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) :
    Embeds G Q ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)) where
  indep := ⟨fun h => by simp [Under] at h, fun h => by simp [Under] at h⟩
  nodeA := TTree.nil_mem_nodes _
  nodeB := TTree.nil_mem_nodes _
  treeA := hQ.2.1
  treeB := hQ.2.2.1
  pairs := fun q hq ℓ hℓ => by
    obtain ⟨ℓ', h1, h2⟩ := pair_of_decoded hQ (p := q) hq
    have : ℓ = ℓ' := Subtype.ext (hℓ.trans h1.symm)
    subst this
    exact h2

/-- **A decoded tree carrier embeds its chain code at its root** (lone position: a leaf). -/
theorem ChainEmb.of_decodesTree {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) :
    ChainEmb G X (G.sig 0) ((0 : Fin 1), ([] : Path)) .leaf where
  node := TTree.nil_mem_nodes _
  tree := hX.1
  pairs := fun q hq ℓ hℓ => by
    obtain ⟨ℓ', h1, h2⟩ := tree_pair_of_decoded hX (p := q) hq
    have : ℓ = ℓ' := Subtype.ext (hℓ.trans h1.symm)
    subst this
    exact h2

theorem parAt_root {w : ℕ} (LG : LayeredGarden w) (p : ℕ) (j : Fin w) :
    parAt LG p (j, []) = p := by
  rw [parAt_of_mem LG p (TTree.nil_mem_nodes _)]
  unfold LayeredGarden.parentLayer
  simp

/-- **A coherent regular couple that is a whole canonical couple `𝒢 ∈ 𝒞_{p+1}`** lies in layer `p`
(TARGET `layerreg1` with `q = q' = p`). -/
theorem layerreg1_canonCouple {LG : LayeredGarden 2} {p : ℕ} {Q : RegCpl}
    (hC : IsCanonC (p + 1) LG) (hQ : Q.Decodes LG.garden) (hwf : Q.wf = true)
    (hcoh : LG.incoherency Q.links = 0) :
    ∀ z ∈ cplNodes Q ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)), layerAt LG z = p := by
  have h := (cpl_coherent hC.2 hC.1.1 Q _ _ hwf (Embeds.of_decodes hQ)
    ((coherent_iff hQ).1 hcoh)).2 ((parAt_root LG p 0).trans (parAt_root LG p 1).symm)
  intro z hz
  rw [h z hz, parAt_root]

end WaveTurbulence.Links
