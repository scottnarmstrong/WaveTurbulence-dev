/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CutExists
public import WaveTurbulence.Foundations.RegStruct.DecodedTree
public import WaveTurbulence.Foundations.RegStruct.DecodedPairProperties

/-! # D2c PROT-CUT: cap couples are paired trees times one input

A cap couple (`w = 2`, code `capCode X = type2 X nil triv`, tree `1` the trivial cap) and the paired tree of `X` with
the same layers (`CapData`) have the same branches (`CapData.βc`), the same free-time integrals
(`protTime_transport`) and decorations in bijection (`CapData.decEquiv`). The cap couple has one more input leaf, the
lone leaf of `X`, which carries the output `k`:

* **`CapData.kernelProt_cap`**: `kernelProt LG H m up s fix k = H (0, X.lonePath) k · kernelProt LG1 (capH H)
  (D.capM m) (up ∘ βc) 0 (fix ∘ βc) k` for every `fix` (the cap couple has no lone parent, so its `s` is void; the
  tree's lone-port time `0` is void too, since all free times are positive).
* `CapData.exists_of_decodes`: the paired tree exists (`Reg.decodedTree X 1` with the pulled-back layers).
* Bookkeeping: `protSize_cap`, `protIncoh_cap`, `protShape_cap`, `cfg_fix_cap`, `cfg_valid_cap`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

variable {w w' d : ℕ}

/-! ### Transport of the free-time integral along a branch equivalence -/

/-- `protTime` is invariant under a relabelling of the branches that matches the pins, the time domains and the
phases. -/
theorem protTime_transport (L γ δ : ℝ) {LG : LayeredGarden w} {LG' : LayeredGarden w'}
    (e : GBranch LG.garden.tree ≃ GBranch LG'.garden.tree)
    {up : GBranch LG.garden.tree → ℝ} {up' : GBranch LG'.garden.tree → ℝ} {s s' : ℝ}
    {fix : GBranch LG.garden.tree → Option ℝ} {fix' : GBranch LG'.garden.tree → Option ℝ}
    (hfix : ∀ b, fix' (e b) = fix b) {K : GNode LG.garden.tree → Mom d} {K' : GNode LG'.garden.tree → Mom d}
    (hdom : ∀ τ' : GBranch LG'.garden.tree → ℝ,
      τ' ∈ protDom LG' up' s' fix' ↔ (fun b => τ' (e b)) ∈ protDom LG up s fix)
    (hph : ∀ τ' : GBranch LG'.garden.tree → ℝ,
      phaseProd L γ δ LG'.garden K' τ' = phaseProd L γ δ LG.garden K (fun b => τ' (e b))) :
    protTime L γ δ LG' up' s' fix' K' = protTime L γ δ LG up s fix K := by
  let ef : {b // fix b = none} ≃ {b' // fix' b' = none} :=
    e.subtypeEquiv (fun b => by rw [hfix])
  unfold protTime
  refine (integral_arrow_equiv ef _).symm.trans ?_
  congr 1
  funext σ
  have hext : (fun b => LG'.garden.extendFix fix' (fun b' => σ (ef.symm b')) (e b)) =
      LG.garden.extendFix fix σ := by
    funext b
    cases hb : fix b with
    | some v =>
      rw [extendFix_some _ _ _ hb, extendFix_some _ _ _ ((hfix b).trans hb)]
    | none =>
      have h1 := extendFix_free LG'.garden fix' (fun b' => σ (ef.symm b')) ⟨e b, (hfix b).trans hb⟩
      have h2 := extendFix_free LG.garden fix σ ⟨b, hb⟩
      simp only at h1 h2
      rw [h1, h2]
      congr 1
      exact ef.symm_apply_apply ⟨b, hb⟩
  by_cases hm : LG'.garden.extendFix fix' (fun b' => σ (ef.symm b')) ∈ protDom LG' up' s' fix'
  · have hm' := (hdom _).1 hm
    rw [hext] at hm'
    rw [indicator_of_mem hm, indicator_of_mem hm', hph, hext]
  · have hm' : LG.garden.extendFix fix σ ∉ protDom LG up s fix := fun h => hm ((hdom _).2 (by rw [hext]; exact h))
    rw [indicator_of_notMem hm, indicator_of_notMem hm']

/-! ### The cap code -/

/-- The code of a cap couple. -/
abbrev capCode (X : RegChain) : RegCpl := .type2 X .nil .triv

theorem capCode_pairs (X : RegChain) :
    (capCode X).pairsAt ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), []) =
      X.pairsAt 1 ((0 : Fin 2), []) ++ [(((0 : Fin 2), X.lonePath), ((1 : Fin 2), []))] := by
  simp [capCode, RegCpl.pairsAt, RegChain.pairsAt, RegChain.lonePath, addrExt]

theorem capCode_links (X : RegChain) :
    (capCode X).links = X.linksAt 1 ((0 : Fin 2), []) := by
  simp [capCode, RegCpl.links, RegCpl.linksAt, RegChain.linksAt]

/-- The leaf profiles of the paired tree. -/
def capH (H : LeafProfiles 2 d) : LeafProfiles 1 d := fun z => H ((0 : Fin 2), z.2)

/-- **A cap couple and its paired tree**: `LG` decoded by `capCode X`, `LG1` the paired tree of `X` (sign `+`) with
the layers of tree `0` of `LG`. -/
structure CapData (X : RegChain) (LG : LayeredGarden 2) (LG1 : LayeredGarden 1) : Prop where
  dec : (capCode X).Decodes LG.garden
  dec1 : X.DecodesTree LG1.garden
  sig1 : LG1.garden.sig 0 = 1
  lay : ∀ a : GNode LG1.garden.tree, LG1.layer a = layerAt LG ((0 : Fin 2), a.1.2)

namespace CapData

variable {X : RegChain} {LG : LayeredGarden 2} {LG1 : LayeredGarden 1} (D : CapData X LG LG1)
include D

theorem sig0 : LG.garden.sig 0 = 1 := by rw [D.dec.1.2]; rfl

theorem sig1' : LG.garden.sig 1 = -1 := by rw [D.dec.1.2]; rfl

theorem tree0 : LG.garden.tree 0 = X.plug 1 .leaf := by
  rw [D.dec.2.1]; simp [capCode, RegCpl.trees]

theorem tree1 : LG.garden.tree 1 = .leaf := by
  rw [D.dec.2.2.1]; simp [capCode, RegCpl.trees, RegChain.plug]

theorem treeT : LG1.garden.tree 0 = X.plug 1 .leaf := by
  have h := D.dec1.1
  rw [D.sig1] at h
  exact h

theorem plain : LG.garden.IsPlain := D.dec.1.1

theorem tree_eq : LG1.garden.tree 0 = LG.garden.tree 0 := by rw [D.treeT, D.tree0]

theorem fin1 (j : Fin 1) : j = 0 := Subsingleton.elim _ _

theorem idx (a : Fin 2) (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

theorem branch_zero (b : GBranch LG.garden.tree) : b.1.1 = 0 := by
  by_contra h
  have hb := b.2
  rw [D.idx _ h, D.tree1] at hb
  simp [TTree.branching] at hb

theorem node_one (a : GNode LG.garden.tree) (h : a.1.1 ≠ 0) : a.1 = ((1 : Fin 2), []) := by
  have ha := a.2
  rw [D.idx _ h, D.tree1] at ha
  simp [TTree.nodes] at ha
  exact Prod.ext (D.idx _ h) ha

/-- The placement of the paired tree in the cap couple. -/
def ι (a : GNode LG1.garden.tree) : GNode LG.garden.tree :=
  ⟨((0 : Fin 2), a.1.2), by
    have h := a.2
    rw [D.fin1 a.1.1, D.tree_eq] at h
    exact h⟩

/-- The lone leaf of the paired tree. -/
def lone1 : GNode LG1.garden.tree :=
  ⟨((0 : Fin 1), X.lonePath), by rw [D.treeT]; exact lonePath_mem_plug X _ _⟩

/-- The projection of the cap couple on the paired tree (the cap goes to the lone leaf). -/
def ρ (a : GNode LG.garden.tree) : GNode LG1.garden.tree :=
  ⟨((0 : Fin 1), if a.1.1 = 0 then a.1.2 else X.lonePath), by
    split_ifs with h
    · have h2 := a.2
      rw [h, ← D.tree_eq] at h2
      exact h2
    · rw [D.treeT]; exact lonePath_mem_plug X _ _⟩

theorem ρ_val (a : GNode LG.garden.tree) (h : a.1.1 = 0) : (D.ρ a).1 = ((0 : Fin 1), a.1.2) := by
  show ((0 : Fin 1), if a.1.1 = 0 then a.1.2 else X.lonePath) = _
  rw [if_pos h]

theorem ρ_ι (a : GNode LG1.garden.tree) : D.ρ (D.ι a) = a :=
  Subtype.ext ((D.ρ_val _ rfl).trans (Prod.ext (D.fin1 _).symm rfl))

theorem ι_ρ (a : GNode LG.garden.tree) (h : a.1.1 = 0) : D.ι (D.ρ a) = a := by
  have e : (D.ρ a).1.2 = a.1.2 := congrArg Prod.snd (D.ρ_val a h)
  exact Subtype.ext (Prod.ext h.symm e)

theorem ρ_one (a : GNode LG.garden.tree) (h : a.1.1 ≠ 0) : D.ρ a = D.lone1 := by
  refine Subtype.ext ?_
  show ((0 : Fin 1), if a.1.1 = 0 then a.1.2 else X.lonePath) = _
  rw [if_neg h]
  rfl

/-- The branches of the cap couple are those of the paired tree. -/
def βc : GBranch LG1.garden.tree ≃ GBranch LG.garden.tree where
  toFun b := ⟨((0 : Fin 2), b.1.2), by
    have h := b.2
    rw [D.fin1 b.1.1, D.tree_eq] at h
    exact h⟩
  invFun b := ⟨((0 : Fin 1), b.1.2), by
    have h := b.2
    rw [D.branch_zero b, ← D.tree_eq] at h
    exact h⟩
  left_inv b := Subtype.ext (Prod.ext (D.fin1 _).symm rfl)
  right_inv b := Subtype.ext (Prod.ext (D.branch_zero b).symm rfl)

theorem βc_toNode (b : GBranch LG1.garden.tree) : (D.βc b).toNode = D.ι b.toNode := rfl

theorem βc_child (b : GBranch LG1.garden.tree) (i : Fin 3) : (D.βc b).child i = D.ι (b.child i) := rfl

theorem ρ_βc_toNode (b : GBranch LG.garden.tree) : D.ρ b.toNode = (D.βc.symm b).toNode :=
  Subtype.ext (D.ρ_val _ (D.branch_zero b))

theorem ρ_βc_child (b : GBranch LG.garden.tree) (i : Fin 3) : D.ρ (b.child i) = (D.βc.symm b).child i :=
  Subtype.ext (D.ρ_val _ (D.branch_zero b))

theorem sign_ι (a : GNode LG1.garden.tree) : LG.garden.sign (D.ι a) = LG1.garden.sign a := by
  unfold Garden.sign nodeSign
  simp only [ι]
  rw [D.sig0, D.fin1 a.1.1, D.sig1]

theorem layer_ι (a : GNode LG1.garden.tree) : LG.layer (D.ι a) = LG1.layer a := by
  rw [D.lay a, ← layerAt_node LG (D.ι a)]
  rfl

theorem layerAt1 (x : Fin 1 × Path) : layerAt LG1 x = layerAt LG ((0 : Fin 2), x.2) := by
  obtain ⟨j, p⟩ := x
  rw [D.fin1 j]
  by_cases h : p ∈ (LG1.garden.tree 0).nodes
  · rw [layerAt_node LG1 ⟨((0 : Fin 1), p), h⟩]
    exact D.lay _
  · have h' : p ∉ (LG.garden.tree 0).nodes := by rwa [← D.tree_eq]
    unfold layerAt
    rw [dif_neg h, dif_neg h']

/-! #### Leaves and pairs -/

/-- The leaves of the paired tree in the cap couple. -/
def ιL (ℓ : GLeaf LG1.garden.tree) : GLeaf LG.garden.tree :=
  ⟨((0 : Fin 2), ℓ.1.2), by
    have h := ℓ.2
    rw [D.fin1 ℓ.1.1, D.tree_eq] at h
    exact h⟩

theorem ιL_injective : Function.Injective D.ιL := by
  intro ℓ ℓ' h
  have h2 := congrArg (fun z : GLeaf LG.garden.tree => z.1.2) h
  exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) h2)

theorem ιL_toNode (ℓ : GLeaf LG1.garden.tree) : (D.ιL ℓ).toNode = D.ι ℓ.toNode := rfl

/-- The lone leaf of `X` in the cap couple. -/
def ℓ0 : GLeaf LG.garden.tree :=
  ⟨((0 : Fin 2), X.lonePath), by rw [D.tree0]; exact lonePath_mem_leaves X 1⟩

theorem mem_raw (ℓ : GLeaf LG.garden.tree) :
    (ℓ.1, (LG.garden.pair ℓ).1) ∈ symmPairs (capCode X).raw.2 := D.dec.2.2.2 ℓ

theorem pair_ℓ0 : (LG.garden.pair D.ℓ0).1 = ((1 : Fin 2), []) := by
  have hc : (D.ℓ0.1, ((1 : Fin 2), ([] : Path))) ∈ symmPairs (capCode X).raw.2 := by
    rw [mem_symmPairs]
    left
    show _ ∈ (capCode X).pairsAt _ _
    rw [capCode_pairs]
    exact List.mem_append_right _ (List.mem_singleton.2 rfl)
  exact decodedPair_functional (capCode X) (D.mem_raw D.ℓ0) hc

theorem pair_ιL (ℓ : GLeaf LG1.garden.tree) (hℓ : ℓ.1.2 ≠ X.lonePath) :
    LG.garden.pair (D.ιL ℓ) = D.ιL (LG1.garden.pair ℓ) := by
  have h1 := D.dec1.2.2 ℓ hℓ
  rw [D.sig1] at h1
  let φ : Fin 1 × Path → Fin 2 × Path := fun z => ((0 : Fin 2), z.2)
  have hφ : ∀ z q, φ (addrExt z q) = addrExt (φ z) q := by intro z q; simp [φ, addrExt]
  have hm : ((D.ιL ℓ).1, (D.ιL (LG1.garden.pair ℓ)).1) ∈ symmPairs (capCode X).raw.2 := by
    rw [mem_symmPairs] at h1 ⊢
    have hmap : X.pairsAt 1 ((0 : Fin 2), ([] : Path)) =
        (X.pairsAt 1 ((0 : Fin 1), ([] : Path))).map (fun p => (φ p.1, φ p.2)) :=
      chain_pairsAt_map X φ hφ 1 ((0 : Fin 1), [])
    show _ ∈ (capCode X).pairsAt _ _ ∨ _ ∈ (capCode X).pairsAt _ _
    rw [capCode_pairs, hmap]
    rcases h1 with h1 | h1
    · exact Or.inl (List.mem_append_left _ (List.mem_map.2 ⟨_, h1, rfl⟩))
    · exact Or.inr (List.mem_append_left _ (List.mem_map.2 ⟨_, h1, rfl⟩))
  exact Subtype.ext (decodedPair_functional (capCode X) (D.mem_raw (D.ιL ℓ)) hm)

theorem leaf_cases (ℓ : GLeaf LG.garden.tree) :
    ℓ = D.ℓ0 ∨ ℓ.1 = ((1 : Fin 2), []) ∨ ∃ ℓ1 : GLeaf LG1.garden.tree, ℓ1.1.2 ≠ X.lonePath ∧ ℓ = D.ιL ℓ1 := by
  by_cases h0 : ℓ.1.1 = 0
  · by_cases hl : ℓ.1.2 = X.lonePath
    · exact Or.inl (Subtype.ext (Prod.ext h0 hl))
    · right; right
      refine ⟨⟨((0 : Fin 1), ℓ.1.2), ?_⟩, hl, Subtype.ext (Prod.ext h0 rfl)⟩
      have h := ℓ.2
      rw [h0, ← D.tree_eq] at h
      exact h
  · right; left
    have h := TTree.leaves_subset_nodes _ ℓ.2
    exact D.node_one ⟨ℓ.1, h⟩ h0

theorem pair_one (ℓ : GLeaf LG.garden.tree) (h : ℓ.1 = ((1 : Fin 2), [])) : LG.garden.pair ℓ = D.ℓ0 := by
  have hp : LG.garden.pair D.ℓ0 = ℓ := Subtype.ext (D.pair_ℓ0.trans h.symm)
  rw [← hp, LG.garden.pair_pair]

theorem ρ_ℓ0 : D.ρ D.ℓ0.toNode = D.lone1 :=
  Subtype.ext (D.ρ_val _ rfl)

/-! #### Decorations -/

theorem lone1_eq_root {V : Type*} [AddCommGroup V] {κ : GNode LG1.garden.tree → V}
    (hκ : IsDecoration LG1.garden κ) : κ D.lone1 = κ (GNode.root LG1.garden.tree 0) := by
  have hc := chainDec_of_decoration D.dec1 hκ
  have h := chainDec_lone_eq _ X _ _ hc
  have e1 : extend κ ((0 : Fin 1), ([] : Path)) = κ (GNode.root LG1.garden.tree 0) :=
    extend_node κ (GNode.root LG1.garden.tree 0)
  have e2 : extend κ (addrExt ((0 : Fin 1), ([] : Path)) X.lonePath) = κ D.lone1 := by
    have : addrExt ((0 : Fin 1), ([] : Path)) X.lonePath = D.lone1.1 := by simp [addrExt, lone1]
    rw [this]
    exact extend_node κ D.lone1
  rw [← e1, ← e2, h]

theorem not_flower1 (ℓ : GLeaf LG1.garden.tree) : ¬ LG1.garden.IsFlower ℓ := by
  unfold Garden.IsFlower
  rw [D.dec1.2.1 ℓ]
  split_ifs <;> simp

theorem not_flower (ℓ : GLeaf LG.garden.tree) : ¬ LG.garden.IsFlower ℓ := by
  unfold Garden.IsFlower
  rw [D.plain ℓ]
  simp

/-- Restriction of a cap-couple decoration to the paired tree. -/
def decFwd (κ : GenDecoration LG.garden d (fun _ => 0) 0) : GenDecoration LG1.garden d (fun _ => 0) 0 :=
  ⟨κ.1 ∘ D.ι, by
    refine ⟨⟨fun b => ?_, fun ℓ => ?_⟩, fun j => ?_, fun ℓ h => absurd h (D.not_flower1 ℓ)⟩
    · have := κ.2.1.1 (D.βc b)
      simpa only [Function.comp_apply, D.βc_toNode, D.βc_child] using this
    · by_cases hl : ℓ.1.2 = X.lonePath
      · have hm : LG1.garden.mark ℓ ≠ none := by rw [D.dec1.2.1 ℓ, if_pos hl]; simp
        rw [(LG1.garden.pair_eq_iff ℓ).2 hm]
      · have := κ.2.1.2 (D.ιL ℓ)
        rw [D.pair_ιL ℓ hl, D.ιL_toNode, D.ιL_toNode] at this
        simpa only [Function.comp_apply] using this
    · rw [D.fin1 j]
      exact κ.2.2.1 0⟩

/-- Extension of a paired-tree decoration to the cap couple. -/
def decBwd (κ : GenDecoration LG1.garden d (fun _ => 0) 0) : GenDecoration LG.garden d (fun _ => 0) 0 :=
  ⟨κ.1 ∘ D.ρ, by
    refine ⟨⟨fun b => ?_, fun ℓ => ?_⟩, fun j => ?_, fun ℓ h => absurd h (D.not_flower ℓ)⟩
    · have := κ.2.1.1 (D.βc.symm b)
      simp only [Function.comp_apply, D.ρ_βc_toNode, D.ρ_βc_child]
      exact this
    · simp only [Function.comp_apply]
      rcases D.leaf_cases ℓ with h | h | ⟨ℓ1, hne, rfl⟩
      · subst h
        have h1 : (LG.garden.pair D.ℓ0).toNode.1.1 ≠ 0 := by
          rw [show (LG.garden.pair D.ℓ0).toNode.1 = (LG.garden.pair D.ℓ0).1 from rfl, D.pair_ℓ0]; decide
        rw [D.ρ_one _ h1, D.ρ_ℓ0]
      · have h1 : ℓ.toNode.1.1 ≠ 0 := by
          rw [show ℓ.toNode.1 = ℓ.1 from rfl, h]; decide
        rw [D.ρ_one _ h1, D.pair_one ℓ h, D.ρ_ℓ0]
      · rw [D.pair_ιL ℓ1 hne, D.ιL_toNode, D.ιL_toNode, D.ρ_ι, D.ρ_ι]
        exact κ.2.1.2 ℓ1
    · by_cases hj : j = 0
      · subst hj
        have : D.ρ (GNode.root LG.garden.tree 0) = GNode.root LG1.garden.tree 0 :=
          Subtype.ext (D.ρ_val _ rfl)
        simp only [Function.comp_apply, this]
        exact κ.2.2.1 0
      · simp only [Function.comp_apply]
        rw [D.ρ_one (GNode.root LG.garden.tree j) hj, D.lone1_eq_root κ.2.1]
        exact κ.2.2.1 0⟩

end CapData

end WaveTurbulence.Flower.ProtCut
