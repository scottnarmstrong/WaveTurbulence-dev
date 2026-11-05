/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.GlueDomain
public import WaveTurbulence.Foundations.RegStruct.PairNaturality

/-!
# Layerings of the two pieces of a glued garden

* `topLayered`: the top paired tree with the single-layer layering of B2.1 (2) — layer `r` at every node
  except the lone leaf, which is in layer `r' ≤ r`;
* `botLayered_couple`, `botLayered_tree`: the bottom garden with the layering read off the glued garden
  along `ι₂` (a layering because decoded pairs of the bottom piece are decoded pairs of the glued garden).
-/

@[expose] public section

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine

/-- The single-layer layering of a decoded paired tree: `r` except at the lone leaf (`r'`). -/
def topLayer (G₁ : Garden 1) (X : RegChain) (r r' : ℕ) (a : GNode G₁.tree) : ℕ :=
  if a.1.2 = X.lonePath then r' else r

theorem topLayer_isLayering {G₁ : Garden 1} {X : RegChain} (h₁ : X.DecodesTree G₁) {r r' : ℕ}
    (hr : r' ≤ r) : IsLayering G₁ (topLayer G₁ X r r') := by
  have hlone_marked : ∀ ℓ : GLeaf G₁.tree, ℓ.1.2 = X.lonePath → G₁.pair ℓ = ℓ := by
    intro ℓ hℓ
    refine (G₁.pair_eq_iff ℓ).2 ?_
    rw [h₁.2.1 ℓ]
    simp [hℓ]
  constructor
  · intro b i
    have hb : b.1.2 ≠ X.lonePath := by
      intro he
      have hl : b.1.2 ∈ (G₁.tree b.1.1).leaves := by
        have hb0 : b.1.1 = 0 := Subsingleton.elim _ _
        rw [hb0, h₁.1, he]
        exact lonePath_mem_leaves X _
      exact TTree.not_mem_branching_of_mem_leaves _ hl b.2
    have : topLayer G₁ X r r' b.toNode = r := by
      unfold topLayer
      exact ite_eq_right hb
    rw [this]
    unfold topLayer
    split_ifs <;> omega
  · intro ℓ
    unfold topLayer
    by_cases hℓ : ℓ.1.2 = X.lonePath
    · rw [hlone_marked ℓ hℓ]
    · have hp : (G₁.pair ℓ).1.2 ≠ X.lonePath := by
        intro he
        have := hlone_marked _ he
        rw [G₁.pair_pair] at this
        exact hℓ ((congrArg (fun z : GLeaf G₁.tree => z.1.2) this).trans he)
      show (if ℓ.1.2 = X.lonePath then r' else r) = if (G₁.pair ℓ).1.2 = X.lonePath then r' else r
      rw [ite_eq_right hℓ, ite_eq_right hp]

/-- The top piece as a layered paired tree. -/
def topLayered (G₁ : Garden 1) (X : RegChain) (h₁ : X.DecodesTree G₁) (r r' : ℕ) (hr : r' ≤ r) :
    LayeredGarden 1 :=
  ⟨G₁, topLayer G₁ X r r', topLayer_isLayering h₁ hr⟩

/-- Decoded pairs of a couple carrier have equal layers. -/
theorem layer_eq_of_decoded_pair {LG : LayeredGarden 2} {Q : RegCpl} (hQ : Q.Decodes LG.garden)
    {p : (Fin 2 × Path) × (Fin 2 × Path)} (hp : p ∈ Q.pairsAt (0, []) (1, [])) :
    layerAt LG p.1 = layerAt LG p.2 := by
  obtain ⟨ℓ, h1, h2⟩ := pair_of_decoded hQ (p := p) hp
  rw [← h1, ← h2]
  show layerAt LG ℓ.toNode.1 = layerAt LG (LG.garden.pair ℓ).toNode.1
  rw [layerAt_node, layerAt_node]
  exact LG.isLayering.2 ℓ

/-- Decoded pairs of a paired-tree carrier have equal layers. -/
theorem layer_eq_of_decoded_treePair {LG : LayeredGarden 1} {X : RegChain}
    (hX : X.DecodesTree LG.garden) {p : (Fin 1 × Path) × (Fin 1 × Path)}
    (hp : p ∈ X.pairsAt (LG.garden.sig 0) (0, [])) : layerAt LG p.1 = layerAt LG p.2 := by
  obtain ⟨ℓ, h1, h2⟩ := tree_pair_of_decoded hX (p := p) hp
  rw [← h1, ← h2]
  show layerAt LG ℓ.toNode.1 = layerAt LG (LG.garden.pair ℓ).toNode.1
  rw [layerAt_node, layerAt_node]
  exact LG.isLayering.2 ℓ

theorem mem_symmPairs {α : Type*} {P : List (α × α)} {x y : α} :
    (x, y) ∈ symmPairs P ↔ (x, y) ∈ P ∨ (y, x) ∈ P := by
  unfold symmPairs
  simp only [List.mem_append, List.mem_map, Prod.swap, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro (h | ⟨a, b, h, rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨y, x, h, rfl, rfl⟩

variable {LG : LayeredGarden 2} {G₁ : Garden 1} {G₂ : Garden 2} {X X₂ Xm : RegChain} {Qlp : RegCpl}

theorem pairsAt_closeCouple {w : ℕ} (X₂ Xm : RegChain) (Qlp : RegCpl) (a b : Fin w × Path) :
    (SourceApp.closeCouple X₂ Xm Qlp).pairsAt a b = (RegCpl.type2 X₂ Xm Qlp).pairsAt a b := by
  unfold SourceApp.closeCouple
  split_ifs with hn
  · simp only [Bool.and_eq_true] at hn
    cases X₂ <;> cases Xm <;> simp_all [RegChain.isNil, RegCpl.pairsAt, RegChain.pairsAt,
      RegChain.lonePath, addrExt]
  · rfl

/-- **The bottom couple as a layered garden**, with the layers of the glued couple. -/
def botLayered_couple (hQ : (RegCpl.type2 (appendChain X X₂) Xm Qlp).Decodes LG.garden)
    (h₁ : X.DecodesTree G₁) (hs₁ : G₁.sig 0 = 1)
    (h₂ : (SourceApp.closeCouple X₂ Xm Qlp).Decodes G₂) : LayeredGarden 2 :=
  ⟨G₂, fun y => LG.layer ((glueData_couple hQ h₁ hs₁ h₂).ι₂ y), by
    set h := glueData_couple hQ h₁ hs₁ h₂
    constructor
    · intro y i
      show LG.layer (h.ι₂ (y.child i)) ≤ LG.layer (h.ι₂ y.toNode)
      rw [← h.ofSum_inr_child, ← h.ofSum_inr_toNode]
      exact LG.isLayering.1 _ i
    · intro ℓ
      have hm := h₂.2.2.2 ℓ
      rw [mem_symmPairs] at hm
      have key : ∀ u v : Fin 2 × Path, (u, v) ∈ (SourceApp.closeCouple X₂ Xm Qlp).raw.2 →
          layerAt LG (botAddr X.lonePath u) = layerAt LG (botAddr X.lonePath v) := by
        intro u v huv
        have hmap : (botAddr X.lonePath u, botAddr X.lonePath v) ∈
            (RegCpl.type2 (appendChain X X₂) Xm Qlp).pairsAt (0, []) (1, []) := by
          have e := couple_pairsAt_map (SourceApp.closeCouple X₂ Xm Qlp) (botAddr X.lonePath)
            (botAddr_hom X.lonePath) ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path))
          have e0 : botAddr X.lonePath ((0 : Fin 2), ([] : Path)) = (0, X.lonePath) := by
            simp [botAddr]
          have e1 : botAddr X.lonePath ((1 : Fin 2), ([] : Path)) = (1, []) := by simp [botAddr]
          rw [e0, e1, pairsAt_closeCouple] at e
          have hin : (botAddr X.lonePath u, botAddr X.lonePath v) ∈
              (RegCpl.type2 X₂ Xm Qlp).pairsAt (0, X.lonePath) (1, []) := by
            rw [e]
            exact List.mem_map.mpr ⟨(u, v), huv, rfl⟩
          simp only [RegCpl.pairsAt, appendChain_pairsAt, appendChain_lonePath, List.mem_append,
            addrExt_zero_nil] at hin ⊢
          have e2 : addrExt ((0 : Fin 2), X.lonePath) X₂.lonePath =
              ((0 : Fin 2), X.lonePath ++ X₂.lonePath) := by simp [addrExt]
          rw [e2] at hin
          tauto
        exact layer_eq_of_decoded_pair hQ hmap
      have e1 : LG.layer (h.ι₂ ℓ.toNode) = layerAt LG (botAddr X.lonePath ℓ.1) :=
        (layerAt_node LG (h.ι₂ ℓ.toNode)).symm
      have e2 : LG.layer (h.ι₂ (G₂.pair ℓ).toNode) = layerAt LG (botAddr X.lonePath (G₂.pair ℓ).1) :=
        (layerAt_node LG (h.ι₂ (G₂.pair ℓ).toNode)).symm
      show LG.layer (h.ι₂ ℓ.toNode) = LG.layer (h.ι₂ (G₂.pair ℓ).toNode)
      rw [e1, e2]
      rcases hm with hm | hm
      · exact key _ _ hm
      · exact (key _ _ hm).symm⟩

/-- **The bottom paired tree as a layered garden**, with the layers of the glued tree. -/
def botLayered_tree {LGt : LayeredGarden 1} {G₁t G₂t : Garden 1} {Xt X₂t : RegChain}
    (hG : (appendChain Xt X₂t).DecodesTree LGt.garden) (h₁ : Xt.DecodesTree G₁t)
    (hs₁ : G₁t.sig 0 = LGt.garden.sig 0) (h₂ : X₂t.DecodesTree G₂t)
    (hs₂ : G₂t.sig 0 = LGt.garden.sig 0) : LayeredGarden 1 :=
  ⟨G₂t, fun y => LGt.layer ((glueData_tree hG h₁ hs₁ h₂ hs₂).ι₂ y), by
    set h := glueData_tree hG h₁ hs₁ h₂ hs₂
    constructor
    · intro y i
      show LGt.layer (h.ι₂ (y.child i)) ≤ LGt.layer (h.ι₂ y.toNode)
      rw [← h.ofSum_inr_child, ← h.ofSum_inr_toNode]
      exact LGt.isLayering.1 _ i
    · intro ℓ
      show LGt.layer (h.ι₂ ℓ.toNode) = LGt.layer (h.ι₂ (G₂t.pair ℓ).toNode)
      by_cases hl : ℓ.1.2 = X₂t.lonePath
      · have hm : G₂t.mark ℓ ≠ none := by rw [h₂.2.1 ℓ]; simp [hl]
        rw [(G₂t.pair_eq_iff ℓ).2 hm]
      · have hm := h₂.2.2 ℓ hl
        rw [mem_symmPairs] at hm
        have key : ∀ u v : Fin 1 × Path, (u, v) ∈ X₂t.pairsAt (G₂t.sig 0) (0, []) →
            layerAt LGt (botAddr Xt.lonePath u) = layerAt LGt (botAddr Xt.lonePath v) := by
          intro u v huv
          refine layer_eq_of_decoded_treePair hG (p := (botAddr Xt.lonePath u, botAddr Xt.lonePath v)) ?_
          rw [appendChain_pairsAt, List.mem_append]
          right
          have e := chain_pairsAt_map X₂t (botAddr Xt.lonePath) (botAddr_hom Xt.lonePath)
            (G₂t.sig 0) ((0 : Fin 1), ([] : Path))
          have e0 : botAddr Xt.lonePath ((0 : Fin 1), ([] : Path)) =
              addrExt ((0 : Fin 1), ([] : Path)) Xt.lonePath := by simp [botAddr, addrExt]
          rw [e0, hs₂] at e
          rw [e]
          exact List.mem_map.mpr ⟨(u, v), by rw [← hs₂]; exact huv, rfl⟩
        have e1 : LGt.layer (h.ι₂ ℓ.toNode) = layerAt LGt (botAddr Xt.lonePath ℓ.1) :=
          (layerAt_node LGt (h.ι₂ ℓ.toNode)).symm
        have e2 : LGt.layer (h.ι₂ (G₂t.pair ℓ).toNode) =
            layerAt LGt (botAddr Xt.lonePath (G₂t.pair ℓ).1) :=
          (layerAt_node LGt (h.ι₂ (G₂t.pair ℓ).toNode)).symm
        rw [e1, e2]
        rcases hm with hm | hm
        · exact key _ _ hm
        · exact (key _ _ hm).symm⟩

end WaveTurbulence.PL234
