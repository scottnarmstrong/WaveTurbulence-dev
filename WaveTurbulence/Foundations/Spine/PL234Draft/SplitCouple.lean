/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.BlockLayers
public import WaveTurbulence.Foundations.Spine.PL234Draft.LeafSummable
public import WaveTurbulence.Foundations.Spine.LeafwiseCoherentApp

/-!
# Splitting off the top block of a coherent couple (TARGET (prooflayer1-1), one step)

For a couple carrier decoded by `type2 (appendChain B D) Xm Qlp` whose top block `B` lies in layer `r`
(every node of the placed chain `B`) and whose lone position of `B` is in a lower layer `r'' < r`, the
leafwise kernel splits (`coupleLeaves_split`):
`K*_𝒬(t, s, k) = K*_{𝒯}(t, r, k) · K*_{𝒬'}(r'' + 1, s, k)` for `t ≥ r'' + 1`, where `𝒯` is a paired tree
decoded by `B` (layer `r`, lone leaf in layer `r''`) and `𝒬'` a couple decoded by
`closeCouple D Xm Qlp` with the layers of the bottom of the carrier; the leaf profiles are transported
along the address maps.
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine

theorem not_flower_of_plain {w : ℕ} {G : Garden w} (hG : G.IsPlain) (ℓ : GLeaf G.tree) :
    ¬ G.IsFlower ℓ := by
  unfold Garden.IsFlower
  rw [hG ℓ]
  simp

theorem not_flower_of_decodesTree {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (ℓ : GLeaf G.tree) : ¬ G.IsFlower ℓ := by
  unfold Garden.IsFlower
  rw [hX.2.1 ℓ]
  split_ifs <;> simp

theorem not_loneParent_of_plain {w : ℕ} {G : Garden w} (hG : G.IsPlain) (b : GBranch G.tree) :
    ¬ G.IsLoneParent b := by
  rintro ⟨ℓ, hℓ, -⟩
  unfold Garden.IsLone at hℓ
  rw [hG ℓ] at hℓ
  simp at hℓ

theorem card_lone_le_of_plain {w : ℕ} {G : Garden w} (hG : G.IsPlain) (j : Fin w) :
    (Finset.univ.filter fun ℓ : GLeaf G.tree => ℓ.1.1 = j ∧ G.IsLone ℓ).card ≤ 1 := by
  refine Finset.card_le_one.2 fun a ha => ?_
  simp only [mem_filter, mem_univ, true_and] at ha
  exact absurd ha.2 (by unfold Garden.IsLone; rw [hG a]; simp)

theorem card_lone_le_of_decodesTree {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) (j : Fin 1) :
    (Finset.univ.filter fun ℓ : GLeaf G.tree => ℓ.1.1 = j ∧ G.IsLone ℓ).card ≤ 1 := by
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  simp only [mem_filter, mem_univ, true_and] at ha hb
  have pa : a.1.2 = X.lonePath := by
    by_contra hne
    have := ha.2
    unfold Garden.IsLone at this
    rw [hX.2.1 a, ite_eq_right hne] at this
    exact absurd this (by simp)
  have pb : b.1.2 = X.lonePath := by
    by_contra hne
    have := hb.2
    unfold Garden.IsLone at this
    rw [hX.2.1 b, ite_eq_right hne] at this
    exact absurd this (by simp)
  apply Subtype.ext
  exact Prod.ext (Subsingleton.elim _ _) (pa.trans pb.symm)

variable {LG : LayeredGarden 2} {B D Xm : RegChain} {Qlp : RegCpl}

theorem mem_chainNodes_of_branch {X : RegChain} {ζ : ℤˣ} {w : ℕ} [NeZero w] {p : Path}
    (hp : p ∈ (X.plug ζ .leaf).branching) :
    ((0 : Fin w), p) ∈ chainNodesSet X ζ ((0 : Fin w), ([] : Path)) := by
  have hb : ((0 : Fin w), p) ∈ branchAddresses (X.plug ζ .leaf) ((0 : Fin w), ([] : Path)) :=
    Finset.mem_image.mpr ⟨p, hp, by simp [addrExt]⟩
  rw [chain_branchAddresses, branchAddresses_leaf, Finset.union_empty] at hb
  exact Finset.mem_union_left _ hb

/-- **Splitting off the top block of a couple.** -/
theorem coupleLeaves_split (L γ δ : ℝ) {d : ℕ}
    (hQ : (RegCpl.type2 (appendChain B D) Xm Qlp).Decodes LG.garden)
    {G₁ : Garden 1} (h₁ : B.DecodesTree G₁) (hs₁ : G₁.sig 0 = 1)
    {G₂ : Garden 2} (h₂ : (SourceApp.closeCouple D Xm Qlp).Decodes G₂) {r : ℕ}
    (hB : ∀ z ∈ chainNodesSet B 1 ((0 : Fin 2), ([] : Path)), layerAt LG z = r)
    (hlt : layerAt LG ((0 : Fin 2), B.lonePath) < r)
    (H : LeafProfiles 2 d) (k : Mom d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|)
    (t s : ℝ) (ht : (layerAt LG ((0 : Fin 2), B.lonePath) : ℝ) + 1 ≤ t) :
    coupleLeaves L γ δ LG H t s k =
      treeLeaves L γ δ (topLayered G₁ B h₁ r (layerAt LG ((0 : Fin 2), B.lonePath)) hlt.le)
          (fun z => H (topAddr z)) t r k *
        coupleLeaves L γ δ (botLayered_couple hQ h₁ hs₁ h₂) (fun z => H (botAddr B.lonePath z))
          ((layerAt LG ((0 : Fin 2), B.lonePath) : ℝ) + 1) s k := by
  set r'' := layerAt LG ((0 : Fin 2), B.lonePath) with hr''
  set h := glueData_couple hQ h₁ hs₁ h₂ with hh
  have hplain : LG.garden.IsPlain := hQ.1.1
  have hplain₂ : G₂.IsPlain := h₂.1.1
  have hmtop : ∀ ℓ : GLeaf LG.garden.tree, (ℓ.1.1 = 0 ∧ ¬ B.lonePath <+: ℓ.1.2) →
      LG.garden.mark ℓ = none := fun ℓ _ => hplain ℓ
  have hmbot : ∀ (ℓ₂ : GLeaf G₂.tree) (ℓ : GLeaf LG.garden.tree),
      ℓ.1 = botAddr B.lonePath ℓ₂.1 → LG.garden.mark ℓ = G₂.mark ℓ₂ := fun ℓ₂ ℓ _ => by
    rw [hplain ℓ, hplain₂ ℓ₂]
  -- the lone position and the bottom tree `0`
  have nLone : ((0 : Fin 2), B.lonePath).2 ∈ (LG.garden.tree ((0 : Fin 2), B.lonePath).1).nodes := by
    show B.lonePath ∈ (LG.garden.tree 0).nodes
    rw [h.tree0]
    exact lonePath_mem_plug B _ _
  have hbot0 : ∀ y : GNode G₂.tree, y.1.1 = 0 → LG.layer (h.ι₂ y) ≤ r'' := by
    intro y hy
    rw [← layerAt_node LG (h.ι₂ y)]
    have e : (h.ι₂ y).1 = addrExt ((0 : Fin 2), B.lonePath) y.1.2 := by
      show botAddr B.lonePath y.1 = _
      obtain ⟨⟨j, p⟩, _⟩ := y
      simp only at hy
      subst hy
      simp [botAddr, addrExt]
    have hu : Under ((0 : Fin 2), B.lonePath) (h.ι₂ y).1 := by rw [e]; exact under_ext _ _
    exact layerAt_le_of_under LG nLone (h.ι₂ y).2 hu
  have hD : ∀ τ, τ ∈ kDomain LG (fun b => if b.1.1 = 0 then t else s) 0 ↔
      (fun x => τ (h.ofSum (.inl x))) ∈
        kDomain (topLayered G₁ B h₁ r r'' hlt.le) (fun _ => t) r ∧
      (fun y => τ (h.ofSum (.inr y))) ∈ kDomain (botLayered_couple hQ h₁ hs₁ h₂)
        (fun b => if b.1.1 = 0 then (r'' : ℝ) + 1 else s) 0 := by
    intro τ
    have hlay₁ : ∀ x : GBranch G₁.tree, topLayer G₁ B r r'' x.toNode = r := by
      intro x
      unfold topLayer
      refine ite_eq_right fun he => ?_
      have he' : x.1.2 = B.lonePath := he
      have hl : x.1.2 ∈ (G₁.tree x.1.1).leaves := by
        rw [Subsingleton.elim x.1.1 0, h₁.1, hs₁, he']
        exact lonePath_mem_leaves B _
      exact TTree.not_mem_branching_of_mem_leaves _ hl x.2
    refine kDomain_glue (LG₁ := topLayered G₁ B h₁ r r'' hlt.le)
      (LG₂ := botLayered_couple hQ h₁ hs₁ h₂) h _ 0 _ r _ 0 ?_ (fun _ => rfl) ?_ ?_ ?_ ?_ rfl ?_ τ
    · intro x
      refine (hlay₁ x).trans ?_
      rw [← layerAt_node]
      refine (hB _ ?_).symm
      have hm : x.1.2 ∈ (B.plug 1 .leaf).branching := by
        have hx := x.2
        have e : (topLayered G₁ B h₁ r r'' hlt.le).garden.tree x.1.1 = B.plug 1 .leaf := by
          show G₁.tree x.1.1 = _
          rw [Subsingleton.elim x.1.1 0, h₁.1, hs₁]
        rw [e] at hx
        exact hx
      exact mem_chainNodes_of_branch hm
    · intro x
      rfl
    · intro y
      by_cases hy : y.1.1 = 0
      · right
        have hle := hbot0 y.toNode hy
        have hle' : (LG.layer (h.ι₂ y.toNode) : ℝ) ≤ r'' := by exact_mod_cast hle
        show (LG.layer (h.ι₂ y.toNode) : ℝ) + 1 ≤ (if (h.ofSum (.inr y)).1.1 = 0 then t else s) ∧
          (LG.layer (h.ι₂ y.toNode) : ℝ) + 1 ≤ (if y.1.1 = 0 then (r'' : ℝ) + 1 else s)
        have e : (h.ofSum (.inr y)).1.1 = 0 := by
          show (botAddr B.lonePath y.1).1 = 0
          obtain ⟨⟨j, p⟩, _⟩ := y
          simp only at hy
          subst hy
          simp [botAddr]
        rw [ite_eq_left e, ite_eq_left hy]
        exact ⟨by linarith, by linarith⟩
      · left
        have e : ¬ (h.ofSum (.inr y)).1.1 = 0 := by
          show ¬ (botAddr B.lonePath y.1).1 = 0
          obtain ⟨⟨j, p⟩, _⟩ := y
          simp only at hy
          simp [botAddr, hy]
        show (if (h.ofSum (.inr y)).1.1 = 0 then t else s) = if y.1.1 = 0 then (r'' : ℝ) + 1 else s
        rw [ite_eq_right e, ite_eq_right hy]
    · intro x y hc
      have hy : y.1.1 = 0 := by
        obtain ⟨h1, -⟩ := hc
        change (botAddr B.lonePath y.1).1 = (0 : Fin 2) at h1
        obtain ⟨⟨j, p⟩, _⟩ := y
        by_contra hj
        simp only at hj
        simp [botAddr, hj] at h1
      have hle := hbot0 y.toNode hy
      have e : ((topLayered G₁ B h₁ r r'' hlt.le).layer x.toNode : ℝ) = r := by
        exact_mod_cast hlay₁ x
      have : (LG.layer (h.ι₂ y.toNode) : ℝ) ≤ r'' := by exact_mod_cast hle
      have hlt' : (r'' : ℝ) + 1 ≤ r := by exact_mod_cast hlt
      show (LG.layer (h.ι₂ y.toNode) : ℝ) + 1 ≤ ((topLayered G₁ B h₁ r r'' hlt.le).layer x.toNode : ℝ)
      rw [e]
      linarith
    · intro b
      exact iff_of_false (not_loneParent_of_plain hplain b)
        (fun ⟨y, _, hy⟩ => not_loneParent_of_plain hplain₂ y hy)
    · intro x _
      have e : ((topLayered G₁ B h₁ r r'' hlt.le).layer x.toNode : ℝ) = r := by
        exact_mod_cast hlay₁ x
      rw [e]
  have hH₁ : ∀ ℓ ∈ inputLeaves G₁,
      Summable fun n : Fin d → ℤ => |H (topAddr ℓ.1) (k + latticePoint L n)| := by
    intro ℓ hℓ
    obtain ⟨ℓ', hℓ', he⟩ := h.inputLeaf_ofTop h₁.2.1 hmtop ℓ hℓ
    rw [← he]
    exact hH ℓ' hℓ'
  have hH₂ : ∀ ℓ ∈ inputLeaves G₂,
      Summable fun n : Fin d → ℤ => |H (botAddr B.lonePath ℓ.1) (k + latticePoint L n)| := by
    intro ℓ hℓ
    obtain ⟨ℓ', hℓ', he⟩ := h.inputLeaf_ofBot hmbot ℓ hℓ
    rw [← he]
    exact hH ℓ' hℓ'
  unfold coupleLeaves treeLeaves
  exact kernelLeaves_glue L γ δ (LG₁ := topLayered G₁ B h₁ r r'' hlt.le)
    (LG₂ := botLayered_couple hQ h₁ hs₁ h₂) h (decSplit_couple hQ h₁ hs₁ h₂)
    (decGlue_couple hQ h₁ hs₁ h₂) (not_flower_of_plain hplain) (not_flower_of_decodesTree h₁)
    (not_flower_of_plain hplain₂) h₁.2.1 hmtop hmbot H _ 0 _ r _ 0 hD k
    (summable_norm_leavesSummand L γ δ _ _ _ _ k _ _ (card_lone_le_of_decodesTree h₁) hH₁)
    (summable_norm_leavesSummand L γ δ _ _ _ _ k _ _ (card_lone_le_of_plain hplain₂) hH₂)

end WaveTurbulence.PL234
