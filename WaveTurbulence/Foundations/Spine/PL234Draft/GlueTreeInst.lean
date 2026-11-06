/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.GlueCouple

/-!
# Gluing data for a regular tree split at a chain append (TARGET L1244–L1246)

A paired-tree carrier `G` decoded by `appendChain X X₂`, and paired trees `G₁`, `G₂` decoded by `X`, `X₂`,
all of the same sign, satisfy the gluing data (`glueData_tree`) and the two decoration hypotheses
(`decSplit_tree`, `decGlue_tree`).
-/

@[expose] public section
open WaveTurbulence.Induct

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine

variable {LG : LayeredGarden 1} {G₁ G₂ : Garden 1} {X X₂ : RegChain}

/-- **The gluing data of a split regular tree.** -/
theorem glueData_tree (hG : (appendChain X X₂).DecodesTree LG.garden) (h₁ : X.DecodesTree G₁)
    (hs₁ : G₁.sig 0 = LG.garden.sig 0) (h₂ : X₂.DecodesTree G₂) (hs₂ : G₂.sig 0 = LG.garden.sig 0) :
    GlueData LG.garden G₁ G₂ X := by
  refine ⟨?_, fun j hj => absurd (Subsingleton.elim j 0) hj, ?_, hs₁, h₁⟩
  · rw [hG.1, h₂.1, hs₂, appendChain_plug]
  · funext j
    rw [Subsingleton.elim j 0, hs₂]

variable (hG : (appendChain X X₂).DecodesTree LG.garden) (h₁ : X.DecodesTree G₁)
    (hs₁ : G₁.sig 0 = LG.garden.sig 0) (h₂ : X₂.DecodesTree G₂) (hs₂ : G₂.sig 0 = LG.garden.sig 0)

theorem botAddr_zero_nil (lp : Path) : botAddr lp ((0 : Fin 1), ([] : Path)) = ((0 : Fin 1), lp) := by
  simp [botAddr]

include hG h₁ hs₁ h₂ hs₂ in
/-- **Splitting decorations of the glued tree.** -/
theorem decSplit_tree {V : Type*} [AddCommGroup V] :
    (glueData_tree hG h₁ hs₁ h₂ hs₂).DecSplit V := by
  intro κ hκ
  set h := glueData_tree hG h₁ hs₁ h₂ hs₂
  have hc := (chainDec_append (extend κ) X X₂ _ _).mp (chainDec_of_decoration hG hκ)
  rw [addrExt_zero_nil] at hc
  constructor
  · have h1 : ChainDec (extend κ ∘ topAddr) X (G₁.sig 0) (0, []) := by
      rw [hs₁, chainDec_comp (topAddr_hom (w := 1))]
      exact hc.1
    have := isDecoration_of_chainDec h₁ h1
    convert this using 1
    funext x
    show κ (h.ι₁ x) = extend κ (h.ι₁ x).1
    rw [extend_node]
  · have h2 : ChainDec (extend κ ∘ botAddr X.lonePath) X₂ (G₂.sig 0) (0, []) := by
      rw [hs₂, chainDec_comp (botAddr_hom X.lonePath), botAddr_zero_nil]
      exact hc.2
    have := isDecoration_of_chainDec h₂ h2
    convert this using 1
    funext y
    show κ (h.ι₂ y) = extend κ (h.ι₂ y).1
    rw [extend_node]

include hG h₁ hs₁ h₂ hs₂ in
/-- **Gluing decorations of the two pieces of a tree.** -/
theorem decGlue_tree {V : Type*} [AddCommGroup V] :
    GlueData.DecGlue (G := LG.garden) (G₁ := G₁) (G₂ := G₂) (X := X) V := by
  intro κ₁ κ₂ hκ₁ hκ₂ h0₁ h0₂
  set h := glueData_tree hG h₁ hs₁ h₂ hs₂
  let F : Fin 1 × Path → V := GlueData.glueAddr (w := 1) (X := X) κ₁ κ₂
  have hF : GlueData.glue (X := X) κ₁ κ₂ = fun a : GNode LG.garden.tree => F a.1 := rfl
  rw [hF]
  refine isDecoration_of_chainDec hG ((chainDec_append F X X₂ _ _).mpr ⟨?_, ?_⟩)
  · have hd₁ := chainDec_of_decoration h₁ hκ₁
    rw [hs₁] at hd₁
    have hcong : ∀ q ∈ (X.plug (LG.garden.sig 0) .leaf).nodes,
        (F ∘ topAddr) (addrExt ((0 : Fin 1), ([] : Path)) q) =
          extend κ₁ (addrExt ((0 : Fin 1), ([] : Path)) q) := by
      intro q hq
      simp only [Function.comp_apply, topAddr, addrExt_zero_nil]
      by_cases hpre : X.lonePath <+: q
      · have hq' := plug_leaf_prefix X _ hq hpre
        subst hq'
        simp only [F, GlueData.glueAddr, List.prefix_refl, not_true_eq_false, and_false, ite_false]
        have hu : GlueData.unbot X.lonePath ((0 : Fin 1), X.lonePath) = (GNode.root G₂.tree 0).1 := by
          simp [GlueData.unbot, GNode.root]
        rw [hu, extend_node, h0₂]
        have hl : ((0 : Fin 1), X.lonePath) = h.lone.1 := rfl
        rw [hl, extend_node, h.lone_eq_root hκ₁, h0₁]
      · simp [F, GlueData.glueAddr, hpre]
    have hc : ChainDec (F ∘ topAddr) X (LG.garden.sig 0) ((0 : Fin 1), ([] : Path)) :=
      (chainDec_congr X _ ((0 : Fin 1), ([] : Path)) hcong).mpr hd₁
    exact (chainDec_comp (topAddr_hom (w := 1)) F X _ ((0 : Fin 1), ([] : Path))).mp hc
  · rw [addrExt_zero_nil, ← botAddr_zero_nil, ← chainDec_comp (botAddr_hom X.lonePath)]
    have hFb : F ∘ botAddr X.lonePath = extend κ₂ := by
      funext y
      simp only [Function.comp_apply, F, GlueData.glueAddr, GlueData.botAddr_not_top X.lonePath y,
        ite_false, GlueData.unbot_botAddr]
    rw [hFb, ← hs₂]
    exact chainDec_of_decoration h₂ hκ₂

end WaveTurbulence.PL234
