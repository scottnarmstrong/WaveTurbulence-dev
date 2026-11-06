/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.GlueKernel

/-!
# Gluing data for a type-2 couple split at a chain append (TARGET L1236–L1241)

A couple carrier `G` decoded by `type2 (appendChain X X₂) Xm Qlp`, a paired tree `G₁` of sign `+` decoded
by `X`, and a couple carrier `G₂` decoded by `closeCouple X₂ Xm Qlp` (the spine's residual couple
`SourceApp.closeCouple`) satisfy the gluing data (`glueData_couple`) and the two decoration hypotheses
(`decSplit_couple`, `decGlue_couple`), via LINKS' code-level decorations `CplDec`, `ChainDec`.
-/

@[expose] public section
open WaveTurbulence.Induct

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine

theorem closeCouple_trees (X₂ Xm : RegChain) (Qlp : RegCpl) :
    (SourceApp.closeCouple X₂ Xm Qlp).trees = (X₂.plug 1 Qlp.trees.1, Xm.plug (-1) Qlp.trees.2) := by
  unfold SourceApp.closeCouple
  split_ifs with hn
  · simp only [Bool.and_eq_true] at hn
    cases X₂ <;> cases Xm <;> simp_all [RegChain.isNil, RegChain.plug]
  · rfl

theorem cplDec_closeCouple {V : Type*} [AddCommGroup V] {w : ℕ} (f : Fin w × Path → V)
    (X₂ Xm : RegChain) (Qlp : RegCpl) (a b : Fin w × Path) :
    CplDec f (SourceApp.closeCouple X₂ Xm Qlp) a b ↔ CplDec f (.type2 X₂ Xm Qlp) a b := by
  unfold SourceApp.closeCouple
  split_ifs with hn
  · simp only [Bool.and_eq_true] at hn
    cases X₂ <;> cases Xm <;> simp_all [RegChain.isNil, CplDec, ChainDec, RegChain.lonePath, addrExt]
  · rfl

theorem addrExt_zero_nil {w : ℕ} [NeZero w] (p : Path) :
    addrExt ((0 : Fin w), ([] : Path)) p = ((0 : Fin w), p) := by simp [addrExt]

variable {LG : LayeredGarden 2} {G₁ : Garden 1} {G₂ : Garden 2} {X X₂ Xm : RegChain} {Qlp : RegCpl}

/-- **The gluing data of a split type-2 couple.** -/
theorem glueData_couple (hQ : (RegCpl.type2 (appendChain X X₂) Xm Qlp).Decodes LG.garden)
    (h₁ : X.DecodesTree G₁) (hs₁ : G₁.sig 0 = 1)
    (h₂ : (SourceApp.closeCouple X₂ Xm Qlp).Decodes G₂) : GlueData LG.garden G₁ G₂ X := by
  have hsig : LG.garden.sig = ![1, -1] := hQ.1.2
  have hsig₂ : G₂.sig = ![1, -1] := h₂.1.2
  have t2 := closeCouple_trees X₂ Xm Qlp
  refine ⟨?_, ?_, ?_, ?_, h₁⟩
  · rw [hQ.2.1, h₂.2.1, t2, hsig]
    simp [RegCpl.trees, appendChain_plug]
  · intro j hj
    have hj1 : j = 1 := by fin_cases j <;> simp_all
    subst hj1
    rw [hQ.2.2.1, h₂.2.2.1, t2]
    rfl
  · rw [hsig, hsig₂]
  · rw [hs₁, hsig]
    rfl

variable (hQ : (RegCpl.type2 (appendChain X X₂) Xm Qlp).Decodes LG.garden)
    (h₁ : X.DecodesTree G₁) (hs₁ : G₁.sig 0 = 1)
    (h₂ : (SourceApp.closeCouple X₂ Xm Qlp).Decodes G₂)

/-- The code-level decoration of the glued couple, split. -/
theorem cplDec_glued_iff {V : Type*} [AddCommGroup V] (f : Fin 2 × Path → V) :
    CplDec f (.type2 (appendChain X X₂) Xm Qlp) (0, []) (1, []) ↔
      ChainDec f X 1 (0, []) ∧ CplDec f (.type2 X₂ Xm Qlp) (0, X.lonePath) (1, []) := by
  simp only [CplDec, chainDec_append, appendChain_lonePath, addrExt_zero_nil]
  have e : addrExt ((0 : Fin 2), X.lonePath) X₂.lonePath = ((0 : Fin 2), X.lonePath ++ X₂.lonePath) := by
    simp [addrExt]
  rw [e]
  tauto

include hQ h₁ hs₁ h₂ in
/-- **Splitting decorations of the glued couple.** -/
theorem decSplit_couple {V : Type*} [AddCommGroup V] :
    (glueData_couple hQ h₁ hs₁ h₂).DecSplit V := by
  intro κ hκ
  set h := glueData_couple hQ h₁ hs₁ h₂
  have hc := (cplDec_glued_iff (X := X) (X₂ := X₂) (Xm := Xm) (Qlp := Qlp) (extend κ)).mp
    (cplDec_of_decoration hQ hκ)
  constructor
  · have h1 : ChainDec (extend κ ∘ topAddr) X (G₁.sig 0) (0, []) := by
      rw [hs₁, chainDec_comp (topAddr_hom (w := 2))]
      exact hc.1
    have := isDecoration_of_chainDec h₁ h1
    convert this using 1
    funext x
    show κ (h.ι₁ x) = extend κ (h.ι₁ x).1
    rw [extend_node]
  · have h2 : CplDec (extend κ ∘ botAddr X.lonePath) (SourceApp.closeCouple X₂ Xm Qlp) (0, []) (1, []) := by
      rw [cplDec_closeCouple, cplDec_comp (botAddr_hom X.lonePath)]
      have e0 : botAddr X.lonePath ((0 : Fin 2), ([] : Path)) = (0, X.lonePath) := by simp [botAddr]
      have e1 : botAddr X.lonePath ((1 : Fin 2), ([] : Path)) = (1, []) := by simp [botAddr]
      rw [e0, e1]
      exact hc.2
    have := isDecoration_of_cplDec h₂ h2
    convert this using 1
    funext y
    show κ (h.ι₂ y) = extend κ (h.ι₂ y).1
    rw [extend_node]

include hQ h₁ hs₁ h₂ in
/-- **Gluing decorations of the two pieces.** -/
theorem decGlue_couple {V : Type*} [AddCommGroup V] :
    GlueData.DecGlue (G := LG.garden) (G₁ := G₁) (G₂ := G₂) (X := X) V := by
  intro κ₁ κ₂ hκ₁ hκ₂ h0₁ h0₂
  set h := glueData_couple hQ h₁ hs₁ h₂
  classical
  let F : Fin 2 × Path → V := GlueData.glueAddr (w := 2) (X := X) κ₁ κ₂
  have hF : GlueData.glue (X := X) κ₁ κ₂ = fun a : GNode LG.garden.tree => F a.1 := rfl
  rw [hF]
  refine isDecoration_of_cplDec hQ ((cplDec_glued_iff F).mpr ⟨?_, ?_⟩)
  · have hd₁ := chainDec_of_decoration h₁ hκ₁
    rw [hs₁] at hd₁
    have hcong : ∀ q ∈ (X.plug 1 .leaf).nodes, (F ∘ topAddr) (addrExt ((0 : Fin 1), ([] : Path)) q) =
        extend κ₁ (addrExt ((0 : Fin 1), ([] : Path)) q) := by
      intro q hq
      simp only [Function.comp_apply, topAddr, addrExt_zero_nil]
      by_cases hpre : X.lonePath <+: q
      · have hq' := plug_leaf_prefix X 1 hq hpre
        subst hq'
        simp only [F, GlueData.glueAddr, List.prefix_refl, not_true_eq_false, and_false, ite_false]
        have hu : GlueData.unbot X.lonePath ((0 : Fin 2), X.lonePath) = (GNode.root G₂.tree 0).1 := by
          simp [GlueData.unbot, GNode.root]
        rw [hu, extend_node, h0₂]
        have hl : ((0 : Fin 1), X.lonePath) = h.lone.1 := rfl
        rw [hl, extend_node, h.lone_eq_root hκ₁, h0₁]
      · simp [F, GlueData.glueAddr, hpre]
    have hc : ChainDec (F ∘ topAddr) X 1 ((0 : Fin 1), ([] : Path)) :=
      (chainDec_congr X 1 ((0 : Fin 1), ([] : Path)) hcong).mpr hd₁
    exact (chainDec_comp (topAddr_hom (w := 2)) F X 1 ((0 : Fin 1), ([] : Path))).mp hc
  · rw [← cplDec_closeCouple]
    have e0 : botAddr X.lonePath ((0 : Fin 2), ([] : Path)) = (0, X.lonePath) := by simp [botAddr]
    have e1 : botAddr X.lonePath ((1 : Fin 2), ([] : Path)) = (1, []) := by simp [botAddr]
    rw [← e0, ← e1, ← cplDec_comp (botAddr_hom X.lonePath)]
    have hFb : F ∘ botAddr X.lonePath = extend κ₂ := by
      funext y
      simp only [Function.comp_apply, F, GlueData.glueAddr, GlueData.botAddr_not_top X.lonePath y,
        ite_false, GlueData.unbot_botAddr]
    rw [hFb]
    exact cplDec_of_decoration h₂ hκ₂

end WaveTurbulence.PL234
