/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsGlue.Weights
/-! # A3a CAPS-GLUE: frontier cutoffs, anchored pair-type profiles and dagger indicators of a glue
are products over the components -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsGlue
open TTree Finset WaveTurbulence WaveTurbulence.FlowerP7 WaveTurbulence.Flower.MkDefs

variable {m w d : ℕ} {a : Fin m → ℕ}

theorem parentLayer_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c)) (p : ℕ)
    (c : Fin m) (x : GNode (LA c).garden.tree) :
    (glueL σ LA).parentLayer p (glueNodeN σ (fun c => (LA c).garden.tree) ⟨c, x⟩) = (LA c).parentLayer p x := by
  unfold LayeredGarden.parentLayer
  by_cases hx : x.1.2 = []
  · rw [if_pos (by simpa using hx), if_pos hx]
  · rw [if_neg (by simpa using hx), if_neg hx]
    refine glueL_layer σ LA c ⟨(x.1.1, x.1.2.dropLast), ?_⟩

theorem isTopLeaf_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c)) (p : ℕ)
    (c : Fin m) (x : GNode (LA c).garden.tree) :
    (glueL σ LA).IsTopLeaf p (glueNodeN σ (fun c => (LA c).garden.tree) ⟨c, x⟩) ↔ (LA c).IsTopLeaf p x := by
  unfold LayeredGarden.IsTopLeaf
  rw [parentLayer_glueN, glueL_layer]
  simp only [glueNodeN_val]
  simp only [gT_apply]

theorem isFlowerNode_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (c : Fin m) (x : GNode (LA c).garden.tree) :
    (glueL σ LA).IsFlowerNode (glueNodeN σ (fun c => (LA c).garden.tree) ⟨c, x⟩) ↔ (LA c).IsFlowerNode x := by
  unfold LayeredGarden.IsFlowerNode
  rw [exists_leaf_glueN]
  constructor
  · rintro ⟨c', y, h1, h2⟩
    rw [glueLeafN_toNode] at h2
    have := (glueNodeN σ fun c => (LA c).garden.tree).injective h2
    simp only [Sigma.mk.injEq] at this
    obtain ⟨rfl, h3⟩ := this
    refine ⟨y, ?_, eq_of_heq h3⟩
    unfold Garden.IsFlower at h1 ⊢
    rwa [show (glueL σ LA).garden.mark = (glueGardenN σ fun c => (LA c).garden).mark from rfl,
      glueN_mark_leaf] at h1
  · rintro ⟨y, h1, h2⟩
    refine ⟨c, y, ?_, by rw [glueLeafN_toNode, h2]⟩
    unfold Garden.IsFlower at h1 ⊢
    rwa [show (glueL σ LA).garden.mark = (glueGardenN σ fun c => (LA c).garden).mark from rfl,
      glueN_mark_leaf]

theorem frontierW_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c)) (p : ℕ)
    (Rf : Fin w → Option ℝ) (k : GNode (glueL σ LA).garden.tree → Mom d) :
    Typed.frontierW (glueL σ LA) p Rf k =
      ∏ c, Typed.frontierW (LA c) p (resF σ Rf c) (resK σ (fun c => (LA c).garden.tree) k c) := by
  unfold Typed.frontierW
  rw [← (glueNodeN σ fun c => (LA c).garden.tree).prod_comp, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun c _ => Finset.prod_congr rfl fun x _ => ?_
  have hc : ((glueL σ LA).IsTopLeaf p (glueNodeN σ (fun c => (LA c).garden.tree) ⟨c, x⟩) ∧
      (glueL σ LA).layer (glueNodeN σ (fun c => (LA c).garden.tree) ⟨c, x⟩) < p ∧
      ¬ (glueL σ LA).IsFlowerNode (glueNodeN σ (fun c => (LA c).garden.tree) ⟨c, x⟩)) ↔
      ((LA c).IsTopLeaf p x ∧ (LA c).layer x < p ∧ ¬ (LA c).IsFlowerNode x) := by
    rw [isTopLeaf_glueN, glueL_layer, isFlowerNode_glueN]
  by_cases h : ((LA c).IsTopLeaf p x ∧ (LA c).layer x < p ∧ ¬ (LA c).IsFlowerNode x)
  · rw [if_pos (hc.2 h), if_pos h]
    rfl
  · rw [if_neg (fun h' => h (hc.1 h')), if_neg h]

end WaveTurbulence.Flower.CapsGlue
