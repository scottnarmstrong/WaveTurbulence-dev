/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsGlue.Cap
/-! # A3a CAPS-GLUE: capped stems, depth selections `stemAt`/`selCap`, and `selOK` of a glue are those of the
components (the stem set of tree `σ ⟨c,i⟩` is the image of the stem set of tree `i` of component `c`). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsGlue
open TTree Finset WaveTurbulence WaveTurbulence.FlowerP7 WaveTurbulence.Flower.MkDefs

variable {m w d : ℕ} {a : Fin m → ℕ}

/-- The embedding of the branching nodes of component `c` into the glue. -/
def embBr (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) (c : Fin m) :
    GBranch (TA c) ↪ GBranch (gT σ TA) :=
  ⟨fun x => glueBranchN σ TA ⟨c, x⟩, fun x y h => by
    have := (glueBranchN σ TA).injective h
    simpa using this⟩

@[simp] theorem embBr_apply (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) (c : Fin m)
    (x : GBranch (TA c)) : embBr σ TA c x = glueBranchN σ TA ⟨c, x⟩ := rfl

theorem glueN_isDesc_same (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) (c : Fin m)
    (x x' : GNode (TA c)) :
    (glueNodeN σ TA ⟨c, x⟩).IsDesc (glueNodeN σ TA ⟨c, x'⟩) ↔ x.IsDesc x' := by
  simp only [GNode.IsDesc, glueNodeN_val, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq, heq_eq_eq, true_and]

theorem glueN_not_isDesc (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree) {c c' : Fin m}
    (h : c' ≠ c) (x : GNode (TA c')) (x' : GNode (TA c)) :
    ¬ (glueNodeN σ TA ⟨c', x⟩).IsDesc (glueNodeN σ TA ⟨c, x'⟩) := by
  rintro ⟨h1, -⟩
  simp only [glueNodeN_val, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq] at h1
  exact h h1.1

theorem onCapStem_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (J : Finset (Fin w)) (c : Fin m) (x : GNode (LA c).garden.tree) :
    OnCapStem (glueL σ LA) J (glueNodeN σ (fun c => (LA c).garden.tree) ⟨c, x⟩) ↔
      OnCapStem (LA c) (resJ σ J c) x := by
  unfold OnCapStem
  rw [exists_leaf_glueN]
  constructor
  · rintro ⟨c', y, h1, h2⟩
    rw [glueLeafN_toNode] at h2
    by_cases hc : c' = c
    · subst hc
      exact ⟨y, (isCapFlower_glueN σ LA J c' y).1 h1,
        (glueN_isDesc_same σ (fun c => (LA c).garden.tree) c' x y.toNode).1 h2⟩
    · exact absurd h2 (glueN_not_isDesc σ (fun c => (LA c).garden.tree) (c := c') (c' := c) (Ne.symm hc) x
        y.toNode)
  · rintro ⟨y, h1, h2⟩
    exact ⟨c, y, (isCapFlower_glueN σ LA J c y).2 h1, by
      rw [glueLeafN_toNode]; exact (glueN_isDesc_same σ (fun c => (LA c).garden.tree) c x y.toNode).2 h2⟩

end WaveTurbulence.Flower.CapsGlue
