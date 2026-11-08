/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsGlue.Decoration
/-! # A3a CAPS-GLUE: the factors of the kernel summand split over the components (general `fix`, `off`, `wt`) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.CapsGlue
open TTree Finset WaveTurbulence.FlowerP7

variable {m w d : ℕ} {a : Fin m → ℕ}

/-- Glued data on branching nodes: pins `fix`, times, upper bounds. -/
noncomputable def gBr {α : Type*} (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree)
    (f : ∀ c, GBranch (TA c) → α) : GBranch (gT σ TA) → α :=
  fun b => f ((glueBranchN σ TA).symm b).1 ((glueBranchN σ TA).symm b).2

@[simp] theorem gBr_apply {α : Type*} (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree)
    (f : ∀ c, GBranch (TA c) → α) (c : Fin m) (x : GBranch (TA c)) :
    gBr σ TA f (glueBranchN σ TA ⟨c, x⟩) = f c x := by
  unfold gBr
  rw [Equiv.symm_apply_apply]

/-- Glued removed-phase set. -/
noncomputable def gOff (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree)
    (off : ∀ c, Finset (GBranch (TA c))) : Finset (GBranch (gT σ TA)) :=
  Finset.univ.filter fun b => ((glueBranchN σ TA).symm b).2 ∈ off ((glueBranchN σ TA).symm b).1

theorem mem_gOff (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree)
    (off : ∀ c, Finset (GBranch (TA c))) (c : Fin m) (x : GBranch (TA c)) :
    glueBranchN σ TA ⟨c, x⟩ ∈ gOff σ TA off ↔ x ∈ off c := by
  unfold gOff
  rw [Finset.mem_filter, Equiv.symm_apply_apply]
  simp

/-- The glued decoration weight: the product of the weights of the restrictions. -/
noncomputable def gWt (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree)
    (wt : ∀ c, (GNode (TA c) → Mom d) → ℝ) : (GNode (gT σ TA) → Mom d) → ℝ :=
  fun k => ∏ c, wt c (fun x => k (glueNodeN σ TA ⟨c, x⟩))

theorem epsDec_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c))
    (κ : ∀ c, GNode (GA c).tree → (Fin d → ℤ)) :
    epsDec (glueGardenN σ GA) (gLabelN σ GA κ) = ∏ c, epsDec (GA c) (κ c) := by
  unfold epsDec
  rw [← (glueBranchN σ fun c => (GA c).tree).prod_comp, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun c _ => Finset.prod_congr rfl fun x _ => ?_
  simp only [glueBranchN_child, gLabelN_apply]

theorem coset_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c)) (L : ℝ) (k : Mom d)
    (κ : ∀ c, GNode (GA c).tree → (Fin d → ℤ)) (c : Fin m) (x : GNode (GA c).tree) :
    cosetDecoration (glueGardenN σ GA) L k (gLabelN σ GA κ) (glueNodeN σ (fun c => (GA c).tree) ⟨c, x⟩) =
      cosetDecoration (GA c) L k (κ c) x := by
  simp [cosetDecoration]

theorem omega_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c)) (L : ℝ) (k : Mom d)
    (κ : ∀ c, GNode (GA c).tree → (Fin d → ℤ)) (c : Fin m) (x : GBranch (GA c).tree) :
    omegaNode (glueGardenN σ GA) (cosetDecoration (glueGardenN σ GA) L k (gLabelN σ GA κ))
      (glueBranchN σ (fun c => (GA c).tree) ⟨c, x⟩) = omegaNode (GA c) (cosetDecoration (GA c) L k (κ c)) x := by
  unfold omegaNode
  rw [glueBranchN_child, glueBranchN_child, glueBranchN_child, glueBranchN_toNode,
    coset_glueN, coset_glueN, coset_glueN, coset_glueN]

theorem phaseProd_glueN (L γ δ : ℝ) (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (GA : ∀ c, Garden (a c))
    (off : ∀ c, Finset (GBranch (GA c).tree)) (k : Mom d)
    (κ : ∀ c, GNode (GA c).tree → (Fin d → ℤ)) (τ : ∀ c, GBranch (GA c).tree → ℝ) :
    phaseProdOff L γ δ (glueGardenN σ GA) (gOff σ (fun c => (GA c).tree) off)
        (cosetDecoration (glueGardenN σ GA) L k (gLabelN σ GA κ)) (gBr σ (fun c => (GA c).tree) τ) =
      ∏ c, phaseProdOff L γ δ (GA c) (off c) (cosetDecoration (GA c) L k (κ c)) (τ c) := by
  unfold phaseProdOff
  rw [← (glueBranchN σ fun c => (GA c).tree).prod_comp, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun c _ => Finset.prod_congr rfl fun x _ => ?_
  simp only [mem_gOff, gBr_apply, glueBranchN_toNode, glueN_sign, omega_glueN]

theorem inputProd_glueN (L : ℝ) (F : ℕ → Mom d → ℝ) (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w)
    (LA : ∀ c, LayeredGarden (a c)) (k : Mom d) (κ : ∀ c, GNode (LA c).garden.tree → (Fin d → ℤ)) :
    (∏ ℓ ∈ inputLeaves (glueL σ LA).garden,
        (F ((glueL σ LA).layer ℓ.toNode)
          (cosetDecoration (glueL σ LA).garden L k (gLabelN σ (fun c => (LA c).garden) κ) ℓ.toNode) : ℂ)) =
      ∏ c, ∏ ℓ ∈ inputLeaves (LA c).garden,
        (F ((LA c).layer ℓ.toNode) (cosetDecoration (LA c).garden L k (κ c) ℓ.toNode) : ℂ) := by
  classical
  unfold inputLeaves
  simp only [Finset.prod_filter]
  rw [← (glueLeafN σ fun c => (LA c).garden.tree).prod_comp, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun c _ => Finset.prod_congr rfl fun x _ => ?_
  have hc : ((glueL σ LA).garden.sign (glueLeafN σ (fun c => (LA c).garden.tree) ⟨c, x⟩).toNode = 1 ∧
      (glueL σ LA).garden.mark (glueLeafN σ (fun c => (LA c).garden.tree) ⟨c, x⟩) = none) ↔
      ((LA c).garden.sign x.toNode = 1 ∧ (LA c).garden.mark x = none) := by
    rw [glueLeafN_toNode, glueN_sign, glueN_mark_leaf]
  by_cases h : ((LA c).garden.sign x.toNode = 1 ∧ (LA c).garden.mark x = none)
  · rw [if_pos (hc.2 h), if_pos h, glueLeafN_toNode, coset_glueN]
    simp only [gLayerN_apply]
  · rw [if_neg (fun h' => h (hc.1 h')), if_neg h]

end WaveTurbulence.Flower.CapsGlue
