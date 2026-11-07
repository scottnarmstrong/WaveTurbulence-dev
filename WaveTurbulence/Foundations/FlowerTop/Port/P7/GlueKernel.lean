/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueTerm
/-! FLOWER-P7: factorisation of the summand and of the time integral of a glued garden. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset MeasureTheory

variable {a b w d : ℕ}

/-- Integral over `(α ⊕ β → ℝ)` of a product. -/
theorem integral_sum_pi_mul {α β : Type*} [Fintype α] [Fintype β] (f : (α → ℝ) → ℂ) (g : (β → ℝ) → ℂ) :
    ∫ ρ : α ⊕ β → ℝ, f (fun i => ρ (.inl i)) * g (fun i => ρ (.inr i)) =
      (∫ x, f x) * ∫ y, g y := by
  have hmp := volume_measurePreserving_sumPiEquivProdPi (fun _ : α ⊕ β => ℝ)
  have := hmp.integral_comp' (f := MeasurableEquiv.sumPiEquivProdPi (fun _ : α ⊕ β => ℝ))
    (fun z => f z.1 * g z.2)
  have h2 : ∫ z : (α → ℝ) × (β → ℝ), f z.1 * g z.2 = (∫ x, f x) * ∫ y, g y := by
    rw [← integral_prod_mul]
    rfl
  rw [← h2, ← this]
  rfl

theorem epsDec_glue (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b)
    (κA : GNode GA.tree → (Fin d → ℤ)) (κB : GNode GB.tree → (Fin d → ℤ)) :
    epsDec (glueGarden σ GA GB) (gLabel σ GA GB κA κB) = epsDec GA κA * epsDec GB κB := by
  unfold epsDec
  rw [← (glueBranch σ GA.tree GB.tree).prod_comp, Fintype.prod_sum_type]
  congr 1
  · refine Finset.prod_congr rfl fun x _ => ?_
    simp only [glueBranch_child_inl, gLabel_inl]
  · refine Finset.prod_congr rfl fun x _ => ?_
    simp only [glueBranch_child_inr, gLabel_inr]

theorem coset_glue_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) (L : ℝ) (k : Mom d)
    (κA : GNode GA.tree → (Fin d → ℤ)) (κB : GNode GB.tree → (Fin d → ℤ)) (x : GNode GA.tree) :
    cosetDecoration (glueGarden σ GA GB) L k (gLabel σ GA GB κA κB) (glueNode σ GA.tree GB.tree (.inl x)) =
      cosetDecoration GA L k κA x := by
  simp [cosetDecoration]

theorem coset_glue_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) (L : ℝ) (k : Mom d)
    (κA : GNode GA.tree → (Fin d → ℤ)) (κB : GNode GB.tree → (Fin d → ℤ)) (x : GNode GB.tree) :
    cosetDecoration (glueGarden σ GA GB) L k (gLabel σ GA GB κA κB) (glueNode σ GA.tree GB.tree (.inr x)) =
      cosetDecoration GB L k κB x := by
  simp [cosetDecoration]

theorem omega_glue_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) (L : ℝ) (k : Mom d)
    (κA : GNode GA.tree → (Fin d → ℤ)) (κB : GNode GB.tree → (Fin d → ℤ)) (x : GBranch GA.tree) :
    omegaNode (glueGarden σ GA GB) (cosetDecoration (glueGarden σ GA GB) L k (gLabel σ GA GB κA κB))
      (glueBranch σ GA.tree GB.tree (.inl x)) = omegaNode GA (cosetDecoration GA L k κA) x := by
  unfold omegaNode
  rw [glueBranch_child_inl, glueBranch_child_inl, glueBranch_child_inl, glueBranch_toNode_inl,
    coset_glue_inl, coset_glue_inl, coset_glue_inl, coset_glue_inl]

theorem omega_glue_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) (L : ℝ) (k : Mom d)
    (κA : GNode GA.tree → (Fin d → ℤ)) (κB : GNode GB.tree → (Fin d → ℤ)) (x : GBranch GB.tree) :
    omegaNode (glueGarden σ GA GB) (cosetDecoration (glueGarden σ GA GB) L k (gLabel σ GA GB κA κB))
      (glueBranch σ GA.tree GB.tree (.inr x)) = omegaNode GB (cosetDecoration GB L k κB) x := by
  unfold omegaNode
  rw [glueBranch_child_inr, glueBranch_child_inr, glueBranch_child_inr, glueBranch_toNode_inr,
    coset_glue_inr, coset_glue_inr, coset_glue_inr, coset_glue_inr]

theorem phaseProd_glue (L γ δ : ℝ) (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) (k : Mom d)
    (κA : GNode GA.tree → (Fin d → ℤ)) (κB : GNode GB.tree → (Fin d → ℤ))
    (τA : GBranch GA.tree → ℝ) (τB : GBranch GB.tree → ℝ) :
    phaseProdOff L γ δ (glueGarden σ GA GB) ∅
        (cosetDecoration (glueGarden σ GA GB) L k (gLabel σ GA GB κA κB)) (gTime σ GA.tree GB.tree τA τB) =
      phaseProdOff L γ δ GA ∅ (cosetDecoration GA L k κA) τA *
        phaseProdOff L γ δ GB ∅ (cosetDecoration GB L k κB) τB := by
  unfold phaseProdOff
  simp only [Finset.notMem_empty, ite_false]
  rw [← (glueBranch σ GA.tree GB.tree).prod_comp, Fintype.prod_sum_type]
  congr 1
  · refine Finset.prod_congr rfl fun x _ => ?_
    rw [gTime_inl, glueBranch_toNode_inl, glue_sign_inl, omega_glue_inl]
  · refine Finset.prod_congr rfl fun x _ => ?_
    rw [gTime_inr, glueBranch_toNode_inr, glue_sign_inr, omega_glue_inr]

theorem inputProd_glue (L : ℝ) (F : ℕ → Mom d → ℝ) (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a)
    (LB : LayeredGarden b) (k : Mom d) (κA : GNode LA.garden.tree → (Fin d → ℤ))
    (κB : GNode LB.garden.tree → (Fin d → ℤ)) :
    (∏ ℓ ∈ inputLeaves (glueLayered σ LA LB).garden,
        (F ((glueLayered σ LA LB).layer ℓ.toNode)
          (cosetDecoration (glueLayered σ LA LB).garden L k (gLabel σ LA.garden LB.garden κA κB) ℓ.toNode) : ℂ)) =
      (∏ ℓ ∈ inputLeaves LA.garden, (F (LA.layer ℓ.toNode) (cosetDecoration LA.garden L k κA ℓ.toNode) : ℂ)) *
      ∏ ℓ ∈ inputLeaves LB.garden, (F (LB.layer ℓ.toNode) (cosetDecoration LB.garden L k κB ℓ.toNode) : ℂ) := by
  classical
  unfold inputLeaves
  rw [Finset.prod_filter, Finset.prod_filter, Finset.prod_filter,
    ← (glueLeaf σ LA.garden.tree LB.garden.tree).prod_comp, Fintype.prod_sum_type]
  congr 1
  · refine Finset.prod_congr rfl fun x _ => ?_
    have hc : ((glueGarden σ LA.garden LB.garden).sign (glueLeaf σ LA.garden.tree LB.garden.tree (.inl x)).toNode = 1 ∧
        (glueGarden σ LA.garden LB.garden).mark (glueLeaf σ LA.garden.tree LB.garden.tree (.inl x)) = none) ↔
        (LA.garden.sign x.toNode = 1 ∧ LA.garden.mark x = none) := by
      rw [glueLeaf_toNode_inl, glue_sign_inl, glue_mark_leaf_inl]
    by_cases h : (LA.garden.sign x.toNode = 1 ∧ LA.garden.mark x = none)
    · rw [if_pos (hc.2 h), if_pos h, glueLeaf_toNode_inl]
      simp only [glueLayered_layer_inl, gLayer_inl, coset_glue_inl]
    · rw [if_neg (fun h' => h (hc.1 h')), if_neg h]
  · refine Finset.prod_congr rfl fun x _ => ?_
    have hc : ((glueGarden σ LA.garden LB.garden).sign (glueLeaf σ LA.garden.tree LB.garden.tree (.inr x)).toNode = 1 ∧
        (glueGarden σ LA.garden LB.garden).mark (glueLeaf σ LA.garden.tree LB.garden.tree (.inr x)) = none) ↔
        (LB.garden.sign x.toNode = 1 ∧ LB.garden.mark x = none) := by
      rw [glueLeaf_toNode_inr, glue_sign_inr, glue_mark_leaf_inr]
    by_cases h : (LB.garden.sign x.toNode = 1 ∧ LB.garden.mark x = none)
    · rw [if_pos (hc.2 h), if_pos h, glueLeaf_toNode_inr]
      simp only [glueLayered_layer_inr, gLayer_inr, coset_glue_inr]
    · rw [if_neg (fun h' => h (hc.1 h')), if_neg h]

end WaveTurbulence.FlowerP7
