/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueDecoration
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapSum
/-! FLOWER-P7: the summand `kgTerm` of a glued garden (no designated nodes, no removed phases, weight `1`)
is the product of the summands of the two parts. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset MeasureTheory

variable {a b w d : ℕ}

/-- Branching nodes of the glued garden: the child relation. -/
theorem glue_isChildOf_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x' x : GBranch TA) :
    (glueBranch σ TA TB (.inl x')).IsChildOf (glueBranch σ TA TB (.inl x)) ↔ x'.IsChildOf x := by
  simp only [GBranch.IsChildOf, glueBranch_inl, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq]

theorem glue_isChildOf_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x' x : GBranch TB) :
    (glueBranch σ TA TB (.inr x')).IsChildOf (glueBranch σ TA TB (.inr x)) ↔ x'.IsChildOf x := by
  simp only [GBranch.IsChildOf, glueBranch_inr, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq]

theorem glue_not_isChildOf_inl_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x' : GBranch TA) (x : GBranch TB) :
    ¬ (glueBranch σ TA TB (.inl x')).IsChildOf (glueBranch σ TA TB (.inr x)) := by
  rintro ⟨h, -⟩
  simp only [glueBranch_inl, glueBranch_inr, EmbeddingLike.apply_eq_iff_eq, reduceCtorEq] at h

theorem glue_not_isChildOf_inr_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (x' : GBranch TB) (x : GBranch TA) :
    ¬ (glueBranch σ TA TB (.inr x')).IsChildOf (glueBranch σ TA TB (.inl x)) := by
  rintro ⟨h, -⟩
  simp only [glueBranch_inl, glueBranch_inr, EmbeddingLike.apply_eq_iff_eq, reduceCtorEq] at h

/-- Glued times. -/
noncomputable def gTime (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (τA : GBranch TA → ℝ) (τB : GBranch TB → ℝ) : GBranch (gT σ TA TB) → ℝ :=
  fun br => Sum.elim τA τB ((glueBranch σ TA TB).symm br)

@[simp] theorem gTime_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (τA : GBranch TA → ℝ) (τB : GBranch TB → ℝ) (x : GBranch TA) :
    gTime σ TA TB τA τB (glueBranch σ TA TB (.inl x)) = τA x := by simp [gTime]

@[simp] theorem gTime_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (TA : Fin a → TTree) (TB : Fin b → TTree)
    (τA : GBranch TA → ℝ) (τB : GBranch TB → ℝ) (x : GBranch TB) :
    gTime σ TA TB τA τB (glueBranch σ TA TB (.inr x)) = τB x := by simp [gTime]

theorem glue_layer_branch_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b)
    (x : GBranch LA.garden.tree) :
    (glueLayered σ LA LB).layer (glueBranch σ LA.garden.tree LB.garden.tree (.inl x)).toNode =
      LA.layer x.toNode := by
  rw [glueBranch_toNode_inl]; exact glueLayered_layer_inl ..

theorem glue_layer_branch_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b)
    (x : GBranch LB.garden.tree) :
    (glueLayered σ LA LB).layer (glueBranch σ LA.garden.tree LB.garden.tree (.inr x)).toNode =
      LB.layer x.toNode := by
  rw [glueBranch_toNode_inr]; exact glueLayered_layer_inr ..

theorem gLayer_branch_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b)
    (lA : GNode GA.tree → ℕ) (lB : GNode GB.tree → ℕ) (x : GBranch GA.tree) :
    gLayer σ GA GB lA lB (glueBranch σ GA.tree GB.tree (.inl x)).toNode = lA x.toNode := by
  rw [glueBranch_toNode_inl]; exact gLayer_inl ..

theorem gLayer_branch_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b)
    (lA : GNode GA.tree → ℕ) (lB : GNode GB.tree → ℕ) (x : GBranch GB.tree) :
    gLayer σ GA GB lA lB (glueBranch σ GA.tree GB.tree (.inr x)).toNode = lB x.toNode := by
  rw [glueBranch_toNode_inr]; exact gLayer_inr ..

theorem glue_domain_iff (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b)
    (upA : GBranch LA.garden.tree → ℝ) (upB : GBranch LB.garden.tree → ℝ)
    (τA : GBranch LA.garden.tree → ℝ) (τB : GBranch LB.garden.tree → ℝ) :
    gTime σ LA.garden.tree LB.garden.tree τA τB ∈
        kDomainFix (glueLayered σ LA LB)
          (fun br => Sum.elim upA upB ((glueBranch σ LA.garden.tree LB.garden.tree).symm br))
          (fun _ => none) ↔
      τA ∈ kDomainFix LA upA (fun _ => none) ∧ τB ∈ kDomainFix LB upB (fun _ => none) := by
  constructor
  · intro h
    refine ⟨fun x => ?_, fun x => ?_⟩
    · have hx := h (glueBranch σ LA.garden.tree LB.garden.tree (.inl x))
      refine ⟨fun _ => ?_, fun x' hx' _ => ?_⟩
      · have := hx.1 rfl
        simpa only [gLayer_branch_inl, glue_layer_branch_inl, gTime_inl, Equiv.symm_apply_apply, Sum.elim_inl] using this
      · have := hx.2 (glueBranch σ LA.garden.tree LB.garden.tree (.inl x'))
          ((glue_isChildOf_inl σ _ _ x' x).2 hx') (Or.inl rfl)
        simpa only [gTime_inl] using this
    · have hx := h (glueBranch σ LA.garden.tree LB.garden.tree (.inr x))
      refine ⟨fun _ => ?_, fun x' hx' _ => ?_⟩
      · have := hx.1 rfl
        simpa only [gLayer_branch_inr, glue_layer_branch_inr, gTime_inr, Equiv.symm_apply_apply, Sum.elim_inr] using this
      · have := hx.2 (glueBranch σ LA.garden.tree LB.garden.tree (.inr x'))
          ((glue_isChildOf_inr σ _ _ x' x).2 hx') (Or.inl rfl)
        simpa only [gTime_inr] using this
  · rintro ⟨hA, hB⟩ br
    obtain ⟨y, rfl⟩ := (glueBranch σ LA.garden.tree LB.garden.tree).surjective br
    rcases y with x | x
    · refine ⟨fun _ => ?_, fun b' hb' _ => ?_⟩
      · have := (hA x).1 rfl
        simpa only [gLayer_branch_inl, glue_layer_branch_inl, gTime_inl, Equiv.symm_apply_apply, Sum.elim_inl] using this
      · obtain ⟨y', rfl⟩ := (glueBranch σ LA.garden.tree LB.garden.tree).surjective b'
        rcases y' with x' | x'
        · have := (hA x).2 x' ((glue_isChildOf_inl σ _ _ x' x).1 hb') (Or.inl rfl)
          simpa only [gTime_inl] using this
        · exact absurd hb' (glue_not_isChildOf_inr_inl σ _ _ x' x)
    · refine ⟨fun _ => ?_, fun b' hb' _ => ?_⟩
      · have := (hB x).1 rfl
        simpa only [gLayer_branch_inr, glue_layer_branch_inr, gTime_inr, Equiv.symm_apply_apply, Sum.elim_inr] using this
      · obtain ⟨y', rfl⟩ := (glueBranch σ LA.garden.tree LB.garden.tree).surjective b'
        rcases y' with x' | x'
        · exact absurd hb' (glue_not_isChildOf_inl_inr σ _ _ x' x)
        · have := (hB x).2 x' ((glue_isChildOf_inr σ _ _ x' x).1 hb') (Or.inl rfl)
          simpa only [gTime_inr] using this

end WaveTurbulence.FlowerP7
