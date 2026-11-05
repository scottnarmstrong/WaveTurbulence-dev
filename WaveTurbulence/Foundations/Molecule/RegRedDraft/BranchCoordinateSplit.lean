/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeBranchEquiv
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Actual core / regular-couple / regular-tree clock splitting (TARGET redkg) -/

@[expose] public section
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton MeasureTheory

abbrev CoupleBranchIndex {w : ℕ} {S : Garden w} (D : ReconstructionData S) :=
  Σ p : SourcePair S, GBranch (decodedCouple (D.couple p)).tree

abbrev ChainBranchIndex {w : ℕ} {S : Garden w} (D : ReconstructionData S) :=
  Σ b : GBranch S.tree, ChainBranchPath D b

abbrev ReplacementBranchIndex {w : ℕ} {S : Garden w} (D : ReconstructionData S) :=
  CoupleBranchIndex D ⊕ ChainBranchIndex D

noncomputable def nativeBranchIndicesEquiv {w : ℕ} {S : Garden w} (D : ReconstructionData S) :
    (Σ slot : ReplacementSlot S, NativeBranch D slot) ≃ GBranch S.tree ⊕ ReplacementBranchIndex D where
  toFun
    | ⟨.inl p,x⟩ => .inr (.inl ⟨p,x⟩)
    | ⟨.inr b,none⟩ => .inl b
    | ⟨.inr b,some q⟩ => .inr (.inr ⟨b,q⟩)
  invFun
    | .inl b => ⟨.inr b,none⟩
    | .inr (.inl ⟨p,x⟩) => ⟨.inl p,x⟩
    | .inr (.inr ⟨b,q⟩) => ⟨.inr b,some q⟩
  left_inv := by
    rintro ⟨slot,x⟩
    cases slot with
    | inl p => rfl
    | inr b => cases x <;> rfl
  right_inv := by
    rintro (b | (⟨p,x⟩ | ⟨b,q⟩)) <;> rfl

/-- All branching nodes are exactly the retained original core and the actual
branches of the native regular replacements. -/
noncomputable def sourceBranchEquiv {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : GBranch S.tree ⊕ ReplacementBranchIndex D ≃ GBranch (D.forest hS) :=
  (nativeBranchIndicesEquiv D).symm.trans (nativeBranchEquiv D hS)

theorem sourceBranchEquiv_core {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) : sourceBranchEquiv D hS (.inl b) = D.coreBranch hS b := rfl

theorem sourceBranchEquiv_couple {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (p : SourcePair S) (b : GBranch (decodedCouple (D.couple p)).tree) :
    sourceBranchEquiv D hS (.inr (.inl ⟨p,b⟩)) = coupleContextBranch D hS p b := rfl

theorem sourceBranchEquiv_chain {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) (q : ChainBranchPath D b) :
    sourceBranchEquiv D hS (.inr (.inr ⟨b,q⟩)) = chainContextBranch D hS b q := rfl

noncomputable def sourceTimeSplit {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : (GBranch (D.forest hS) → ℝ) ≃ᵐ
      (GBranch S.tree → ℝ) × (ReplacementBranchIndex D → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (sourceBranchEquiv D hS)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ))

theorem sourceTimeSplit_core {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (τ : GBranch (D.forest hS) → ℝ) (b : GBranch S.tree) :
    (sourceTimeSplit D hS τ).1 b = τ (D.coreBranch hS b) := rfl

theorem measurePreserving_sourceTimeSplit {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : MeasurePreserving (sourceTimeSplit D hS) volume
      ((volume : Measure (GBranch S.tree → ℝ)).prod (volume : Measure (ReplacementBranchIndex D → ℝ))) := by
  have h₁ := (measurePreserving_piCongrLeft
    (fun _ : GBranch (D.forest hS) => (volume : Measure ℝ)) (sourceBranchEquiv D hS)).symm
  have h₂ := measurePreserving_sumPiEquivProdPi
    (fun _ : GBranch S.tree ⊕ ReplacementBranchIndex D => (volume : Measure ℝ))
  exact h₂.comp h₁

end WaveTurbulence.RegRed
