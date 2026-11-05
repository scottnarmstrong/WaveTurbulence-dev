/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftFreeTimes
public import WaveTurbulence.Foundations.XChain.GraftLeafParents
/-! Prescribed flower-parent times on arbitrary top forests and free lower components. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open scoped Classical

abbrev GraftTopFreeBranch {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) :=
  {b : GBranch top // ¬ (markedGardenGraft sig top P low hsig).IsFlowerParent
    (gardenBranchEquiv top P low (.inl b))}

noncomputable def graftFlowerFreeBranchEquiv {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hf : ∀ B b, ¬ (low B).IsFlowerParent b) :
    GraftTopFreeBranch sig top P low hsig ⊕ (Σ B : P.parts, GBranch (low B).tree) ≃
      (markedGardenGraft sig top P low hsig).FreeBranch :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeUnivEquiv
    (fun z : Σ B : P.parts, GBranch (low B).tree => fun h => hf z.1 z.2
      ((markedGardenGraft_flowerParent_lower_iff sig top P low hsig z.1 z.2).mp h))).symm).trans
    (graftFreeBranchEquiv top P low (fun b => ¬ (markedGardenGraft sig top P low hsig).IsFlowerParent b))

noncomputable def graftFlowerFreeTimeSplit {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hf : ∀ B b, ¬ (low B).IsFlowerParent b) :
    ((markedGardenGraft sig top P low hsig).FreeBranch → ℝ) ≃ᵐ
      (GraftTopFreeBranch sig top P low hsig → ℝ) × ((Σ B : P.parts, GBranch (low B).tree) → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (graftFlowerFreeBranchEquiv sig top P low hsig hf)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ))

theorem measurePreserving_graftFlowerFreeTimeSplit {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hf : ∀ B b, ¬ (low B).IsFlowerParent b) :
    MeasurePreserving (graftFlowerFreeTimeSplit sig top P low hsig hf) volume
      ((volume : Measure (GraftTopFreeBranch sig top P low hsig → ℝ)).prod
        (volume : Measure ((Σ B : P.parts, GBranch (low B).tree) → ℝ))) := by
  have h₁ := (measurePreserving_piCongrLeft
    (fun _ : (markedGardenGraft sig top P low hsig).FreeBranch => (volume : Measure ℝ))
    (graftFlowerFreeBranchEquiv sig top P low hsig hf)).symm
  have h₂ := measurePreserving_sumPiEquivProdPi
    (fun _ : GraftTopFreeBranch sig top P low hsig ⊕ (Σ B : P.parts, GBranch (low B).tree) =>
      (volume : Measure ℝ))
  exact h₂.comp h₁

noncomputable def graftTopExtendTime {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (s : ℝ) (τ : GraftTopFreeBranch sig top P low hsig → ℝ) (b : GBranch top) : ℝ :=
  if h : (markedGardenGraft sig top P low hsig).IsFlowerParent (gardenBranchEquiv top P low (.inl b))
    then s else τ ⟨b, h⟩

theorem graft_extendTime_top {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hf : ∀ B b, ¬ (low B).IsFlowerParent b) (s : ℝ)
    (τ : (markedGardenGraft sig top P low hsig).FreeBranch → ℝ) (b : GBranch top) :
    (markedGardenGraft sig top P low hsig).extendTime s τ (gardenBranchEquiv top P low (.inl b)) =
      graftTopExtendTime sig top P low hsig s (graftFlowerFreeTimeSplit sig top P low hsig hf τ).1 b := by
  unfold Garden.extendTime graftTopExtendTime
  split_ifs
  · rfl
  · rfl

theorem graft_extendTime_lower {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hf : ∀ B b, ¬ (low B).IsFlowerParent b) (s : ℝ)
    (τ : (markedGardenGraft sig top P low hsig).FreeBranch → ℝ)
    (B : P.parts) (b : GBranch (low B).tree) :
    (markedGardenGraft sig top P low hsig).extendTime s τ (gardenBranchEquiv top P low (.inr ⟨B, b⟩)) =
      (graftFlowerFreeTimeSplit sig top P low hsig hf τ).2 ⟨B, b⟩ := by
  have hn : ¬ (markedGardenGraft sig top P low hsig).IsFlowerParent
      (gardenBranchEquiv top P low (.inr ⟨B, b⟩)) := fun h =>
    hf B b ((markedGardenGraft_flowerParent_lower_iff sig top P low hsig B b).mp h)
  simp only [Garden.extendTime, hn, dite_false]
  rfl

theorem graftTimeSplit_extendTime_top {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hf : ∀ B b, ¬ (low B).IsFlowerParent b) (s : ℝ)
    (τ : (markedGardenGraft sig top P low hsig).FreeBranch → ℝ) :
    (graftTimeSplit top P low ((markedGardenGraft sig top P low hsig).extendTime s τ)).1 =
      graftTopExtendTime sig top P low hsig s (graftFlowerFreeTimeSplit sig top P low hsig hf τ).1 := by
  funext b
  exact graft_extendTime_top sig top P low hsig hf s τ b

theorem graftTimeSplit_extendTime_lower {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hf : ∀ B b, ¬ (low B).IsFlowerParent b) (s : ℝ)
    (τ : (markedGardenGraft sig top P low hsig).FreeBranch → ℝ) :
    (graftTimeSplit top P low ((markedGardenGraft sig top P low hsig).extendTime s τ)).2 =
      (graftFlowerFreeTimeSplit sig top P low hsig hf τ).2 := by
  funext z
  exact graft_extendTime_lower sig top P low hsig hf s τ z.1 z.2

end WaveTurbulence.Induct
