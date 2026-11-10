/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.PiCurryVolume
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeClockTransport

/-! # Independent actual replacement time blocks, with their source volume -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton MeasureTheory

def NativeClockBranch {w : ℕ} {S : Garden w} (D : ReconstructionData S) : ReplacementSlot S → Type
  | .inl p => GBranch (decodedCouple (D.couple p)).tree
  | .inr b => GBranch (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree

noncomputable instance {w : ℕ} {S : Garden w} (D : ReconstructionData S) (s : ReplacementSlot S) :
    Fintype (NativeClockBranch D s) := by
  cases s <;> dsimp only [NativeClockBranch] <;> infer_instance

abbrev NativeTimeBlock {w : ℕ} {S : Garden w} (D : ReconstructionData S) (s : ReplacementSlot S) :=
  NativeClockBranch D s → ℝ

noncomputable def replacementTimeIndexEquiv {w : ℕ} {S : Garden w} (D : ReconstructionData S) :
    ReplacementBranchIndex D ≃ Σ s : ReplacementSlot S, NativeClockBranch D s where
  toFun
    | .inl ⟨p,q⟩ => ⟨.inl p,q⟩
    | .inr ⟨b,q⟩ => ⟨.inr b,chainBranchEquiv D b q⟩
  invFun
    | ⟨.inl p,q⟩ => .inl ⟨p,q⟩
    | ⟨.inr b,q⟩ => .inr ⟨b,(chainBranchEquiv D b).symm q⟩
  left_inv := by
    rintro (⟨p,q⟩ | ⟨b,q⟩)
    · rfl
    · exact congrArg (fun q => Sum.inr (Sigma.mk b q)) ((chainBranchEquiv D b).symm_apply_apply q)
  right_inv := by
    rintro ⟨s,q⟩
    cases s with
    | inl p => rfl
    | inr b => exact congrArg (fun q => Sigma.mk (Sum.inr b) q) ((chainBranchEquiv D b).apply_symm_apply q)

noncomputable def replacementTimeSplit {w : ℕ} {S : Garden w} (D : ReconstructionData S) :
    (ReplacementBranchIndex D → ℝ) ≃ᵐ ((s : ReplacementSlot S) → NativeTimeBlock D s) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (replacementTimeIndexEquiv D)).trans
    (MeasurableEquiv.piCurry (fun (s : ReplacementSlot S) (_ : NativeClockBranch D s) => ℝ))

theorem measurePreserving_replacementTimeSplit {w : ℕ} {S : Garden w} (D : ReconstructionData S) :
    MeasurePreserving (replacementTimeSplit D) volume volume :=
  (measurePreserving_piCurry_real (NativeClockBranch D)).comp
    (measurePreserving_piCongrLeft
      (fun _ : (Σ s : ReplacementSlot S, NativeClockBranch D s) => (volume : Measure ℝ))
      (replacementTimeIndexEquiv D))

end WaveTurbulence.RegRed
