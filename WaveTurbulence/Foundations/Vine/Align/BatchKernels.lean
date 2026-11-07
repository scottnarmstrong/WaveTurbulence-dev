/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.OperationKernels
/-! Native outer-kernel invariance along an actual selected LF batch. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS4 VineA VineB RedSplice Stage1 Twist RegRed Represents LFTwist Reg.Skeleton
variable {w p d : ℕ} {kind : Bool} {ι : Type*}

theorem slotCast_trans {G H K : Garden w} (e : G = H) (f : H = K) (s : ReplacementSlot G) :
    slotCast f (slotCast e s) = slotCast (e.trans f) s := by subst H; subst K; rfl

theorem spliceKernel_congr (A : FamilyReconstruction w ι) {σ τ : Prescription A.skeleton}
    (h : σ = τ) {G : Garden w} (e : G = (stSt A.skeleton σ).G) (e' : G = (stSt A.skeleton τ).G)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (s : ReplacementSlot G) :
    spliceKernel A σ f L γ δ (slotCast e s) = spliceKernel A τ f L γ δ (slotCast e' s) := by
  subst τ
  rfl

/-- R-SLOT for an arbitrary actual selected-operation trace, at all times and momenta. -/
theorem batch_spliceKernel {A B : FamilyReconstruction w ι} {xs : List ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : BatchIso p kind xs A B F)
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (s : ReplacementSlot (stSt A.skeleton σ).G) :
    spliceKernel B (transportPrescription F σ) f L γ δ (slotCast (h.splice_garden_eq σ hA).symm s) =
      spliceKernel A σ f L γ δ s := by
  induction h with
  | nil A =>
    exact spliceKernel_congr A (transportPrescription_refl σ) _ rfl f L γ δ s
  | skip _ _ ih => exact ih σ hA s
  | @apply xs A B i op F h ih =>
    let τ := transportPrescription (operationMolIso op) σ
    let hB := isV0Fam_operation hA op
    let e0 := (operation_splice_garden_eq hA op).symm
    let e1 := (h.splice_garden_eq τ hB).symm
    calc
      _ = spliceKernel B (transportPrescription F τ) f L γ δ (slotCast (e0.trans e1) s) :=
        spliceKernel_congr B (transportPrescription_trans _ _ σ).symm _ _ f L γ δ s
      _ = spliceKernel B (transportPrescription F τ) f L γ δ (slotCast e1 (slotCast e0 s)) :=
        congrArg _ (slotCast_trans e0 e1 s).symm
      _ = spliceKernel op.output τ f L γ δ (slotCast e0 s) := ih τ hB (slotCast e0 s)
      _ = _ := operation_spliceKernel hA op f L γ δ s

end WaveTurbulence.VineAlign
