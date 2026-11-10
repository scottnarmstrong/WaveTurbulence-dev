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

/-- B1b-3 (Mk-general form of `spliceKernel_congr`). -/
theorem spliceKernel_congrMk (A : FamilyReconstruction w ι) {σ τ : Prescription A.skeleton}
    (Mk : Set (CLVine A.skeleton)) (h : σ = τ) {G : Garden w} (e : G = (stSt A.skeleton σ Mk).G)
    (e' : G = (stSt A.skeleton τ Mk).G) (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (s : ReplacementSlot G) :
    spliceKernelMk A σ Mk f L γ δ (slotCast e s) = spliceKernelMk A τ Mk f L γ δ (slotCast e' s) := by
  subst τ
  rfl

/-- B1b-3 (Mk-general form of `batch_spliceKernel`): R-SLOT along a batch carrying the marking. -/
theorem batch_spliceKernelMk {A B : FamilyReconstruction w ι} {xs : List ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : BatchIso p kind xs A B F)
    (σ : Prescription A.skeleton) {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (s : ReplacementSlot (stSt A.skeleton σ Mk).G) :
    spliceKernelMk B (transportPrescription F σ) Mk' f L γ δ (slotCast (h.splice_garden_eqMk σ hT hA).symm s) =
      spliceKernelMk A σ Mk f L γ δ s := by
  induction h with
  | nil A =>
    obtain rfl := Stage1Mk.markTransported_refl_eq hT
    exact spliceKernel_congrMk A Mk (transportPrescription_refl σ) _ rfl f L γ δ s
  | skip _ _ ih => exact ih σ hT hA s
  | @apply xs A B i op F h ih =>
    obtain ⟨h1, h2⟩ := Stage1Mk.markTransported_split (operationMolIso op) F hT
    let τ := transportPrescription (operationMolIso op) σ
    let hB := isV0Fam_operationMk hA op h1
    let e0 := (operation_splice_garden_eqMk hA op h1).symm
    let e1 := (h.splice_garden_eqMk τ h2 hB).symm
    calc
      _ = spliceKernelMk B (transportPrescription F τ) Mk' f L γ δ (slotCast (e0.trans e1) s) :=
        spliceKernel_congrMk B Mk' (transportPrescription_trans _ _ σ).symm _ _ f L γ δ s
      _ = spliceKernelMk B (transportPrescription F τ) Mk' f L γ δ (slotCast e1 (slotCast e0 s)) :=
        congrArg _ (slotCast_trans e0 e1 s).symm
      _ = spliceKernelMk op.output τ _ f L γ δ (slotCast e0 s) := ih τ h2 hB (slotCast e0 s)
      _ = _ := operation_spliceKernelMk hA op h1 f L γ δ s

end WaveTurbulence.VineAlign
