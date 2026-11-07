/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.OperationSlots
public import WaveTurbulence.Foundations.Vine.Align.NativeKernels
/-! Actual native outer kernels commute with one selected LF operation. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS4 VineA VineB RedSplice Stage1 Twist RegRed Represents LFTwist Reg.Skeleton LGSpine
variable {w p d : ℕ} {kind : Bool} {ι : Type*}

noncomputable def stateSlotFn (A : FamilyReconstruction w ι)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) :=
  slotFn A.data A.plain L γ δ (typeProfiles A.layered f) (stateLayer A) (stateLayer_isLayering A)

/-- Equality of the complete native kernel functions at an ordinary slot. -/
theorem operation_kernel {A : FamilyReconstruction w ι} {i : ι}
    (op : FamilyOperation (p := p) (kind := kind) A i)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (s : ReplacementSlot A.skeleton)
    (hs : match s with
      | .inl q => q ≠ pairOfLeaf A.skeleton A.plain (A.family.placement i).retained
      | .inr b => b ≠ (A.family.placement i).lower) :
    stateSlotFn op.output f L γ δ (operationSlotMap op s) = stateSlotFn A f L γ δ s := by
  cases op with
  | mk hc he ht hq ε C =>
    let B := (⟨hc, he, ht, hq, ε, C⟩ : FamilyOperation (p := p) (kind := kind) A i).output
    funext ts k
    cases s with
    | inl q =>
      exact ordinary_couple_kernel C (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer B) (stateLayer_isLayering B) (stateLayer_spec B) f L γ δ q hs ts k
    | inr b =>
      exact ordinary_tree_kernel C (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer B) (stateLayer_isLayering B) (stateLayer_spec B) f L γ δ b hs ts k

/-- The actual kernel of a slot of the simultaneously spliced garden. -/
noncomputable def spliceKernel (A : FamilyReconstruction w ι) (σ : Prescription A.skeleton)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ)
    (s : ReplacementSlot (stSt A.skeleton σ).G) : (Fin 2 → ℝ) → Mom d → ℂ :=
  stateSlotFn A f L γ δ ((stShape (Mole.garden_isMolecule A.skeleton) σ).iota
    A.plain ((stSt _ _).plain A.plain) s)

/-- Every outer slot is ordinary: the exceptional pair and lower joint have been removed. -/
theorem operation_spliceKernel {A : FamilyReconstruction w ι} {i : ι} {σ : Prescription A.skeleton}
    (hA : IsV0Fam A.family σ) (op : FamilyOperation (p := p) (kind := kind) A i)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (s : ReplacementSlot (stSt A.skeleton σ).G) :
    spliceKernel op.output (transportPrescription (operationMolIso op) σ) f L γ δ
      (slotCast (operation_splice_garden_eq hA op).symm s) = spliceKernel A σ f L γ δ s := by
  unfold spliceKernel
  rw [operation_iota hA op]
  apply operation_kernel
  cases s with
  | inl q =>
    exact surviving_pair_ne (selectedMemberSite hA i) σ
      ⟨familyVine A.family i, hA.1 i, rfl⟩ A.plain (q.firstLeaf ((stSt _ _).plain A.plain))
  | inr b =>
    exact fun he => active_lower_not_surviving (selectedMemberSite hA i) σ
      ⟨familyVine A.family i, hA.1 i, rfl⟩ ⟨b, he⟩

end WaveTurbulence.VineAlign
