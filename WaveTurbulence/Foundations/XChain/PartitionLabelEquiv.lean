/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.IndependentDecorationSums
public import WaveTurbulence.Foundations.Cumulant.Basic
/-! Independent labels on partition blocks are exactly labels on the original root set. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def partitionLabelEquiv {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (P : Finpartition s) (α : ι → Type*) :
    ((i : ↥s) → α i.1) ≃ ((B : P.parts) → (i : ↥B.1) → α i.1) :=
  (Equiv.piCongrLeft (fun i : ↥s => α i.1) P.equivSigmaParts.symm).symm.trans
    (Equiv.piCurry (fun (B : P.parts) (i : ↥B.1) => α i.1))

theorem partitionLabelEquiv_apply {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (P : Finpartition s) (α : ι → Type*) (a : (i : ↥s) → α i.1)
    (B : P.parts) (i : ↥B.1) : partitionLabelEquiv P α a B i = a ⟨i.1, P.le B.2 i.2⟩ := rfl

theorem tsum_partition_labels {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (P : Finpartition s) (α : ι → Type*) [∀ i, Countable (α i)]
    (f : (B : P.parts) → ((i : ↥B.1) → α i.1) → ℂ) :
    (∑' a : (i : ↥s) → α i.1, ∏ B, f B (fun i => a ⟨i.1, P.le B.2 i.2⟩)) =
      ∏ B, ∑' a, f B a := by
  have he := (partitionLabelEquiv P α).tsum_eq (fun b => ∏ B, f B (b B))
  exact he.trans (tsum_independent_prod f)

end WaveTurbulence.Induct
