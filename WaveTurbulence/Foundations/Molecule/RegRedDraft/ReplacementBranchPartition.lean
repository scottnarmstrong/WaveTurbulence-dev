/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.ReplacementNodeBudget

/-! # The exact branching-coordinate partition of a literal reconstructed forest -/

@[expose] public section
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

abbrev ReplacementBranchOccurrence {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) := Σ slot : ReplacementSlot S,
      {b : GBranch (D.forest hS) // b.1 ∈ D.nodeBlock hS slot}

theorem replacementBranchProjection_bijective {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : Function.Bijective
      (fun p : ReplacementBranchOccurrence D hS => p.2.1) := by
  classical
  obtain ⟨e,he⟩ := exists_replacementNodeEquiv D hS
  constructor
  · intro p q hpq
    let P : (Σ slot : ReplacementSlot S, ↥(D.nodeBlock hS slot)) := ⟨p.1,⟨p.2.1.1,p.2.2⟩⟩
    let Q : (Σ slot : ReplacementSlot S, ↥(D.nodeBlock hS slot)) := ⟨q.1,⟨q.2.1.1,q.2.2⟩⟩
    have haddr : P.2.1 = Q.2.1 := congrArg Subtype.val hpq
    have heq : P = Q := e.injective (Subtype.ext ((he P).trans (haddr.trans (he Q).symm)))
    have hslot := congrArg (fun z : (Σ slot : ReplacementSlot S, ↥(D.nodeBlock hS slot)) => z.1) heq
    change p.1 = q.1 at hslot
    cases p with
    | mk i p =>
      cases q with
      | mk j q =>
        change i = j at hslot
        subst j
        exact congrArg (fun z => Sigma.mk i z) (Subtype.ext hpq)
  · intro b
    obtain ⟨slot,hslot⟩ := D.node_covered hS b.toNode
    exact ⟨⟨slot,⟨b,hslot⟩⟩,rfl⟩

/-- No new or missing clock coordinates: every actual branch is represented once. -/
noncomputable def replacementBranchEquiv {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : ReplacementBranchOccurrence D hS ≃ GBranch (D.forest hS) :=
  Equiv.ofBijective (fun p => p.2.1) (replacementBranchProjection_bijective D hS)

theorem replacementBranchEquiv_apply {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (p : ReplacementBranchOccurrence D hS) : replacementBranchEquiv D hS p = p.2.1 := rfl

end WaveTurbulence.RegRed
