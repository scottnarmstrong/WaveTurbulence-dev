/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeCoupleBranches
public import WaveTurbulence.Foundations.Molecule.RegRedDraft.NativeChainBranches

/-! # The actual native replacement branches together with the retained source core -/

@[expose] public section
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

def NativeBranch {w : ℕ} {S : Garden w} (D : ReconstructionData S) : ReplacementSlot S → Type
  | .inl p => GBranch (decodedCouple (D.couple p)).tree
  | .inr b => Option (ChainBranchPath D b)

noncomputable instance {w : ℕ} {S : Garden w} (D : ReconstructionData S) (slot : ReplacementSlot S) :
    Fintype (NativeBranch D slot) := by
  cases slot <;> dsimp only [NativeBranch] <;> infer_instance

noncomputable def nativeBranchAt {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) :
    (slot : ReplacementSlot S) → NativeBranch D slot → GBranch (D.forest hS)
  | .inl p,b => coupleContextBranch D hS p b
  | .inr b,none => D.coreBranch hS b
  | .inr b,some q => chainContextBranch D hS b q

theorem nativeBranchAt_mem_block {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (slot : ReplacementSlot S) (x : NativeBranch D slot) :
    (nativeBranchAt D hS slot x).1 ∈ D.nodeBlock hS slot := by
  cases slot with
  | inl p => exact coupleContextBranch_mem_block D hS p x
  | inr b =>
    cases x with
    | none => exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    | some q => exact chainContextBranch_mem_block D hS b q

theorem nativeBranchAt_injective {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (slot : ReplacementSlot S) : Function.Injective (nativeBranchAt D hS slot) := by
  cases slot with
  | inl p => exact (coupleContextBranch D hS p).injective
  | inr b =>
    intro x y he
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some q => exact (chainContextBranch_ne_core D hS b q he.symm).elim
    | some q =>
      cases y with
      | none => exact (chainContextBranch_ne_core D hS b q he).elim
      | some r => exact congrArg some (chainContextBranch_injective D hS b he)

noncomputable def nativeBranchMap {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) :
    (Σ slot : ReplacementSlot S, NativeBranch D slot) → GBranch (D.forest hS) :=
  fun p => nativeBranchAt D hS p.1 p.2

theorem nativeBranchMap_injective {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : Function.Injective (nativeBranchMap D hS) := by
  let f : (Σ slot : ReplacementSlot S, NativeBranch D slot) → ReplacementBranchOccurrence D hS :=
    fun p => ⟨p.1,⟨nativeBranchAt D hS p.1 p.2,nativeBranchAt_mem_block D hS p.1 p.2⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨i,x⟩ ⟨j,y⟩ he
    have hi := congrArg (fun p : ReplacementBranchOccurrence D hS => p.1) he
    change i = j at hi
    subst j
    have hx := congrArg (fun p : ReplacementBranchOccurrence D hS => p.2.1) he
    exact congrArg (fun z => Sigma.mk i z) (nativeBranchAt_injective D hS i hx)
  exact (replacementBranchProjection_bijective D hS).1.comp hf

end WaveTurbulence.RegRed
