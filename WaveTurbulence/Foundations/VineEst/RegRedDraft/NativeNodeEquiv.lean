/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeNodeMap

/-! # The native replacement nodes exhaust the actual reconstructed forest -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem card_nativeNode {w : ℕ} {S : Garden w} (D : ReconstructionData S) (s : ReplacementSlot S) :
    Fintype.card (NativeNode D s) = replacementNodeBudget D s := by
  cases s with
  | inl p =>
    change Fintype.card (GNode (decodedCouple (D.couple p)).tree) = 3 * (D.couple p).size + 2
    rw [Comb.card_gnode]
    have he := decodedCouple_order (D.couple p)
    exact congrArg (fun n => 3*n+2) he
  | inr b =>
    change Fintype.card (GNode (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree) =
      3 * (D.tree b).size + 1
    rw [Comb.card_gnode]
    have he := decodedTree_order (D.tree b) (nodeSign S.sig b.1)
    exact congrArg (fun n => 3*n+1) he

theorem nativeNodeMap_bijective {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : Function.Bijective (nativeNodeMap D hS) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨nativeNodeMap_injective D hS,?_⟩
  rw [Fintype.card_sigma,Comb.card_gnode]
  simp only [card_nativeNode]
  exact (sum_replacementNodeBudget D hS).trans
    (congrArg (fun n => 3*n+w) (D.forest_order hS).symm)

/-- A literal bijection, including the replacement roots and distinguished
paired-tree lone nodes; it supplies node-label gluing without an overlap premise. -/
noncomputable def nativeNodeEquiv {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : (Σ s : ReplacementSlot S, NativeNode D s) ≃ GNode (D.forest hS) :=
  Equiv.ofBijective (nativeNodeMap D hS) (nativeNodeMap_bijective D hS)

noncomputable def glueNativeLabels {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) {V : Type*} (η : (s : ReplacementSlot S) → NativeNode D s → V) :
    GNode (D.forest hS) → V := fun a =>
  let p := (nativeNodeEquiv D hS).symm a
  η p.1 p.2

theorem glueNativeLabels_at {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) {V : Type*} (η : (s : ReplacementSlot S) → NativeNode D s → V)
    (s : ReplacementSlot S) (a : NativeNode D s) :
    glueNativeLabels D hS η (nativeNodeAt D hS s a) = η s a := by
  change (fun p : (Σ s : ReplacementSlot S, NativeNode D s) => η p.1 p.2)
    ((nativeNodeEquiv D hS).symm ((nativeNodeEquiv D hS) ⟨s,a⟩)) = _
  rw [Equiv.symm_apply_apply]

end WaveTurbulence.RegRed
