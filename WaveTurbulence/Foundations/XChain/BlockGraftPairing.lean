/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.BlockGraftLeaves
/-! A literal garden obtained by grafting a family of plain lower gardens onto partition blocks. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

def blockPair {β : Type*} {w : β → ℕ} (low : (B : β) → Garden (w B)) :
    (Σ B : β, GLeaf (low B).tree) → (Σ B : β, GLeaf (low B).tree) :=
  fun x => ⟨x.1, (low x.1).pair x.2⟩

theorem blockPair_involutive {β : Type*} {w : β → ℕ} (low : (B : β) → Garden (w B)) :
    Function.Involutive (blockPair low) := by
  rintro ⟨B, ℓ⟩
  change (⟨B, (low B).pair ((low B).pair ℓ)⟩ : Σ B : β, GLeaf (low B).tree) = ⟨B, ℓ⟩
  rw [(low B).pair_pair]

theorem blockPair_ne_self {β : Type*} {w : β → ℕ} (low : (B : β) → Garden (w B))
    (hplain : ∀ B, (low B).IsPlain) (x : Σ B : β, GLeaf (low B).tree) : blockPair low x ≠ x := by
  rcases x with ⟨B, ℓ⟩
  intro h
  have he : (low B).pair ℓ = ℓ := eq_of_heq (Sigma.mk.inj h).2
  exact ((low B).pair_eq_iff ℓ).mp he (hplain B ℓ)

theorem blockPair_sign {β : Type*} {w : β → ℕ} (low : (B : β) → Garden (w B))
    (hplain : ∀ B, (low B).IsPlain) (x : Σ B : β, GLeaf (low B).tree) :
    nodeSign (low (blockPair low x).1).sig (blockPair low x).2.1 =
      -nodeSign (low x.1).sig x.2.1 := by
  rcases x with ⟨B, ℓ⟩
  exact (low B).pair_sign ℓ (fun h => ((low B).pair_eq_iff ℓ).mp h (hplain B ℓ))

noncomputable def blockGraftPair {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card) :
    AttachedLeaf top (blockGraftTrees top P low) → AttachedLeaf top (blockGraftTrees top P low) :=
  fun x => (blockLeafEquiv top P low).symm (blockPair low (blockLeafEquiv top P low x))

theorem blockGraftPair_involutive {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card) :
    Function.Involutive (blockGraftPair top P low) := by
  intro x
  unfold blockGraftPair
  rw [Equiv.apply_symm_apply, blockPair_involutive low _, Equiv.symm_apply_apply]

theorem blockGraftPair_ne_self {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hplain : ∀ B, (low B).IsPlain) (x : AttachedLeaf top (blockGraftTrees top P low)) :
    blockGraftPair top P low x ≠ x := by
  intro h
  have he := congrArg (blockLeafEquiv top P low) h
  simp only [blockGraftPair, Equiv.apply_symm_apply] at he
  exact blockPair_ne_self low hplain _ he

theorem blockGraftPair_sign {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hplain : ∀ B, (low B).IsPlain)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (x : AttachedLeaf top (blockGraftTrees top P low)) :
    attachedSign sig (blockGraftPair top P low x) = -attachedSign sig x := by
  calc
    _ = nodeSign (low (blockLeafEquiv top P low (blockGraftPair top P low x)).1).sig
        (blockLeafEquiv top P low (blockGraftPair top P low x)).2.1 :=
      (blockLeafEquiv_sign sig top P low hsig _).symm
    _ = nodeSign (low (blockPair low (blockLeafEquiv top P low x)).1).sig
        (blockPair low (blockLeafEquiv top P low x)).2.1 := by
      exact congrArg (fun z : Σ B : P.parts, GLeaf (low B).tree => nodeSign (low z.1).sig z.2.1)
        ((blockLeafEquiv top P low).apply_symm_apply (blockPair low (blockLeafEquiv top P low x)))
    _ = -nodeSign (low (blockLeafEquiv top P low x).1).sig
        (blockLeafEquiv top P low x).2.1 := blockPair_sign low hplain _
    _ = _ := congrArg Neg.neg (blockLeafEquiv_sign sig top P low hsig x)

/-- The concrete grafted garden for the canonical reindexing; all pairing proof fields are proved. -/
noncomputable def gardenGraft {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hplain : ∀ B, (low B).IsPlain)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) : Garden w :=
  plainGraftedGarden sig top (blockGraftTrees top P low) (blockGraftPair top P low)
    (blockGraftPair_involutive top P low) (blockGraftPair_ne_self top P low hplain)
    (blockGraftPair_sign sig top P low hplain hsig)

end WaveTurbulence.Induct
