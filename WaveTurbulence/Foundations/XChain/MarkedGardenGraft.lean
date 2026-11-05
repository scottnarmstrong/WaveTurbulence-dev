/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftAddresses
/-! Grafting arbitrary marked lower gardens, including untouched flower and lone leaves. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

theorem gardenLeafEquiv_sign {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (ℓ : GLeaf (graftForest top (blockGraftTrees top P low))) :
    nodeSign (low (gardenLeafEquiv top P low ℓ).1).sig (gardenLeafEquiv top P low ℓ).2.1 =
      nodeSign sig ℓ.1 := by
  have hb := blockLeafEquiv_sign sig top P low hsig
    ((graftForestLeafEquiv top (blockGraftTrees top P low)).symm ℓ)
  have hf := nodeSign_graftForestLeafEquiv top (blockGraftTrees top P low) sig
    ((graftForestLeafEquiv top (blockGraftTrees top P low)).symm ℓ)
  rw [Equiv.apply_symm_apply] at hf
  exact hb.trans hf.symm

/-- Pairings and marks are transported together. A singleton marked leaf is therefore allowed
as a lower component, and is retained without introducing a fictitious pair. -/
noncomputable def markedGardenGraft {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) : Garden w where
  sig := sig
  tree := graftForest top (blockGraftTrees top P low)
  pair := fun ℓ => (gardenLeafEquiv top P low).symm (blockPair low (gardenLeafEquiv top P low ℓ))
  mark := fun ℓ => (low (gardenLeafEquiv top P low ℓ).1).mark (gardenLeafEquiv top P low ℓ).2
  pair_pair ℓ := by
    simp only [Equiv.apply_symm_apply]
    exact (congrArg (gardenLeafEquiv top P low).symm (blockPair_involutive low _)).trans
      ((gardenLeafEquiv top P low).symm_apply_apply ℓ)
  pair_eq_iff ℓ := by
    constructor
    · intro he
      have he' := congrArg (gardenLeafEquiv top P low) he
      simp only [Equiv.apply_symm_apply] at he'
      have hp := eq_of_heq (Sigma.mk.inj he').2
      exact ((low (gardenLeafEquiv top P low ℓ).1).pair_eq_iff _).mp hp
    · intro hm
      have hp := ((low (gardenLeafEquiv top P low ℓ).1).pair_eq_iff _).mpr hm
      have he : blockPair low (gardenLeafEquiv top P low ℓ) = gardenLeafEquiv top P low ℓ :=
        congrArg (Sigma.mk (gardenLeafEquiv top P low ℓ).1) hp
      exact (congrArg (gardenLeafEquiv top P low).symm he).trans
        ((gardenLeafEquiv top P low).symm_apply_apply ℓ)
  pair_sign ℓ hne := by
    have hp : (low (gardenLeafEquiv top P low ℓ).1).pair (gardenLeafEquiv top P low ℓ).2 ≠
        (gardenLeafEquiv top P low ℓ).2 := by
      intro he
      apply hne
      have he' : blockPair low (gardenLeafEquiv top P low ℓ) = gardenLeafEquiv top P low ℓ :=
        congrArg (Sigma.mk (gardenLeafEquiv top P low ℓ).1) he
      exact (congrArg (gardenLeafEquiv top P low).symm he').trans
        ((gardenLeafEquiv top P low).symm_apply_apply ℓ)
    have hs := (low (gardenLeafEquiv top P low ℓ).1).pair_sign _ hp
    have hleft := gardenLeafEquiv_sign sig top P low hsig
      ((gardenLeafEquiv top P low).symm (blockPair low (gardenLeafEquiv top P low ℓ)))
    have he := congrArg (fun z : Σ B : P.parts, GLeaf (low B).tree =>
      nodeSign (low z.1).sig z.2.1)
      ((gardenLeafEquiv top P low).apply_symm_apply (blockPair low (gardenLeafEquiv top P low ℓ)))
    exact hleft.symm.trans (he.trans
      (hs.trans (congrArg Neg.neg (gardenLeafEquiv_sign sig top P low hsig ℓ))))

end WaveTurbulence.Induct
