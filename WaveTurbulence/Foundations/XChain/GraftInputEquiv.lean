/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftLeafProducts
/-! The precise input-leaf bijection for kernel product factorization. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def graftInputLeavesEquiv {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) :
    ↥(inputLeaves (markedGardenGraft sig top P low hsig)) ≃
      Σ B : P.parts, ↥(inputLeaves (low B)) :=
  ((gardenLeafEquiv top P low).subtypeEquiv
    (q := fun z : Σ B : P.parts, GLeaf (low B).tree => z.2 ∈ inputLeaves (low z.1)) (fun ℓ => by
    have hi := markedGardenGraft_inputLeaf_iff sig top P low hsig
      (gardenLeafEquiv top P low ℓ).1 (gardenLeafEquiv top P low ℓ).2
    have he := congrArg (fun l => l ∈ inputLeaves (markedGardenGraft sig top P low hsig))
      ((gardenLeafEquiv top P low).symm_apply_apply ℓ)
    exact he.to_iff.symm.trans hi)).trans
    { toFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem graftInputLeavesEquiv_symm_val {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (B : P.parts) (ℓ : ↥(inputLeaves (low B))) :
    ((graftInputLeavesEquiv sig top P low hsig).symm ⟨B, ℓ⟩).1 =
      lowerLeafEmbedding top P low B ℓ.1 := rfl

theorem prod_graft_inputLeaves {M : Type*} [CommMonoid M] {w : ℕ}
    (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (f : GLeaf (graftForest top (blockGraftTrees top P low)) → M) :
    (∏ ℓ ∈ inputLeaves (markedGardenGraft sig top P low hsig), f ℓ) =
      ∏ B : P.parts, ∏ ℓ ∈ inputLeaves (low B), f (lowerLeafEmbedding top P low B ℓ) := by
  have he := Fintype.prod_equiv (graftInputLeavesEquiv sig top P low hsig).symm
    (fun z => f ((graftInputLeavesEquiv sig top P low hsig).symm z).1)
    (fun ℓ => f ℓ.1) (fun _ => rfl)
  have he' := he.symm
  simp only [Fintype.prod_sigma, graftInputLeavesEquiv_symm_val] at he'
  have hb := Finset.prod_coe_sort (inputLeaves (markedGardenGraft sig top P low hsig)) f
  have hl := Finset.prod_congr (s₁ := (univ : Finset P.parts)) rfl (fun B _ =>
    Finset.prod_coe_sort (inputLeaves (low B)) (fun ℓ => f (lowerLeafEmbedding top P low B ℓ)))
  exact hb.symm.trans (he'.trans hl)

end WaveTurbulence.Induct
