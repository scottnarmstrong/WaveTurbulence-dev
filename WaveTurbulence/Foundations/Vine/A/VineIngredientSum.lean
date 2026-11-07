/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineBatchIngredients
/-! Actual chosen vine incoherency sums transport along selected LF batches. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.LFTwist
variable {w : ℕ} {G H : Garden w}

/-- Transport the finite sum of actual vine indices using actual unit-list transport. -/
theorem vineIndexSum_transport (F : MolIso G.molecule H.molecule)
    (σ : Prescription G) (τ : Prescription H)
    (hp : ((unitBlocks G σ).map (fun u => F.img u.atoms)).Perm ((unitBlocks H τ).map CLBlock.atoms))
    (layer : GBranch H.tree → ℕ) :
    (∑ S ∈ (Set.toFinite (unitIngredients G σ)).toFinset, vineIncoh G (layer ∘ F.e) S) =
    ∑ T ∈ (Set.toFinite (unitIngredients H τ)).toFinset, vineIncoh H layer T := by
  classical
  apply Finset.sum_bij (fun S _ => F.img S)
  · intro S hS
    exact (Set.toFinite (unitIngredients H τ)).mem_toFinset.mpr
      ((unitIngredients_image_iff_of_units F σ τ hp S).mpr
        ((Set.toFinite (unitIngredients G σ)).mem_toFinset.mp hS))
  · intro S _ T _ he
    exact F.img_injective he
  · intro T hT
    refine ⟨F.symm.img T, ?_, F.img_symm_img T⟩
    apply (Set.toFinite (unitIngredients G σ)).mem_toFinset.mpr
    apply (unitIngredients_image_iff_of_units F σ τ hp (F.symm.img T)).mp
    rw [F.img_symm_img]
    exact (Set.toFinite (unitIngredients H τ)).mem_toFinset.mp hT
  · intro S _
    exact (vineIncoh_image F layer S).symm

/-- The actual vine part of gsk is constant along every selected-family batch. -/
theorem BatchIso.vineIndexSum {p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
    {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ) :
    (∑ S ∈ (Set.toFinite (RedSplice.unitIngredients A.skeleton σ)).toFinset,
      vineIncoh A.skeleton (RegRed.coreLayer A.layered A.data A.plain A.decodes) S) =
    ∑ T ∈ (Set.toFinite (RedSplice.unitIngredients B.skeleton (transportPrescription F σ))).toFinset,
      vineIncoh B.skeleton (RegRed.coreLayer B.layered B.data B.plain B.decodes) T := by
  have he : (RegRed.coreLayer B.layered B.data B.plain B.decodes) ∘ F.e =
      RegRed.coreLayer A.layered A.data A.plain A.decodes := funext h.coreLayer
  simpa only [he] using vineIndexSum_transport F σ _ (h.units σ hA)
    (RegRed.coreLayer B.layered B.data B.plain B.decodes)

end WaveTurbulence.VineA
