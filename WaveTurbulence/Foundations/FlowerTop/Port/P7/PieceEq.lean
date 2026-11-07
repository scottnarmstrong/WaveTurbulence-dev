/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueClosed
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueSurj
/-! FLOWER-P7: the pieces of a carrier according to the minimal closed block of a chosen tree are glue images
of product sets (generic in the splitting `σ` and in the transferable condition `Q`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {a b w : ℕ}

theorem piece_eq_image (σ : Fin a ⊕ Fin b ≃ Fin w) (i0 : Fin a) (ζ : Fin w → ℤˣ)
    (Q : LayeredGarden w → Prop) (QA : LayeredGarden a → Prop) (QB : LayeredGarden b → Prop)
    (J : LayeredGarden a → LayeredGarden b → Prop)
    (hQ : ∀ LA LB, Q (glueLayered σ LA LB) ↔ QA LA ∧ QB LB ∧ J LA LB)
    (hplainQ : ∀ y, Q y → y.garden.IsPlain) (hplainA : ∀ LA, QA LA → LA.garden.IsPlain) :
    {y : LayeredGarden w | y.garden.sig = ζ ∧ Q y ∧
        MinimalAt y.garden (σ (.inl i0)) (Finset.univ.image fun i => σ (.inl i))} =
      (fun x : LayeredGarden a × LayeredGarden b => glueLayered σ x.1 x.2) ''
        {x | x.1.garden.sig = (fun i => ζ (σ (.inl i))) ∧ x.2.garden.sig = (fun i => ζ (σ (.inr i))) ∧
          QA x.1 ∧ IrrAt x.1.garden i0 ∧ QB x.2 ∧ J x.1 x.2} := by
  classical
  ext y
  constructor
  · rintro ⟨hsig, hQy, hmin⟩
    have hplain := hplainQ y hQy
    have hcl : ∀ ℓ : GLeaf y.garden.tree, (∃ i, ℓ.1.1 = σ (.inl i)) → ∃ i, (y.garden.pair ℓ).1.1 = σ (.inl i) := by
      intro ℓ ⟨i, hi⟩
      have := (closedTrees_iff y.garden hplain _).1 hmin.2.1 ℓ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi.symm⟩)
      obtain ⟨j, -, hj⟩ := Finset.mem_image.1 this
      exact ⟨j, hj.symm⟩
    obtain ⟨LA, LB, hg⟩ := exists_glue_layered σ y hcl
    subst hg
    rw [hQ] at hQy
    refine ⟨(LA, LB), ⟨?_, ?_, hQy.1, ?_, hQy.2.1, hQy.2.2⟩, rfl⟩
    · funext i
      have := congrFun hsig (σ (.inl i))
      simpa [glueLayered, glueGarden, gSig] using this
    · funext i
      have := congrFun hsig (σ (.inr i))
      simpa [glueLayered, glueGarden, gSig] using this
    · exact (glue_minimalAt_inl_iff σ LA.garden LB.garden (hplainA _ hQy.1) i0).1 hmin
  · rintro ⟨x, ⟨hs1, hs2, hQA, hIrr, hQB, hJ⟩, rfl⟩
    refine ⟨?_, (hQ _ _).2 ⟨hQA, hQB, hJ⟩, (glue_minimalAt_inl_iff σ _ _ (hplainA _ hQA) i0).2 hIrr⟩
    funext c
    obtain ⟨s, rfl⟩ := σ.surjective c
    rcases s with i | i
    · have := congrFun hs1 i
      simpa [glueLayered, glueGarden, gSig] using this
    · have := congrFun hs2 i
      simpa [glueLayered, glueGarden, gSig] using this

end WaveTurbulence.FlowerP7
