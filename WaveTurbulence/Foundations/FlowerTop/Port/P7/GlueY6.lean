/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueAttach
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapCond
/-! FLOWER-P7: the decapitated-carrier condition `Y6Cond` of a glued garden is the conjunction of the
component conditions, the order relation and the condition on the vector of top orders. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

/-- The component conditions: plain, canonical, attached orders `≤ N_p`. -/
def CompCond (P : WTParams) (p : ℕ) {w : ℕ} (L : LayeredGarden w) : Prop :=
  L.garden.IsPlain ∧ L.CanonCriterion p ∧ ∀ u ∈ L.attachNodes p, L.attachedOrder p u ≤ P.N p

/-- The top-order vector of a glued garden. -/
def glueVec {a b w : ℕ} (σ : Fin a ⊕ Fin b ≃ Fin w) (vA : Fin a → ℕ) (vB : Fin b → ℕ) : Fin w → ℕ :=
  fun c => Sum.elim vA vB (σ.symm c)

theorem glue_topVec {a b w : ℕ} (σ : Fin a ⊕ Fin b ≃ Fin w) (LA : LayeredGarden a) (LB : LayeredGarden b)
    (p : ℕ) :
    (fun c => (glueLayered σ LA LB).topOrder p c) = glueVec σ (fun i => LA.topOrder p i) (fun i => LB.topOrder p i) := by
  funext c
  obtain ⟨s, rfl⟩ := σ.surjective c
  rcases s with i | i
  · simp [glueVec, glue_topOrder_inl]
  · simp [glueVec, glue_topOrder_inr]

theorem glue_Y6Cond_iff {a b : ℕ} (P : WTParams) (p N : ℕ) (kind : TreeKind) (σ : Fin a ⊕ Fin b ≃ Fin (2 * 3))
    (LA : LayeredGarden a) (LB : LayeredGarden b) :
    Y6Cond P p N kind (glueLayered σ LA LB) ↔
      CompCond P p LA ∧ CompCond P p LB ∧ LA.garden.order + LB.garden.order + 2 = N ∧
        VecKindOK (P.N (p + 1)) kind (glueVec σ (fun i => LA.topOrder p i) (fun i => LB.topOrder p i)) := by
  unfold Y6Cond CompCond
  rw [glue_isPlain_iff, glue_canonCriterion_iff, glue_attach_cond, glue_topVec]
  have : (glueLayered σ LA LB).garden.order = LA.garden.order + LB.garden.order := glue_order σ LA.garden LB.garden
  rw [this]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, h7, h8⟩
    exact ⟨⟨h1, h3, h5⟩, ⟨h2, h4, h6⟩, h7, h8⟩
  · rintro ⟨⟨h1, h3, h5⟩, ⟨h2, h4, h6⟩, h7, h8⟩
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, h7, h8⟩

end WaveTurbulence.FlowerP7
