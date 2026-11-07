/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GlueForest
/-! FLOWER-P7: the disjoint union (glue) of two gardens along `σ : Fin a ⊕ Fin b ≃ Fin w`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {a b w : ℕ}

/-- The glued signature. -/
def gSig (σ : Fin a ⊕ Fin b ≃ Fin w) (sA : Fin a → ℤˣ) (sB : Fin b → ℤˣ) : Fin w → ℤˣ :=
  fun c => Sum.elim sA sB (σ.symm c)

theorem nodeSign_glue_inl (σ : Fin a ⊕ Fin b ≃ Fin w) (sA : Fin a → ℤˣ) (sB : Fin b → ℤˣ) (x : Fin a × Path) :
    nodeSign (gSig σ sA sB) (σ (.inl x.1), x.2) = nodeSign sA x := by
  simp [nodeSign, gSig]

theorem nodeSign_glue_inr (σ : Fin a ⊕ Fin b ≃ Fin w) (sA : Fin a → ℤˣ) (sB : Fin b → ℤˣ) (x : Fin b × Path) :
    nodeSign (gSig σ sA sB) (σ (.inr x.1), x.2) = nodeSign sB x := by
  simp [nodeSign, gSig]

/-- The glued garden. -/
@[reducible] noncomputable def glueGarden (σ : Fin a ⊕ Fin b ≃ Fin w) (GA : Garden a) (GB : Garden b) : Garden w where
  sig := gSig σ GA.sig GB.sig
  tree := gT σ GA.tree GB.tree
  pair := fun ℓ => glueLeaf σ GA.tree GB.tree
    (Sum.map GA.pair GB.pair ((glueLeaf σ GA.tree GB.tree).symm ℓ))
  mark := fun ℓ => Sum.elim GA.mark GB.mark ((glueLeaf σ GA.tree GB.tree).symm ℓ)
  pair_pair := fun ℓ => by
    have hmm : ∀ y : GLeaf GA.tree ⊕ GLeaf GB.tree,
        Sum.map GA.pair GB.pair (Sum.map GA.pair GB.pair y) = y := by
      rintro (y | y) <;> simp [GA.pair_pair, GB.pair_pair]
    simp only [Equiv.symm_apply_apply, hmm, Equiv.apply_symm_apply]
  pair_eq_iff := fun ℓ => by
    rcases h : (glueLeaf σ GA.tree GB.tree).symm ℓ with x | x
    · have hl : ℓ = glueLeaf σ GA.tree GB.tree (.inl x) := by rw [← h]; simp
      subst hl
      simp only [Equiv.symm_apply_apply, Sum.map_inl, Sum.elim_inl, EmbeddingLike.apply_eq_iff_eq,
        Sum.inl.injEq]
      exact GA.pair_eq_iff x
    · have hl : ℓ = glueLeaf σ GA.tree GB.tree (.inr x) := by rw [← h]; simp
      subst hl
      simp only [Equiv.symm_apply_apply, Sum.map_inr, Sum.elim_inr, EmbeddingLike.apply_eq_iff_eq,
        Sum.inr.injEq]
      exact GB.pair_eq_iff x
  pair_sign := fun ℓ hℓ => by
    rcases h : (glueLeaf σ GA.tree GB.tree).symm ℓ with x | x
    · have hl : ℓ = glueLeaf σ GA.tree GB.tree (.inl x) := by rw [← h]; simp
      subst hl
      simp only [Equiv.symm_apply_apply, Sum.map_inl, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq] at hℓ ⊢
      have h1 := GA.pair_sign x (fun e => hℓ (congrArg _ (congrArg Sum.inl e)))
      change nodeSign (gSig σ GA.sig GB.sig) (σ (.inl (GA.pair x).1.1), (GA.pair x).1.2) =
        -nodeSign (gSig σ GA.sig GB.sig) (σ (.inl x.1.1), x.1.2)
      rw [nodeSign_glue_inl, nodeSign_glue_inl]
      exact h1
    · have hl : ℓ = glueLeaf σ GA.tree GB.tree (.inr x) := by rw [← h]; simp
      subst hl
      simp only [Equiv.symm_apply_apply, Sum.map_inr, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq] at hℓ ⊢
      have h1 := GB.pair_sign x (fun e => hℓ (congrArg _ (congrArg Sum.inr e)))
      change nodeSign (gSig σ GA.sig GB.sig) (σ (.inr (GB.pair x).1.1), (GB.pair x).1.2) =
        -nodeSign (gSig σ GA.sig GB.sig) (σ (.inr x.1.1), x.1.2)
      rw [nodeSign_glue_inr, nodeSign_glue_inr]
      exact h1

end WaveTurbulence.FlowerP7
