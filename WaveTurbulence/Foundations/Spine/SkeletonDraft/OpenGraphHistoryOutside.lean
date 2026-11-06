/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.OpenEmbeddingOutside

/-! # Full local contraction histories preserve the ambient matching outside their literal port image -/

public section
namespace WaveTurbulence.Reg.Skeleton.PortMatching.OpenEmbedding

theorem lift_reduces_outside {V W : Type*} [DecidableEq V] [DecidableEq W]
    {M T : PortMatching V} (h : Reduces M T) (N : PortMatching W) (E : OpenEmbedding M N) :
    ∃ U : PortMatching W, ∃ F : OpenEmbedding T U,
      Reduces N U ∧ F.port = E.port ∧ ∀ x, x ∉ Set.range E.port → U.mate x = N.mate x := by
  induction h generalizing N with
  | refl => exact ⟨N,E,Relation.ReflTransGen.refl,rfl,fun _ _ => rfl⟩
  | @tail T U hr hs ih =>
    obtain ⟨N₁,E₁,hN₁,hport,houtside⟩ := ih N E
    obtain ⟨D,hD⟩ := hs
    let T₂ : PortMatching V := ⟨D.contract,D.contract_involutive T.involutive⟩
    have hu : U = T₂ := PortMatching.ext hD
    subst U
    let ED := E₁.liftDipole D
    let N₂ : PortMatching W := ⟨ED.contract,ED.contract_involutive N₁.involutive⟩
    refine ⟨N₂,E₁.residual D,hN₁.tail ⟨ED,rfl⟩,hport,?_⟩
    intro x hx
    have hx₁ : x ∉ Set.range E₁.port := by rw [hport]; exact hx
    exact (E₁.contract_outside_range D x hx₁).trans (houtside x hx)

end WaveTurbulence.Reg.Skeleton.PortMatching.OpenEmbedding
