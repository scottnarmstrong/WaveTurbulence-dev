/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.OpenGraphEmbedding

/-! # Open graph embeddings lift complete contraction histories with unchanged port identities -/

public section
namespace WaveTurbulence.Reg.Skeleton.PortMatching
namespace OpenEmbedding

theorem lift_reduces {V W : Type*} [DecidableEq V] [DecidableEq W]
    {M T : PortMatching V} (h : Reduces M T) (N : PortMatching W) (E : OpenEmbedding M N) :
    ∃ U : PortMatching W, ∃ F : OpenEmbedding T U, Reduces N U ∧ F.port = E.port := by
  induction h generalizing N with
  | refl => exact ⟨N,E,Relation.ReflTransGen.refl,rfl⟩
  | @tail T U hr hs ih =>
    obtain ⟨N₁,E₁,hN₁,hport⟩ := ih N E
    obtain ⟨D,hD⟩ := hs
    let T₂ : PortMatching V := ⟨D.contract,D.contract_involutive T.involutive⟩
    have hu : U = T₂ := PortMatching.ext hD
    subst U
    let ED := E₁.liftDipole D
    let N₂ : PortMatching W := ⟨ED.contract,ED.contract_involutive N₁.involutive⟩
    exact ⟨N₂,E₁.residual D,hN₁.tail ⟨ED,rfl⟩,hport⟩

/-- A completely proved local contraction history transports any deactivated internal port
into an actual ambient contraction history that deactivates the same original port identity. -/
theorem exists_ambient_reduction_fixed {V W : Type*} [DecidableEq V] [DecidableEq W]
    {M T : PortMatching V} {N : PortMatching W} (E : OpenEmbedding M N)
    (h : Reduces M T) (p : V × Fin 4) (hp : T.mate p = p) :
    ∃ U : PortMatching W, Reduces N U ∧ U.mate (E.port p) = E.port p := by
  obtain ⟨U,F,hU,hport⟩ := lift_reduces h N E
  refine ⟨U,hU,?_⟩
  rw [← hport,F.mate,hp]

end OpenEmbedding
end WaveTurbulence.Reg.Skeleton.PortMatching
