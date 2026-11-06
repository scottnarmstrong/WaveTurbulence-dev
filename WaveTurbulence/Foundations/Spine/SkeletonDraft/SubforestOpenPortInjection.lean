/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SubforestOpenPorts

/-! # The actual open subforest port map is injective, including all inactive padding -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

theorem subforestOpenPort_injective {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) :
    Function.Injective (subforestOpenPort G E hc) := by
  intro p q he
  rcases uniformPort_actual_or_dummy (E.inducedGarden hc) p with ⟨a,rfl⟩ | ⟨j,i,hi,rfl⟩
  · rcases uniformPort_actual_or_dummy (E.inducedGarden hc) q with ⟨b,rfl⟩ | ⟨j,i,hi,rfl⟩
    · rw [subforestOpenPort_pad,subforestOpenPort_pad] at he
      exact congrArg (padPort (E.inducedGarden hc)) ((subforestActualPort G E hc).injective he)
    · rw [subforestOpenPort_pad,subforestOpenPort_dummy G E hc j i hi] at he
      exact (subforestActualPort_ne_dummy G E hc a j i he).elim
  · rcases uniformPort_actual_or_dummy (E.inducedGarden hc) q with ⟨b,rfl⟩ | ⟨k,l,hl,rfl⟩
    · rw [subforestOpenPort_dummy G E hc j i hi,subforestOpenPort_pad] at he
      exact (subforestActualPort_ne_dummy G E hc b j i he.symm).elim
    · rw [subforestOpenPort_dummy G E hc j i hi,subforestOpenPort_dummy G E hc k l hl] at he
      have hj : j = k := Sum.inr.inj (Sum.inr.inj
        (congrArg (fun z : (Fin w ⊕ (GBranch G.tree ⊕ Fin v)) × Fin 4 => z.1) he))
      have hil := congrArg (fun z : (Fin w ⊕ (GBranch G.tree ⊕ Fin v)) × Fin 4 => z.2) he
      exact Prod.ext (congrArg Sum.inl hj) hil

noncomputable def subforestOpenPortEmbedding {w v : ℕ} (G : Garden w)
    (E : Comb.RootedSubforest G.tree v) (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) :
    UniformPort (E.inducedGarden hc) ↪ (Fin w ⊕ (GBranch G.tree ⊕ Fin v)) × Fin 4 :=
  ⟨subforestOpenPort G E hc,subforestOpenPort_injective G E hc⟩

end WaveTurbulence.Reg.Skeleton
