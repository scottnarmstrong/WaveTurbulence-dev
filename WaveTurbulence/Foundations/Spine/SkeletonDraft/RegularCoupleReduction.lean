/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SourceExpansionHistories
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RegularCoupleHistories
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.GardenGraphHistories
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.TrivialGardens

/-! # An actual source regular couple contracts to the actual trivial couple -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem regularCouple_reduces_trivial {G : Garden 2} (hG : IsRegularCouple G) :
    GardenReduces G (decodedCouple .triv) := by
  have hp : G.IsPlain := by
    obtain ⟨R,hR,hm⟩ := hG
    exact hm.1.1
  have hr := regularCouple_reconstructs hG
  have ht := rawOfGarden_eq_code_raw (decodedCouple_decodes .triv)
  change Reconstructs (rawCplSet RegCpl.triv.raw) (rawOfGarden G) at hr
  rw [← ht] at hr
  exact gardenReduces_of_reconstructs _ G (decodedCouple_decodes .triv).1.1 hp hr

theorem LabelledGarden.graph_branch_fixed_of_trivial {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    (hG : IsTrivialGarden G.garden) (b : B) (i : Fin 4) :
    G.graph.mate (.inr b,i) = (.inr b,i) := by
  apply extendMate_outside
  rintro ⟨p,hp⟩
  cases p with
  | inl j =>
    have he : (Sum.inl j : Fin w ⊕ B) = .inr b := congrArg (fun z : (Fin w ⊕ B) × Fin 4 => z.1) hp
    cases he
  | inr p =>
    have hn := p.1.2
    rw [hG.2] at hn
    exact Finset.notMem_empty _ hn

end WaveTurbulence.Reg.Skeleton
