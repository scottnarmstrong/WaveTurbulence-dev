/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.GraphStepRealization

/-! # Every matching reduction from an ordinary source garden has an actual source trace -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem realize_graph_history_of_eq {w : ℕ} {B : Type*} [DecidableEq B]
    {M N : PortMatching (Fin w ⊕ B)} (h : PortMatching.Reduces M N)
    (G : LabelledGarden w B) (hG : G.garden.IsPlain) (he : G.graph = M) :
    ∃ H : Garden w, H.IsPlain ∧ ∃ T : ReductionTrace G.garden H,
      (LabelledGarden.mk H (T.branches.trans G.label)).graph = N := by
  induction h generalizing G with
  | refl => exact ⟨G.garden,hG,ReductionTrace.refl G.garden,he⟩
  | @tail P Q hr hs ih =>
    obtain ⟨H,hH,T,hT⟩ := ih G hG he
    let L := LabelledGarden.mk H (T.branches.trans G.label)
    have hstep : PortMatching.Step L.graph Q := hT.symm ▸ hs
    obtain ⟨K,hK,U,hU⟩ := L.realize_graph_step hH Q hstep
    exact ⟨K,hK,ReductionTrace.trans T U,hU⟩

theorem LabelledGarden.realize_graph_history {w : ℕ} {B : Type*} [DecidableEq B]
    (G : LabelledGarden w B) (hG : G.garden.IsPlain) (N : PortMatching (Fin w ⊕ B))
    (h : PortMatching.Reduces G.graph N) :
    ∃ H : Garden w, H.IsPlain ∧ ∃ T : ReductionTrace G.garden H,
      (LabelledGarden.mk H (T.branches.trans G.label)).graph = N :=
  realize_graph_history_of_eq h G hG rfl

end WaveTurbulence.Reg.Skeleton
