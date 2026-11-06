/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SourceMiniDipoles
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.PrimeGraph

/-! # Exact equivalence of literal source primeness and terminal labelled graph matching -/

public section
namespace WaveTurbulence.Reg.Skeleton
namespace LabelledGarden

/-- Embed the three actual source bonds at the original injective branch labels. -/
@[expose] noncomputable def graphDipole_of_branch {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    (hG : G.garden.IsPlain) (D : BranchDipole G.garden) : Dipole G.graph.mate where
  u := .inr (G.label D.u)
  v := .inr (G.label D.v)
  ne := fun he => D.ne (G.label.injective (Sum.inr.inj he))
  perm := D.perm
  free := D.free
  active_u := G.graph_branch_active hG D.u
  active_v := G.graph_branch_active hG D.v
  internal := by
    intro i hi
    change G.graph.mate (G.portEmbedding (.inr (D.u,i))) =
      G.portEmbedding (.inr (D.v,D.perm i))
    rw [G.graph_mate_embedding,D.internal i hi]

/-- Any actual embedded source mini produces a genuine labelled graph contraction. -/
theorem graph_not_normal_of_mini {w : ℕ} {B : Type*} [DecidableEq B]
    (G : LabelledGarden w B) (hG : G.garden.IsPlain) (h : MiniOccurrence G.garden) :
    ¬ PortMatching.Normal G.graph := by
  have hd : Nonempty (Dipole G.graph.mate) := by
    cases h with
    | opA b c k hm => exact ⟨G.graphDipole_of_branch hG (hm.branchDipole hG)⟩
    | opB b c m hm => exact ⟨G.graphDipole_of_branch hG hm.branchDipole⟩
  obtain ⟨D⟩ := hd
  intro hn
  exact hn ⟨D.contract,D.contract_involutive G.graph.involutive⟩ ⟨D,rfl⟩

/-- Literal source primeness is exactly terminality of its labelled graph. -/
theorem isPrimeGarden_iff_graph_normal {w : ℕ} {B : Type*} [DecidableEq B]
    (G : LabelledGarden w B) (hG : G.garden.IsPlain) :
    IsPrimeGarden G.garden ↔ PortMatching.Normal G.graph := by
  constructor
  · exact G.graph_normal_of_prime
  · intro hn
    refine ⟨hG,?_⟩
    rintro ⟨hm⟩
    exact G.graph_not_normal_of_mini hG hm hn

end LabelledGarden
end WaveTurbulence.Reg.Skeleton
