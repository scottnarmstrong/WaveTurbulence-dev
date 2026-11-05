/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.MatchingExtension
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.GraphConfluence

/-! # The exact source garden graph with persistent branching-node labels -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- An actual garden with distinct persistent labels on its branching nodes. -/
structure LabelledGarden (w : ℕ) (B : Type*) where
  garden : Garden w
  label : GBranch garden.tree ↪ B

namespace LabelledGarden

/-- Preserve every ordered port and replace only its branch identifier by the persistent label. -/
def portEmbedding {w : ℕ} {B : Type*} (G : LabelledGarden w B) :
    Port G.garden ↪ (Fin w ⊕ B) × Fin 4 where
  toFun p := match p with
    | .inl j => (.inl j,0)
    | .inr (b,i) => (.inr (G.label b),i)
  inj' := by
    intro p q he
    cases p with
    | inl j =>
      cases q with
      | inl k => exact congrArg Sum.inl (Sum.inl.inj (congrArg Prod.fst he))
      | inr q =>
        have hv : (Sum.inl j : Fin w ⊕ B) = .inr (G.label q.1) := congrArg Prod.fst he
        cases hv
    | inr p =>
      cases q with
      | inl k =>
        have hv : (Sum.inr (G.label p.1) : Fin w ⊕ B) = .inl k := congrArg Prod.fst he
        cases hv
      | inr q =>
        have hv := congrArg (fun z : (Fin w ⊕ B) × Fin 4 => z.1) he
        have hi := congrArg (fun z : (Fin w ⊕ B) × Fin 4 => z.2) he
        exact congrArg Sum.inr (Prod.ext (G.label.injective (Sum.inr.inj hv)) hi)

/-- The full exact matching, with inactive identities on unused original labels. -/
noncomputable def graph {w : ℕ} {B : Type*} (G : LabelledGarden w B) : PortMatching (Fin w ⊕ B) where
  mate := extendMate G.portEmbedding (portMate G.garden)
  involutive := extendMate_involutive _ _ (portMate_involutive G.garden)

/-- All source edges are retained on their literal labelled ports. -/
theorem graph_mate_embedding {w : ℕ} {B : Type*} (G : LabelledGarden w B) (p : Port G.garden) :
    G.graph.mate (G.portEmbedding p) = G.portEmbedding (portMate G.garden p) :=
  extendMate_apply _ _ p

/-- For an ordinary garden, the active ports are exactly the actual source ports. -/
theorem graph_active_iff {w : ℕ} {B : Type*} (G : LabelledGarden w B) (hG : G.garden.IsPlain)
    (x : (Fin w ⊕ B) × Fin 4) : G.graph.mate x ≠ x ↔ x ∈ Set.range G.portEmbedding :=
  extendMate_active_iff _ _ (portMate_ne G.garden hG) x

/-- Every original branch label has all four active ports. -/
theorem graph_branch_active {w : ℕ} {B : Type*} (G : LabelledGarden w B) (hG : G.garden.IsPlain)
    (b : GBranch G.garden.tree) (i : Fin 4) : G.graph.mate (.inr (G.label b),i) ≠ (.inr (G.label b),i) :=
  (G.graph_active_iff hG _).mpr ⟨.inr (b,i),rfl⟩

/-- Root ports other than 0 are explicitly inactive. -/
theorem graph_root_inactive {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    (j : Fin w) (i : Fin 4) (hi : i ≠ 0) : G.graph.mate (.inl j,i) = (.inl j,i) := by
  apply extendMate_outside
  rintro ⟨p,hp⟩
  cases p with
  | inl k => exact hi (congrArg Prod.snd hp).symm
  | inr p =>
    have hv : (Sum.inr (G.label p.1) : Fin w ⊕ B) = .inl j := congrArg Prod.fst hp
    cases hv

/-- An all-active vertex of the graph really is an original branching node. -/
theorem graph_active_vertex_iff {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    (hG : G.garden.IsPlain) (b : B) :
    (∀ i, G.graph.mate (.inr b,i) ≠ (.inr b,i)) ↔ b ∈ Set.range G.label := by
  constructor
  · intro ha
    obtain ⟨p,hp⟩ := (G.graph_active_iff hG _).mp (ha 0)
    cases p with
    | inl j =>
      have hv : (Sum.inl j : Fin w ⊕ B) = .inr b := congrArg Prod.fst hp
      cases hv
    | inr p => exact ⟨p.1,Sum.inr.inj (congrArg Prod.fst hp)⟩
  · rintro ⟨a,rfl⟩
    exact G.graph_branch_active hG a

end LabelledGarden
end WaveTurbulence.Reg.Skeleton
