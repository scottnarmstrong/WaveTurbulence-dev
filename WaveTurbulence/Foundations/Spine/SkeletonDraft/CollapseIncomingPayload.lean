/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapseCoupleNodes

/-! # Incoming ports of the exact leaf payload of source couple collapse -/

public section
namespace WaveTurbulence.Reg.Skeleton.LabelledGarden

theorem collapseCouple_incoming_old {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    {a b : GNode G.garden.tree} (h : Comb.IsSubCouple G.garden a b)
    (ℓ : OutsideRoots G.garden.tree a b) :
    (G.collapseCouple h).incoming
      (collapseLeafEquiv G.garden.tree a b (Comb.subCouple_incomparable h) (.inl ℓ)).toNode =
      G.incoming ℓ.1.toNode := by
  exact (G.collapseCouple_incoming h _).trans (congrArg G.incoming (Subtype.ext rfl))

theorem collapseCouple_incoming_left {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    {a b : GNode G.garden.tree} (h : Comb.IsSubCouple G.garden a b) :
    (G.collapseCouple h).incoming
      (collapseLeafEquiv G.garden.tree a b (Comb.subCouple_incomparable h) (.inr 0)).toNode =
      G.incoming a := by
  exact (G.collapseCouple_incoming h _).trans (congrArg G.incoming (Subtype.ext rfl))

theorem collapseCouple_incoming_right {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    {a b : GNode G.garden.tree} (h : Comb.IsSubCouple G.garden a b) :
    (G.collapseCouple h).incoming
      (collapseLeafEquiv G.garden.tree a b (Comb.subCouple_incomparable h) (.inr 1)).toNode =
      G.incoming b := by
  exact (G.collapseCouple_incoming h _).trans (congrArg G.incoming (Subtype.ext rfl))

/-- Any actual incoming node slot is in the actual port family. -/
theorem incoming_mem_range {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    (a : GNode G.garden.tree) : G.incoming a ∈ Set.range G.portEmbedding :=
  ⟨encodeIncidence G.garden (.inl a),rfl⟩

end WaveTurbulence.Reg.Skeleton.LabelledGarden
