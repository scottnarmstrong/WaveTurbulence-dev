/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.LabelledGraph

/-! # Every unused branch label is an inactive vertex of the exact source graph -/

public section
namespace WaveTurbulence.Reg.Skeleton.LabelledGarden

theorem graph_unused_label {w : ℕ} {B : Type*} (G : LabelledGarden w B) (b : B)
    (hb : b ∉ Set.range G.label) (i : Fin 4) : G.graph.mate (.inr b,i) = (.inr b,i) := by
  apply extendMate_outside
  rintro ⟨p,hp⟩
  cases p with
  | inl j =>
    have he : (Sum.inl j : Fin w ⊕ B) = .inr b := congrArg (fun z : (Fin w ⊕ B) × Fin 4 => z.1) hp
    cases he
  | inr p => exact hb ⟨p.1,Sum.inr.inj (congrArg (fun z : (Fin w ⊕ B) × Fin 4 => z.1) hp)⟩

end WaveTurbulence.Reg.Skeleton.LabelledGarden
