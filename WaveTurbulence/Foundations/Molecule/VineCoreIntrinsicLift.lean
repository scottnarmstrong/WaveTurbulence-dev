/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCoreCoherencePaths
public import WaveTurbulence.Foundations.Molecule.VineCoreUndoubledActual
public import WaveTurbulence.Foundations.Molecule.VineUntouchedCoreEdges
import Mathlib.Tactic

/-! # Every original group is intrinsically connected in the actual molecule -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Literal intrinsic edges lift to actual intrinsic edges. -/
theorem VineRealization.core_intrinsic_edge (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (hB : M.IsBlock S a b) (i j : Fin X.template.n) (he : CoreCoherenceEdge X i j) :
    CoherenceEdge M S a b (R.coreAtom i).1 (R.coreAtom j).1 := by
  obtain ⟨hi,hj,hd | hu | ⟨hu,w,hw,hjw,hcount,hadj,hadj'⟩⟩ := he
  · exact Or.inl (R.core_double hB i j hi hj hd.1 hd.2)
  · exact Or.inr (Or.inl ⟨R.core_undoubled_actual M hM hB i hi hu.1,
      R.core_undoubled_actual M hM hB j hj hu.2⟩)
  · have unmarked := template_triangle_attachment_unmarked X i j w hi hj hw hu hjw hcount hadj hadj'
    have unmarked' := template_triangle_attachment_unmarked X i w j hi hw hj hu hjw.symm
      (by omega) hadj' hadj
    have actualAdj (p q : Fin X.template.n) (h : EdgeAdj X.template.bonds p.1 q.1)
        (hslots : ∀ s ∈ X.template.slots,
          ((p.1,q.1) ≠ s.1 ∧ (p.1,q.1) ≠ s.2) ∧
          ((q.1,p.1) ≠ s.1 ∧ (q.1,p.1) ≠ s.2)) :
        M.Adj (R.coreAtom p).1 (R.coreAtom q).1 := by
      rcases h with h | h
      · exact R.core_untouched_adj p q h (fun s hs => (hslots s hs).1)
      · exact Mole.adj_symmetric M (R.core_untouched_adj q p h (fun s hs => (hslots s hs).2))
    exact Or.inr (Or.inr ⟨R.core_undoubled_actual M hM hB i hi hu,
      (R.coreAtom w).1,R.core_double hB j w hj hw hjw hcount,
      actualAdj i j hadj unmarked,actualAdj i w hadj' unmarked'⟩)

/-- Original source groups are connected by the graph-defined relation. -/
theorem VineRealization.core_group_intrinsic_connected (M : Molecule V D)
    (hM : M.IsMolecule) {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (hB : M.IsBlock S a b)
    {g : List ℕ} (hg : g ∈ X.template.groups) (i j : Fin X.template.n)
    (hi : i.1 ∈ g) (hj : j.1 ∈ g) :
    Relation.EqvGen (CoherenceEdge M S a b) (R.coreAtom i).1 (R.coreAtom j).1 := by
  have step (p q : Fin X.template.n) (h : CoreCoherenceEdge X p q ∨ CoreCoherenceEdge X q p) :
      Relation.EqvGen (CoherenceEdge M S a b) (R.coreAtom p).1 (R.coreAtom q).1 := by
    rcases h with h | h
    · exact Relation.EqvGen.rel _ _ (R.core_intrinsic_edge M hM hB p q h)
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (R.core_intrinsic_edge M hM hB q p h))
  rcases template_group_intrinsic_paths X g hg i j hi hj with he | he | ⟨m,hm,hm'⟩
  · subst j; exact Relation.EqvGen.refl _
  · exact step i j he
  · exact Relation.EqvGen.trans _ _ _ (step i m hm) (step m j hm')

end WaveTurbulence.Vine
