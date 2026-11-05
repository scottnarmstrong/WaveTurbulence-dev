/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.DartGeometry

/-! # Exact ordered child slots of LP incidences

TARGET molecpl: distinct LP bonds use distinct children at both atoms.
-/

public section
namespace WaveTurbulence.Molecpl
open TTree
variable {w : ℕ} (G : Garden w)

/-- Decode an actual LP dart, retaining both child positions. -/
theorem dart_leaf_pair_positions {x : GardenDart G} (h : ¬ IsPCDart G x)
    {a b : GBranch G.tree} (ha : G.molecule.atom x = a)
    (hb : G.molecule.atom (G.molecule.mate x) = b) :
    ∃ (l : GLeaf G.tree) (i j : Fin 3), G.mark l = none ∧
      l.toNode = a.child i ∧ (G.pair l).toNode = b.child j ∧
      Mole.dartPosition G x = i.succ ∧ Mole.dartPosition G (G.molecule.mate x) = j.succ := by
  cases x with
  | inl c => exact (h ⟨c.1,c.2,rfl⟩).elim
  | inr l =>
    let i := l.1.1.2.getLast l.2.2.1
    let j := (G.pair l.1).1.2.getLast l.2.2.2
    change GNode.parent l.1.toNode l.2.2.1 = a at ha
    change GNode.parent (G.pair l.1).toNode l.2.2.2 = b at hb
    refine ⟨l.1,i,j,l.2.1,?_,?_,rfl,rfl⟩
    · rw [← ha]
      exact (Mole.parent_child_eq_node l.1.toNode l.2.2.1).symm
    · rw [← hb]
      exact (Mole.parent_child_eq_node (G.pair l.1).toNode l.2.2.2).symm

/-- Distinct actual darts at one atom occupy distinct incidence positions. -/
theorem dart_positions_ne {x y : GardenDart G} (ha : G.molecule.atom x = G.molecule.atom y)
    (hne : x ≠ y) : Mole.dartPosition G x ≠ Mole.dartPosition G y := by
  intro he
  exact hne (Mole.atom_position_injective G (Prod.ext ha he))

/-- Two LP bonds between a pair of atoms use two distinct child slots at each atom. -/
theorem double_leaf_pair_positions {a b : GBranch G.tree}
    (R : Vine.TwoIncidences G.molecule a b) (h : ∀ i, ¬ IsPCDart G (R.dart i)) :
    ∃ (l₀ l₁ : GLeaf G.tree) (i₀ i₁ j₀ j₁ : Fin 3),
      G.mark l₀ = none ∧ G.mark l₁ = none ∧
      l₀.toNode = a.child i₀ ∧ (G.pair l₀).toNode = b.child j₀ ∧
      l₁.toNode = a.child i₁ ∧ (G.pair l₁).toNode = b.child j₁ ∧ i₀ ≠ i₁ ∧ j₀ ≠ j₁ := by
  obtain ⟨l₀,i₀,j₀,hm₀,ha₀,hb₀,hp₀,hq₀⟩ := dart_leaf_pair_positions G (h 0) (R.atom_eq 0) (R.neighbor_eq 0)
  obtain ⟨l₁,i₁,j₁,hm₁,ha₁,hb₁,hp₁,hq₁⟩ := dart_leaf_pair_positions G (h 1) (R.atom_eq 1) (R.neighbor_eq 1)
  have hne : R.dart 0 ≠ R.dart 1 := R.injective.ne (by decide)
  have hpn := dart_positions_ne G ((R.atom_eq 0).trans (R.atom_eq 1).symm) hne
  have hqn := dart_positions_ne G ((R.neighbor_eq 0).trans (R.neighbor_eq 1).symm)
    (fun he => hne (Mole.mate_injective G.molecule he))
  rw [hp₀,hp₁] at hpn
  rw [hq₀,hq₁] at hqn
  exact ⟨l₀,l₁,i₀,i₁,j₀,j₁,hm₀,hm₁,ha₀,hb₀,ha₁,hb₁,
    fun he => hpn (congrArg Fin.succ he),fun he => hqn (congrArg Fin.succ he)⟩

end WaveTurbulence.Molecpl
