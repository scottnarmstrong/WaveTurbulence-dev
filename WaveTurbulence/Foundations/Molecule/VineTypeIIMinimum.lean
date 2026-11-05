/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRealizationCounts
import Mathlib.Tactic

/-! # Source rung convention for type II, including the Q-block (F72) -/

public section
namespace WaveTurbulence.Vine

/-- F72/defvine: k is the number of inserted rungs and m=k+1 counts
all doubled pairs. The family starts at m=1, with four atoms. -/
theorem typeII_expand_counts (k : ℕ) :
    (VineType.II.expand [k]).n=2+2*(k+1) ∧
    (VineType.II.expand [k]).bonds.length=2+4*(k+1) ∧
    (VineType.II.expand [k]).groups.length=k+1 := by
  have ha := expand_atoms_exact .II [k] rfl
  have hb := expand_bonds .II [k] rfl
  have hg := expand_groups_exact .II [k] rfl
  norm_num [VineType.template] at ha hb hg
  omega

/-- The one-double-bond type-II template is precisely the four-atom,
six-bond Q-block, with one two-atom coherence group. -/
theorem typeII_Q_block_counts :
    (VineType.II.expand [0]).n=4 ∧
    (VineType.II.expand [0]).bonds.length=6 ∧
    (VineType.II.expand [0]).groups=[[2,3]] := by decide

/-- Every actual type-II vine has m≥1 doubled pairs, 2+2m atoms and
2+4m bonds. No six-atom minimum is imposed. -/
theorem isVine_typeII_counts {V D : Type*} [DecidableEq V] [Fintype D]
    {M : Molecule V D} {S : Finset V} {a b : V} (h : M.IsVine .II S a b) :
    ∃ m : ℕ,1 ≤ m ∧ S.card=2+2*m ∧ (M.groupBonds S).card=2+4*m := by
  obtain ⟨k,_hk,ha,hb⟩ := isVine_counts h
  norm_num [VineType.template] at ha hb
  exact ⟨k.sum+1,by omega,by omega,by omega⟩

end WaveTurbulence.Vine
