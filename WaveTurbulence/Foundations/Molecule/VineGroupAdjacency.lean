/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
import Mathlib.Tactic

/-! # Bond-multiset membership and actual group adjacency -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

/-- Membership in the induced bond multiset is precisely adjacency with
both atoms in the induced group. Loops and multiple bonds are retained. -/
theorem mem_groupBonds_iff (S : Finset V) (u v : V) :
    s(u,v) ∈ M.groupBonds S ↔ M.Adj u v ∧ u ∈ S ∧ v ∈ S := by
  simp only [Molecule.groupBonds,Multiset.mem_map,Finset.mem_val,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨x,⟨_hx,hg⟩,he⟩
    have hh := Sym2.eq_iff.mp he
    change (M.atom x=u ∧ M.atom (M.mate x)=v) ∨
      (M.atom x=v ∧ M.atom (M.mate x)=u) at hh
    rcases hh with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · exact ⟨⟨x,hu,hv⟩,hu ▸ hg.1,hv ▸ hg.2⟩
    · exact ⟨⟨M.mate x,hu,by rw [M.mate_mate]; exact hv⟩,hu ▸ hg.2,hv ▸ hg.1⟩
  · rintro ⟨⟨x,hxu,hxv⟩,hu,hv⟩
    cases hx : M.out x
    · refine ⟨M.mate x,⟨?_,?_,?_⟩,?_⟩
      · rw [M.out_mate,hx]; rfl
      · exact hxv.symm ▸ hv
      · rw [M.mate_mate]; exact hxu.symm ▸ hu
      · simp only [Molecule.ends,M.mate_mate,hxu,hxv,Sym2.eq_swap]
    · exact ⟨x,⟨hx,hxu.symm ▸ hu,hxv.symm ▸ hv⟩,by simp only [Molecule.ends,hxu,hxv]⟩

end WaveTurbulence.Vine
