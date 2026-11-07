/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.DirectedMoleculeIso
public import WaveTurbulence.Foundations.FinalCount.AppBBridgeComponents
import Mathlib.Tactic

/-! # Component invariance under actual atom-and-dart isomorphisms -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D W E : Type*}

namespace DirectedMoleculeIso
variable {M : Molecule V D} {N : Molecule W E} (e : DirectedMoleculeIso M N)

/-- Actual half-edge isomorphisms preserve and reflect undirected adjacency. -/
theorem appb_adj_iff (u v : M.atoms) :
    N.Adj (e.atoms u).val (e.atoms v).val ↔ M.Adj u.val v.val := by
  constructor
  · rintro ⟨x,hx,hy⟩
    let y := e.darts.symm x
    have hxy : e.darts y = x := e.darts.apply_symm_apply x
    have hax : e.atoms ⟨M.atom y,M.atom_mem y⟩ = e.atoms u := by
      apply Subtype.ext
      rw [← e.atom_comm y,hxy,hx]
    have hay : e.atoms ⟨M.atom (M.mate y),M.atom_mem _⟩ = e.atoms v := by
      apply Subtype.ext
      rw [← e.atom_comm (M.mate y),← e.mate_comm y,hxy,hy]
    exact ⟨y,congrArg Subtype.val (e.atoms.injective hax),congrArg Subtype.val (e.atoms.injective hay)⟩
  · rintro ⟨x,hx,hy⟩
    have hu : (⟨M.atom x,M.atom_mem x⟩ : M.atoms) = u := Subtype.ext hx
    have hv : (⟨M.atom (M.mate x),M.atom_mem _⟩ : M.atoms) = v := Subtype.ext hy
    refine ⟨e.darts x,?_,?_⟩
    · rw [e.atom_comm,hu]
    · rw [e.mate_comm,e.atom_comm,hv]

/-- The induced equivalence acts on the actual adjacency quotients. -/
@[expose] def appbComponentsEquiv : AppbComponents M ≃ AppbComponents N where
  toFun := Quot.map e.atoms (fun u v h => (e.appb_adj_iff u v).mpr h)
  invFun := Quot.map e.atoms.symm (fun u v h => by
    have hh := (e.appb_adj_iff (e.atoms.symm u) (e.atoms.symm v)).mp
    apply hh
    simpa only [e.atoms.apply_symm_apply] using h)
  left_inv q := by
    induction q using Quot.inductionOn with | h u =>
      change appbComponent M (e.atoms.symm (e.atoms u)) = appbComponent M u
      rw [e.atoms.symm_apply_apply]
  right_inv q := by
    induction q using Quot.inductionOn with | h u =>
      change appbComponent N (e.atoms (e.atoms.symm u)) = appbComponent N u
      rw [e.atoms.apply_symm_apply]

/-- The declared finite component statistic is invariant under the full
molecule isomorphism, with no assumed equality of graph counts. -/
theorem appb_numComponents_eq (e : DirectedMoleculeIso M N) : M.numComponents = N.numComponents :=
  Nat.card_congr (appbComponentsEquiv e)

end DirectedMoleculeIso
end WaveTurbulence.Mole
