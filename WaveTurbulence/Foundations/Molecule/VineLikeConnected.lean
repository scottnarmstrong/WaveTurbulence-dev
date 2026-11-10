/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.Molecule.MoleculeHyperBlocks
import Mathlib.Tactic

/-! # Connectivity of all drafted vine-like objects (TARGET defvine) -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
/-- Deleting a bond cannot create an adjacency that was absent before. -/
theorem eraseBond_adj (M : Molecule V D) (e : D) {u v : V}
    (h : (Mole.eraseBond M e).Adj u v) : M.Adj u v := by
  obtain ⟨x,hx,hv⟩ := h
  exact ⟨x.1,hx,hv⟩

omit [DecidableEq V] [Fintype D] [DecidableEq D] in
/-- An induced path in a bond deletion lifts to the original induced group. -/
theorem eraseBond_induced_path (M : Molecule V D) (e : D) (S : Finset V) {u v : V}
    (h : (Mole.induced (Mole.eraseBond M e) S).SameComponent u v) :
    (Mole.induced M S).SameComponent u v := by
  induction h with
  | rel a b hab =>
    obtain ⟨hadj,ha,hb⟩ := (Mole.induced_adj_iff (Mole.eraseBond M e) S a b).mp hab
    exact Relation.EqvGen.rel _ _ ((Mole.induced_adj_iff M S a b).mpr
      ⟨eraseBond_adj M e hadj,ha,hb⟩)
  | refl a => exact Relation.EqvGen.refl a
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- TARGET defvine: every hyper-vine is connected. -/
theorem isHV_connected {M : Molecule V D} {S : Finset V} {a b : V}
    (h : IsHV M S a b) : GroupConnected M S := by
  obtain ⟨e,_he,X,hX⟩ := h
  intro u hu v hv
  exact eraseBond_induced_path M e S (isVine_connected hX u hu v hv)

/-- TARGET defvine: every hyper-vine-chain is connected. -/
theorem isHVC_connected {M : Molecule V D} {S : Finset V} {a b : V}
    (h : IsHVC M S a b) : GroupConnected M S := by
  obtain ⟨e,_he,_hB,n,_hn,hchain⟩ := h
  intro u hu v hv
  exact eraseBond_induced_path M e S (chain_connected hchain u hu v hv)

omit [DecidableEq D] in
/-- TARGET vinechainlem: a DV is connected through either common joint. -/
theorem isDV_connected {M : Molecule V D} {S : Finset V} {a b : V}
    (h : IsDV M S a b) : GroupConnected M S := by
  obtain ⟨A,B,hA,hB,_hi,rfl⟩ := h
  exact groupConnected_union M (isVine_connected hA) (isVine_connected hB) hA.1.2.1 hB.1.2.1

end WaveTurbulence.Vine
