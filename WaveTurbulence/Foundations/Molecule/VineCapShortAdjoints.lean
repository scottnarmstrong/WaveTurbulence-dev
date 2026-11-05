/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapFrontBranches
public import WaveTurbulence.Foundations.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.Molecule.VineShortGraphConnectivity
public import WaveTurbulence.Foundations.Molecule.VineCapIncidenceRealization
public import WaveTurbulence.Foundations.Molecule.VineDeletedBondMultiset
public import WaveTurbulence.Foundations.Molecule.VineCapSideGraph
public import WaveTurbulence.Foundations.Molecule.VineEraseBondMolecule
import Mathlib.Tactic

/-! # The zero-rung cap adjoint is a double chain; one/two-rung caps are not vine-like -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace CapPrefixData
variable {M : Molecule V D} {A : Finset V} {n r : ℕ} (C : CapPrefixData M A n r)

include C in
/-- A triangle-only hyper-vine-like cap has exactly the source two-double-
bond adjoint. The designated actual deleted bond is retained. -/
theorem zero_prefix_adjoint_doubleChain {x y : V} (h : IsHV M A x y ∨ IsHVC M A x y)
    (hr : r=0) : ∃ e : D,M.ends e=s(x,y) ∧ DoubleChain (Mole.eraseBond M e) A x y 2 := by
  apply hyperLike_three_atom_adjoint h
  have hc := C.card_atoms
  omega

include C in
/-- Caps with one or two selected full rungs cannot be HV or HVC: their
five/seven-atom adjoints have no separating atom and cannot be VCs,
including after the F72 addition of four-atom type-II vines. -/
theorem short_prefix_not_hyperLike (hM : M.IsMolecule) {x y : V} (hr : r=1 ∨ r=2) :
    ¬(IsHV M A x y ∨ IsHVC M A x y) := by
  intro h
  obtain ⟨e,he,hVC⟩ := hyperLike_iff_adjoint_VC.mp h
  have hH : Mole.IsHyperBlock M A x y := ⟨e,he,hVC.1⟩
  have hrpos : 1 ≤ r := by omega
  have heA : M.InGroup A e := by
    have he' := Sym2.eq_iff.mp he
    change (M.atom e=x ∧ M.atom (M.mate e)=y) ∨
      (M.atom e=y ∧ M.atom (M.mate e)=x) at he'
    rcases he' with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact ⟨h1.symm ▸ hVC.1.2.1,h2.symm ▸ hVC.1.2.2.1⟩
    · exact ⟨h1.symm ▸ hVC.1.2.2.1,h2.symm ▸ hVC.1.2.1⟩
  have hj := C.hyper_front_labels_pos hM hH hrpos
  have hdelete := congrArg (Multiset.map (Sym2.map C.label))
    (eraseBond_groupBonds_cons M e A heA)
  rw [Multiset.map_cons,C.bonds_eq hM,he,Sym2.map_mk,hj] at hdelete
  have hcap : rawBondMultiset (capBonds 9 r)=
      ({s(9+(r-1),9+r+(r-1))} : Multiset (Sym2 ℕ))+
        rawBondMultiset (capAdjointBonds 9 (r-1)) := by
    have hh := capBonds_bondMultiset 9 (r-1)
    simpa only [show r-1+1=r by omega] using hh
  have hb : ((Mole.eraseBond M e).groupBonds A).map (Sym2.map C.label)=
      rawBondMultiset (capAdjointBonds 9 (r-1)) := by
    apply add_left_cancel (a := ({s(9+(r-1),9+r+(r-1))} : Multiset (Sym2 ℕ)))
    exact hdelete.trans hcap
  have hconn := erase_connected_of_label_paths x hVC.1.2.1 C.label C.label_injOn
    (capLabels 9 r) C.label_image (capAdjointBonds 9 (r-1))
    (short_cap_endpoints r hr)
    (fun u hu v hv hedge => adj_of_label_bonds C.label C.label_injOn _ hb hu hv hedge)
    (isVC_connected hVC) (fun z hz u hu v hv huz hvz => short_cap_paths r hr z u v hz hu hv huz hvz)
  have hc : A.card=5 ∨ A.card=7 := by
    have hh := C.card_atoms
    omega
  have hne : M.atom e ≠ M.atom (M.mate e) := by
    have hh := Sym2.eq_iff.mp he
    rcases hh with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · rw [h1,h2]
      exact hVC.1.2.2.2.1
    · rw [h1,h2]
      exact Ne.symm hVC.1.2.2.2.1
  have hN := eraseBond_isMolecule M hM e hne
  exact not_isVC_five_or_seven_of_erase_connected (Mole.eraseBond M e) hN hc hconn hVC

end CapPrefixData
end WaveTurbulence.Vine
