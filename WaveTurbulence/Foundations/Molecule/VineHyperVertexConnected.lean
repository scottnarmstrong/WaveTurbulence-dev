/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.Molecule.VineLikeConnected
import Mathlib.Tactic

/-! # Hyper-vine-like objects have no separating atom -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET defvine/subsetvc: removing any one atom from an HV or HVC
leaves its atom group connected. The retained designated closing bond joins
the surviving chain ends; every other atom reaches one of those ends. -/
theorem hyperLike_erase_connected (M : Molecule V D) {S : Finset V} {a b : V}
    (h : IsHV M S a b ∨ IsHVC M S a b) (z : V) : GroupConnected M (S.erase z) := by
  obtain ⟨e,he,hB,n,hchain⟩ := hyperLike_iff_adjoint_VC.mp h
  have hab : M.Adj a b := by
    rcases Sym2.eq_iff.mp he with he | he
    · exact ⟨e,he.1,he.2⟩
    · exact ⟨M.mate e,he.2,by rw [M.mate_mate]; exact he.1⟩
  have bridge (haz : a ≠ z) (hbz : b ≠ z) : (Mole.induced M (S.erase z)).SameComponent a b :=
    Relation.EqvGen.rel _ _ ((Mole.induced_adj_iff M (S.erase z) a b).mpr
      ⟨hab,mem_erase.mpr ⟨haz,hB.2.1⟩,mem_erase.mpr ⟨hbz,hB.2.2.1⟩⟩)
  intro u hu v hv
  have hu' := chain_erase_endpoint_reach hchain u hu
  have hv' := chain_erase_endpoint_reach hchain v hv
  rcases hu' with ⟨haz,hau⟩ | ⟨hbz,hbu⟩ <;> rcases hv' with ⟨haz',hav⟩ | ⟨hbz',hbv⟩
  · exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (eraseBond_induced_path M e _ hau))
      (eraseBond_induced_path M e _ hav)
  · exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (eraseBond_induced_path M e _ hau))
      (Relation.EqvGen.trans _ _ _ (bridge haz hbz') (eraseBond_induced_path M e _ hbv))
  · exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (eraseBond_induced_path M e _ hbu))
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (bridge haz' hbz)) (eraseBond_induced_path M e _ hav))
  · exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (eraseBond_induced_path M e _ hbu))
      (eraseBond_induced_path M e _ hbv)

end WaveTurbulence.Vine
