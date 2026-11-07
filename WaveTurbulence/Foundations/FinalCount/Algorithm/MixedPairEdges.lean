/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.BoundarySeparation
public import Mathlib.Data.Sum.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-! # Parallel pair and two complete boundary families for mixed-degree figures -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

structure MixedPairEdges (M : Molecule V D) (a b : V) (n k m : ℕ) where
  middle : Fin n ≃ {x // x ∈ parallelBonds M a b}
  left : BoundaryStar M a b k
  right : BoundaryStar M b a m

noncomputable def mixedPairEdges (M : Molecule V D) (hno : AppbNoLoops M)
    {a b : V} {n k m : ℕ} (hda : M.deg a = n+k) (hdb : M.deg b = n+m)
    (hm : M.bondsBetween a b = n) : MixedPairEdges M a b n k m := by
  have hm' : M.bondsBetween b a = n := by
    unfold Molecule.bondsBetween at hm ⊢
    simpa only [Sym2.eq_swap (a := b) (b := a)] using hm
  exact ⟨parallelBondEnumeration M hm,boundaryStarOfDegree M hno hda hm,
    boundaryStarOfDegree M hno hdb hm'⟩

namespace MixedPairEdges
variable {M : Molecule V D} {a b : V} {n k m : ℕ}

def index : Fin (n+(k+m)) ≃ Fin n ⊕ (Fin k ⊕ Fin m) :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm)

def enumeration (data : MixedPairEdges M a b n k m) : Fin (n+(k+m)) → D :=
  Sum.elim (fun i => (data.middle i).val)
    (Sum.elim (fun i => (data.left.edge i).val) (fun i => (data.right.edge i).val)) ∘ index

theorem enumeration_injective (data : MixedPairEdges M a b n k m) (hab : a ≠ b) :
    Function.Injective data.enumeration := by
  have hmid : Function.Injective fun i => (data.middle i).val := by
    intro i j h
    exact data.middle.injective (Subtype.ext h)
  have hlr := data.left.edge_val_injective.sumElim data.right.edge_val_injective
    (data.left.edge_ne_reverse_boundary data.right hab)
  apply Function.Injective.comp (hmid.sumElim hlr ?_) index.injective
  intro i j
  cases j with
  | inl j => exact Ne.symm (data.left.edge_ne_parallel j (data.middle i).property)
  | inr j =>
    have hm' : (data.middle i).val ∈ parallelBonds M b a := by
      have hm := (data.middle i).property
      simpa only [parallelBonds,Sym2.eq_swap (a := b) (b := a)] using hm
    exact Ne.symm (data.right.edge_ne_parallel j hm')

theorem enumeration_outgoing (data : MixedPairEdges M a b n k m) (i : Fin (n+(k+m))) :
    M.out (data.enumeration i) = true := by
  simp only [enumeration,Function.comp_apply]
  rcases index i with j | (j | j)
  · exact (mem_filter.mp (mem_filter.mp (data.middle j).property).1).2
  · exact data.left.outgoing j
  · exact data.right.outgoing j

end MixedPairEdges
end WaveTurbulence.Mole.AppbAlgorithm
