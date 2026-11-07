/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.BoundaryStar
import Mathlib.Tactic

/-! # The five actual bonds at a single-bonded degree-three pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

structure SinglePairEdges (M : Molecule V D) (a b : V) where
  left : BoundaryStar M a b 2
  right : BoundaryStar M b a 2
  middle : D
  middle_out : M.out middle = true
  middle_ends : M.ends middle = s(a,b)

noncomputable def singlePairEdges (M : Molecule V D) (hno : AppbNoLoops M)
    {a b : V} (hda : M.deg a = 3) (hdb : M.deg b = 3)
    (hm : M.bondsBetween a b = 1) : SinglePairEdges M a b := by
  classical
  let e := parallelBondEnumeration M hm
  have hm' : M.bondsBetween b a = 1 := by
    unfold Molecule.bondsBetween at hm ⊢
    simpa only [Sym2.eq_swap (a := b) (b := a)] using hm
  exact {
    left := boundaryStarOfDegree M hno hda hm
    right := boundaryStarOfDegree M hno hdb hm'
    middle := (e 0).val
    middle_out := (mem_filter.mp (mem_filter.mp (e 0).property).1).2
    middle_ends := (mem_filter.mp (e 0).property).2
  }

namespace SinglePairEdges
variable {M : Molecule V D} {a b : V}

/-- Exchange the centers without modifying any old edge. -/
def swap (e : SinglePairEdges M a b) : SinglePairEdges M b a where
  left := e.right
  right := e.left
  middle := e.middle
  middle_out := e.middle_out
  middle_ends := e.middle_ends.trans Sym2.eq_swap

/-- Reorder either pair of boundary bonds. -/
def reindex (e : SinglePairEdges M a b) (p q : Equiv.Perm (Fin 2)) : SinglePairEdges M a b where
  left := {
    edge := p.trans e.left.edge
    neighbor := e.left.neighbor ∘ p
    neighbor_mem i := e.left.neighbor_mem (p i)
    neighbor_ne_center i := e.left.neighbor_ne_center (p i)
    neighbor_ne_partner i := e.left.neighbor_ne_partner (p i)
    endpoints i := e.left.endpoints (p i)
  }
  right := {
    edge := q.trans e.right.edge
    neighbor := e.right.neighbor ∘ q
    neighbor_mem i := e.right.neighbor_mem (q i)
    neighbor_ne_center i := e.right.neighbor_ne_center (q i)
    neighbor_ne_partner i := e.right.neighbor_ne_partner (q i)
    endpoints i := e.right.endpoints (q i)
  }
  middle := e.middle
  middle_out := e.middle_out
  middle_ends := e.middle_ends

end SinglePairEdges
end WaveTurbulence.Mole.AppbAlgorithm
