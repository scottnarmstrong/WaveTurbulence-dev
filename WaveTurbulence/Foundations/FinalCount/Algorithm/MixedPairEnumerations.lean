/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.MixedPairEdges
import Mathlib.Tactic

/-! # The source edge orders for the 3D4 and 3S2 figures -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace MixedPairEdges
variable {M : Molecule V D} {a b : V}

def reindex {n k m : ℕ} (data : MixedPairEdges M a b n k m)
    (p : Equiv.Perm (Fin k)) (q : Equiv.Perm (Fin m)) : MixedPairEdges M a b n k m where
  middle := data.middle
  left := {
    edge := p.trans data.left.edge
    neighbor := data.left.neighbor ∘ p
    neighbor_mem i := data.left.neighbor_mem (p i)
    neighbor_ne_center i := data.left.neighbor_ne_center (p i)
    neighbor_ne_partner i := data.left.neighbor_ne_partner (p i)
    endpoints i := data.left.endpoints (p i)
  }
  right := {
    edge := q.trans data.right.edge
    neighbor := data.right.neighbor ∘ q
    neighbor_mem i := data.right.neighbor_mem (q i)
    neighbor_ne_center i := data.right.neighbor_ne_center (q i)
    neighbor_ne_partner i := data.right.neighbor_ne_partner (q i)
    endpoints i := data.right.endpoints (q i)
  }

theorem d34_endpoints (data : MixedPairEdges M a b 2 1 2) (i : Fin 5) :
    M.ends (data.enumeration i) =
      (![s(a,b),s(a,b),s(a,data.left.neighbor 0),
        s(b,data.right.neighbor 0),s(b,data.right.neighbor 1)] : Fin 5 → Sym2 V) i := by
  fin_cases i
  · exact (mem_filter.mp (data.middle 0).property).2
  · exact (mem_filter.mp (data.middle 1).property).2
  · exact data.left.endpoints 0
  · exact data.right.endpoints 0
  · exact data.right.endpoints 1

def s32Order : Fin 4 → Fin 4 := ![0,3,1,2]

def s32Enumeration (data : MixedPairEdges M a b 1 2 1) : Fin 4 → D :=
  data.enumeration ∘ s32Order

theorem s32Enumeration_injective (data : MixedPairEdges M a b 1 2 1) (hab : a ≠ b) :
    Function.Injective data.s32Enumeration :=
  (data.enumeration_injective hab).comp (by decide : Function.Injective s32Order)

theorem s32Enumeration_outgoing (data : MixedPairEdges M a b 1 2 1) (i : Fin 4) :
    M.out (data.s32Enumeration i) = true := data.enumeration_outgoing (s32Order i)

theorem s32_endpoints (data : MixedPairEdges M a b 1 2 1) (i : Fin 4) :
    M.ends (data.s32Enumeration i) =
      (![s(a,b),s(b,data.right.neighbor 0),s(a,data.left.neighbor 0),
        s(a,data.left.neighbor 1)] : Fin 4 → Sym2 V) i := by
  fin_cases i
  · exact (mem_filter.mp (data.middle 0).property).2
  · exact data.right.endpoints 0
  · exact data.left.endpoints 0
  · exact data.left.endpoints 1

end MixedPairEdges
end WaveTurbulence.Mole.AppbAlgorithm
