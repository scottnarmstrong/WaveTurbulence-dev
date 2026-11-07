/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCutInternalSign
import Mathlib.Tactic

/-! # Cut sign at a chosen inside endpoint with the other endpoint outside -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_cutSign_eq_inside_second (M : Molecule V D) (S : Finset V) (x : D) (a b : V)
    (he : M.ends x = s(a,b)) (ha : a ∉ S) (hb : b ∈ S) :
    appbCutSign M S x = appbIncidenceSign M b x :=
  appb_cutSign_eq_internal M S x b a (he.trans Sym2.eq_swap) hb ha

end WaveTurbulence.Mole
