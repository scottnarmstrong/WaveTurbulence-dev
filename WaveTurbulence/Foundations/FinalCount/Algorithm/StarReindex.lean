/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.Star
import Mathlib.Tactic

/-! # Permuting a star's actual bond enumeration -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace Star
variable {M : Molecule V D} {a : V} {k : ℕ}

def reindex (st : Star M a k) (e : Equiv.Perm (Fin k)) : Star M a k where
  edge := e.trans st.edge
  neighbor := st.neighbor ∘ e
  neighbor_mem i := st.neighbor_mem (e i)
  neighbor_ne i := st.neighbor_ne (e i)
  endpoints i := st.endpoints (e i)

end Star
end WaveTurbulence.Mole.AppbAlgorithm
