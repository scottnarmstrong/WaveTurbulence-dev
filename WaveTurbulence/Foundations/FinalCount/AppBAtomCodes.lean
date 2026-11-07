/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBRealizations
import Mathlib.Tactic

/-! # Finite atom codes for graph-dependent removal tables -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbAtomCode (M : Molecule V D) (v : M.atoms) : ℕ :=
  (Fintype.equivFin M.atoms v).val

noncomputable def appbDecodeAtom (M : Molecule V D) (v0 : M.atoms) (n : ℕ) : M.atoms := by
  classical
  exact if h : n < Fintype.card M.atoms then (Fintype.equivFin M.atoms).symm ⟨n,h⟩ else v0

theorem appb_atom_code_lt (M : Molecule V D) (v : M.atoms) :
    appbAtomCode M v < Fintype.card M.atoms := (Fintype.equivFin M.atoms v).isLt

theorem appb_decode_atom_code (M : Molecule V D) (v0 v : M.atoms) :
    appbDecodeAtom M v0 (appbAtomCode M v) = v := by
  classical
  rw [appbDecodeAtom,dite_eq_left (appb_atom_code_lt M v)]
  exact (Fintype.equivFin M.atoms).symm_apply_apply v

theorem appb_decode_atom_injOn (M : Molecule V D) (v0 : M.atoms) :
    Set.InjOn (appbDecodeAtom M v0) (Set.Iio (Fintype.card M.atoms)) := by
  classical
  intro a ha b hb he
  change a < Fintype.card M.atoms at ha
  change b < Fintype.card M.atoms at hb
  rw [appbDecodeAtom,dite_eq_left ha,appbDecodeAtom,dite_eq_left hb] at he
  exact congrArg Fin.val ((Fintype.equivFin M.atoms).symm.injective he)

end WaveTurbulence.Mole
