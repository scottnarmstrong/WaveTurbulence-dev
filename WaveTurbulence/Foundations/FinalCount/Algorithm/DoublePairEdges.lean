/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.PairBondEnumeration
import Mathlib.Tactic

/-! # Four distinct outgoing edges at a double-bonded degree-three pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

structure DoublePairEdges (M : Molecule V D) (a b c d : V) where
  edge : Fin 4 → D
  injective : Function.Injective edge
  outgoing : ∀ i,M.out (edge i) = true
  endpoints : ∀ i,M.ends (edge i) = (![s(a,b),s(a,b),s(a,c),s(b,d)] : Fin 4 → Sym2 V) i

noncomputable def doublePairEdges (M : Molecule V D)
    {a b c d : V} (hab : a ≠ b) (hcb : c ≠ b) (hda : d ≠ a)
    (hm : M.bondsBetween a b = 2)
    {x y : D} (hx : x ∈ M.bonds) (hy : y ∈ M.bonds)
    (hex : M.ends x = s(a,c)) (hey : M.ends y = s(b,d)) : DoublePairEdges M a b c d := by
  classical
  let e := parallelBondEnumeration M hm
  have hem (i : Fin 2) : (e i).val ∈ M.bonds := (mem_filter.mp (e i).property).1
  have he (i : Fin 2) : M.ends (e i).val = s(a,b) := (mem_filter.mp (e i).property).2
  have hxe (i : Fin 2) : (e i).val ≠ x := by
    intro h
    have hh : s(a,b) = s(a,c) := (he i).symm.trans (h ▸ hex)
    rcases Sym2.eq_iff.mp hh with h | h
    · exact hcb h.2.symm
    · exact hab h.2.symm
  have hye (i : Fin 2) : (e i).val ≠ y := by
    intro h
    have hh : s(a,b) = s(b,d) := (he i).symm.trans (h ▸ hey)
    rcases Sym2.eq_iff.mp hh with h | h
    · exact hab h.1
    · exact hda h.1.symm
  have hxy : x ≠ y := by
    intro h
    have hh : s(a,c) = s(b,d) := hex.symm.trans (h ▸ hey)
    rcases Sym2.eq_iff.mp hh with h | h
    · exact hab h.1
    · exact hcb h.2
  have he01 : (e (0 : Fin 2)).val ≠ (e (1 : Fin 2)).val := by
    intro h
    have hh := e.injective (Subtype.ext h)
    exact (by decide : (0 : Fin 2) ≠ 1) hh
  exact {
    edge := ![(e 0).val,(e 1).val,x,y]
    injective := by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
        Matrix.cons_val_succ] at hij
      all_goals first
        | rfl
        | exact (he01 hij).elim
        | exact (he01 hij.symm).elim
        | exact (hxe 0 hij).elim
        | exact (hxe 0 hij.symm).elim
        | exact (hxe 1 hij).elim
        | exact (hxe 1 hij.symm).elim
        | exact (hye 0 hij).elim
        | exact (hye 0 hij.symm).elim
        | exact (hye 1 hij).elim
        | exact (hye 1 hij.symm).elim
        | exact (hxy hij).elim
        | exact (hxy hij.symm).elim
    outgoing := by
      intro i
      fin_cases i
      · exact (mem_filter.mp (hem 0)).2
      · exact (mem_filter.mp (hem 1)).2
      · exact (mem_filter.mp hx).2
      · exact (mem_filter.mp hy).2
    endpoints := by
      intro i
      fin_cases i
      · exact he 0
      · exact he 1
      · exact hex
      · exact hey
  }

end WaveTurbulence.Mole.AppbAlgorithm
