/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBGoodReinsertionEffects
import Mathlib.Tactic

/-! # In a two-component molecule the complement of one component is connected -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_sameComponent_of_two_of_not (M : Molecule V D) (hF : M.numComponents = 2)
    {a b c : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hc : c ∈ M.atoms)
    (hab : ¬M.SameComponent a b) (hac : ¬M.SameComponent a c) : M.SameComponent b c := by
  let qa := appbComponent M ⟨a,ha⟩
  let qb := appbComponent M ⟨b,hb⟩
  let qc := appbComponent M ⟨c,hc⟩
  have hbq : qb ≠ qa := by
    intro he
    exact hab ((quotient_eq_iff_sameComponent M ⟨a,ha⟩ ⟨b,hb⟩).mp he.symm)
  have hcq : qc ≠ qa := by
    intro he
    exact hac ((quotient_eq_iff_sameComponent M ⟨a,ha⟩ ⟨c,hc⟩).mp he.symm)
  obtain ⟨q,hq,hu⟩ := (Nat.card_eq_two_iff' qa).mp hF
  have he : qb = qc := (hu qb hbq).trans (hu qc hcq).symm
  exact (quotient_eq_iff_sameComponent M ⟨b,hb⟩ ⟨c,hc⟩).mp he

end WaveTurbulence.Mole
