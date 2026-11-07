/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Data.Fin.Basic
import Lean.Elab.Tactic.Omega
/-! Elementary port rigidity for the proposed ordered-splice proof.
Fixing the negative slot alone is insufficient; one outer slot also suffices.
No assertion about actual LF maps is made here. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA

/-- A ternary child permutation fixing the middle and one outer slot is the identity. -/
theorem child_equiv_eq_refl (e : Fin 3 ≃ Fin 3) (hm : e 1 = 1)
    (i : Fin 3) (hi : i ≠ 1) (hf : e i = i) : e = Equiv.refl _ := by
  apply Equiv.ext
  intro j
  change e j = j
  by_cases hj : j = 1
  · exact hj ▸ hm
  by_cases hji : j = i
  · exact hji ▸ hf
  have hem : e j ≠ 1 := fun h => hj (e.injective (h.trans hm.symm))
  have hei : e j ≠ i := fun h => hji (e.injective (h.trans hf.symm))
  simp only [Fin.ext_iff, ne_eq] at hi hj hji hem hei ⊢
  omega

end WaveTurbulence.VineA
