/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.RegularHeldOut
public import WaveTurbulence.Foundations.RegAsymp.SpecialSign

/-! # Assembly of the corrected B2 couple leading term

DH23 (KQZapprox), corrected DH21 Prop7.5/F61. This conditional algebraic
helper consumes the pending CANCEL7 coefficient identity. It is not the
asymptotic theorem or a substitute for the coefficient/momentum analysis.
-/

public section
namespace WaveTurbulence.RegAsymp
open Finset TTree

/-- After CANCEL7 identifies the time coefficient and the momentum integral
has been identified with Mstar, finite summation is exactly B2's actual app.
The coefficient sign is moved to the negative inverse product only here. -/
theorem assemble_couple_app_of_coefficient_identity {d : ℕ}
    (Q : RegCpl) (δ r : ℝ) (F : Mom d → ℝ) (t s : ℝ) (k : Mom d)
    (c : Finset (Fin 2 × Path) → ℂ)
    (hcoeff : ∀ Z ⊆ chosenSet Q.links, c Z =
      if Q.dominant = true ∧ IsSpecialSet Q.links Z then
        (-1 : ℂ) ^ Z.card * (Q.JB r t s : ℂ) else 0) :
    ((2 : ℂ)⁻¹ ^ Q.size * (δ : ℂ) ^ (Q.size / 2) *
      zetaOfTrees ![1,-1] ![Q.trees.1,Q.trees.2]) *
      (∑ Z ∈ (chosenSet Q.links).powerset,
        (∏ z ∈ Z, (((((nodeSign ![1,-1] z : ℤˣ) : ℤ) : ℂ) * Real.pi * Complex.I))⁻¹) *
          c Z * (Q.Mstar F Z (0,[]) (1,[]) k : ℂ)) = Q.app δ r F t s k := by
  classical
  unfold RegCpl.app
  by_cases hdom : Q.dominant = true
  · rw [ite_eq_left hdom]
    congr 1
    rw [specialSets,sum_filter]
    apply sum_congr rfl
    intro Z hZ
    rw [hcoeff Z (mem_powerset.mp hZ)]
    by_cases hs : IsSpecialSet Q.links Z
    · rw [ite_eq_left ⟨hdom,hs⟩,ite_eq_left hs]
      exact special_coefficient_sign Z
        (fun z => ((((nodeSign ![1,-1] z : ℤˣ) : ℤ) : ℂ) * Real.pi * Complex.I)) _ _
    · rw [ite_eq_right (by tauto),ite_eq_right hs]
      simp only [mul_zero,zero_mul]
  · rw [ite_eq_right hdom]
    apply mul_eq_zero_of_right
    apply sum_eq_zero
    intro Z hZ
    rw [hcoeff Z (mem_powerset.mp hZ),ite_eq_right (by tauto)]
    simp only [mul_zero,zero_mul]

end WaveTurbulence.RegAsymp
