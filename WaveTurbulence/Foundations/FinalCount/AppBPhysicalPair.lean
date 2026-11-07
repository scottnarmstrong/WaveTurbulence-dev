/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLogWindows
import Mathlib.Tactic

/-! # From prescribed real momentum to actual integer pair fibers -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset CountLemmas

/-- Injectivity of the pinned lattice embedding at nonzero scale. -/
theorem appb_latticePoint_injective {d : ℕ} {L : ℝ} (hL : L ≠ 0) :
    Function.Injective (latticePoint (d := d) L) := by
  intro a b he
  funext i
  have hi := congrArg (fun x : Mom d => x i) he
  change (a i : ℝ)/L = (b i : ℝ)/L at hi
  exact Int.cast_injective ((div_left_inj' hL).mp hi)

/-- Equal prescribed physical pair momentum fixes the actual integer
momentum, on every affine coset and for both source signs. -/
theorem appb_pair_integer_momentum {d : ℕ} {L : ℝ} (hL : L ≠ 0) (w : Mom d)
    (ε : ℤˣ) (a b : (Fin d → ℤ) × (Fin d → ℤ))
    (hm : (w+latticePoint L a.1)+(ε : ℤ) • (w+latticePoint L a.2) =
      (w+latticePoint L b.1)+(ε : ℤ) • (w+latticePoint L b.2)) :
    a.1+(ε : ℤ) • a.2 = b.1+(ε : ℤ) • b.2 := by
  apply appb_latticePoint_injective hL
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simp only [Units.val_one,one_smul] at hm ⊢
    rw [WeylSums.latticePoint_add_eq,WeylSums.latticePoint_add_eq]
    apply add_left_cancel (a := w+w)
    calc
      _ = (w+latticePoint L a.1)+(w+latticePoint L a.2) := by abel
      _ = (w+latticePoint L b.1)+(w+latticePoint L b.2) := hm
      _ = _ := by abel
  · simp only [Units.val_neg,Units.val_one,neg_smul,one_smul] at hm ⊢
    simp only [← sub_eq_add_neg,WeylSums.latticePoint_sub_eq]
    calc
      _ = (w+latticePoint L a.1)-(w+latticePoint L a.2) := by abel
      _ = (w+latticePoint L b.1)-(w+latticePoint L b.2) := hm
      _ = _ := by abel

/-- A finite family with fixed physical momentum is contained in one
actual integer-momentum coset pair set. -/
theorem appb_physical_pair_subset {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    (w a b momentum : Mom d) (β τ : ℝ) (ε : ℤˣ)
    (s : Finset ((Fin d → ℤ) × (Fin d → ℤ)))
    (hs : ∀ q ∈ s, ‖w+latticePoint L q.1-a‖ ≤ 1 ∧ ‖w+latticePoint L q.2-b‖ ≤ 1 ∧
      (w+latticePoint L q.1)+(ε : ℤ) • (w+latticePoint L q.2) = momentum ∧
      |‖w+latticePoint L q.1‖^2+(ε : ℤ)*‖w+latticePoint L q.2‖^2-β| ≤ τ)
    {q₀ : (Fin d → ℤ) × (Fin d → ℤ)} (hq₀ : q₀ ∈ s) :
    (s : Set _) ⊆ appbCosetPairSet L w a b (q₀.1+(ε : ℤ) • q₀.2) β τ ε := by
  intro q hq
  have h := hs q hq
  exact ⟨h.1,h.2.1,appb_pair_integer_momentum hL w ε q q₀ (h.2.2.1.trans (hs q₀ hq₀).2.2.1.symm),h.2.2.2⟩

/-- Finiteness of the actual affine-coset pair set, for all centers. -/
theorem appb_cosetPairSet_finite {d : ℕ} {L : ℝ} (hL : 0 < L)
    (w a b : Mom d) (nk : Fin d → ℤ) (β τ : ℝ) (ε : ℤˣ) :
    (appbCosetPairSet L w a b nk β τ ε).Finite := by
  rw [appb_cosetPairSet_eq]
  exact finite_atomPairSet hL _ _ _ _ _ _

end WaveTurbulence.Mole
