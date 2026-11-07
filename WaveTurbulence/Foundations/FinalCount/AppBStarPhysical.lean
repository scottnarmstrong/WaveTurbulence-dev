/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBStarCount
public import WaveTurbulence.Foundations.FinalCount.AppBPhysicalTriple
import Mathlib.Tactic

/-! # Overlapping triples with prescribed physical source momenta -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset

theorem appb_star_physical_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) (m : ℕ) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, 0 < L → ∀ ζ : Fin 3, ∀ w K1 K2 : Mom d,
    ∀ centers : Fin 5 → Mom d, ∀ β1 β2 : ℝ,
    ∀ s : Finset (Fin 5 → (Fin d → ℤ)),
      (∀ q ∈ s, (∀ j,‖w+latticePoint L (q j)-centers j‖ ≤ 1) ∧
        (w+latticePoint L (q 0))-(w+latticePoint L (q 1))+(w+latticePoint L (q 2)) = K1 ∧
        (w+latticePoint L (appbStarSecond ζ q).1)-(w+latticePoint L (appbStarSecond ζ q).2.1)+
          (w+latticePoint L (appbStarSecond ζ q).2.2) = K2 ∧
        |‖w+latticePoint L (q 0)‖^2-‖w+latticePoint L (q 1)‖^2+‖w+latticePoint L (q 2)‖^2-β1| ≤ appbWidth δ γ m L ∧
        |‖w+latticePoint L (appbStarSecond ζ q).1‖^2-‖w+latticePoint L (appbStarSecond ζ q).2.1‖^2+
          ‖w+latticePoint L (appbStarSecond ζ q).2.2‖^2-β2| ≤ appbWidth δ γ m L) →
      (s.card : ℝ) ≤ L^(3*((d : ℝ)-γ)-3*min γ (1-γ)/4) := by
  obtain ⟨L₀,hL₀⟩ := appb_star_count_bound d hd γ hγ δ hδ m
  refine ⟨L₀,?_⟩
  intro L hL hLp ζ w K1 K2 centers β1 β2 s hs
  by_cases hn : s.Nonempty
  · obtain ⟨q0,hq0⟩ := hn
    let nk1 := q0 0-q0 1+q0 2
    let nk2 := (appbStarSecond ζ q0).1-(appbStarSecond ζ q0).2.1+(appbStarSecond ζ q0).2.2
    apply hL₀ L hL hLp ζ w centers nk1 nk2 β1 β2 s
    intro q hq
    have hh := hs q hq
    have h0 := hs q0 hq0
    refine ⟨hh.1,?_,?_,hh.2.2.2.1,hh.2.2.2.2⟩
    · exact appb_triple_integer_momentum hLp.ne' w (q 0,q 1,q 2) (q0 0,q0 1,q0 2)
        (hh.2.1.trans h0.2.1.symm)
    · exact appb_triple_integer_momentum hLp.ne' w (appbStarSecond ζ q) (appbStarSecond ζ q0)
        (hh.2.2.1.trans h0.2.2.1.symm)
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

end WaveTurbulence.Mole
