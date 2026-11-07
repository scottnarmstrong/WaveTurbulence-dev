/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCosetTriples
import Mathlib.Tactic

/-! # The independent strip in signed triple difference coordinates -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole

/-- Each actual triple label is the conserved physical momentum minus
one of the three selectors y, x+y, x in the two free differences. -/
theorem appb_triple_difference_selector {d : ℕ} (L : ℝ) (w : Mom d)
    (q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) (nk : Fin d → ℤ)
    (hcon : q.1-q.2.1+q.2.2 = nk) (j : Fin 3) :
    (w+latticePoint L nk)-
      (![latticePoint L (WeylSums.threeVectorDifferences q).1,
        latticePoint L (WeylSums.threeVectorDifferences q).2,
        latticePoint L (WeylSums.threeVectorDifferences q).1+
          latticePoint L (WeylSums.threeVectorDifferences q).2] (![1,2,0] j)) =
      (![w+latticePoint L q.1,w+latticePoint L q.2.1,w+latticePoint L q.2.2] j) := by
  have hK : latticePoint L nk = latticePoint L q.1-latticePoint L q.2.1+latticePoint L q.2.2 := by
    rw [← WeylSums.latticePoint_sub_eq,← WeylSums.latticePoint_add_eq,hcon]
  fin_cases j
  · change (w+latticePoint L nk)-latticePoint L (q.2.2-q.2.1) = w+latticePoint L q.1
    rw [WeylSums.latticePoint_sub_eq,hK]
    abel
  · change (w+latticePoint L nk)-(latticePoint L (q.1-q.2.1)+latticePoint L (q.2.2-q.2.1)) = w+latticePoint L q.2.1
    rw [WeylSums.latticePoint_sub_eq,WeylSums.latticePoint_sub_eq,hK]
    abel
  · change (w+latticePoint L nk)-latticePoint L (q.1-q.2.1) = w+latticePoint L q.2.2
    rw [WeylSums.latticePoint_sub_eq,hK]
    abel

/-- Transporting the strip changes only its fixed real center. -/
theorem appb_triple_strip_difference_bound {d : ℕ} (L : ℝ) (w r : Mom d)
    (q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) (nk : Fin d → ℤ)
    (hcon : q.1-q.2.1+q.2.2 = nk) (j : Fin 3) (β τ : ℝ)
    (hs : |inner ℝ r (![w+latticePoint L q.1,w+latticePoint L q.2.1,w+latticePoint L q.2.2] j)-β| ≤ τ) :
    |inner ℝ r (![latticePoint L (WeylSums.threeVectorDifferences q).1,
        latticePoint L (WeylSums.threeVectorDifferences q).2,
        latticePoint L (WeylSums.threeVectorDifferences q).1+
          latticePoint L (WeylSums.threeVectorDifferences q).2] (![1,2,0] j))-
      (inner ℝ r (w+latticePoint L nk)-β)| ≤ τ := by
  rw [← appb_triple_difference_selector L w q nk hcon j,inner_sub_right] at hs
  have he : inner ℝ r (![latticePoint L (WeylSums.threeVectorDifferences q).1,
        latticePoint L (WeylSums.threeVectorDifferences q).2,
        latticePoint L (WeylSums.threeVectorDifferences q).1+
          latticePoint L (WeylSums.threeVectorDifferences q).2] (![1,2,0] j))-
      (inner ℝ r (w+latticePoint L nk)-β) =
      -(inner ℝ r (w+latticePoint L nk)-
        inner ℝ r (![latticePoint L (WeylSums.threeVectorDifferences q).1,
          latticePoint L (WeylSums.threeVectorDifferences q).2,
          latticePoint L (WeylSums.threeVectorDifferences q).1+
            latticePoint L (WeylSums.threeVectorDifferences q).2] (![1,2,0] j))-β) := by ring
  rw [he,abs_neg]
  exact hs

end WaveTurbulence.Mole
