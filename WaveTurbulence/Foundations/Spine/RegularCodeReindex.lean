/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.UniformRegularCouple
/-! Exact reindexing of the full coherent carrier by the unique regular B2 codes. -/
public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

theorem finsum_topRegular_eq_codes (p n : ℕ) (f : LayeredGarden 2 → ℂ) :
    (∑ᶠ (LG : LayeredGarden 2) (_ : LG ∈ topRegularCarrier p (2 * n)), f LG) =
      ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n),
        f (uniformDecodedCouple p Q) := by
  rw [← finsum_subtype_eq_finsum_cond, ← finsum_subtype_eq_finsum_cond]
  exact (finsum_comp (codeToTopRegular p n) (codeToTopRegular_bijective p n)).symm

theorem coherentCoupleSum_eq_codes (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    (p n : ℕ) (hn : 2 * n ≤ P.N (p + 1)) (t : ℝ) (k : Mom P.d) :
    coherentCoupleSum P F (p + 1) (2 * n) t k =
      ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n),
        KQ P.L P.γ P.δ F (uniformDecodedCouple p Q) t k := by
  rw [coherentCoupleSum_eq_full_of_small_order P F p (2 * n) hn]
  rw [← finsum_topRegular_eq_sum p (2 * n)]
  exact finsum_topRegular_eq_codes p n (fun LG => KQ P.L P.γ P.δ F LG t k)

end WaveTurbulence.LGSpine
