/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RegularCodeReindex
public import WaveTurbulence.Foundations.XChain.LeafPairKernel
/-! The actual coherent order-zero difference is exactly the input remainder. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open WaveTurbulence.Reg

theorem KQ_uniform_triv {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (p : ℕ) (t : ℝ) (k : Mom d) :
    KQ L γ δ F (uniformDecodedCouple p .triv) t k = (F p k : ℂ) := by
  have ht : ∀ j, (uniformDecodedCouple p .triv).garden.tree j = TTree.leaf := by
    intro j
    fin_cases j <;> rfl
  have he := kernelK_leafPair L γ δ F (uniformDecodedCouple p .triv) ht
    (uniformDecodedCouple_decodes p .triv).1.1 p (uniformDecodedCouple_layer p .triv)
    (fun b => if b.1.1 = 0 then t else t) 0 k (fun _ => 0) 0
  have hz : latticePoint L (0 : Fin d → ℤ) = 0 := by
    ext j
    change ((0 : ℤ) : ℝ) / L = 0
    simp only [Int.cast_zero, zero_div]
  simpa only [KQ, KQstar, ite_true, hz, add_zero] using he

theorem coherentCoupleSum_zero (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    (p : ℕ) (t : ℝ) (k : Mom P.d) :
    coherentCoupleSum P F (p + 1) 0 t k = (F p k : ℂ) := by
  classical
  have he := coherentCoupleSum_eq_codes P F p 0 (by simp) t k
  simp only [Nat.mul_zero] at he
  rw [he, ← finsum_subtype_eq_finsum_cond]
  letI : Unique {Q : RegCpl // Q.wf = true ∧ Q.size = 0} :=
    ⟨⟨.triv, rfl, rfl⟩, fun Q => Subtype.ext (eq_triv_of_wf_size_zero Q.1 Q.2.1 Q.2.2)⟩
  rw [finsum_eq_sum_of_fintype, Fintype.sum_unique]
  exact KQ_uniform_triv P.L P.γ P.δ F p t k

/-- The source zero-order term requires no geometric-tail estimate. -/
theorem coherentCoupleSum_zero_sub_taylor (P : WTParams) (R : ℕ → Mom P.d → ℝ)
    (p : ℕ) (t : ℝ) (k : Mom P.d) :
    coherentCoupleSum P (inputsF P R) (p + 1) 0 t k -
      (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p 0 t k : ℂ) = (R p k : ℂ) := by
  rw [coherentCoupleSum_zero]
  simp only [wkeTaylorTerm, inputsF, Complex.ofReal_add, add_sub_cancel_left]

end WaveTurbulence.LGSpine
