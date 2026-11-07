/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceFactorTerms
public import WaveTurbulence.Foundations.SumintPar.FiniteFactorization

/-!
# Fixed finite support of every independent source factor

Support depends only on the inserted centres and mesh scale. It is
independent of every Fourier frequency, output momentum and time.
-/

@[expose] public section
set_option autoImplicit false

open Finset

namespace WaveTurbulence.SumintPar

/-- The literal finite box for each independent factor's lattice variables. -/
@[expose] noncomputable def sourceFactorSupport {d : ℕ} (D : SumintDatum d) (L : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) :
    (a : FactorIdx D.S) → Finset (FactorInput D.S (Fin d → ℤ) a) := by
  classical
  intro a
  rcases a with i | (a | i)
  · exact Counting.latticeBox (fun j => L*p (D.S.x0Slot i) j) (4*L)
  · exact (Counting.latticeBox (fun j => L*p (D.S.xSlot a.1 a.2) j) (4*L)).product
      (Counting.latticeBox (fun j => L*p (D.S.ySlot a.1 a.2) j) (4*L))
  · exact inputCutoffBox L (fun j => p (D.S.uSlot i.1 i.2 j))

/-- Every factor summand is zero outside its fixed finite input box. -/
theorem sourceFactorTerm_eq_zero_of_not_support {d : ℕ} (D : SumintDatum d)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (p : D.S.VIdx → Fin d → ℝ)
    (ν : D.S.VIdx → Mom d) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ)
    (a : FactorIdx D.S) (n : FactorInput D.S (Fin d → ℤ) a)
    (hn : n ∉ sourceFactorSupport D L p a) : sourceFactorTerm D L γ δ p ν r t τ a n = 0 := by
  classical
  rcases a with i | (a | i)
  · change n ∉ Counting.latticeBox (fun j => L*p (D.S.x0Slot i) j) (4*L) at hn
    have hz : inputCutoff (p (D.S.x0Slot i)) (latticePoint L n) = 0 := by
      by_contra hh
      exact hn (inputCutoff_mem_integerBox hL _ n hh)
    change linearFactorTerm D L γ δ p ν r t τ i n = 0
    unfold linearFactorTerm
    rw [hz,Complex.ofReal_zero,zero_mul]
  · rcases n with ⟨nx,ny⟩
    change (nx,ny) ∉ (Counting.latticeBox (fun j => L*p (D.S.xSlot a.1 a.2) j) (4*L)).product
      (Counting.latticeBox (fun j => L*p (D.S.ySlot a.1 a.2) j) (4*L)) at hn
    have hz : inputCutoff (p (D.S.xSlot a.1 a.2)) (latticePoint L nx)*
        inputCutoff (p (D.S.ySlot a.1 a.2)) (latticePoint L ny) = 0 := by
      by_contra hh
      exact hn (Finset.mem_product.mpr
        ⟨inputCutoff_mem_integerBox hL _ nx (left_ne_zero_of_mul hh),
          inputCutoff_mem_integerBox hL _ ny (right_ne_zero_of_mul hh)⟩)
    change pairFactorTerm D L γ δ p ν r t τ a (nx,ny) = 0
    change (((inputCutoff (p (D.S.xSlot a.1 a.2)) (latticePoint L nx)*
      inputCutoff (p (D.S.ySlot a.1 a.2)) (latticePoint L ny) : ℝ) : ℂ) * _) = 0
    exact mul_eq_zero_of_left (by exact_mod_cast hz) _
  · change Fin 3 → Fin d → ℤ at n
    change n ∉ inputCutoffBox L (fun j => p (D.S.uSlot i.1 i.2 j)) at hn
    have hz := inputCutoff_product_eq_zero hL (fun j => p (D.S.uSlot i.1 i.2 j)) n hn
    change normalFactorTerm D L γ δ p ν r t τ i n = 0
    change (((∏ j : Fin 3, inputCutoff (p (D.S.uSlot i.1 i.2 j))
      (latticePoint L (n j)) : ℝ) : ℂ) * _) = 0
    exact mul_eq_zero_of_left (by exact_mod_cast hz) _

end WaveTurbulence.SumintPar
