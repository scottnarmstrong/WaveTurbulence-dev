/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.BilinearTensor

/-! # Exact coordinate factorization of the two cubic lattice sums -/

public section
open Finset
open scoped BigOperators
namespace WaveTurbulence.WeylSums

/-- Reorder three integer vectors as a vector of integer triples. -/
@[expose] def tripleArrowEquiv (d : ℕ) : (Fin d → ℤ × ℤ × ℤ) ≃
    (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) where
  toFun v := (fun j => (v j).1,fun j => (v j).2.1,fun j => (v j).2.2)
  invFun q j := (q.1 j,q.2.1 j,q.2.2 j)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem tripleArrowEquiv_apply (d : ℕ) (v : Fin d → ℤ × ℤ × ℤ) :
    tripleArrowEquiv d v = (fun j => (v j).1,fun j => (v j).2.1,fun j => (v j).2.2) := rfl

/-- One coordinate factor, in the exact phase convention of the draft. -/
@[expose] noncomputable def scalarCubicTerm (L t s : ℝ) (sel : Bool)
    (a b c ξ ζ ω : ℝ) (q : ℤ × ℤ × ℤ) : ℂ :=
  (Fourier.chi0 ((q.1 : ℝ)/L-a)*Fourier.chi0 ((q.2.1 : ℝ)/L-b)*
    Fourier.chi0 ((q.2.2 : ℝ)/L-c) : ℝ) *
  e (t*((q.1 : ℝ)/L)*((q.2.1 : ℝ)/L)+
    s*(if sel then ((q.1 : ℝ)/L)*((q.2.2 : ℝ)/L)
      else ((q.2.2 : ℝ)/L)*((q.1 : ℝ)/L+(q.2.1 : ℝ)/L-(q.2.2 : ℝ)/L))+
    ξ*((q.1 : ℝ)/L)+ζ*((q.2.1 : ℝ)/L)+ω*((q.2.2 : ℝ)/L))

@[expose] noncomputable def scalarCubicSum (L t s : ℝ) (sel : Bool)
    (a b c ξ ζ ω : ℝ) : ℂ := ∑' q : ℤ × ℤ × ℤ, scalarCubicTerm L t s sel a b c ξ ζ ω q

theorem finite_scalarCubicTerm {L : ℝ} (hL : 0 < L) (t s : ℝ) (sel : Bool)
    (a b c ξ ζ ω : ℝ) : (Function.support (scalarCubicTerm L t s sel a b c ξ ζ ω)).Finite := by
  refine ((finite_scalar_cutoff hL a).prod ((finite_scalar_cutoff hL b).prod (finite_scalar_cutoff hL c))).subset ?_
  intro q hq
  simp only [Function.mem_support, scalarCubicTerm, ne_eq, mul_eq_zero,
    Complex.ofReal_eq_zero, not_or] at hq
  exact ⟨hq.1.1.1,hq.1.1.2,hq.1.2⟩

/-- Both cubic phases factor exactly into scalar coordinate sums. -/
theorem cubicLatticeSum_eq_prod {d : ℕ} {L : ℝ} (hL : 0 < L)
    (t s : ℝ) (sel : Bool) (a b c ξ ζ ω : Mom d) :
    cubicLatticeSum L t s sel a b c ξ ζ ω =
      ∏ j, scalarCubicSum L t s sel (a j) (b j) (c j) (ξ j) (ζ j) (ω j) := by
  let E := tripleArrowEquiv d
  let f (j : Fin d) := scalarCubicTerm L t s sel (a j) (b j) (c j) (ξ j) (ζ j) (ω j)
  unfold cubicLatticeSum
  rw [← E.tsum_eq]
  have hterm (v : Fin d → ℤ × ℤ × ℤ) :
      ((latticeCutoff (latticePoint L (E v).1-a)*latticeCutoff (latticePoint L (E v).2.1-b)*
        latticeCutoff (latticePoint L (E v).2.2-c) : ℝ) : ℂ)*
      e (t*inner ℝ (latticePoint L (E v).1) (latticePoint L (E v).2.1)+
        s*cubicQuadraticForm sel (latticePoint L (E v).1) (latticePoint L (E v).2.1) (latticePoint L (E v).2.2)+
        inner ℝ ξ (latticePoint L (E v).1)+inner ℝ ζ (latticePoint L (E v).2.1)+
        inner ℝ ω (latticePoint L (E v).2.2)) = ∏ j, f j (v j) := by
    have hphase : t*inner ℝ (latticePoint L (E v).1) (latticePoint L (E v).2.1)+
        s*cubicQuadraticForm sel (latticePoint L (E v).1) (latticePoint L (E v).2.1) (latticePoint L (E v).2.2)+
        inner ℝ ξ (latticePoint L (E v).1)+inner ℝ ζ (latticePoint L (E v).2.1)+
        inner ℝ ω (latticePoint L (E v).2.2) =
        ∑ j, (t*(((v j).1 : ℝ)/L)*(((v j).2.1 : ℝ)/L)+
          s*(if sel then (((v j).1 : ℝ)/L)*(((v j).2.2 : ℝ)/L)
            else ((v j).2.2 : ℝ)/L*(((v j).1 : ℝ)/L+((v j).2.1 : ℝ)/L-((v j).2.2 : ℝ)/L))+
          ξ j*(((v j).1 : ℝ)/L)+ζ j*(((v j).2.1 : ℝ)/L)+ω j*(((v j).2.2 : ℝ)/L)) := by
      cases sel <;> simp only [cubicQuadraticForm, Bool.false_eq_true, ite_false, ite_true,
        PiLp.inner_apply, Real.inner_apply, latticePoint, E, tripleArrowEquiv_apply,
        PiLp.add_apply, PiLp.sub_apply, ← sum_add_distrib, mul_sum]
      all_goals
        apply sum_congr rfl
        intro j hj
        ring
    rw [hphase, e_sum]
    simp only [latticeCutoff, Complex.ofReal_mul, Complex.ofReal_prod, latticePoint,
      PiLp.sub_apply, E, tripleArrowEquiv_apply, f, scalarCubicTerm, prod_mul_distrib]
  simp_rw [hterm]
  exact tsum_pi_prod_of_finite_support f (fun j => finite_scalarCubicTerm hL t s sel _ _ _ _ _ _)

end WaveTurbulence.WeylSums
