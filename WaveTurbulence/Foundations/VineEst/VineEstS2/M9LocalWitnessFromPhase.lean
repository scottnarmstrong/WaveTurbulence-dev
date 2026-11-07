/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.M9PrimitiveFactorWitness
public import WaveTurbulence.Foundations.VineEst.LocalDifferenceProposal

/-! # A primitive pure phase proves the local coordinate witness -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract
variable {V D : Type} [DecidableEq V] [Fintype D] {M : Molecule V D}
variable {X : VineType} {S : Finset V} {a b : V}

def ChartLocalWitness (A : FullVineChart M X S a b) (i : Fin A.indexing.shape.n) : Prop :=
  ∃ p q : Bond M S ⊕ Fin 2,
    (∃ v ∈ S, ∃ out : Bool, OriginAt M S b p v out ∧ OriginAt M S b q v (!out)) ∧
    ∀ {E : Type} [AddCommGroup E] (g r : E) (k : FlowFiber M S a b E r),
      A.chart g r k i = origin M S k.1 g r p-origin M S k.1 g r q

/-- Conditional algebra helper; the geometric premises name actual
incidences and the coefficient premise comes from primitive factorization. -/
theorem chart_local_witness_of_coeff (A : FullVineChart M X S a b)
    (p q : Bond M S ⊕ Fin 2) (i : Fin A.indexing.shape.n) (v : V) (hv : v ∈ S) (out : Bool)
    (hp : OriginAt M S b p v out) (hq : OriginAt M S b q v (!out))
    (hs : chartDifferenceCoeff A p q (.inl i) = 1 ∨ chartDifferenceCoeff A p q (.inl i) = -1)
    (hc : ∀ j, chartDifferenceCoeff A p q j =
      chartDifferenceCoeff A p q (.inl i)*(if j = .inl i then 1 else 0)) : ChartLocalWitness A i := by
  rcases chart_difference_witness_of_coeff A p q i hs hc with h | h
  · exact ⟨p,q,⟨v,hv,out,hp,hq⟩,h⟩
  · exact ⟨q,p,⟨v,hv,!out,hq,by simpa only [Bool.not_not] using hp⟩,h⟩

/-- The uniform pure phase identity supplies the local witness itself;
no assumption about a garden inverse matrix is introduced. -/
theorem chart_local_witness_of_primitive_phase (A : FullVineChart M X S a b)
    (p q s t : Bond M S ⊕ Fin 2) (i : Fin A.indexing.shape.n)
    (v : V) (hv : v ∈ S) (out₁ out₂ : Bool)
    (hp : OriginAt M S b p v out₁) (hq : OriginAt M S b q v (!out₁))
    (hs : OriginAt M S b s v out₂) (ht : OriginAt M S b t v (!out₂))
    (c : ChartAffineIndex A → ℤ) (j : ChartAffineIndex A) (hji : j ≠ .inl i)
    (hc : c j = 1 ∨ c j = -1)
    (hprod : ∀ x : ChartAffineIndex A → ℤ,
      integerLinearForm (chartDifferenceCoeff A p q) x *
        integerLinearForm (chartDifferenceCoeff A s t) x = x (.inl i)*integerLinearForm c x) :
    ChartLocalWitness A i := by
  rcases integer_primitive_phase_factor _ _ c (.inl i) j hji hc hprod with ⟨hsgn,hrow⟩ | ⟨hsgn,hrow⟩
  · exact chart_local_witness_of_coeff A p q i v hv out₁ hp hq hsgn hrow
  · exact chart_local_witness_of_coeff A s t i v hv out₂ hs ht hsgn hrow

end WaveTurbulence.VineEstS2
