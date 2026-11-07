/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.FiberBigOperators
public import WaveTurbulence.Foundations.SumintPar.SourceCoreGroupProperties

/-!
# Concrete products over the source core fibers

Normal cores contain precisely their distinguished linear factor and
normal triple. A pair core contains only its own pair when it is not
collapsed into a first bad core.
-/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators Classical
namespace WaveTurbulence.SumintPar

/-- The normal coarse fiber contains exactly the original linear and normal factors. -/
theorem prod_sourceCore_normal_fiber {d : ℕ} (D : SumintDatum d) {M : Type*} [CommMonoid M]
    (i : {i : Fin D.S.I // D.S.nor i = true})
    [Fintype {a : FactorIdx D.S // sourceCoreGroup D a = .inl i.1}]
    (f : FactorIdx D.S → M) :
    (∏ a : {a : FactorIdx D.S // sourceCoreGroup D a = .inl i.1}, f a.1) =
      f (.inl i.1)*f (.inr (.inr i)) := by
  rw [prod_fiber_subtype_eq_ite,Fintype.prod_sum_type,Fintype.prod_sum_type]
  have hp (a : Σ j : Fin D.S.I, Fin (D.S.m j)) :
      sourceCoreGroup D (.inr (.inl a)) ≠ .inl i.1 := sourceCoreGroup_pair_ne_normal D a i
  have hn (j : {i : Fin D.S.I // D.S.nor i = true}) :
      sourceCoreGroup D (.inr (.inr j)) = .inl i.1 ↔ j = i := by
    constructor
    · intro h
      exact Subtype.ext (Sum.inl.inj h)
    · rintro rfl
      rfl
  simp_rw [ite_eq_right (hp _),hn]
  simp [sourceCoreGroup]

/-- A noncollapsed pair coarse fiber contains exactly its original pair factor. -/
theorem prod_sourceCore_pair_fiber {d : ℕ} (D : SumintDatum d) {M : Type*} [CommMonoid M]
    (a : Σ j : Fin D.S.I, Fin (D.S.m j)) (ha : ¬ (caseAPair D a ∨ caseCPair D a))
    [Fintype {b : FactorIdx D.S // sourceCoreGroup D b = .inr (.inl a)}]
    (f : FactorIdx D.S → M) :
    (∏ b : {b : FactorIdx D.S // sourceCoreGroup D b = .inr (.inl a)}, f b.1) = f (.inr (.inl a)) := by
  have he (b : FactorIdx D.S) : sourceCoreGroup D b = .inr (.inl a) ↔ b = .inr (.inl a) := by
    rcases b with i | (b | i)
    · simp only [sourceCoreGroup,Sum.inl_ne_inr]
    · have hga : sourceCoreGroup D (.inr (.inl a)) = .inr (.inl a) := by simp only [sourceCoreGroup,ite_eq_right ha]
      constructor
      · intro h
        exact congrArg (fun b => Sum.inr (Sum.inl b)) (sourceCoreGroup_pair_injective D (h.trans hga.symm))
      · intro h
        simpa only [h] using hga
    · simp only [sourceCoreGroup,Sum.inl_ne_inr,Sum.inr.injEq,Sum.inr_ne_inl]
  rw [prod_fiber_subtype_eq_ite]
  simp only [he]
  simp

end WaveTurbulence.SumintPar
