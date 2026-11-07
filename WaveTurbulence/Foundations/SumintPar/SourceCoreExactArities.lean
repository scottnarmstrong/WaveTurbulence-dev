/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceCoreBareLinear
public import WaveTurbulence.Foundations.SumintPar.SourceSpecialCoreGrouping

/-!
# Exact arities of the nonempty source core classes

The four-, three-, two-, and one-input powers in the analytic estimates
are exactly the native coordinate counts of their respective cores.
-/

@[expose] public section
set_option autoImplicit false
open scoped Classical
namespace WaveTurbulence.SumintPar

/-- A normal core has exactly its distinguished input and its three normal inputs. -/
theorem sourceCoreArity_normal {d : ℕ} (D : SumintDatum d)
    (i : {i : Fin D.S.I // D.S.nor i = true}) : sourceCoreArity D (.inl i.1) = 4 := by
  have he := prod_sourceCore_normal_fiber D i (fun a => Multiplicative.ofAdd (factorArity D.S a))
  have hh := congrArg Multiplicative.toAdd he
  simpa only [toAdd_prod,toAdd_ofAdd,toAdd_mul,
    ← sum_factorArity_sourceCore,factorArity] using hh

/-- A first bad core has exactly the three original scalar time coordinates. -/
theorem sourceCoreArity_special {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a) :
    sourceCoreArity D (.inl a.1) = 3 := by
  have he := Fintype.card_congr (sourceSpecialCoordinateEquiv D a ha)
  simpa only [Fintype.card_fin,sourceCoreArity] using he.symm

/-- An ordinary pair core has exactly its original two inputs. -/
theorem sourceCoreArity_pair {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : ¬ (caseAPair D a ∨ caseCPair D a)) :
    sourceCoreArity D (.inr (.inl a)) = 2 := by
  have he := prod_sourceCore_pair_fiber D a ha (fun a => Multiplicative.ofAdd (factorArity D.S a))
  have hh := congrArg Multiplicative.toAdd he
  simpa only [toAdd_prod,toAdd_ofAdd,← sum_factorArity_sourceCore,factorArity] using hh

/-- A bare linear core has exactly its original distinguished input. -/
theorem sourceCoreArity_bare_linear {d : ℕ} (D : SumintDatum d) (i : Fin D.S.I)
    (hnor : D.S.nor i = false)
    (hpair : ∀ a : Σ j : Fin D.S.I, Fin (D.S.m j), a.1 = i → ¬ (caseAPair D a ∨ caseCPair D a)) :
    sourceCoreArity D (.inl i) = 1 := by
  have he := prod_sourceCore_bare_linear_fiber D i hnor hpair (fun a => Multiplicative.ofAdd (factorArity D.S a))
  have hh := congrArg Multiplicative.toAdd he
  simpa only [toAdd_prod,toAdd_ofAdd,← sum_factorArity_sourceCore,factorArity] using hh

end WaveTurbulence.SumintPar
