/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceCoreFiberProducts
public import WaveTurbulence.Foundations.SumintPar.SourceCoreArity
public import WaveTurbulence.Foundations.SumintPar.TripleTimeBox

/-!
# The three native coordinates of a first bad source core

The coordinate order is pair outer, pair inner, distinguished linear.
It matches the established outer-third-time Fubini formula, so the
case-(a) middle-time strip can be retained during pair integration.
-/

@[expose] public section
set_option autoImplicit false
open scoped Classical BigOperators
namespace WaveTurbulence.SumintPar

/-- A first bad coarse fiber consists exactly of its distinguished linear factor and its unique first pair. -/
theorem sourceCoreGroup_eq_special_iff {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a)
    (b : FactorIdx D.S) :
    sourceCoreGroup D b = .inl a.1 ↔ b = .inl a.1 ∨ b = .inr (.inl a) := by
  have hga : sourceCoreGroup D (.inr (.inl a)) = .inl a.1 := by simp only [sourceCoreGroup,ite_eq_left ha]
  rcases b with i | (b | i)
  · simp only [sourceCoreGroup,Sum.inl.injEq,Sum.inl_ne_inr,or_false]
  · constructor
    · intro h
      exact Or.inr (congrArg (fun b => Sum.inr (Sum.inl b))
        (sourceCoreGroup_pair_injective D (h.trans hga.symm)))
    · rintro (h | h)
      · cases h
      · simpa only [h] using hga
  · constructor
    · intro h
      exact False.elim (sourceCoreGroup_pair_ne_normal D a i (hga.trans h.symm))
    · rintro (h | h) <;> cases h

/-- The first bad core raw product has precisely its linear and first pair factors. -/
theorem prod_sourceCore_special_fiber {d : ℕ} (D : SumintDatum d) {M : Type*} [CommMonoid M]
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a)
    [Fintype {b : FactorIdx D.S // sourceCoreGroup D b = .inl a.1}]
    (f : FactorIdx D.S → M) :
    (∏ b : {b : FactorIdx D.S // sourceCoreGroup D b = .inl a.1}, f b.1) =
      f (.inl a.1)*f (.inr (.inl a)) := by
  rw [prod_fiber_subtype_eq_ite,Fintype.prod_sum_type,Fintype.prod_sum_type]
  have hga : sourceCoreGroup D (.inr (.inl a)) = .inl a.1 := by simp only [sourceCoreGroup,ite_eq_left ha]
  have hp (b : Σ i : Fin D.S.I, Fin (D.S.m i)) :
      sourceCoreGroup D (.inr (.inl b)) = .inl a.1 ↔ b = a := by
    constructor
    · intro h
      exact sourceCoreGroup_pair_injective D (h.trans hga.symm)
    · rintro rfl
      exact hga
  have hn (i : {i : Fin D.S.I // D.S.nor i = true}) : sourceCoreGroup D (.inr (.inr i)) ≠ .inl a.1 :=
    fun h => sourceCoreGroup_pair_ne_normal D a i (hga.trans h.symm)
  simp_rw [ite_eq_right (hn _),hp]
  simp [sourceCoreGroup]

/-- The literal three source coordinates in pair-outer, pair-inner, linear order. -/
@[expose] noncomputable def sourceSpecialCoordinate {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a) :
    Fin 3 → SourceCoreCoordinate D (.inl a.1) :=
  ![⟨⟨.inr (.inl a),by simp only [sourceCoreGroup,ite_eq_left ha]⟩,0⟩,
    ⟨⟨.inr (.inl a),by simp only [sourceCoreGroup,ite_eq_left ha]⟩,1⟩,
    ⟨⟨.inl a.1,rfl⟩,0⟩]

/-- Every coordinate in a first bad core is one of the literal three native times. -/
theorem sourceSpecialCoordinate_surjective {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a) :
    Function.Surjective (sourceSpecialCoordinate D a ha) := by
  rintro ⟨⟨b,hb⟩,j⟩
  rcases (sourceCoreGroup_eq_special_iff D a ha b).mp hb with h | h
  · subst b
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact ⟨2,rfl⟩
  · subst b
    fin_cases j
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩

/-- The literal three special coordinates are distinct. -/
theorem sourceSpecialCoordinate_injective {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a) :
    Function.Injective (sourceSpecialCoordinate D a ha) := by
  intro j k h
  have hc := congrArg (sourceCoreCoordinateCode D (.inl a.1)) h
  have hcodes (j : Fin 3) : sourceCoreCoordinateCode D (.inl a.1) (sourceSpecialCoordinate D a ha j) =
      (![1,2,0] : Fin 3 → Fin 4) j := by
    fin_cases j <;> rfl
  rw [hcodes,hcodes] at hc
  fin_cases j <;> fin_cases k
  all_goals first | rfl | norm_num at hc

end WaveTurbulence.SumintPar
