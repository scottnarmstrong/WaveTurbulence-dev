/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceCoreCoordinates

/-!
# Fiber properties of the actual source core grouping

Pair factors remain injectively labelled after coarsening: the only
collapsed pair in any block is its unique first bad pair. Normal
triples map injectively to their distinguished linear labels. A pair
and a normal triple never share a core, since their block flags differ.
-/

public section

open scoped Classical

namespace WaveTurbulence.Sumint

/-- A special pair has the literal first pair index and a non-normal block flag. -/
theorem special_pair_first_and_bad {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : caseAPair D a ∨ caseCPair D a) :
    D.S.nor a.1 = false ∧ (a.2:ℕ) = 0 := by
  rcases ha with ha | ha <;> exact ⟨ha.1,ha.2.2⟩

/-- Distinct pair factors remain distinct under the actual source core grouping. -/
theorem sourceCoreGroup_pair_injective {d : ℕ} (D : SumintDatum d) :
    Function.Injective (fun a : Σ i : Fin D.S.I, Fin (D.S.m i) => sourceCoreGroup D (.inr (.inl a))) := by
  intro a b h
  by_cases ha : caseAPair D a ∨ caseCPair D a
  · by_cases hb : caseAPair D b ∨ caseCPair D b
    · simp only [sourceCoreGroup,ite_eq_left ha,ite_eq_left hb] at h
      have hi := Sum.inl.inj h
      have hja := (special_pair_first_and_bad D a ha).2
      have hjb := (special_pair_first_and_bad D b hb).2
      rcases a with ⟨i,j⟩
      rcases b with ⟨k,l⟩
      change i = k at hi
      cases hi
      exact congrArg (Sigma.mk i) (Fin.ext (hja.trans hjb.symm))
    · simp only [sourceCoreGroup,ite_eq_left ha,ite_eq_right hb] at h
      cases h
  · by_cases hb : caseAPair D b ∨ caseCPair D b
    · simp only [sourceCoreGroup,ite_eq_right ha,ite_eq_left hb] at h
      cases h
    · simp only [sourceCoreGroup,ite_eq_right ha,ite_eq_right hb] at h
      exact Sum.inl.inj (Sum.inr.inj h)

/-- Distinct normal triples remain distinct after grouping with their linear factors. -/
theorem sourceCoreGroup_normal_injective {d : ℕ} (D : SumintDatum d) :
    Function.Injective (fun i : {i : Fin D.S.I // D.S.nor i = true} => sourceCoreGroup D (.inr (.inr i))) := by
  intro i j h
  exact Subtype.ext (Sum.inl.inj h)

/-- A pair and a normal triple can never belong to the same coarse source core. -/
theorem sourceCoreGroup_pair_ne_normal {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (i : {i : Fin D.S.I // D.S.nor i = true}) :
    sourceCoreGroup D (.inr (.inl a)) ≠ sourceCoreGroup D (.inr (.inr i)) := by
  intro h
  by_cases ha : caseAPair D a ∨ caseCPair D a
  · simp only [sourceCoreGroup,ite_eq_left ha] at h
    have hi := Sum.inl.inj h
    have hf := (special_pair_first_and_bad D a ha).1
    have ht : D.S.nor a.1 = true := by rw [hi]; exact i.2
    rw [hf] at ht
    cases ht
  · simp only [sourceCoreGroup,ite_eq_right ha] at h
    cases h

end WaveTurbulence.Sumint
