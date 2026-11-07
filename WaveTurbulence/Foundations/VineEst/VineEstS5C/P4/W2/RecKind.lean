/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecOrd
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcDisp3

/-! # P4-W2 (session 17): `recKind`, the engine kind of a summand, and kind-0 summands under equal slot values -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS4c
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 MeasureTheory
open scoped ENNReal

/-- The kind used for the engine: `3` for a remainder summand, `kindOf` otherwise. -/
def recKind {β : Type*} {d : ℕ} {S : SepTerms β d} {bs₁ bs₂ rA rB : Finset β} (c : Ch S bs₁ bs₂ rA rB) : ℕ :=
  Sum.elim (fun pc => kindOf (S := S) (bs₁ := bs₁) (bs₂ := bs₂) (rA := rA) (rB := rB) (Sum.inl pc)) (fun _ => 3) c

section RK
variable {β : Type*} {d : ℕ} {S : SepTerms β d} {bs₁ bs₂ rA rB : Finset β} (c : Ch S bs₁ bs₂ rA rB)

theorem recKind_eq_one_iff : recKind c = 1 ↔ kindOf c = 1 := by
  rcases c with pc | z <;> simp [recKind, kindOf]

theorem recKind_ne_two_iff : recKind c ≠ 2 ↔ kindOf c ≠ 2 := by
  rcases c with pc | z <;> simp [recKind, kindOf]

theorem recKind_le_three : recKind c ≤ 3 := by
  rcases c with pc | z
  · simp only [recKind, kindOf, Sum.elim_inl]
    rcases pc with _ | _ | _ | _ | _ | _ <;> simp
  · simp [recKind]
end RK

section KD0
variable {β : Type*} {d : ℕ} {S : SepTerms β d} {bs₁ bs₂ rA rB : Finset β}

open Classical in
/-- A kind-0 summand needs `s₁ ≤ t₀ < t₁` or `t₁ ≤ t₀ < s₁`, impossible when the two slot values agree. -/
theorem not_excOrd_of_kd0 (caseA : Prop) (c : Ch S bs₁ bs₂ rA rB) (h : recKind c = 0) (t0 s : ℝ) :
    ¬ ExcOrd caseA t0 s s c := by
  rcases c with (c | c | c | c | c | c) | c
  · by_cases hc : caseA <;> simp [ExcOrd, hc] <;> intro h1 h2 <;> linarith
  all_goals first
    | (exfalso; simp [recKind, kindOf] at h; done)
    | skip
  · by_cases hc : caseA <;> simp [ExcOrd, hc] <;> intro h1 h2 <;> linarith
  all_goals first
    | (exfalso; simp [recKind, kindOf] at h; done)
    | skip
end KD0


end WaveTurbulence.VineEstS5C.P4.W2
