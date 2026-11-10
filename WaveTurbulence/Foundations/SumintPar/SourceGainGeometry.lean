/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.EnlargedTimeBox
public import WaveTurbulence.Foundations.SumintPar.TimeGaps

/-!
# The actual source restrictions behind bad and incoherent gains

The inequalities here are extracted directly from the admissible datum
and the exact enlarged/static domains. They supply the ordering strips
and endpoint strips used in the oscillatory integral estimates.
-/

@[expose] public section
set_option autoImplicit false

open Set

namespace WaveTurbulence.SumintPar

/-- The source case-(a) order constraints force the first pair into the middle-time strip. -/
theorem source_case_a_strip {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (i : Fin D.S.I) (hi : D.S.nor i = false) (hk : D.badKind i = 0)
    (u : D.S.TVar → ℝ) (hu : u ∈ staticTimeDomain D) :
    ∃ hm : 0 < D.S.m i,
      |u (.inl ⟨i,⟨1,by omega⟩⟩)-u (.inl ⟨i,0⟩)| ≤
        |u (.inl ⟨i,⟨1,by omega⟩⟩)-u (.inr (.inl ⟨i,⟨0,hm⟩⟩))| := by
  obtain ⟨hm,horder⟩ := (hD.2.2.2.2.2.2.2.2.2.1 i hi).1 hk
  refine ⟨hm,abs_sub_middle_le ?_⟩
  rcases horder with h | h
  · exact Or.inl ⟨hu.2 _ h.1,hu.2 _ h.2⟩
  · exact Or.inr ⟨hu.2 _ h.1,hu.2 _ h.2⟩

/-- Every incoherent normal triple has a discrepant label relative to its third time. -/
theorem source_normal_incoherence_choice {d : ℕ} (D : SumintDatum d)
    (i : {i : Fin D.S.I // D.S.nor i = true})
    (hq : ¬ (D.q (.inr (.inr ⟨i,0⟩)) = D.q (.inr (.inr ⟨i,1⟩)) ∧
      D.q (.inr (.inr ⟨i,1⟩)) = D.q (.inr (.inr ⟨i,2⟩)))) :
    D.q (.inr (.inr ⟨i,0⟩)) ≠ D.q (.inr (.inr ⟨i,2⟩)) ∨
      D.q (.inr (.inr ⟨i,1⟩)) ≠ D.q (.inr (.inr ⟨i,2⟩)) := by
  by_contra h
  push Not at h
  exact hq ⟨h.1.trans h.2.symm,h.2⟩

end WaveTurbulence.SumintPar
