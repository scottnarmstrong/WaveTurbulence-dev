/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.EnlargedTimeBox
public import WaveTurbulence.Foundations.Sumint.TimeGaps

/-!
# The actual source restrictions behind bad and incoherent gains

The inequalities here are extracted directly from the admissible datum
and the exact enlarged/static domains. They supply the ordering strips
and endpoint strips used in the oscillatory integral estimates.
-/

public section

open Set

namespace WaveTurbulence.Sumint

/-- The source case-(a) order constraints force the first pair into the middle-time strip. -/
theorem source_case_a_strip {d : ℕ} (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hD : D.Admissible A L γ η Dsteps)
    (i : Fin D.S.I) (hi : D.S.nor i = false) (hk : D.badKind i = 0)
    (u : D.S.TVar → ℝ) (hu : u ∈ staticTimeDomain D) :
    ∃ hm : 0 < D.S.m i,
      |u (.inl ⟨i,⟨1,by omega⟩⟩)-u (.inl ⟨i,0⟩)| ≤
        |u (.inl ⟨i,⟨1,by omega⟩⟩)-u (.inr (.inl ⟨i,⟨0,hm⟩⟩))| := by
  obtain ⟨hm,horder⟩ := (hD.2.2.2.2.2.2.2.2.2 i hi).1 hk
  refine ⟨hm,abs_sub_middle_le ?_⟩
  rcases horder with h | h
  · exact Or.inl ⟨hu.2 _ h.1,hu.2 _ h.2⟩
  · exact Or.inr ⟨hu.2 _ h.1,hu.2 _ h.2⟩

/-- A source pair counted in M₀ lies in an endpoint strip after enlargement. -/
theorem source_pair_incoherence_strip {d : ℕ} (D : SumintDatum d)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i))
    (hq : D.q (.inl ⟨a.1,a.2.succ⟩) ≠ D.q (.inr (.inl a)))
    {c h : ℝ} (hh : 0 ≤ h) (u : D.S.TVar → ℝ)
    (hu : u ∈ enlargedInputTimeBox D c h) :
    ∃ e : ℝ,
      (e = (D.q (.inl ⟨a.1,a.2.succ⟩):ℝ)-c ∨
        e = (D.q (.inl ⟨a.1,a.2.succ⟩):ℝ)+1-c) ∧
      |u (.inl ⟨a.1,a.2.succ⟩)-e| ≤
        2*h+|u (.inl ⟨a.1,a.2.succ⟩)-u (.inr (.inl a))| :=
  enlarged_unit_gap_endpoint hq hh ⟨hu.1 _,hu.2 _⟩ ⟨hu.1 _,hu.2 _⟩

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

/-- Any discrepant normal label gives an endpoint strip for its first or second time. -/
theorem source_normal_incoherence_strip {d : ℕ} (D : SumintDatum d)
    (i : {i : Fin D.S.I // D.S.nor i = true}) (j : Fin 3)
    (hq : D.q (.inr (.inr ⟨i,j⟩)) ≠ D.q (.inr (.inr ⟨i,2⟩)))
    {c h : ℝ} (hh : 0 ≤ h) (u : D.S.TVar → ℝ)
    (hu : u ∈ enlargedInputTimeBox D c h) :
    ∃ e : ℝ,
      (e = (D.q (.inr (.inr ⟨i,j⟩)):ℝ)-c ∨
        e = (D.q (.inr (.inr ⟨i,j⟩)):ℝ)+1-c) ∧
      |u (.inr (.inr ⟨i,j⟩))-e| ≤
        2*h+|u (.inr (.inr ⟨i,j⟩))-u (.inr (.inr ⟨i,2⟩))| :=
  enlarged_unit_gap_endpoint hq hh ⟨hu.1 _,hu.2 _⟩ ⟨hu.1 _,hu.2 _⟩

/-- The normal strip can be placed on the third time, which fixes all spatial modulations. -/
theorem source_normal_outer_incoherence_strip {d : ℕ} (D : SumintDatum d)
    (i : {i : Fin D.S.I // D.S.nor i = true}) (j : Fin 3)
    (hq : D.q (.inr (.inr ⟨i,j⟩)) ≠ D.q (.inr (.inr ⟨i,2⟩)))
    {c h : ℝ} (hh : 0 ≤ h) (u : D.S.TVar → ℝ)
    (hu : u ∈ enlargedInputTimeBox D c h) :
    ∃ e : ℝ,
      (e = (D.q (.inr (.inr ⟨i,2⟩)):ℝ)-c ∨
        e = (D.q (.inr (.inr ⟨i,2⟩)):ℝ)+1-c) ∧
      |u (.inr (.inr ⟨i,2⟩))-e| ≤
        2*h+|u (.inr (.inr ⟨i,2⟩))-u (.inr (.inr ⟨i,j⟩))| :=
  enlarged_unit_gap_endpoint hq.symm hh ⟨hu.1 _,hu.2 _⟩ ⟨hu.1 _,hu.2 _⟩

end WaveTurbulence.Sumint
