/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriSib3
/-! **FINALCOUNT-ASSEMBLY, phase 2: the triangle class bridge.**  G3's `triCls` decides `α`/`β` of `f₀, f₁` by components of
`T.kept` (DH23 L1777), whereas G2's `excessprop1` bound is stated with `T.IsA0`, `T.IsA1` (the cuts of `t₀`, `t₁` are `α` cuts).  Here:
`IsA1 ↔ kept.SC f₁ f₂` and `IsA0 ↔ kept.SC f₀ f₂ ∨ kept.SC f₀ f₁`, purely graph-theoretically (no classes). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} (T : TriData M)

private theorem kept_sc_m3 {u w : V} (h : T.kept.SameComponent u w) : T.m3.SameComponent u w := by
  induction h with
  | rel a b hab =>
    obtain ⟨x, hx1, hx2⟩ := hab
    exact Relation.EqvGen.rel _ _ ⟨x.1, hx1, hx2⟩
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

private theorem not_sc_t_m3 {x : V} (hx : T.TP x) (j : Fin 3) : ¬ T.m3.SameComponent x (T.t j) := by
  intro h
  have := (PClosed.sc_iff T.m3 T.TP T.pclosed h).1 hx
  exact this j rfl

private theorem sc_t_m3 (i j : Fin 3) : T.m3.SameComponent (T.t i) (T.t j) :=
  T.sc_t T.m3 (fun _ => rfl) (fun x j h => T.m3_atom_tri x j h) i j

private theorem m3_sc_kept {u w : V} (hu : T.TP u) (h : T.m3.SameComponent u w) : T.kept.SameComponent u w :=
  restrictP_sc_of T.m3 T.TP T.pclosed h hu

/-- `IsA1 ↔ f₁ ~ f₂` in `kept`. -/
theorem isA1_iff : T.IsA1 ↔ T.kept.SameComponent (T.f 1) (T.f 2) := by
  have h12 : T.f 1 ≠ T.f 2 := T.f_ne (by decide)
  have hP1 : T.TP (T.f 1) := T.TP_f 1
  have hP2 : T.TP (T.f 2) := T.TP_f 2
  unfold TriData.IsA1
  rw [isAlphaCut_iff T.m1 T.cd2]
  change T.m2.SameComponent (T.t 1) (T.f 1) ↔ _
  constructor
  · intro h
    have h' : T.m2.SameComponent (T.f 1) (T.t 1) := Relation.EqvGen.symm _ _ h
    rcases sc_glue T.m2 T.cd3 h' with h1 | ⟨h1, -⟩
    · exact absurd h1 (not_sc_t_m3 T hP1 1)
    · rcases h1 with h1 | h1
      · exact absurd h1 (not_sc_t_m3 T hP1 2)
      · exact m3_sc_kept T hP1 h1
  · intro h
    have h3 := kept_sc_m3 T h
    have := cutSC_pi T.m2 T.cd3 h3
    have e1 : piV (T.t 2) (T.f 2) (T.f 1) = T.f 1 := by simp [piV, h12]
    have e2 : piV (T.t 2) (T.f 2) (T.f 2) = T.t 2 := by simp [piV]
    rw [e1, e2] at this
    exact Relation.EqvGen.trans _ _ _ (T.sc_t_m2 1 2) (Relation.EqvGen.symm _ _ this)

/-- From a `m2` connection of `x ∈ TP` to the triangle or to `f₁`-free data: `x ~ t₂` in `m2` gives `x ~ f₂` in `kept`. -/
private theorem m2_t2_to_f2 {x : V} (hx : T.TP x) (h : T.m2.SameComponent x (T.t 2)) :
    T.kept.SameComponent x (T.f 2) := by
  rcases sc_glue T.m2 T.cd3 h with h1 | ⟨h1, -⟩
  · exact absurd h1 (not_sc_t_m3 T hx 2)
  · rcases h1 with h1 | h1
    · exact absurd h1 (not_sc_t_m3 T hx 2)
    · exact m3_sc_kept T hx h1

private theorem m2_f1_to_kept {x : V} (hx : T.TP x) (h : T.m2.SameComponent x (T.f 1)) :
    T.kept.SameComponent x (T.f 2) ∨ T.kept.SameComponent x (T.f 1) := by
  rcases sc_glue T.m2 T.cd3 h with h1 | ⟨h1, -⟩
  · exact Or.inr (m3_sc_kept T hx h1)
  · rcases h1 with h1 | h1
    · exact absurd h1 (not_sc_t_m3 T hx 2)
    · exact Or.inl (m3_sc_kept T hx h1)

/-- `IsA0 ↔ f₀ ~ f₂ ∨ f₀ ~ f₁` in `kept`. -/
theorem isA0_iff : T.IsA0 ↔ T.kept.SameComponent (T.f 0) (T.f 2) ∨ T.kept.SameComponent (T.f 0) (T.f 1) := by
  have h01 : T.f 0 ≠ T.f 1 := T.f_ne (by decide)
  have h02 : T.f 0 ≠ T.f 2 := T.f_ne (by decide)
  have hP0 : T.TP (T.f 0) := T.TP_f 0
  unfold TriData.IsA0
  rw [isAlphaCut_iff M T.cd1]
  change T.m1.SameComponent (T.t 0) (T.f 0) ↔ _
  constructor
  · intro h
    have h' : T.m1.SameComponent (T.f 0) (T.t 0) := Relation.EqvGen.symm _ _ h
    rcases sc_glue T.m1 T.cd2 h' with h1 | ⟨h1, -⟩
    · -- `m2.SC f0 t0`
      exact Or.inl (m2_t2_to_f2 T hP0 (Relation.EqvGen.trans _ _ _ h1 (T.sc_t_m2 0 2)))
    · rcases h1 with h1 | h1
      · exact Or.inl (m2_t2_to_f2 T hP0 (Relation.EqvGen.trans _ _ _ h1 (T.sc_t_m2 1 2)))
      · exact m2_f1_to_kept T hP0 h1
  · intro h
    rcases h with h | h
    · have h3 := kept_sc_m3 T h
      have h2 := cutSC_pi T.m2 T.cd3 h3
      have e1 : piV (T.t 2) (T.f 2) (T.f 0) = T.f 0 := by simp [piV, h02]
      have e2 : piV (T.t 2) (T.f 2) (T.f 2) = T.t 2 := by simp [piV]
      rw [e1, e2] at h2
      have h1 := cutSC_pi T.m1 T.cd2 h2
      have e3 : piV (T.t 1) (T.f 1) (T.f 0) = T.f 0 := by simp [piV, h01]
      have e4 : piV (T.t 1) (T.f 1) (T.t 2) = T.t 2 := by
        simp only [piV]; rw [if_neg]; intro e; exact T.f_ne_t 1 2 e.symm
      rw [e3, e4] at h1
      exact Relation.EqvGen.trans _ _ _ (T.sc_t_m1 0 2) (Relation.EqvGen.symm _ _ h1)
    · have h3 := kept_sc_m3 T h
      have h2 := cutSC_pi T.m2 T.cd3 h3
      have e1 : piV (T.t 2) (T.f 2) (T.f 0) = T.f 0 := by simp [piV, h02]
      have e2 : piV (T.t 2) (T.f 2) (T.f 1) = T.f 1 := by simp [piV, T.f_ne (show (1 : Fin 3) ≠ 2 by decide)]
      rw [e1, e2] at h2
      have h1 := cutSC_pi T.m1 T.cd2 h2
      have e3 : piV (T.t 1) (T.f 1) (T.f 0) = T.f 0 := by simp [piV, h01]
      have e4 : piV (T.t 1) (T.f 1) (T.f 1) = T.t 1 := by simp [piV]
      rw [e3, e4] at h1
      exact Relation.EqvGen.trans _ _ _ (T.sc_t_m1 0 1) (Relation.EqvGen.symm _ _ h1)

end WaveTurbulence.FinalCountG3
