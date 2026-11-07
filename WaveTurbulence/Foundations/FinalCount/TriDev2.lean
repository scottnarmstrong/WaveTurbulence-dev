/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriDev1
/-! Triangles, part 21 (FINALCOUNT-G2): the number of components of the cut molecules and the value of `ΔF`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace TriData
variable {M : Molecule V D} (T : TriData M)

/-- The first cut is an `α`-cut. -/
def IsA0 : Prop := M.IsAlphaCut (T.t 0) (T.f 0) (T.a 0) (T.b 0)
/-- The second cut is an `α`-cut. -/
def IsA1 : Prop := T.m1.IsAlphaCut (T.t 1) (T.f 1) (T.a 1) (T.b 1)

theorem m3_not_same : ¬ T.m3.SameComponent (T.t 2) (T.f 2) := by
  intro hs
  have := (PClosed.sc_iff T.m3 T.TP T.pclosed hs).2 (T.TP_f 2)
  exact this 2 rfl

theorem numComponents_m3_kept : T.m3.numComponents = T.kept.numComponents + 1 := by
  have h := numComponents_restrictP_add T.m3 T.TP T.pclosed
  change T.kept.numComponents + T.tcomp.numComponents = T.m3.numComponents at h
  rw [T.tcomp_numComponents] at h
  exact h.symm

theorem numComponents_m1 : (T.m1.numComponents : ℤ) = M.numComponents + (if T.IsA0 then 0 else 1) := by
  by_cases h : T.IsA0
  · rw [if_pos h]
    have := numComponents_cut_of_same M T.cd1 ((isAlphaCut_iff M T.cd1).1 h)
    change (T.m1.numComponents : ℤ) = _
    simp [m1, this]
  · rw [if_neg h]
    have := numComponents_cut_of_not_same M T.cd1 (fun hs => h ((isAlphaCut_iff M T.cd1).2 hs))
    change (T.m1.numComponents : ℤ) = _
    simp [m1, this]

theorem numComponents_m2 : (T.m2.numComponents : ℤ) = T.m1.numComponents + (if T.IsA1 then 0 else 1) := by
  by_cases h : T.IsA1
  · rw [if_pos h]
    have := numComponents_cut_of_same T.m1 T.cd2 ((isAlphaCut_iff T.m1 T.cd2).1 h)
    simp [m2, this]
  · rw [if_neg h]
    have := numComponents_cut_of_not_same T.m1 T.cd2 (fun hs => h ((isAlphaCut_iff T.m1 T.cd2).2 hs))
    simp [m2, this]

theorem numComponents_m3 : (T.m3.numComponents : ℤ) = T.m2.numComponents + 1 := by
  have := numComponents_cut_of_not_same T.m2 T.cd3 T.m3_not_same
  simp [m3, this]

/-- **`ΔF`** (DH23 L1793): the number of new components, `[β₁] + [β₂]`. -/
theorem deltaF_eq : ((T.kept.numComponents : ℤ) - M.numComponents) =
    (if T.IsA0 then 0 else 1) + (if T.IsA1 then 0 else 1) := by
  have h1 := T.numComponents_m1
  have h2 := T.numComponents_m2
  have h3 := T.numComponents_m3
  have h4 : (T.m3.numComponents : ℤ) = T.kept.numComponents + 1 := by exact_mod_cast T.numComponents_m3_kept
  linarith

end TriData
end WaveTurbulence.FinalCount
