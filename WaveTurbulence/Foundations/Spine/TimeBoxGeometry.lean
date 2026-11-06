/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentSourceTypes
/-! The source time boxes are the closures of their interiors, including the diagonal endpoints. -/
public section
open WaveTurbulence.Induct
namespace WaveTurbulence.LGSpine
open Set

theorem timeBox_eq_pi (q q' : ℝ) : timeBox q q' =
    Set.pi Set.univ (fun j : Fin 2 => Icc (![q, q'] j) (![q, q'] j + 1)) := by
  ext ts
  simp only [timeBox, mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const,
    Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, mem_Icc]

theorem closure_interior_timeBox (q q' : ℝ) :
    closure (interior (timeBox q q')) = timeBox q q' := by
  rw [timeBox_eq_pi, interior_pi_set Set.finite_univ, closure_pi_set]
  apply congrArg (Set.pi Set.univ)
  funext j
  exact closure_interior_Icc (by linarith : ![q, q'] j ≠ ![q, q'] j + 1)

/-- A point of the tree time box also lies in the closure of its interior; strict t>s
is retained while approaching the rectangular boundary. -/
theorem mem_closure_interior_timeBoxGt {q q' : ℝ} {ts : Fin 2 → ℝ}
    (hts : ts ∈ timeBoxGt q q') : ts ∈ closure (interior (timeBoxGt q q')) := by
  let O : Set (Fin 2 → ℝ) := {ts | ts 1 < ts 0}
  have hO : IsOpen O := isOpen_lt (continuous_apply 1) (continuous_apply 0)
  have he : timeBoxGt q q' = timeBox q q' ∩ O := rfl
  rw [he, interior_inter, hO.interior_eq]
  exact hO.closure_inter ⟨by rw [closure_interior_timeBox]; exact hts.1, hts.2⟩

end WaveTurbulence.LGSpine
