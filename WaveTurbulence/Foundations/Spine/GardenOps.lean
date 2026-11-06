/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RootWeightOps
public import WaveTurbulence.Foundations.Spine.EvalAssemble
/-! AMEND6' (design P*, F2): counts of the operation list of a root-weight choice `c`: no derivatives, at most
`2 w n` operations, and at the pair type `(j, j')` at most `4 n` acting forms (only the forms of the trees `j`, `j'`
act, `2 n` each). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem sum_flatMap_aux {α : Type*} (l : List α) (g : α → List ℕ) :
    (l.flatMap g).sum = (l.map fun a => (g a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- The acting-form indicator of the tree `j0` at the pair type `(j, j')`. -/
noncomputable def nzForm {w : ℕ} (j j' j0 : Fin w) : ℕ :=
  if ((if j = j0 then (1 : ℝ) else 0) - (if j' = j0 then (1 : ℝ) else 0)) = 0 then 0 else 1

theorem nzForm_le {w : ℕ} (j j' j0 : Fin w) :
    nzForm j j' j0 ≤ (if j0 = j then 1 else 0) + (if j0 = j' then 1 else 0) := by
  unfold nzForm
  by_cases h1 : j = j0 <;> by_cases h2 : j' = j0 <;> simp [h1, h2, eq_comm]


theorem sum_nzForm_le {w : ℕ} (j j' : Fin w) : ∑ j0 : Fin w, nzForm j j' j0 ≤ 2 := by
  calc ∑ j0 : Fin w, nzForm j j' j0 ≤ ∑ j0 : Fin w, ((if j0 = j then 1 else 0) + (if j0 = j' then 1 else 0)) :=
        Finset.sum_le_sum fun j0 _ => nzForm_le j j' j0
    _ = 2 := by
        rw [Finset.sum_add_distrib]
        simp

theorem fcnt_forms {d w : ℕ} (j j' : Fin w) (fs : List (Fin w × Fin d)) :
    fcnt j j' (fs.map fun f => TOp.form f.1 f.2) = (fs.map fun f => nzForm j j' f.1).sum := by
  unfold fcnt
  simp only [List.map_map]
  congr 1

theorem dcnt_forms {d w : ℕ} (fs : List (Fin w × Fin d)) : dcnt (fs.map fun f => TOp.form f.1 f.2) = 0 := by
  have : ∀ f : Fin w × Fin d, TOp.dc (TOp.form (d := d) f.1 f.2) = 0 := fun _ => rfl
  simp [dcnt, List.map_map, Function.comp_def, this]

theorem fcnt_opsOfChoice {d w n : ℕ} (c : Fin w → Fin n → Option (Fin d)) (j j' : Fin w) :
    fcnt j j' ((opsOfChoice c).map fun f => TOp.form f.1 f.2) ≤ 4 * n := by
  rw [fcnt_forms]
  unfold opsOfChoice
  rw [List.map_flatMap]
  rw [sum_flatMap_aux, ← Fin.sum_univ_def]
  have hin : ∀ j0 : Fin w, (((List.finRange n).flatMap fun t => match c j0 t with
      | none => []
      | some i => [(j0, i), (j0, i)]).map fun f => nzForm j j' f.1).sum ≤ 2 * n * nzForm j j' j0 := by
    intro j0
    rw [List.map_flatMap, sum_flatMap_aux, ← Fin.sum_univ_def]
    calc _ ≤ ∑ t : Fin n, 2 * nzForm j j' j0 := by
          refine Finset.sum_le_sum fun t _ => ?_
          cases c j0 t <;> simp [nzForm] <;> split_ifs <;> omega
      _ = _ := by simp [mul_comm, mul_assoc]
  calc _ ≤ ∑ j0 : Fin w, 2 * n * nzForm j j' j0 := Finset.sum_le_sum fun j0 _ => hin j0
    _ = 2 * n * ∑ j0 : Fin w, nzForm j j' j0 := by rw [Finset.mul_sum]
    _ ≤ 2 * n * 2 := Nat.mul_le_mul_left _ (sum_nzForm_le j j')
    _ = 4 * n := by ring

theorem length_opsOfChoice_le {d w n : ℕ} (c : Fin w → Fin n → Option (Fin d)) :
    (opsOfChoice c).length ≤ 2 * w * n := by
  unfold opsOfChoice
  rw [List.length_flatMap]
  have hin : ∀ j : Fin w, (List.map (fun t => (match c j t with
      | none => []
      | some i => [(j, i), (j, i)]).length) (List.finRange n)).sum ≤ 2 * n := by
    intro j
    have := List.sum_le_length_nsmul ((List.finRange n).map fun t => (match c j t with
      | none => []
      | some i => [(j, i), (j, i)]).length) 2 (by
        intro x hx
        obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
        cases c j t <;> simp)
    simpa [mul_comm] using this
  have h2 := List.sum_le_length_nsmul ((List.finRange w).map fun j => (List.map (fun t => (match c j t with
      | none => []
      | some i => [(j, i), (j, i)]).length) (List.finRange n)).sum) (2 * n) (by
        intro x hx
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
        exact hin j)
  simp only [List.length_map, List.length_finRange, smul_eq_mul] at h2
  simp only [List.length_flatMap]
  calc _ ≤ w * (2 * n) := h2
    _ = 2 * w * n := by ring

end WaveTurbulence.LGSpine
