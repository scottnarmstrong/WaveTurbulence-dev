/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.EdgeCellError
public import WaveTurbulence.Foundations.Sumint.BoxCounting
import Mathlib.Tactic

/-!
# Fixed boxes for alternative-variable localization differences

Centers depend on the primary labels and output centers, but not on the
alternative labels. This independence permits the finite-product count.
-/

public section

open Finset

namespace WaveTurbulence.Sumint

/-- Twice the affine center predicted by the primary labels and output centers. -/
@[expose] noncomputable def edgeCenter {ι κ : Type*} [Fintype ι] [Fintype κ]
    {d : ℕ} (σk : ι → ι → ℝ) (σe : ι → κ → ℝ)
    (a : ι → Fin d → ℤ) (C : κ → Fin d → ℝ) (v : ι) (j : Fin d) : ℝ :=
  (∑ w, σk v w * (a w j : ℝ)) + 2 * ∑ c, σe v c * C c j

/-- Coordinate errors put every predecessor difference in its fixed lattice box. -/
theorem edgeDifference_mem_box {ι κ : Type*} [Fintype ι] [Fintype κ]
    {d : ℕ} (prev : ι → Option ι) (σk : ι → ι → ℝ) (σe : ι → κ → ℝ)
    (k l : ι → Fin d → ℝ) (E C : κ → Fin d → ℝ)
    (a b : ι → Fin d → ℤ) (Λ : ι → ℝ)
    (hrel : ∀ v j, l v j - (prev v).elim 0 (fun w => l w j) =
      (∑ w, σk v w * k w j) + ∑ c, σe v c * E c j)
    (hk : ∀ w j, |2 * k w j - (a w j : ℝ)| ≤ 1)
    (hE : ∀ c j, |E c j - C c j| ≤ 1)
    (hl : ∀ w j, |2 * l w j - (b w j : ℝ)| ≤ 1)
    (hm : ∀ v, (∑ w, |σk v w|) + ∑ c, |σe v c| ≤ Λ v)
    (hΛ : ∀ v, 1 ≤ Λ v) (v : ι) :
    edgeDifference prev b v ∈ Counting.latticeBox (edgeCenter σk σe a C v) (4 * Λ v) := by
  classical
  apply (Counting.mem_latticeBox _ _ _).mpr
  intro j
  cases hp : prev v with
  | none =>
    have h := abs_edge_cell_error_le (σk v) (fun w => k w j) (fun w => (a w j : ℝ))
      (σe v) (fun c => E c j) (fun c => C c j) (l v j) 0 (b v j) 0 (Λ v)
      (by simpa [hp] using hrel v j) (fun w => hk w j) (fun c => hE c j)
      (hl v j) (by norm_num) (hm v) (hΛ v)
    simpa [edgeDifference, hp, edgeCenter] using h
  | some w =>
    have h := abs_edge_cell_error_le (σk v) (fun u => k u j) (fun u => (a u j : ℝ))
      (σe v) (fun c => E c j) (fun c => C c j) (l v j) (l w j) (b v j) (b w j) (Λ v)
      (by simpa [hp] using hrel v j) (fun u => hk u j) (fun c => hE c j)
      (hl v j) (hl w j) (hm v) (hΛ v)
    simpa [edgeDifference, hp, edgeCenter] using h

end WaveTurbulence.Sumint
