/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepSupM
public import WaveTurbulence.Foundations.Stage1.Represents.RepGate1
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-D (moments): slot-level superpositions with the frequency moment

The moment-carrying versions of `cenSup_couple` / `sup_tree` (RepGate1): an `XNormRestr` bound at `θ = η` of a
continuous slot kernel on its time box gives a superposition whose weights carry `⟨m/2⟩^η` (`CenSupM P.η`,
`SupM P.η`; R58, finding F-LOWCLOCK: the routed slot frequencies become VINEEST modulations).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic Set
open scoped ENNReal

open Classical in
/-- The explicit constant of the moment-carrying couple superposition (depends only on `d` and `η`). -/
noncomputable def cenCplCM (d : ℕ) (η : ℝ) : ℝ≥0∞ :=
  if h : 1 ≤ d ∧ 0 ≤ η then
    (exists_cenSupM (r := 2) (d := d) h.1 h.2 (Λ₁ := 30 * d) (Λ₂ := 30 * d) (by omega) (by omega)).choose
  else 0

open Classical in
/-- The explicit constant of the moment-carrying tree superposition (depends only on `d` and `η`). -/
noncomputable def supTreeCM (d : ℕ) (η : ℝ) : ℝ≥0∞ :=
  if h : 1 ≤ d ∧ 0 ≤ η then
    (exists_supM (r := 2) (d := d) h.2 (Λ₁ := 30 * d) (by have := h.1; omega)).choose
  else 0

theorem cenCplCM_spec (d : ℕ) (η : ℝ) (hd : 1 ≤ d) (hη0 : 0 ≤ η) :
    cenCplCM d η ≠ ⊤ ∧ ∀ (q q' : ℕ) (f : (Fin 2 → ℝ) → Mom d → ℂ) (X : ℝ≥0∞), X ≠ ⊤ →
      (∀ k, Continuous fun t => f t k) →
      XNormRestr η (30 * d) (30 * d) (timeBox (q : ℝ) q') Set.univ f ≤ X →
      CenSupM η (30 * d) (timeBox (q : ℝ) q') f (cenCplCM d η * X) := by
  have hh : 1 ≤ d ∧ 0 ≤ η := ⟨hd, hη0⟩
  obtain ⟨hC, h⟩ := (exists_cenSupM (r := 2) (d := d) hd hη0 (Λ₁ := 30 * d) (Λ₂ := 30 * d) (by omega)
    (by omega)).choose_spec
  have e : cenCplCM d η = (exists_cenSupM (r := 2) (d := d) hd hη0 (Λ₁ := 30 * d) (Λ₂ := 30 * d) (by omega)
    (by omega)).choose := by
    unfold cenCplCM; simp only [hh, and_self, ↓reduceDIte]
  rw [e]
  exact ⟨hC, fun q q' f X hX hfc hn => h ![(q : ℝ), q'] _ f X hX (timeBox_subset_cell _ _)
    (timeBox_subset_closure_interior _ _) hfc hn⟩

theorem supTreeCM_spec (d : ℕ) (η : ℝ) (hd : 1 ≤ d) (hη0 : 0 ≤ η) :
    supTreeCM d η ≠ ⊤ ∧ ∀ (q q' : ℕ) (f : (Fin 2 → ℝ) → Mom d → ℂ) (X : ℝ≥0∞), X ≠ ⊤ → q' ≤ q →
      (∀ k, Continuous fun t => f t k) →
      XNormRestr η (30 * d) 0 (timeBoxGt (q : ℝ) q') Set.univ f ≤ X →
      SupM η (30 * d) (timeBoxGt (q : ℝ) q') f (supTreeCM d η * X) := by
  have hh : 1 ≤ d ∧ 0 ≤ η := ⟨hd, hη0⟩
  obtain ⟨hC, h⟩ := (exists_supM (r := 2) (d := d) hη0 (Λ₁ := 30 * d) (by omega)).choose_spec
  have e : supTreeCM d η = (exists_supM (r := 2) (d := d) hη0 (Λ₁ := 30 * d) (by omega)).choose := by
    unfold supTreeCM; simp only [hh, and_self, ↓reduceDIte]
  rw [e]
  exact ⟨hC, fun q q' f X hX hqq hfc hn => h ![(q : ℝ), q'] _ f X hX (timeBoxGt_subset_cell _ _)
    (timeBoxGt_subset_closure_interior (by exact_mod_cast hqq)) hfc hn⟩

theorem cenSupM_couple (P : WTParams) (hd : 1 ≤ P.d) (hη0 : 0 ≤ P.η) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ C = cenCplCM P.d P.η ∧ ∀ (q q' : ℕ) (f : (Fin 2 → ℝ) → Mom P.d → ℂ) (X : ℝ≥0∞),
      X ≠ ⊤ → (∀ k, Continuous fun t => f t k) →
      XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox (q : ℝ) q') Set.univ f ≤ X →
      CenSupM P.η (30 * P.d) (timeBox (q : ℝ) q') f (C * X) := by
  obtain ⟨hC, h⟩ := cenCplCM_spec P.d P.η hd hη0
  exact ⟨_, hC, rfl, h⟩

theorem supM_tree (P : WTParams) (hd : 1 ≤ P.d) (hη0 : 0 ≤ P.η) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ C = supTreeCM P.d P.η ∧ ∀ (q q' : ℕ) (f : (Fin 2 → ℝ) → Mom P.d → ℂ) (X : ℝ≥0∞),
      X ≠ ⊤ → q' ≤ q → (∀ k, Continuous fun t => f t k) →
      XNormRestr P.η (30 * P.d) 0 (timeBoxGt (q : ℝ) q') Set.univ f ≤ X →
      SupM P.η (30 * P.d) (timeBoxGt (q : ℝ) q') f (C * X) := by
  obtain ⟨hC, h⟩ := supTreeCM_spec P.d P.η hd hη0
  exact ⟨_, hC, rfl, h⟩

end WaveTurbulence.Represents
