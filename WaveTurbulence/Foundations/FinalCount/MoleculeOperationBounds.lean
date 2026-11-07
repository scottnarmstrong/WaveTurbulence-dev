/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.MoleculeCountingQuantities
import Mathlib.Tactic

/-!
# Counting quantities under restrictions and sequences of operations

TARGET `defcounta2` and `defdev`: restrictions reduce E and A; operation
bounds compose. The exact draft ratio is retained, with the zero-count
compatibility required for its least-bound interpretation.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open scoped ENNReal
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

/-- Adding admissibility restrictions cannot increase the actual supremum E. -/
theorem countE_mono {d : ℕ} (L gamma delta : ℝ) (base : Mom d)
    {Adm Adm' : (D → (Fin d → ℤ)) → Prop} (h : ∀ k, Adm k → Adm' k) :
    M.countE L gamma delta base Adm ≤ M.countE L gamma delta base Adm' := by
  unfold Molecule.countE
  apply iSup_mono
  intro c
  apply iSup_mono
  intro hc
  apply iSup_mono
  intro beta
  apply iSup_mono
  intro k0
  apply iSup_mono
  intro hk0
  apply Set.encard_mono
  intro k hk
  exact ⟨hk.1,hk.2.1,h k hk.2.2⟩

/-- The normalized quantity A has the same restriction monotonicity, with
all ladder factors and circuit-rank normalization retained. -/
theorem countA_mono {d : ℕ} (L gamma delta C1 : ℝ) (base : Mom d)
    (P : Finset V → ℝ) {Adm Adm' : (D → (Fin d → ℤ)) → Prop}
    (h : ∀ k, Adm k → Adm' k) :
    M.countA L gamma delta C1 base Adm P ≤ M.countA L gamma delta C1 base Adm' P := by
  unfold Molecule.countA
  exact mul_le_mul_left (ENat.toENNReal_mono (countE_mono M L gamma delta base h)) _

/-- An impossible admissibility condition gives exactly zero E, including
all choices of the restriction centers and conservation parameters. -/
theorem countE_false {d : ℕ} (L gamma delta : ℝ) (base : Mom d) :
    M.countE L gamma delta base (fun _ => False) = 0 := by
  simp [Molecule.countE]

/-- The ratio is an actual operation bound also at zero post-count, provided
the operation preserves emptiness in the required direction. -/
theorem deviation_mul_eq_of_zero_compatible {Apre Apos : ℝ≥0∞}
    (htop : Apos ≠ ⊤) (hz : Apos = 0 → Apre = 0) :
    deviation Apre Apos*Apos = Apre := by
  by_cases h0 : Apos = 0
  · simp [h0,hz h0,deviation]
  · exact deviation_mul_eq h0 htop

/-- Exact least-bound interpretation, including the zero-count case. -/
theorem deviation_le_iff_of_zero_compatible {Apre Apos I : ℝ≥0∞}
    (htop : Apos ≠ ⊤) (hz : Apos = 0 → Apre = 0) :
    deviation Apre Apos ≤ I ↔ Apre ≤ I*Apos := by
  by_cases h0 : Apos = 0
  · simp [h0,hz h0,deviation]
  · exact deviation_le_iff h0 htop

/-- Successive operation bounds multiply with no cancellation assumptions. -/
theorem operation_bounds_compose {Apre Amid Apos I J : ℝ≥0∞}
    (h1 : Apre ≤ I*Amid) (h2 : Amid ≤ J*Apos) : Apre ≤ (I*J)*Apos := by
  calc
    Apre ≤ I*Amid := h1
    _ ≤ I*(J*Apos) := mul_le_mul_right h2 I
    _ = (I*J)*Apos := (mul_assoc _ _ _).symm

end WaveTurbulence.Mole
