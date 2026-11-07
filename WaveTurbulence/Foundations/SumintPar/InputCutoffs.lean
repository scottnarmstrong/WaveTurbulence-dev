/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.InputDifferences
public import WaveTurbulence.Foundations.SumintPar.SourceEdgeBoxes
import Mathlib.Tactic

/-!
# Input cutoffs on localized affine cells

Primary and alternative centers are half-integer labels. External centers
are the specified output-ball centers. Every input differs from the
difference of two such centers by at most two in every coordinate.
The source cutoff at scale four is therefore identically one there.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.SumintPar

/-- Center of the selected primary, alternative, or external affine variable. -/
@[expose] noncomputable def choiceCenter {d : ℕ} (D : SumintDatum d)
    (a b : D.S.VIdx → Fin d → ℤ) (z : D.S.VIdx ⊕ D.S.VIdx ⊕ Fin 4) (j : Fin d) : ℝ :=
  match z with
  | .inl v => (a v j : ℝ) / 2
  | .inr (.inl v) => (b v j : ℝ) / 2
  | .inr (.inr c) => D.centre c j

/-- All three localized vector families have coordinate error at most one. -/
theorem choiceVector_coordinate_error {d : ℕ} (D : SumintDatum d) (L : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d)
    (a b : D.S.VIdx → Fin d → ℤ)
    (hk : ∀ v, localizationProfile (a v) (D.kVec L x E v) ≠ 0)
    (hl : ∀ v, localizationProfile (b v) (D.ℓVec L x E v) ≠ 0)
    (hE : ∀ c, ‖E c - D.centre c‖ ≤ 1)
    (z : D.S.VIdx ⊕ D.S.VIdx ⊕ Fin 4) (j : Fin d) :
    |choiceVector D L x E z j - choiceCenter D a b z j| ≤ 1 := by
  rcases z with v | v | c
  · have h := abs_le.mp (profile_coordinate_error (hk v) j)
    change |D.kVec L x E v j - (a v j : ℝ) / 2| ≤ 1
    apply abs_le.mpr
    constructor <;> linarith only [h.1, h.2]
  · have h := abs_le.mp (profile_coordinate_error (hl v) j)
    change |D.ℓVec L x E v j - (b v j : ℝ) / 2| ≤ 1
    apply abs_le.mpr
    constructor <;> linarith only [h.1, h.2]
  · exact (show |E c j - D.centre c j| ≤ ‖E c - D.centre c‖ from
      PiLp.norm_apply_le (E c - D.centre c) j).trans (hE c)

/-- Hypothesis (iii) supplies a unit input cutoff, with a center independent of the lattice input. -/
theorem input_cutoff_eq_one {d : ℕ} (D : SumintDatum d) {A L γ η : ℝ} {Dsteps : ℕ}
    (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (v : D.S.VIdx) :
    ∃ z w : D.S.VIdx ⊕ D.S.VIdx ⊕ Fin 4,
      ∀ (x : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d),
      (∀ u, localizationProfile (a u) (D.kVec L x E u) ≠ 0) →
      (∀ u, localizationProfile (b u) (D.ℓVec L x E u) ≠ 0) →
      (∀ c, ‖E c - D.centre c‖ ≤ 1) →
      Fourier.chi0Tensor (fun j =>
        ((latticePoint L (x v)) j - (choiceCenter D a b z j - choiceCenter D a b w j)) / 4) = 1 := by
  classical
  obtain ⟨z, w, hT, hH⟩ := hD.2.2.2.1 v
  change (∀ j, choiceRowT D z j - choiceRowT D w j = if j = v then 1 else 0) at hT
  change (∀ c, choiceRowH D z c - choiceRowH D w c = 0) at hH
  refine ⟨z, w, ?_⟩
  intro x E hk hl hE
  have heq : latticePoint L (x v) = choiceVector D L x E z - choiceVector D L x E w := by
    rw [choiceVector_eq_rows, choiceVector_eq_rows]
    have ht : ∑ j, (choiceRowT D z j - choiceRowT D w j) • latticePoint L (x j) =
        latticePoint L (x v) := by simp [hT]
    have hh : ∑ c, (choiceRowH D z c - choiceRowH D w c) • E c = 0 := by simp [hH]
    simp only [sub_smul, Finset.sum_sub_distrib] at ht hh
    calc
      _ = ((∑ j, choiceRowT D z j • latticePoint L (x j)) -
          ∑ j, choiceRowT D w j • latticePoint L (x j)) +
          ((∑ c, choiceRowH D z c • E c) - ∑ c, choiceRowH D w c • E c) := by
        rw [ht, hh, add_zero]
      _ = _ := by abel
  apply Fourier.chi0Tensor_eq_one
  intro j
  have hz := choiceVector_coordinate_error D L x E a b hk hl hE z j
  have hw := choiceVector_coordinate_error D L x E a b hk hl hE w j
  have hj := congrArg (fun y : Mom d => y j) heq
  change latticePoint L (x v) j = choiceVector D L x E z j - choiceVector D L x E w j at hj
  rw [hj, abs_div]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hz' := abs_le.mp hz
  have hw' := abs_le.mp hw
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  apply abs_le.mpr
  constructor <;> linarith only [hz'.1, hz'.2, hw'.1, hw'.2]

end WaveTurbulence.SumintPar
