/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.ParityFourierReduction
public import WaveTurbulence.Foundations.WeylSums.LatticeBoxes

/-! # Quantitative joint-amplitude bound on the parity lattice -/

public section
open Finset MeasureTheory
open scoped BigOperators
namespace WaveTurbulence.WeylSums

/-- Physical location of an integer pair lattice, with independent integer centers. -/
@[expose] noncomputable def pairLatticeSample {d : ℕ} (L : ℝ)
    (h : Fin d × Fin 2 → ℤ) (v : Fin d → ℤ × ℤ) : EuclideanSpace ℝ (Fin d × Fin 2) :=
  ∑ j, pairBlockVector j (((v j).1+h (j,0) : ℤ)/L) (((v j).2+h (j,1) : ℤ)/L)

@[simp] theorem pairLatticeSample_apply_zero {d : ℕ} (L : ℝ)
    (h : Fin d × Fin 2 → ℤ) (v : Fin d → ℤ × ℤ) (j : Fin d) :
    pairLatticeSample L h v (j,0) = ((v j).1+h (j,0) : ℤ)/L := by
  simp [pairLatticeSample, pairBlockVector, Pi.single_apply]

@[simp] theorem pairLatticeSample_apply_one {d : ℕ} (L : ℝ)
    (h : Fin d × Fin 2 → ℤ) (v : Fin d → ℤ × ℤ) (j : Fin d) :
    pairLatticeSample L h v (j,1) = ((v j).2+h (j,1) : ℤ)/L := by
  simp [pairLatticeSample, pairBlockVector, Pi.single_apply]

/-- The product of the exact sum/difference parity projectors. -/
@[expose] noncomputable def pairParity {d : ℕ} (h : Fin d × Fin 2 → ℤ)
    (v : Fin d → ℤ × ℤ) : ℂ :=
  ∏ j, if Even ((v j).1+h (j,0)-((v j).2+h (j,1))) then 1 else 0

/-- Diagonal bilinear phase in integer coordinates. -/
@[expose] noncomputable def pairDiagonalPhase {d : ℕ} (h : Fin d × Fin 2 → ℤ)
    (u r w : Fin d → ℝ) (v : Fin d → ℤ × ℤ) : ℝ :=
  ∑ j, (u j*((((v j).1 : ℝ)+h (j,0)))^2-u j*((((v j).2 : ℝ)+h (j,1)))^2+
    r j*(((v j).1 : ℝ)+h (j,0))+w j*(((v j).2 : ℝ)+h (j,1)))

/-- A geometric plateau hypothesis and an actual Fourier representation
suffice for the parity-lattice bound. Both are proved for the source cutoffs. -/
theorem norm_pair_lattice_le_of_fourier_representation {d : ℕ}
    (χ F : EuclideanSpace ℝ (Fin d × Fin 2) → ℂ) (hF : Integrable F)
    (hf : ∀ x, χ x = ∫ ξ, F ξ*e (inner ℝ ξ x))
    (L M : ℝ) (h : Fin d × Fin 2 → ℤ) (hM : 0 < M)
    (hplateau : ∀ v : Fin d → ℤ × ℤ, χ (pairLatticeSample L h v) ≠ 0 →
      ∀ j, weylCutoff (((v j).1 : ℝ)/M) = 1 ∧ weylCutoff (((v j).2 : ℝ)/M) = 1)
    (u r w : Fin d → ℝ) :
    ‖∑' v : Fin d → ℤ × ℤ, pairParity h v*χ (pairLatticeSample L h v)*
      e (pairDiagonalPhase h u r w v)‖ ≤
        (∫ ξ, ‖F ξ‖)*∏ j, weylSupremum M (u j)^2 := by
  classical
  let I := Icc (-⌈M⌉ : ℤ) ⌈M⌉
  let box := Fintype.piFinset (fun _ : Fin d => I ×ˢ I)
  have hfinite : (∑' v : Fin d → ℤ × ℤ, pairParity h v*χ (pairLatticeSample L h v)*
      e (pairDiagonalPhase h u r w v)) =
      ∑ v ∈ box, pairParity h v*χ (pairLatticeSample L h v)*e (pairDiagonalPhase h u r w v) := by
    apply tsum_eq_sum
    intro v hv
    have hz : χ (pairLatticeSample L h v) = 0 := by
      by_contra hz
      apply hv
      apply Fintype.mem_piFinset.mpr
      intro j
      obtain ⟨ha,hb⟩ := hplateau v hz j
      apply mem_product.mpr
      constructor
      · by_contra hn
        exact zero_ne_one ((weylCutoff_eq_zero_of_not_mem hM (v j).1 hn).symm.trans ha)
      · by_contra hn
        exact zero_ne_one ((weylCutoff_eq_zero_of_not_mem hM (v j).2 hn).symm.trans hb)
    rw [hz, mul_zero, zero_mul]
  have hbox (f : (Fin d → ℤ × ℤ) → ℂ) :
      (∑ v ∈ box, f v) = ∑ v : Fin d → (↥I × ↥I), f (fun j => ((v j).1.val,(v j).2.val)) := by
    symm
    apply sum_bij (fun v _ j => ((v j).1.val,(v j).2.val))
    · intro v hv
      exact Fintype.mem_piFinset.mpr (fun j => mem_product.mpr ⟨(v j).1.property,(v j).2.property⟩)
    · intro v hv w hw heq
      funext j
      apply Prod.ext <;> apply Subtype.ext
      · exact congrArg Prod.fst (congrFun heq j)
      · exact congrArg Prod.snd (congrFun heq j)
    · intro v hv
      have hh := Fintype.mem_piFinset.mp hv
      refine ⟨fun j => (⟨(v j).1,(mem_product.mp (hh j)).1⟩,⟨(v j).2,(mem_product.mp (hh j)).2⟩), mem_univ _, ?_⟩
      rfl
    · intro v hv
      rfl
  rw [hfinite,hbox]
  have heq (v : Fin d → (↥I × ↥I)) :
      pairParity h (fun j => ((v j).1.val,(v j).2.val))*
        χ (pairLatticeSample L h (fun j => ((v j).1.val,(v j).2.val))) =
      (∏ j, if Even (((v j).1 : ℤ)+h (j,0)-((v j).2 : ℤ)-h (j,1)) then
        weylCutoff (((v j).1 : ℤ)/M)*weylCutoff (((v j).2 : ℤ)/M) else 0)*
      (∫ ξ, F ξ*e (inner ℝ ξ (pairLatticeSample L h (fun j => ((v j).1.val,(v j).2.val))))) := by
    rw [← hf]
    by_cases hz : χ (pairLatticeSample L h (fun j => ((v j).1.val,(v j).2.val))) = 0
    · simp [hz]
    · have hp := hplateau _ hz
      simp only [(hp _).1, (hp _).2, one_mul, pairParity, sub_sub]
  simp_rw [heq]
  simpa only [pairLatticeSample, pairDiagonalPhase, Int.cast_add] using
    norm_parity_fourier_reduction_le hM F hF h u r w

end WaveTurbulence.WeylSums
