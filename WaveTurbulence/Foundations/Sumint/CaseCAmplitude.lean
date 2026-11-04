/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.PhaseNorm

/-!
# Assigning each case-(c) multiplier to its first pair

The modulus of the zero-input phase is exactly a product of independent
pair gap amplitudes. The nonempty-pair guard in the literal source is
retained by the dependent finite product, without an arbitrary choice
of a first pair in an empty block.
-/

public section

namespace WaveTurbulence.Sumint

/-- The case-(c) multiplier belongs to the first pair of that bad block. -/
@[expose] noncomputable def pairGapAmplitude {d : ℕ} (D : SumintDatum d) (η : ℝ)
    (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (z : ℝ × ℝ) : ℝ :=
  if D.S.nor a.1 = false ∧ D.badKind a.1 = 2 ∧ (a.2:ℕ) = 0 then
    |z.1-z.2|^(1-3*η) else 1

/-- Exact assignment of the scalar phase modulus to the independent pairs. -/
theorem norm_phase_eq_pair_gap_product {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) :
    ‖D.phase L γ δ η x r t τ‖ =
      ∏ a : Σ i : Fin D.S.I, Fin (D.S.m i), pairGapAmplitude D η a
        (τ (.inl ⟨a.1,a.2.succ⟩),τ (.inr (.inl a))) := by
  classical
  rw [norm_phase,Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hcase : D.S.nor i = false ∧ D.badKind i = 2
  · by_cases hm : 0 < D.S.m i
    · rw [dite_eq_left ⟨hcase.1,hcase.2,hm⟩]
      symm
      rw [Finset.prod_eq_single (⟨0,hm⟩ : Fin (D.S.m i))]
      · simp only [pairGapAmplitude,hcase.1,hcase.2,and_self,ite_true]
        rfl
      · intro j _ hj
        have hj0 : (j:ℕ) ≠ 0 := by
          intro hj0
          exact hj (Fin.ext hj0)
        simp only [pairGapAmplitude,hcase.1,hcase.2,hj0,and_false,ite_false]
      · intro hh
        exact (hh (Finset.mem_univ _)).elim
    · have hm0 : D.S.m i = 0 := by omega
      rw [dite_eq_right (by tauto)]
      have : IsEmpty (Fin (D.S.m i)) := by rw [hm0]; infer_instance
      simp
  · rw [dite_eq_right (by tauto)]
    symm
    apply Finset.prod_eq_one
    intro j _
    unfold pairGapAmplitude
    exact ite_eq_right (by tauto)

end WaveTurbulence.Sumint
