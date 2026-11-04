/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceCoefficient
public import WaveTurbulence.Foundations.Sumint.AffineCharacter

/-!
# Exact localized spatial expansion of the source oscillatory sum

The cutoff centres are chosen once for each pair of localization labels,
independently of output momenta and all times. Compact support makes the
spatial sum finite before Fourier Fubini is used. The resulting expression
has exactly the independent input modulation and the external unit phase.
-/

public section

open MeasureTheory Finset

namespace WaveTurbulence.Sumint

/-- The literal primary/alternative localized weight product. -/
@[expose] noncomputable def localizedSourceWeight {d : ℕ} (D : SumintDatum d) (L : ℝ)
    (a b : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) (x : D.S.VIdx → Fin d → ℤ) : ℂ :=
  ∏ v, localizedWeight (a v) (D.wK v) (D.kVec L x E v) *
    localizedWeight (b v) (D.wL v) (D.ℓVec L x E v)

/-- Exact source Step 1 expansion for a fixed pair of localization labels. -/
theorem exists_localized_spatial_expansion {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ δ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) :
    ∃ p : D.S.VIdx → Fin d → ℝ,
      ∀ (E : Fin 4 → Mom d), (∀ j, ‖E j-D.centre j‖ ≤ 1) →
      ∀ (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ),
      (∑' x : D.S.VIdx → Fin d → ℤ,
        localizedSourceWeight D L a b E x * D.phase L γ δ η x r t τ) =
      ∫ ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d,
        sourceCoefficient D a b ξ *
          (Real.fourierChar (externalModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v)) E) : ℂ) *
          cutoffPhaseSum D L γ δ η p
            (inputModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v))) r t τ := by
  classical
  obtain ⟨p,hp⟩ := exists_inputCutoff_insertion D hD a b
  refine ⟨p,?_⟩
  intro E hE r t τ
  let S := inputCutoffBox L p
  let W := localizedSourceWeight D L a b E
  let C := sourceCoefficient D a b
  let T := fun x => tensorCharacter (Sum.elim (D.kVec L x E) (D.ℓVec L x E))
  let Q := fun x : D.S.VIdx → Fin d → ℤ =>
    ((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ) : ℂ)
  have hW (x : D.S.VIdx → Fin d → ℤ) : W x = Q x * W x := hp E hE x
  have hz (x : D.S.VIdx → Fin d → ℤ) (hx : x ∉ S) : W x = 0 := by
    rw [hW]
    dsimp [Q]
    rw [inputCutoff_product_eq_zero hL p x hx, Complex.ofReal_zero,zero_mul]
  have hi (x : D.S.VIdx → Fin d → ℤ) : Integrable (fun ξ =>
      Q x*(T x ξ*C ξ)*D.phase L γ δ η x r t τ) :=
    ((integrable_source_modulatedCoefficient hd D hL hD a b x E).const_mul (Q x)).mul_const _
  change (∑' x, W x*D.phase L γ δ η x r t τ) = _
  calc
    _ = ∑ x ∈ S, W x*D.phase L γ δ η x r t τ := by
      apply tsum_eq_sum
      intro x hx
      rw [hz x hx,zero_mul]
    _ = ∑ x ∈ S, ∫ ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d,
        Q x*(T x ξ*C ξ)*D.phase L γ δ η x r t τ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [integral_mul_const,integral_const_mul]
      have hc : (∫ ξ, T x ξ*C ξ) = W x := source_coefficient_expansion hd D hL hD a b x E
      rw [hc]
      exact congrArg (fun z : ℂ => z*D.phase L γ δ η x r t τ) (hW x)
    _ = ∫ ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d,
        ∑ x ∈ S, Q x*(T x ξ*C ξ)*D.phase L γ δ η x r t τ :=
      (integral_finsetSum S (fun x _ => hi x)).symm
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro ξ
      change (∑ x ∈ S, Q x*(T x ξ*C ξ)*D.phase L γ δ η x r t τ) =
        C ξ * (Real.fourierChar (externalModulation D (fun v => ξ (.inl v))
          (fun v => ξ (.inr v)) E) : ℂ) * cutoffPhaseSum D L γ δ η p
          (inputModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v))) r t τ
      rw [cutoffPhaseSum_eq_sum D hL γ δ η p]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      have hchar : T x ξ = inputCharacter D L
          (inputModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v))) x *
          (Real.fourierChar (externalModulation D (fun v => ξ (.inl v)) (fun v => ξ (.inr v)) E) : ℂ) :=
        source_affine_character_eq D L x E ξ
      rw [hchar]
      change Q x * (_*C ξ) * _ = C ξ * _ * (Q x * _ * _)
      ring

end WaveTurbulence.Sumint
