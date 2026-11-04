/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.Fourier.Norm00VCutoff
/-! Exact time and order-zero norm bridges against the unchanged snapshot 3. -/
public section
namespace WaveTurbulence.NormBridgeScratch
open MeasureTheory Set
open scoped ENNReal

theorem timeFT_eq_timeFourier {r : ℕ} {V : Type*}
    (F : (Fin r → ℝ) → V → ℂ) (ξ : Fin r → ℝ) (v : V) :
    timeFT F ξ v = Fourier.timeFourier (fun t => F t v) ξ := by
  unfold timeFT Fourier.timeFourier VectorFourier.fourierIntegral
  apply integral_congr_ae
  apply ae_of_all
  intro t
  dsimp only
  simp only [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  have he : Fourier.timePairing r t ξ = ∑ i, ξ i * t i := by
    change (∑ i, t i * ξ i) = _
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [he]
  have hx : -(↑(2 * Real.pi * ∑ i, ξ i * t i) : ℂ) * Complex.I =
      ↑(2 * Real.pi * -(∑ i, ξ i * t i)) * Complex.I := by push_cast; ring
  rw [hx, mul_comm]

theorem timeBracket_eq_max {r : ℕ} (ξ : Fin r → ℝ) :
    Fourier.timeBracket ξ = (⨆ i, Real.sqrt (1 + ξ i ^ 2)) ⊔ 1 := by
  cases Nat.eq_zero_or_pos r with
  | inl hr =>
    subst r
    have hz : (⨆ i : Fin 0, Real.sqrt (1 + ξ i ^ 2)) = (0 : ℝ) := by
      simp only [iSup, Set.range_eq_empty, Real.sSup_empty]
    rw [hz, max_eq_right (zero_le_one : (0 : ℝ) ≤ 1)]
    apply le_antisymm
    · exact Fourier.timeBracket_le le_rfl (fun i => Fin.elim0 i)
    · exact Fourier.one_le_timeBracket ξ
  | inr hr =>
    have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    have hb : BddAbove (range (fun i => Real.sqrt (1 + ξ i ^ 2))) := (finite_range _).bddAbove
    apply le_antisymm
    · exact Fourier.timeBracket_le (le_max_right _ _) (fun i => (le_ciSup hb i).trans (le_max_left _ _))
    · exact max_le (ciSup_le (fun i => Fourier.bracket_le_timeBracket ξ i)) (Fourier.one_le_timeBracket ξ)

theorem maxBracketPow_eq_timeWeight {r : ℕ} (θ : ℝ) (ξ : Fin r → ℝ) :
    maxBracketPow θ ξ = Fourier.timeWeight θ ξ := by
  unfold maxBracketPow Fourier.timeWeight
  rw [timeBracket_eq_max]

theorem XNorm00_eq_mixedFourierNorm00 {r : ℕ} {V : Type*} (θ : ℝ)
    (F : (Fin r → ℝ) → V → ℂ) : XNorm00 θ F = Fourier.mixedFourierNorm00 θ F := by
  unfold XNorm00 Fourier.mixedFourierNorm00
  split_ifs
  · simp only [Fourier.mixedFourierEnvelope00, timeFT_eq_timeFourier, maxBracketPow_eq_timeWeight]
  · rfl

theorem XNorm00_unit_eq_timeFourierNorm {r : ℕ} (θ : ℝ) (F : (Fin r → ℝ) → ℂ) :
    XNorm00 θ (fun t (_ : Unit) => F t) = Fourier.timeFourierNorm θ F := by
  rw [XNorm00_eq_mixedFourierNorm00, Fourier.mixedFourierNorm00_unit]

theorem XNorm00Restr_eq_mixedRestrictionNorm00 {r : ℕ} {V : Type*} (θ : ℝ)
    (B : Set (Fin r → ℝ)) (K : Set V) (F : (Fin r → ℝ) → V → ℂ) :
    XNorm00Restr θ B K F = Fourier.mixedRestrictionNorm00 θ B K (fun t v => F t v) := by
  rw [Fourier.mixedRestrictionNorm00_eq_agreement]
  unfold XNorm00Restr
  simp only [XNorm00_eq_mixedFourierNorm00]
theorem iterPartial_zero {d : ℕ} (F : Mom d → ℂ) : iterPartial (0 : Fin d → ℕ) F = F := by
  unfold iterPartial
  generalize List.finRange d = l
  induction l with
  | nil => rfl
  | cons j l ih => simpa only [List.foldr_cons, Pi.zero_apply, Function.iterate_zero, id_eq] using ih

theorem sum_le_zero_iff {d : ℕ} (ρ : Fin d → ℕ) : (∑ j, ρ j ≤ 0) ↔ ρ = 0 := by
  simp only [Nat.le_zero, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_const]
  exact ⟨fun h => funext h, fun h j => congrFun h j⟩

theorem XNorm_zero_order_eq_mixedFourierNorm {r d : ℕ} (θ : ℝ) (Λ₂ : ℕ)
    (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNorm θ 0 Λ₂ F = Fourier.mixedFourierNorm θ 0 Λ₂ F := by
  by_cases hi : ∀ k, Integrable (fun t => F t k)
  · rw [Fourier.mixedFourierNorm_zero_order θ Λ₂ F hi, XNorm,
      ite_eq_left (And.intro hi (Or.inl rfl))]
    simp only [sum_le_zero_iff, iSup_iSup_eq_left]
    apply lintegral_congr
    intro ξ
    rw [maxBracketPow_eq_timeWeight]
    congr 1
    unfold Fourier.momentumSupNorm
    apply iSup_congr
    intro k
    rw [ENNReal.ofReal_mul (show 0 ≤ jbr k ^ Λ₂ from pow_nonneg (Real.sqrt_nonneg _) _), ofReal_norm]
    rw [iterPartial_zero, timeFT_eq_timeFourier]
    rfl
  · rw [XNorm, ite_eq_right (not_and_of_not_left _ hi),
      Fourier.mixedFourierNorm_of_not_admissible (by simpa only [Fourier.mixedFourierAdmissible_zero_iff] using hi)]

theorem XNorm_zero_eq_XNorm00 {r d : ℕ} (θ : ℝ) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNorm θ 0 0 F = XNorm00 θ F := by
  unfold XNorm XNorm00
  split_ifs with h₁ h₂ h₂
  · simp only [sum_le_zero_iff, pow_zero, one_mul, iSup_iSup_eq_left, iterPartial_zero, ofReal_norm]
  · exact (h₂ h₁.1).elim
  · exact (h₁ ⟨h₂, Or.inl rfl⟩).elim
  · rfl

theorem XNorm_zero_eq_mixedFourierNorm {r d : ℕ} (θ : ℝ) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNorm θ 0 0 F = Fourier.mixedFourierNorm θ 0 0 F := by
  rw [XNorm_zero_eq_XNorm00, XNorm00_eq_mixedFourierNorm00, Fourier.mixedFourierNorm00_eq_mixedFourierNorm]

theorem XNormRestr_zero_eq_mixedRestrictionNorm {r d : ℕ} (θ : ℝ)
    (B : Set (Fin r → ℝ)) (K : Set (Mom d)) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNormRestr θ 0 0 B K F = Fourier.mixedRestrictionNorm θ 0 0 B K (fun t k => F t k) := by
  unfold XNormRestr
  rw [← Fourier.mixedRestrictionNorm00_eq_mixedRestrictionNorm,
    Fourier.mixedRestrictionNorm00_eq_agreement]
  simp only [XNorm_zero_eq_XNorm00, XNorm00_eq_mixedFourierNorm00]
/-- The unrestricted equality passes through the infimum over every ambient extension. -/
theorem XNormRestr_zero_order_eq_mixedRestrictionNorm {r d : ℕ} (θ : ℝ) (Λ₂ : ℕ)
    (B : Set (Fin r → ℝ)) (K : Set (Mom d)) (F : (Fin r → ℝ) → Mom d → ℂ) :
    XNormRestr θ 0 Λ₂ B K F = Fourier.mixedRestrictionNorm θ 0 Λ₂ B K (fun t k => F t k) := by
  unfold XNormRestr Fourier.mixedRestrictionNorm
  apply iInf_congr
  intro G
  have he : (∀ t ∈ B, ∀ k ∈ K, G t k = F t k) ↔
      (∀ (t : B) (k : K), G t k = F t k) :=
    ⟨fun h t k => h t t.property k k.property, fun h t ht k hk => h ⟨t, ht⟩ ⟨k, hk⟩⟩
  rw [he, XNorm_zero_order_eq_mixedFourierNorm]

end WaveTurbulence.NormBridgeScratch
