/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeScalarEstimate

/-! # A finite actual coefficient family shares one original-frequency tree envelope -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst ClassJR

/-- Finite original coefficient families are aggregated before the mixed norm, using
actual measurable scalar envelopes and their weighted original-frequency masses. -/
theorem tree_root_finite_scalar_profile_le {d K M J : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) {ι : Type*} [Fintype ι] {θ : ℝ} (hθ : 0 ≤ θ)
    (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ) {Binput Ccover : ℝ}
    (hK : d+2+J ≤ K) (hM : 2*d ≤ M) (hBinput : 0 ≤ Binput)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal Binput)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (G.sig 0)).length)
    (R : ι → (ℝ × ℝ) → (Fin (X.treeLinks (G.sig 0)).length → Mom d) →
      (Fin (X.treeLinks (G.sig 0)).length → Mom d) →
      ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ) → ℂ)
    (hR : ∀ i z, StronglyMeasurable (fun p : (ℝ × ℝ) ×
      ((Fin (X.treeLinks (G.sig 0)).length → Mom d) ×
        (Fin (X.treeLinks (G.sig 0)).length → Mom d)) => R i p.1 p.2.1 p.2.2 z))
    (P : ι → ℝ) (hP : ∀ i, 0 ≤ P i) (c : ι → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (E : ι → (ℝ × ℝ) → ℝ) (hmE : ∀ i, Measurable (E i)) (hpE : ∀ i lam, 0 ≤ E i lam)
    (hfE : ∀ i, (∫⁻ lam, wL θ lam*ENNReal.ofReal (E i lam)) < ⊤)
    (hbR : ∀ i, ∀ᵐ lam : ℝ × ℝ, ∀ z β γ,
      ‖R i lam β γ z‖ ≤ P i*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ j‖)))*E i lam) :
    Fourier.mixedFourierNorm θ J 0
      (treeRootLeafMixture f S (fun t u => unitSquareCutoff t *
        pairedInverseProfile (fun lam => ∑ i, c i*treeNormalizedScalar hX (R i) S lam u) t)) ≤
      (ENNReal.ofReal (rootLocalOverlapConstant d) *
        (ENNReal.ofReal (treeRootLeafDerivativeConstant d J) *
          (ENNReal.ofReal (Ccover^(X.treeLinks (G.sig 0)).length) *
            ENNReal.ofReal (leafMomentLocalizationConstant d (J+1) M *
              treeAugmentedInputBound d K M Binput)^(Fintype.card (TPlus G)+1)))) *
        (ENNReal.ofReal (2^θ)*Fourier.timeFourierNorm θ unitSquareCutoff*
          ∑ i, ENNReal.ofReal (P i*treeSpectralFrequencyLoss X (G.sig 0)) *
            ∫⁻ lam, wL θ lam*ENNReal.ofReal (E i lam)) := by
  classical
  let B := fun lam => ∑ i, ENNReal.ofReal (P i*treeSpectralFrequencyLoss X (G.sig 0))*ENNReal.ofReal (E i lam)
  have hmB : Measurable B := Finset.measurable_sum _ (fun i _ =>
    measurable_const.mul (ENNReal.measurable_ofReal.comp (hmE i)))
  have he : (∫⁻ lam, wL θ lam*B lam) =
      ∑ i, ENNReal.ofReal (P i*treeSpectralFrequencyLoss X (G.sig 0))*
        ∫⁻ lam, wL θ lam*ENNReal.ofReal (E i lam) := by
    simp only [B,Finset.mul_sum]
    rw [lintegral_finsetSum (f := fun i lam => wL θ lam *
      (ENNReal.ofReal (P i*treeSpectralFrequencyLoss X (G.sig 0))*ENNReal.ofReal (E i lam)))
      Finset.univ (fun i _ => (measurable_wL θ).mul
      (measurable_const.mul (ENNReal.measurable_ofReal.comp (hmE i))))]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [mul_left_comm (wL θ _) (ENNReal.ofReal (P i*treeSpectralFrequencyLoss X (G.sig 0)))]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hfB : (∫⁻ lam, wL θ lam*B lam) < ⊤ := by
    rw [he]
    exact ENNReal.sum_lt_top.mpr (fun i _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfE i))
  have hmA : StronglyMeasurable (Function.uncurry (fun lam u =>
      ∑ i, c i*treeNormalizedScalar hX (R i) S lam u)) :=
    Finset.stronglyMeasurable_fun_sum _ (fun i _ =>
      (stronglyMeasurable_treeNormalizedScalar hX (R i) (hR i) S).const_mul (c i))
  have hbA (u) : ∀ᵐ lam : ℝ × ℝ, ‖∑ i, c i*treeNormalizedScalar hX (R i) S lam u‖ₑ ≤ B lam := by
    have hall := (ae_all_iff.mpr hbR)
    filter_upwards [hall] with lam hlam
    apply (enorm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [enorm_mul,← ofReal_norm (c i)]
    have hci : ENNReal.ofReal ‖c i‖ ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal (hc i)
    apply (mul_le_mul' hci le_rfl).trans
    rw [one_mul,← ofReal_norm]
    have hh := ENNReal.ofReal_le_ofReal
      (treeNormalizedScalar_norm_le hX (R i) S (hP i) (hpE i lam) lam (hlam i) u)
    simpa only [ENNReal.ofReal_mul (mul_nonneg (hP i)
      (zero_le_one.trans (one_le_treeSpectralFrequencyLoss X (G.sig 0))))] using hh
  have hh := mixedFourierNorm_treeRootPairedProfile_le hθ f hK hM hBinput hf S hS
    (fun lam u => ∑ i, c i*treeNormalizedScalar hX (R i) S lam u) hmA hmB hbA hfB
  rw [he] at hh
  exact hh

end WaveTurbulence.RegAsymp
