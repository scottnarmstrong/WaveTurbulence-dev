/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LeafFourierMomentMass
public import WaveTurbulence.Foundations.ApproxNT.Products
public import WaveTurbulence.Foundations.Incoh.WeightedSpectralMomentMass
public import WaveTurbulence.Foundations.Incoh.SpectralMomentContinuity

/-! # Root-weighted higher Fourier moments for independent leaf inputs -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh WithLp
open scoped ENNReal

/-- Paying a root weight in each center leaves the summable exponent M-W. -/
theorem tsum_weighted_leafFourierMomentMass_le {d K M W : ℕ} (J : ℕ)
    {f : Mom d → ℂ} {B : ℝ} (hK : d+1+J ≤ K) (hM : W+2*d ≤ M) (hB : 0 ≤ B)
    (hf : Fourier.spatialNorm K M f ≤ ENNReal.ofReal B) :
    (∑' c : Fin d → ℤ, ENNReal.ofReal (Fourier.momentumBracket (NTSP.intVec c)^W)*
      leafFourierMomentMass J f c) ≤
      ENNReal.ofReal (leafWeightedMomentLocalizationConstant d J M W*B) := by
  have hc (c : Fin d → ℤ) : leafFourierMomentMass J f c ≤
      ENNReal.ofReal (leafCellFourierMomentConstant d J M*B/
        Fourier.momentumBracket (NTSP.intVec c)^M) :=
    lintegral_enorm_spectralMomentProfile_leaf_le (n := 0) J (fun _ : Fin 1 => f)
      (fun _ : Fin 1 => c) hK hB (fun _ => hf) 0
  have hweighted (c : Fin d → ℤ) :
      ENNReal.ofReal (Fourier.momentumBracket (NTSP.intVec c)^W)*leafFourierMomentMass J f c ≤
      ENNReal.ofReal (leafCellFourierMomentConstant d J M*B/
        Fourier.momentumBracket (NTSP.intVec c)^(M-W)) := by
    apply (mul_le_mul' le_rfl (hc c)).trans_eq
    rw [← ENNReal.ofReal_mul (pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) W)]
    congr 1
    have hp : 0 < Fourier.momentumBracket (NTSP.intVec c) :=
      zero_lt_one.trans_le (one_le_momentumBracket _)
    have he : Fourier.momentumBracket (NTSP.intVec c)^M =
        Fourier.momentumBracket (NTSP.intVec c)^W * Fourier.momentumBracket (NTSP.intVec c)^(M-W) := by
      rw [← pow_add]
      congr 1
      omega
    rw [he]
    field_simp
  apply (ENNReal.tsum_le_tsum hweighted).trans_eq
  rw [tsum_ofReal_div_momentumBracket_intVec (by omega : 2*d ≤ M-W)
    (mul_nonneg (leafCellFourierMomentConstant_nonneg d J M) hB)]
  congr 1
  unfold leafWeightedMomentLocalizationConstant
  ring

/-- The full leaf-only higher-moment mass is geometric after every center
has paid its share of the root weight. Individual inputs remain separate. -/
theorem tsum_weighted_leafMoment_product_le {d m K M W : ℕ} (J : ℕ)
    (f : Fin m → Mom d → ℂ) {B : ℝ} (hK : d+1+J ≤ K) (hM : W+2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) :
    (∑' c : Fin m → Fin d → ℤ,
      ENNReal.ofReal (∏ a, Fourier.momentumBracket (NTSP.intVec (c a))^W)*
        ∫⁻ α : Fin m → Fin d → ℝ, ∏ a,
          ‖((((1+‖toLp 2 (α a)‖)^J:ℝ):ℂ)*
            Fourier.timeFourier (fun y : Fin d → ℝ => leafCell (f a) (c a) (toLp 2 y)) (α a))‖ₑ) ≤
      ENNReal.ofReal (leafWeightedMomentLocalizationConstant d J M W*B)^m := by
  have hmeas (a : Fin m) (c : Fin d → ℤ) :
      Measurable (fun ξ : Fin d → ℝ => ‖((((1+‖toLp 2 ξ‖)^J:ℝ):ℂ)*
        Fourier.timeFourier (fun y : Fin d → ℝ => leafCell (f a) c (toLp 2 y)) ξ)‖ₑ) :=
    (continuous_spectralMomentProfile (n := 0) J (fun _ : Fin 1 => f a)
      (fun _ : Fin 1 => c) (by omega : d+1 ≤ K) hB (fun _ => hf a) (.inl 0)).measurable.enorm
  calc
    _ = ∑' c : Fin m → Fin d → ℤ, ∏ a,
        ENNReal.ofReal (Fourier.momentumBracket (NTSP.intVec (c a))^W)*
          leafFourierMomentMass J (f a) (c a) := by
      apply tsum_congr
      intro c
      have hi : (∫⁻ α : Fin m → Fin d → ℝ, ∏ a,
          ‖((((1+‖toLp 2 (α a)‖)^J:ℝ):ℂ)*
            Fourier.timeFourier (fun y : Fin d → ℝ => leafCell (f a) (c a) (toLp 2 y)) (α a))‖ₑ) =
          ∏ a, leafFourierMomentMass J (f a) (c a) :=
        ApproxNT.lintegral_fintype_prod_eq_prod (μ := volume)
          (fun (a : Fin m) (ξ : Fin d → ℝ) => ‖((((1+‖toLp 2 ξ‖)^J:ℝ):ℂ)*
            Fourier.timeFourier (fun y : Fin d → ℝ => leafCell (f a) (c a) (toLp 2 y)) ξ)‖ₑ)
          (fun a => hmeas a (c a))
      rw [hi,ENNReal.ofReal_prod_of_nonneg (fun a _ => pow_nonneg (zero_le_one.trans (one_le_momentumBracket _)) W),
        ← Finset.prod_mul_distrib]
    _ = ∏ a : Fin m, ∑' c : Fin d → ℤ,
        ENNReal.ofReal (Fourier.momentumBracket (NTSP.intVec c)^W)*leafFourierMomentMass J (f a) c :=
      tsum_fin_product_ennreal m (fun (a : Fin m) (c : Fin d → ℤ) =>
        ENNReal.ofReal (Fourier.momentumBracket (NTSP.intVec c)^W)*leafFourierMomentMass J (f a) c)
    _ ≤ ∏ _a : Fin m, ENNReal.ofReal (leafWeightedMomentLocalizationConstant d J M W*B) :=
      Finset.prod_le_prod (fun a _ => tsum_weighted_leafFourierMomentMass_le J hK hM hB (hf a))
    _ = _ := by simp

end WaveTurbulence.RegAsymp
