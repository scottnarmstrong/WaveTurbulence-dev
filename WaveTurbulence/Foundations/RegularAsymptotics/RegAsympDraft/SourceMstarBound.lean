/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceMstarIdentification
public import WaveTurbulence.Foundations.RegAsymp.SpatialNormScalar

/-! # The required geometric spatial estimate for literal recursive Mstar -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Reg TTree

/-- DH23 Prop6.1: the literal recursive dominant-couple spatial factor has
full30d geometric control from the original finite40d input norm. The
constant is chosen before every code, placement, and logarithmic order
cutoff. The normalization is removed using its inverse of norm at most1. -/
theorem literal_Mstar_spatial_bound {d : ℕ} (hd : 3 ≤ d) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Q : RegCpl, Q.dominant = true → ∀ F : Mom d → ℝ,
      Fourier.spatialNorm (40*d) (40*d) (fun k => (F k:ℂ)) ≤ ENNReal.ofReal B →
      ∀ (w : ℕ) (Z : Finset (Fin w × Path)) (a b : Fin w × Path), Indep a b →
      IsSpecialSet (Q.linksAt a b) Z →
      Fourier.spatialNorm (30*d) (30*d) (fun k => (Q.Mstar F Z a b k:ℂ)) ≤
        ENNReal.ofReal (C*C^Q.links.length) := by
  obtain ⟨C,hC,hbound⟩ := realCplFold_spatial_bound hd hB
  refine ⟨C,hC,?_⟩
  intro Q hdom F hF w Z a b hab hZ
  let m := (Q.linksAt a b).length
  have hpow : (2:ℂ)^m ≠ 0 := pow_ne_zero _ (by norm_num)
  have he : (fun k => (Q.Mstar F Z a b k:ℂ)) =
      (fun k => ((2:ℂ)^m)⁻¹*(realCplFold F Q Z a b k:ℂ)) := by
    funext k
    have hi := congrArg Complex.ofReal (realCplFold_eq_Mstar hd hB hF Q hdom Z a b hab
      (fun z _ hz => hZ z hz) k)
    simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat] at hi
    rw [hi]
    change (Q.Mstar F Z a b k:ℂ) = ((2:ℂ)^m)⁻¹*((2:ℂ)^m*(Q.Mstar F Z a b k:ℂ))
    rw [← mul_assoc,inv_mul_cancel₀ hpow,one_mul]
  have hc : ‖((2:ℂ)^m)⁻¹‖ ≤ 1 := by
    rw [norm_inv,norm_pow,show ‖(2:ℂ)‖ = 2 by norm_num]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hg : 0 ≤ C*C^Q.links.length :=
    mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hC) _)
  rw [he]
  apply (spatialNorm_const_mul_le (by omega) hg (hbound Q F hF w Z a b hab) _).trans
  apply ENNReal.ofReal_le_ofReal
  exact (mul_le_mul_of_nonneg_right hc hg).trans_eq (one_mul _)

end WaveTurbulence.RegAsymp
