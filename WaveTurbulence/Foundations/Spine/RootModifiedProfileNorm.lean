/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafCoordinateWord
/-! The exact input profiles in the root-weight kernel identity satisfy the producer seminorm premises. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

theorem SNormR_rootModifiedProfile_bound {w d A B m : ℕ} (hd : 1 ≤ d)
    (G : Garden w) (hp : G.IsPlain) (H : LeafProfiles w d)
    (c : RootWeightChoices G d m) (l : ActualInputLeaves G)
    (hf : ContDiff ℝ A (fun x => (H l.1.1 x : ℂ))) (C : ℝ) (hC : 0 ≤ C)
    (hF : SNormR A (B + 4 * m) (H l.1.1) ≤ ENNReal.ofReal C) :
    SNormR A B (rootModifiedProfiles G hp H c l.1.1) ≤
      ENNReal.ofReal ((((2 : ℝ) ^ A * (d : ℝ) ^ A) ^ (4 * m)) * C) := by
  let word := selectedCoordinateWord (rootCoordinateSlots G hp c) l
  have hlen : word.length ≤ 4 * m := root_coordinate_word_length G hp c l
  have hlow : SNorm A (B + word.length) (fun x => (H l.1.1 x : ℂ)) ≤ ENNReal.ofReal C :=
    SNorm_mono_bound le_rfl (Nat.add_le_add_left hlen B) _ hf C hC hF
  have hb := SNorm_coordinateWord_mul hd word (fun x => (H l.1.1 x : ℂ)) hf C hC hlow
  have he : (fun x => (rootModifiedProfiles G hp H c l.1.1 x : ℂ)) =
      (fun x => coordinateWord word x * (H l.1.1 x : ℂ)) := by
    funext x
    rw [rootModifiedProfiles_input]
    unfold monomialLeafProfile
    rw [← selectedCoordinateWord_prod, coordinateWord_eq_ofReal, Complex.ofReal_mul]
    exact mul_comm _ _
  unfold SNormR
  rw [he]
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hK : (1 : ℝ) ≤ 2 ^ A * (d : ℝ) ^ A :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hd1)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK hlen) hC

end WaveTurbulence.LGSpine
