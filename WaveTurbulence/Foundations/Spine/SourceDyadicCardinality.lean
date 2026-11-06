/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceDyadicScales
/-! Exact finite integer encoding of source dyadic scale choices. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set Finset

private theorem int_log_two_zpow (z : ℤ) : Int.log 2 ((2 : ℝ) ^ z) = z :=
  Int.log_zpow (by norm_num : 1 < (2 : ℕ)) z

noncomputable def sourceDyadicScaleEquiv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    {P : ℝ // SourceVine.IsDyadicScale P ∧ a ≤ P ∧ P ≤ b} ≃
      {z : ℤ // Int.clog 2 a ≤ z ∧ z ≤ Int.log 2 b} where
  toFun P := ⟨Int.log 2 P.1, by
    obtain ⟨z, hz⟩ := P.2.1
    rw [hz, int_log_two_zpow]
    exact ⟨(Int.le_zpow_iff_clog_le (by norm_num) ha).mp (hz ▸ P.2.2.1),
      (Int.zpow_le_iff_le_log (by norm_num) hb).mp (hz ▸ P.2.2.2)⟩⟩
  invFun z := ⟨(2 : ℝ) ^ z.1, ⟨z.1, rfl⟩,
    (Int.le_zpow_iff_clog_le (by norm_num) ha).mpr z.2.1,
    (Int.zpow_le_iff_le_log (by norm_num) hb).mpr z.2.2⟩
  left_inv P := by
    apply Subtype.ext
    obtain ⟨z, hz⟩ := P.2.1
    change (2 : ℝ) ^ Int.log 2 P.1 = P.1
    rw [hz, int_log_two_zpow]
  right_inv z := by
    apply Subtype.ext
    change Int.log 2 ((2 : ℝ) ^ z.1) = z.1
    exact int_log_two_zpow z.1

 theorem card_sourceDyadicScales {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Nat.card {P : ℝ // SourceVine.IsDyadicScale P ∧ a ≤ P ∧ P ≤ b} =
      (Finset.Icc (Int.clog 2 a) (Int.log 2 b)).card := by
  rw [Nat.card_congr (sourceDyadicScaleEquiv ha hb)]
  simpa only [Finset.mem_Icc] using Nat.card_eq_finsetCard (Finset.Icc (Int.clog 2 a) (Int.log 2 b))

end WaveTurbulence.LGSpine
