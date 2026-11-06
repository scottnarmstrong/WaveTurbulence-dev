/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceCountingData
public import Mathlib.Data.Int.Log
/-! Literal source dyadic scales with symmetric fixed-constant comparability at interval endpoints. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set Finset

 theorem exists_source_dyadic_scale {a b r : ℝ} (ha : 0 < a) (hab : 2 * a ≤ b)
    (har : a ≤ r) (hrb : r ≤ b) :
    ∃ P : ℝ, SourceVine.IsDyadicScale P ∧ a ≤ P ∧ P ≤ b ∧ P / 2 ≤ r ∧ r ≤ 2 * P := by
  have hr : 0 < r := ha.trans_le har
  let z := Int.log 2 r
  let Q : ℝ := (2 : ℝ) ^ z
  have hQ : 0 < Q := zpow_pos (by norm_num) _
  have hQr : Q ≤ r := Int.zpow_log_le_self (by norm_num) hr
  have hrQ : r < 2 * Q := by
    have hh : r < (2 : ℝ) ^ (Int.log 2 r + 1) := Int.lt_zpow_succ_log_self (by norm_num : 1 < (2 : ℕ)) r
    rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)] at hh
    simpa only [Q, z, mul_comm] using hh
  by_cases haQ : a ≤ Q
  · exact ⟨Q, ⟨z, rfl⟩, haQ, hQr.trans hrb, by linarith, hrQ.le⟩
  · refine ⟨2 * Q, ⟨z + 1, ?_⟩, ?_, ?_, ?_, ?_⟩
    · rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      exact mul_comm _ _
    · exact har.trans hrQ.le
    · linarith [lt_of_not_ge haQ]
    · linarith
    · linarith

 theorem finite_source_dyadic_scales {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    {P : ℝ | SourceVine.IsDyadicScale P ∧ a ≤ P ∧ P ≤ b}.Finite := by
  have hfin := (Set.finite_Icc (Int.clog 2 a) (Int.log 2 b)).image (fun z : ℤ => (2 : ℝ) ^ z)
  apply hfin.subset
  rintro P ⟨⟨z, rfl⟩, hlow, hhigh⟩
  refine ⟨z, ?_, rfl⟩
  exact ⟨(Int.le_zpow_iff_clog_le (by norm_num) ha).mp hlow,
    (Int.zpow_le_iff_le_log (by norm_num) hb).mp hhigh⟩

end WaveTurbulence.LGSpine
