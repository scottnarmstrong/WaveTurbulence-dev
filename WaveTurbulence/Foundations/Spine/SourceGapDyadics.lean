/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceDyadicScales
public import WaveTurbulence.Foundations.Spine.GapLatticeLowerBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-! Cover the literal nonzero lattice gaps by the source dyadic scale ranges. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set Filter

 theorem source_gapKind_eq_small_iff {d : ℕ} (L γ η : ℝ) (r : Mom d) :
    Molecule.gapKind L γ η r = .SG ↔ r ≠ 0 ∧ ‖r‖ ≤ L ^ (-γ + η) := by
  unfold Molecule.gapKind
  split_ifs <;> simp_all

 theorem exists_small_gap_scale {D : Type*} {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ η : ℝ) (hcap : 2 * L⁻¹ ≤ L ^ (-γ + η)) (base : Mom d) (κ : D → (Fin d → ℤ))
    (x y : D) (hgap : Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) = .SG) :
    ∃ Q : ℝ, SourceVine.IsDyadicScale Q ∧ L⁻¹ ≤ Q ∧ Q ≤ L ^ (-γ + η) ∧
      Q / 2 ≤ ‖Molecule.gapAt L base κ x y‖ ∧ ‖Molecule.gapAt L base κ x y‖ ≤ 2 * Q := by
  obtain ⟨hne, hbound⟩ := (source_gapKind_eq_small_iff L γ η _).mp hgap
  exact exists_source_dyadic_scale (inv_pos.mpr hL) hcap
    (inv_scale_le_norm_gap hL base κ x y hne) hbound

private theorem exists_source_dyadic_scale_lt {a b r : ℝ} (ha : 0 < a) (hab : 2 * a ≤ b)
    (har : a ≤ r) (hrb : r < b) :
    ∃ P : ℝ, SourceVine.IsDyadicScale P ∧ a ≤ P ∧ P < b ∧ P / 2 ≤ r ∧ r ≤ 2 * P := by
  have hr : 0 < r := ha.trans_le har
  let z := Int.log 2 r
  let Q : ℝ := (2 : ℝ) ^ z
  have hQr : Q ≤ r := Int.zpow_log_le_self (by norm_num) hr
  have hrQ : r < 2 * Q := by
    have hh : r < (2 : ℝ) ^ (Int.log 2 r + 1) := Int.lt_zpow_succ_log_self (by norm_num : 1 < (2 : ℕ)) r
    rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)] at hh
    simpa only [Q, z, mul_comm] using hh
  by_cases haQ : a ≤ Q
  · exact ⟨Q, ⟨z, rfl⟩, haQ, hQr.trans_lt hrb, by linarith, hrQ.le⟩
  · refine ⟨2 * Q, ⟨z + 1, ?_⟩, har.trans hrQ.le, ?_, ?_, ?_⟩
    · rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      exact mul_comm _ _
    · linarith [lt_of_not_ge haQ]
    · linarith
    · linarith

 theorem exists_ladder_gap_scale {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) {d m : ℕ} {L : ℝ} (hL : 2 ≤ L) (base : Mom d)
    (κ : D → (Fin d → ℤ)) (u v : Fin (m + 1) → V) (hm : 1 ≤ m) (r : Mom d)
    (hr : M.IsLadderGap L base κ u v hm r) :
    ∃ P : ℝ, (P = 0 ∨ (SourceVine.IsDyadicScale P ∧ L⁻¹ ≤ P ∧ P ≤ 1)) ∧
      (P = 0 → r = 0) ∧ (0 < P → P < 1 → P / 2 ≤ ‖r‖ ∧ ‖r‖ ≤ 2 * P) ∧
      (P = 1 → 1 ≤ ‖r‖) := by
  have hL0 : 0 < L := by linarith
  by_cases hz : r = 0
  · exact ⟨0, Or.inl rfl, fun _ => hz, by simp, by norm_num⟩
  by_cases hone : 1 ≤ ‖r‖
  · refine ⟨1, Or.inr ⟨⟨0, by simp⟩, ?_, le_rfl⟩, by norm_num, by norm_num, fun _ => hone⟩
    exact (inv_le_one₀ hL0).mpr (by linarith)
  obtain ⟨x, y, _, _, _, _, hreq⟩ := hr
  have hlow : L⁻¹ ≤ ‖r‖ := by
    rw [hreq]
    exact inv_scale_le_norm_gap hL0 base κ x y (by rwa [← hreq])
  have hcap : 2 * L⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_iff₀ hL0).mpr (by simpa only [one_mul] using hL)
  obtain ⟨P, hdy, hPa, hPb, hPr, hrP⟩ := exists_source_dyadic_scale_lt (inv_pos.mpr hL0) hcap hlow (lt_of_not_ge hone)
  have hP0 : 0 < P := (inv_pos.mpr hL0).trans_le hPa
  exact ⟨P, Or.inr ⟨hdy, hPa, hPb.le⟩, (fun he => (hP0.ne' he).elim),
    (fun _ _ => ⟨hPr, hrP⟩), (fun he => (hPb.ne he).elim)⟩

end WaveTurbulence.LGSpine
