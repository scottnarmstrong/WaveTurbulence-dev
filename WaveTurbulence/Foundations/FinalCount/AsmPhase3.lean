/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPot3
public import WaveTurbulence.Foundations.FinalCount.AsmRun3
/-! **FINALCOUNT-ASSEMBLY, phase 3: nodes, classes and per-node facts of the `SG`-cut phase.**
A node of `h` is `(v, x₁, x₂, z, b, a, sgb)`: the cut data (fresh name canonical), the dyadic label `R = 2^z`, `kp = 50` iff `b`, and, for
`b`, the alive record `a` carrying the earlier cut `q` and the sign.  Its class is the set of `κ ∈ A` for which the step data are valid
(`UStep3` is then uniform).  `AliveHit` is the DEAD-HIT named input in `κ`-form. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- One uniform-in-nothing step of any kind for a fixed decoration. -/
def HAny (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h h' : HSt V D₀) : Prop :=
  HStep1 L γ η w κ h h' ∨ HStep2 L γ η w κ h h' ∨ HStep3 L γ η w κ h h' ∨ HStep4 L w κ h h'

/-- `ι ≠ 0` through a cut that is still carried by a present atom. -/
def IotaAlive (L η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) (p : D₀ × D₀) (R : ℝ) : Prop :=
  ∃ q ∈ h.hist, (∃ a ∈ h.s.M.atoms, ∃ vis, h.crec a = some (q, vis)) ∧ ∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧
    0 < ‖pgap L w κ p + sg • pgap L w κ q‖ ∧ ‖pgap L w κ p + sg • pgap L w κ q‖ ≤ L ^ (-50 * η) * R

/-- **DEAD-HIT is a theorem** (R38(4)): a hit through `h.alive` is a hit through an alive cut. -/
theorem iotaAlive_of_hit {L η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {h : HSt V D₀} {p : D₀ × D₀} {R : ℝ}
    (hh : IotaHit L η w κ h.alive p R) : IotaAlive L η w κ h p R := by
  obtain ⟨q, hq, sg, hsg, h1, h2⟩ := hh
  obtain ⟨hq1, hq2⟩ := HSt.mem_alive.1 hq
  exact ⟨q, hq1, hq2, sg, hsg, h1, h2⟩

/-- The class invariant of the cover (phases 1-3). -/
def Inv3 (M₀ : Molecule V D₀) (Rn : ℕ) (Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop) (L : ℝ) (w : Mom d)
    (A0 A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) : Prop :=
  A ⊆ A0 ∧ (A = ∅ ∨ (UCtx M₀ Rn (fun k => k ∈ A) L w h ∧ ApPos h.s ∧ ∀ κ ∈ A, Rch κ h))

theorem Inv3.mono {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L : ℝ} {w : Mom d} {A0 A B : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀}
    (hA : Inv3 M₀ Rn Rch L w A0 A h) (hB : B ⊆ A) : Inv3 M₀ Rn Rch L w A0 B h := by
  refine ⟨hB.trans hA.1, ?_⟩
  by_cases hBe : B = ∅
  · exact Or.inl hBe
  · right
    rcases hA.2 with he | ⟨hc, hap, hr⟩
    · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hB)) hBe
    · exact ⟨uctx_mono hc fun k hk => hB hk, hap, fun κ hκ => hr κ (hB hκ)⟩

/-- The dyadic labels have exponents in `[-⌈2 log L⌉, 0]`. -/
theorem label_zrange {L γ η : ℝ} (hL : Real.exp 1 ≤ L) (hη : η ≤ γ) {R : ℝ} (hR : IsLabel L γ η R) :
    ∃ z : ℤ, R = (2 : ℝ) ^ z ∧ -(⌈2 * Real.log L⌉₊ : ℤ) ≤ z ∧ z ≤ 0 := by
  obtain ⟨⟨z, rfl⟩, hl, hu⟩ := hR
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hL
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) hL
  refine ⟨z, rfl, ?_, ?_⟩
  · -- 2^z ≥ 1/L
    have h2 : (1 : ℝ) < 2 := by norm_num
    have : (2 : ℝ) ^ (-z) ≤ L := by
      rw [zpow_neg]
      have hp : 0 < (2 : ℝ) ^ z := zpow_pos (by norm_num) z
      rw [inv_le_comm₀ hp hL0]; exact hl
    have hlog : ((-z : ℤ) : ℝ) * Real.log 2 ≤ Real.log L := by
      have := Real.log_le_log (zpow_pos (by norm_num) _) this
      rwa [Real.log_zpow] at this
    have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
    have hz : ((-z : ℤ) : ℝ) ≤ 2 * Real.log L := by
      by_cases hz0 : (0 : ℝ) ≤ ((-z : ℤ) : ℝ)
      · nlinarith
      · linarith
    have hc : (2 * Real.log L) ≤ (⌈2 * Real.log L⌉₊ : ℝ) := Nat.le_ceil _
    have : ((-z : ℤ) : ℝ) ≤ ((⌈2 * Real.log L⌉₊ : ℤ) : ℝ) := by push_cast at hz ⊢; linarith
    have := Int.cast_le.1 this
    omega
  · have hu' : (2 : ℝ) ^ z ≤ 1 := by
      refine hu.trans ?_
      refine Real.rpow_le_one_of_one_le_of_nonpos hL1 ?_
      linarith
    by_contra hz
    push Not at hz
    have : (1 : ℝ) < 2 ^ z := one_lt_zpow₀ (by norm_num) hz
    linarith

end WaveTurbulence.FinalCountAsm
