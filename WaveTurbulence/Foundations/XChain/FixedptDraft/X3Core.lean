/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3LjDiff

/-!
# X3: the deterministic core of `fixedpoint` (T L2316, L2333–L2338)

`fixedpoint_core` gives clauses 3–6 of B1.3 `fixedpoint` for one fixed sample. It assumes:
- a bound `α · w` on `a^tr` over `[p, p+1]` (clause 1 gives `α = e^{3N}`);
- a bound `ε₀ · w` on `ℒ₀` (clause 2 gives `ε₀ = e^{-20N}`);
- the operator bounds `‖𝒴‖, ‖𝒲‖ ≤ 1/2` and `‖𝒳‖ ≤ M` on `Z` (fixedest3);
- the numerical conditions `2M ≤ κ`,
  `κ (ε₀ + 3Kρ²α + Kρ³) ≤ ρ` and `κ (6Kρα + 3Kρ²) ≤ 1/2`, with `K = triK`.

The proof:
- `parametrix_invert`, with `A = 1 − ℒ₁` and the FLOWER identities `(1−ℒ₁)𝒳 = 1−𝒴`, `𝒳(1−ℒ₁) = 1−𝒲`;
- `norm_Lop_le` for the existence clause;
- `norm_Lop_sub_le` for the contraction (`ℒ₀` does not depend on `b`, `L0_eq`).
-/

@[expose] public section

namespace WaveTurbulence.Fixedpt

open MeasureTheory Set SysAPI
open scoped ENNReal

variable (L γ δ : ℝ) {d : ℕ}

/-! ## `Z` and good inputs -/

section Good

variable {p : ℕ} {Λ : ℝ}

theorem summable_wt (hL1 : 1 ≤ L) (hΛ : (d : ℝ) + 1 ≤ Λ) : Summable fun k : Fin d → ℤ => wt L Λ k :=
  Summable.of_nonneg_of_le (fun k => (wt_pos L Λ k).le) (wt_le hΛ) (summable_jbr_rpow_neg hL1)

theorem good_of_mem_ZSpace (hL1 : 1 ≤ L) (hΛ : (d : ℝ) + 1 ≤ Λ) {b : ArrI p d} (hb : b ∈ ZSpace L Λ p) :
    Good p b :=
  ⟨hb.1, ⟨fun k => (ZNorm L Λ b).toReal * wt L Λ k, (summable_wt L hL1 hΛ).mul_left _,
    fun k => mul_nonneg ENNReal.toReal_nonneg (wt_pos L Λ k).le,
    fun t n => (norm_le_of_mem_ZSpace hb t n).trans (le_of_eq (mul_comm _ _))⟩⟩

theorem ZNorm_le_of_wt {f : ArrI p d} {C : ℝ} (hf : ∀ t n, ‖f t n‖ ≤ C * wt L Λ n) :
    ZNorm L Λ f ≤ ENNReal.ofReal C :=
  ZNorm_le_of_decay L Λ C fun t n => (hf t n).trans (le_of_eq (mul_comm _ _))

theorem toReal_ZNorm_le {f : ArrI p d} {ρ : ℝ} (hρ : 0 ≤ ρ) (hf : ZNorm L Λ f ≤ ENNReal.ofReal ρ) :
    (ZNorm L Λ f).toReal ≤ ρ :=
  ENNReal.toReal_le_of_le_ofReal hρ hf

end Good

/-! ## `ℒ_j` on `Z` -/

section LjOp

variable {p : ℕ} (Ntr : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖) {Λ : ℝ}

/-- `ℒ_j` as an operator on arrays over `[p, p+1]` (the `ℒ` of B1.3). -/
noncomputable def LjOp (p Ntr : ℕ) (aP : (Fin d → ℤ) → ℂ) (j : ℕ) (b : ArrI p d) : ArrI p d :=
  fun t n => Lop L γ δ p Ntr aP j b t n

theorem L1op_eq_LjOp (b : ArrI p d) : L1op L γ δ p Ntr aP b = LjOp L γ δ p Ntr aP 1 b := rfl

include haP in
theorem continuous_Lop (hL : 0 < L) (hΛ : (d : ℝ) + 1 ≤ Λ) {b : ArrI p d} (hb : b ∈ ZSpace L Λ p) (j : ℕ)
    (n : Fin d → ℤ) : Continuous fun t : Icc (p : ℝ) (p + 1) => Lop L γ δ p Ntr aP j b t n := by
  have hI := fun t => intervalIntegrable_slotSum L γ δ Ntr haP hΛ hL hb j t n
  have hc : Continuous fun t : ℝ => Lop L γ δ p Ntr aP j b t n := by
    simp_rw [Lop_eq_integral L γ δ Ntr haP hb hΛ hL j]
    exact intervalIntegral.continuous_primitive (fun a c => (hI a).symm.trans (hI c)) _
  exact hc.comp continuous_subtype_val

include haP in
theorem LjOp_mem (hL1 : 1 ≤ L) (hΛ : (d : ℝ) + 1 ≤ Λ) {b : ArrI p d} (hb : b ∈ ZSpace L Λ p) (j : ℕ) {C : ℝ}
    (hC : ∀ (t : Icc (p : ℝ) (p + 1)) n, ‖Lop L γ δ p Ntr aP j b t n‖ ≤ C * wt L Λ n) :
    LjOp L γ δ p Ntr aP j b ∈ ZSpace L Λ p :=
  ⟨fun n => continuous_Lop L γ δ Ntr haP (by linarith) hΛ hb j n,
    (ZNorm_le_of_wt L hC).trans_lt ENNReal.ofReal_lt_top⟩

theorem fOp_sub (p : ℕ) (haP : Summable fun k => ‖aP k‖) {b b' : ArrI p d} (hb : Good p b) (hb' : Good p b')
    (F : FTree) : fOp L γ δ p aP F (b - b') = fOp L γ δ p aP F b - fOp L γ δ p aP F b' := by
  simp only [sub_eq_add_neg]
  rw [fOp_add L γ δ p haP hb hb'.neg, fOp_neg]

include haP in
theorem L1op_sub {b b' : ArrI p d} (hb : Good p b) (hb' : Good p b') :
    L1op L γ δ p Ntr aP (b - b') = L1op L γ δ p Ntr aP b - L1op L γ δ p Ntr aP b' := by
  rw [L1op_eq L γ δ p Ntr haP (hb.sub hb'), L1op_eq L γ δ p Ntr haP hb, L1op_eq L γ δ p Ntr haP hb',
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => fOp_sub L γ δ p haP hb hb' _

include haP in
theorem Yop_sub {b b' : ArrI p d} (hb : Good p b) (hb' : Good p b') :
    Yop L γ δ p Ntr aP (b - b') = Yop L γ δ p Ntr aP b - Yop L γ δ p Ntr aP b' := by
  unfold Yop
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => fOp_sub L γ δ p haP hb hb' _

theorem good_Yop (haP : Summable fun k => ‖aP k‖) {b : ArrI p d} (hb : Good p b) :
    Good p (Yop L γ δ p Ntr aP b) := by
  unfold Yop
  exact Good.sum _ fun x _ => good_fOp L γ δ p haP hb _

include haP in
theorem L0_indep (hL : 0 < L) (b b' : ArrI p d) :
    LjOp L γ δ p Ntr aP 0 b = LjOp L γ δ p Ntr aP 0 b' := by
  funext t n
  unfold LjOp
  rw [L0_eq L γ δ hL p Ntr haP b t n, L0_eq L γ δ hL p Ntr haP b' t n]

end LjOp

/-! ## The core -/

section Core

variable {p : ℕ} (Ntr : ℕ) {aP : (Fin d → ℤ) → ℂ} (haP : Summable fun k => ‖aP k‖) {Λ : ℝ}

include haP in
/-- **Clauses 3–6 of `fixedpoint` for one sample** (T L2316, L2333–L2338). -/
theorem fixedpoint_core (hL1 : 1 ≤ L) (hΛ : (d : ℝ) + 1 ≤ Λ) {α ε₀ ρ κ : ℝ} (hα0 : 0 ≤ α) (hρ : 0 ≤ ρ)
    (hκ : 0 ≤ κ)
    (hα : ∀ s ∈ Icc (p : ℝ) (p + 1), ∀ k, ‖aTr L γ δ p Ntr aP s k‖ ≤ α * wt L Λ k)
    (h0 : ∀ (b : ArrI p d) (t : Icc (p : ℝ) (p + 1)) n, ‖Lop L γ δ p Ntr aP 0 b t n‖ ≤ ε₀ * wt L Λ n)
    (M : ℝ≥0∞) (hM : 2 * M ≤ ENNReal.ofReal κ)
    (hX : ∀ b ∈ ZSpace L Λ p, ZNorm L Λ (Xop L γ δ p Ntr aP b) ≤ M * ZNorm L Λ b)
    (hY : ∀ b ∈ ZSpace L Λ p, ZNorm L Λ (Yop L γ δ p Ntr aP b) ≤ 2⁻¹ * ZNorm L Λ b)
    (hW : ∀ b ∈ ZSpace L Λ p, ZNorm L Λ (Wop L γ δ p Ntr aP b) ≤ 2⁻¹ * ZNorm L Λ b)
    (hsmall : κ * (ε₀ + 3 * triK d L γ δ Λ * ρ ^ 2 * α + triK d L γ δ Λ * ρ ^ 3) ≤ ρ)
    (hcontr : κ * (6 * triK d L γ δ Λ * ρ * α + 3 * triK d L γ δ Λ * ρ ^ 2) ≤ 2⁻¹) :
    (∀ b ∈ ZSpace L Λ p, b - LjOp L γ δ p Ntr aP 1 b ∈ ZSpace L Λ p) ∧
    (∀ c ∈ ZSpace L Λ p, ∃! b, b ∈ ZSpace L Λ p ∧ b - LjOp L γ δ p Ntr aP 1 b = c) ∧
    (∀ b ∈ ZSpace L Λ p, ZNorm L Λ b ≤ ENNReal.ofReal κ * ZNorm L Λ (b - LjOp L γ δ p Ntr aP 1 b)) ∧
    (∀ b ∈ ZSpace L Λ p, ZNorm L Λ b ≤ ENNReal.ofReal ρ →
      ∃ c ∈ ZSpace L Λ p, c - LjOp L γ δ p Ntr aP 1 c =
        LjOp L γ δ p Ntr aP 0 b + LjOp L γ δ p Ntr aP 2 b + LjOp L γ δ p Ntr aP 3 b ∧
        ZNorm L Λ c ≤ ENNReal.ofReal ρ) ∧
    (∀ b ∈ ZSpace L Λ p, ∀ b' ∈ ZSpace L Λ p, ∀ c ∈ ZSpace L Λ p, ∀ c' ∈ ZSpace L Λ p,
      ZNorm L Λ b ≤ ENNReal.ofReal ρ → ZNorm L Λ b' ≤ ENNReal.ofReal ρ →
      c - LjOp L γ δ p Ntr aP 1 c =
        LjOp L γ δ p Ntr aP 0 b + LjOp L γ δ p Ntr aP 2 b + LjOp L γ δ p Ntr aP 3 b →
      c' - LjOp L γ δ p Ntr aP 1 c' =
        LjOp L γ δ p Ntr aP 0 b' + LjOp L γ δ p Ntr aP 2 b' + LjOp L γ δ p Ntr aP 3 b' →
      ZNorm L Λ (c - c') ≤ 2⁻¹ * ZNorm L Λ (b - b')) := by
  have hL : 0 < L := by linarith
  set K := triK d L γ δ Λ with hKdef
  have hK : 0 ≤ K := triK_nonneg L γ δ
  have hMtop : M < ⊤ :=
    lt_of_le_of_lt (le_mul_of_one_le_left' (by norm_num)) (hM.trans_lt ENNReal.ofReal_lt_top)
  have hgood := fun b (hb : b ∈ ZSpace L Λ p) => good_of_mem_ZSpace L hL1 hΛ hb
  -- `ℒ_j` maps `Z` to `Z`
  have hLb : ∀ b ∈ ZSpace L Λ p, ∀ (t : Icc (p : ℝ) (p + 1)) n,
      ‖Lop L γ δ p Ntr aP 1 b t n‖ ≤ 3 * (K * ((ZNorm L Λ b).toReal * α * α)) * wt L Λ n ∧
      ‖Lop L γ δ p Ntr aP 2 b t n‖ ≤
        3 * (K * ((ZNorm L Λ b).toReal * (ZNorm L Λ b).toReal * α)) * wt L Λ n ∧
      ‖Lop L γ δ p Ntr aP 3 b t n‖ ≤
        K * ((ZNorm L Λ b).toReal * (ZNorm L Λ b).toReal * (ZNorm L Λ b).toReal) * wt L Λ n :=
    fun b hb t n => norm_Lop_le L γ δ Ntr haP hb hΛ hL1 hα0 hα t.2 n
  have hmem1 : ∀ b ∈ ZSpace L Λ p, LjOp L γ δ p Ntr aP 1 b ∈ ZSpace L Λ p := fun b hb =>
    LjOp_mem L γ δ Ntr haP hL1 hΛ hb 1 fun t n => (hLb b hb t n).1
  have hmem0 : ∀ b ∈ ZSpace L Λ p, LjOp L γ δ p Ntr aP 0 b ∈ ZSpace L Λ p := fun b hb =>
    LjOp_mem L γ δ Ntr haP hL1 hΛ hb 0 (h0 b)
  have hmem2 : ∀ b ∈ ZSpace L Λ p, LjOp L γ δ p Ntr aP 2 b ∈ ZSpace L Λ p := fun b hb =>
    LjOp_mem L γ δ Ntr haP hL1 hΛ hb 2 fun t n => (hLb b hb t n).2.1
  have hmem3 : ∀ b ∈ ZSpace L Λ p, LjOp L γ δ p Ntr aP 3 b ∈ ZSpace L Λ p := fun b hb =>
    LjOp_mem L γ δ Ntr haP hL1 hΛ hb 3 fun t n => (hLb b hb t n).2.2
  -- the parametrix
  have hAZ : ∀ b ∈ ZSpace L Λ p, b - L1op L γ δ p Ntr aP b ∈ ZSpace L Λ p := fun b hb =>
    zSpace_sub hb (hmem1 b hb)
  have hXZ : ∀ b ∈ ZSpace L Λ p, Xop L γ δ p Ntr aP b ∈ ZSpace L Λ p := fun b hb =>
    ⟨(good_Xop L γ δ p Ntr haP (hgood b hb)).cont, (hX b hb).trans_lt (ENNReal.mul_lt_top hMtop hb.2)⟩
  have hYZ : ∀ b ∈ ZSpace L Λ p, Yop L γ δ p Ntr aP b ∈ ZSpace L Λ p := fun b hb =>
    ⟨(good_Yop L γ δ Ntr haP (hgood b hb)).cont,
      (hY b hb).trans_lt (ENNReal.mul_lt_top (by simp) hb.2)⟩
  have hAlin : ∀ b ∈ ZSpace L Λ p, ∀ b' ∈ ZSpace L Λ p,
      (b - L1op L γ δ p Ntr aP b) - (b' - L1op L γ δ p Ntr aP b') =
        (b - b') - L1op L γ δ p Ntr aP (b - b') := fun b hb b' hb' => by
    rw [L1op_sub L γ δ Ntr haP (hgood b hb) (hgood b' hb')]; abel
  obtain ⟨hbound, huniq⟩ := parametrix_invert (fun b => b - L1op L γ δ p Ntr aP b) (Xop L γ δ p Ntr aP)
    (Yop L γ δ p Ntr aP) (Wop L γ δ p Ntr aP) M hAZ hXZ hYZ
    (fun b hb => one_sub_L1op_Xop L γ δ p Ntr haP (hgood b hb))
    (fun b hb => Xop_one_sub_L1op L γ δ p Ntr haP (hgood b hb)) hAlin
    (fun b hb b' hb' => (Yop_sub L γ δ Ntr haP (hgood b hb) (hgood b' hb')).symm) hX hY hW
  have hbound' : ∀ b ∈ ZSpace L Λ p,
      ZNorm L Λ b ≤ ENNReal.ofReal κ * ZNorm L Λ (b - LjOp L γ δ p Ntr aP 1 b) := fun b hb =>
    by have h := hbound b hb; rw [L1op_eq_LjOp] at h; exact h.trans (by gcongr)
  refine ⟨hAZ, huniq, hbound', ?_, ?_⟩
  · -- existence of the solution with `‖c‖ ≤ ρ`
    intro b hb hbρ
    set β := (ZNorm L Λ b).toReal
    have hβ : 0 ≤ β := ENNReal.toReal_nonneg
    have hβρ : β ≤ ρ := toReal_ZNorm_le L hρ hbρ
    have hr := zSpace_add (zSpace_add (hmem0 b hb) (hmem2 b hb)) (hmem3 b hb)
    obtain ⟨c, ⟨hc, hcA⟩, -⟩ := huniq _ hr
    rw [L1op_eq_LjOp] at hcA
    refine ⟨c, hc, hcA, ?_⟩
    have hβ2 : β * β ≤ ρ ^ 2 := by rw [sq]; exact mul_le_mul hβρ hβρ hβ hρ
    have hβ3 : β * β * β ≤ ρ ^ 3 := by
      rw [pow_succ]; exact mul_le_mul hβ2 hβρ hβ (sq_nonneg ρ)
    have hrn : ZNorm L Λ (LjOp L γ δ p Ntr aP 0 b + LjOp L γ δ p Ntr aP 2 b + LjOp L γ δ p Ntr aP 3 b) ≤
        ENNReal.ofReal (ε₀ + 3 * K * ρ ^ 2 * α + K * ρ ^ 3) := by
      refine ZNorm_le_of_wt L fun t n => ?_
      have hw := (wt_pos L Λ n).le
      obtain ⟨-, h2, h3⟩ := hLb b hb t n
      have e0 := h0 b t n
      have m2 : K * (β * β * α) * wt L Λ n ≤ K * (ρ ^ 2 * α) * wt L Λ n := by gcongr
      have m3 : K * (β * β * β) * wt L Λ n ≤ K * ρ ^ 3 * wt L Λ n := by gcongr
      have n3 := norm_add₃_le (a := Lop L γ δ p Ntr aP 0 b t n) (b := Lop L γ δ p Ntr aP 2 b t n)
        (c := Lop L γ δ p Ntr aP 3 b t n)
      simp only [Pi.add_apply]
      unfold LjOp
      linarith
    calc ZNorm L Λ c ≤ ENNReal.ofReal κ * ZNorm L Λ (c - LjOp L γ δ p Ntr aP 1 c) := hbound' c hc
      _ ≤ ENNReal.ofReal κ * ENNReal.ofReal (ε₀ + 3 * K * ρ ^ 2 * α + K * ρ ^ 3) := by
          rw [hcA]; gcongr
      _ = ENNReal.ofReal (κ * (ε₀ + 3 * K * ρ ^ 2 * α + K * ρ ^ 3)) := (ENNReal.ofReal_mul hκ).symm
      _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal hsmall
  · -- the contraction
    intro b hb b' hb' c hc c' hc' hbρ hb'ρ hcA hc'A
    set β := (ZNorm L Λ b).toReal
    set β' := (ZNorm L Λ b').toReal
    set η := (ZNorm L Λ (b - b')).toReal
    have hβ : 0 ≤ β := ENNReal.toReal_nonneg
    have hβ' : 0 ≤ β' := ENNReal.toReal_nonneg
    have hη : 0 ≤ η := ENNReal.toReal_nonneg
    have hβρ : β ≤ ρ := toReal_ZNorm_le L hρ hbρ
    have hβ'ρ : β' ≤ ρ := toReal_ZNorm_le L hρ hb'ρ
    have hdiff : (c - c') - LjOp L γ δ p Ntr aP 1 (c - c') =
        (LjOp L γ δ p Ntr aP 2 b - LjOp L γ δ p Ntr aP 2 b') +
          (LjOp L γ δ p Ntr aP 3 b - LjOp L γ δ p Ntr aP 3 b') := by
      rw [← L1op_eq_LjOp, ← hAlin c hc c' hc', L1op_eq_LjOp, L1op_eq_LjOp, hcA, hc'A,
        L0_indep L γ δ Ntr haP hL b b']
      abel
    have hQ : ZNorm L Λ ((c - c') - LjOp L γ δ p Ntr aP 1 (c - c')) ≤
        ENNReal.ofReal ((6 * K * ρ * α + 3 * K * ρ ^ 2) * η) := by
      rw [hdiff]
      refine ZNorm_le_of_wt L fun t n => ?_
      have hw := (wt_pos L Λ n).le
      obtain ⟨h2, h3⟩ := norm_Lop_sub_le L γ δ Ntr haP hb hb' hΛ hL1 hα0 hα t.2 n
      have m2 : 3 * (K * ((β + β') * α * η)) * wt L Λ n ≤ 3 * (K * ((ρ + ρ) * α * η)) * wt L Λ n := by
        gcongr
      have m3 : K * ((β ^ 2 + β * β' + β' ^ 2) * η) * wt L Λ n ≤
          K * ((ρ ^ 2 + ρ * ρ + ρ ^ 2) * η) * wt L Λ n := by gcongr
      have n2 := norm_add_le (Lop L γ δ p Ntr aP 2 b t n - Lop L γ δ p Ntr aP 2 b' t n)
        (Lop L γ δ p Ntr aP 3 b t n - Lop L γ δ p Ntr aP 3 b' t n)
      simp only [Pi.add_apply, Pi.sub_apply]
      unfold LjOp
      linarith
    have hfin : ZNorm L Λ (b - b') = ENNReal.ofReal η := (ENNReal.ofReal_toReal (zSpace_sub hb hb').2.ne).symm
    calc ZNorm L Λ (c - c') ≤ ENNReal.ofReal κ * ZNorm L Λ ((c - c') - LjOp L γ δ p Ntr aP 1 (c - c')) :=
          hbound' _ (zSpace_sub hc hc')
      _ ≤ ENNReal.ofReal κ * ENNReal.ofReal ((6 * K * ρ * α + 3 * K * ρ ^ 2) * η) := by gcongr
      _ = ENNReal.ofReal (κ * (6 * K * ρ * α + 3 * K * ρ ^ 2) * η) := by
          rw [← ENNReal.ofReal_mul hκ]; congr 1; ring
      _ ≤ ENNReal.ofReal (η / 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := mul_le_mul_of_nonneg_right hcontr hη
          linarith
      _ = 2⁻¹ * ZNorm L Λ (b - b') := by rw [hfin, ennreal_inv_two_mul_ofReal]

end Core

end WaveTurbulence.Fixedpt
