/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcSrc

/-! # P4-W2 (session 7, step 3d): the algebra of the row-size products of a summand

`bnd_P`: for a separated piece, `bK * bL ≤ C₀² Ksp · J₁ J₂ |c| β_F β_G`; `bnd_R1`..: the remainder shapes.  `kF_le` etc.: the numerical constants
of the spatial factors are `≤ Ksp d`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5C.P2
open scoped ENNReal

theorem abs_flagSign (ex : ℝ) : |flagSign ex| = 1 := by
  unfold flagSign; split_ifs <;> simp

theorem kF_le {d wN wDec : ℕ} (hd : 1 ≤ d) (hwN : wN + 1 = 30 * d) (hwDec : wDec = 30 * d) :
    (2 : ℝ) ^ wDec * (d : ℝ) ^ (wN + 1) ≤ Ksp d := by
  unfold Ksp
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (2 : ℝ) ^ wDec ≤ (2 : ℝ) ^ (90 * d) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (d : ℝ) ^ (wN + 1) ≤ (d : ℝ) ^ (120 * d) := pow_le_pow_right₀ hd' (by omega)
  have h3 : (0 : ℝ) ≤ (d : ℝ) ^ (wN + 1) := by positivity
  have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ (90 * d) := by positivity
  exact mul_le_mul h1 h2 h3 h4

theorem kG_le {d wN : ℕ} (hd : 1 ≤ d) (hwN : wN + 1 = 30 * d) :
    (2 : ℝ) ^ 0 * (d : ℝ) ^ (wN + 1) ≤ Ksp d := by
  unfold Ksp
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (90 * d) := one_le_pow₀ (by norm_num)
  have h2 : (d : ℝ) ^ (wN + 1) ≤ (d : ℝ) ^ (120 * d) := pow_le_pow_right₀ hd' (by omega)
  have h3 : (0 : ℝ) ≤ (d : ℝ) ^ (wN + 1) := by positivity
  have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ (90 * d) := by positivity
  rw [pow_zero]
  exact mul_le_mul h1 h2 h3 h4

theorem kR_le {d wN : ℕ} (hd : 1 ≤ d) (hwN : wN + 1 = 30 * d) :
    (2 : ℝ) ^ (30 * d) * (d : ℝ) ^ wN ≤ Ksp d := by
  unfold Ksp
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (2 : ℝ) ^ (30 * d) ≤ (2 : ℝ) ^ (90 * d) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (d : ℝ) ^ wN ≤ (d : ℝ) ^ (120 * d) := pow_le_pow_right₀ hd' (by omega)
  have h3 : (0 : ℝ) ≤ (d : ℝ) ^ wN := by positivity
  have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ (90 * d) := by positivity
  exact mul_le_mul h1 h2 h3 h4

theorem kR0_le {d wN : ℕ} (hd : 1 ≤ d) (hwN : wN + 1 = 30 * d) :
    (2 : ℝ) ^ 0 * (d : ℝ) ^ wN ≤ Ksp d := by
  unfold Ksp
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (90 * d) := one_le_pow₀ (by norm_num)
  have h2 : (d : ℝ) ^ wN ≤ (d : ℝ) ^ (120 * d) := pow_le_pow_right₀ hd' (by omega)
  have h3 : (0 : ℝ) ≤ (d : ℝ) ^ wN := by positivity
  have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ (90 * d) := by positivity
  rw [pow_zero]
  exact mul_le_mul h1 h2 h3 h4

/-- The product of the row sizes of a separated piece. -/
theorem bnd_P {d wN wDec : ℕ} (hd : 1 ≤ d) (hwN : wN + 1 = 30 * d) (hwDec : wDec = 30 * d) (C C' K0 : ℝ≥0∞)
    (hC : C ≤ K0) (hC' : C' ≤ K0) (J1 J2 c βF βG : ℝ) (h1 : 0 ≤ J1) (h2 : 0 ≤ J2) (hF : 0 ≤ βF) (hG : 0 ≤ βG) :
    (C * ENNReal.ofReal J1 * ENNReal.ofReal (spConst d wN wDec c βF βG)) * (C' * ENNReal.ofReal J2 * ENNReal.ofReal 1) ≤
      K0 * K0 * ENNReal.ofReal (Ksp d) * ENNReal.ofReal (J1 * J2 * (|c| * βF * βG)) := by
  have hsp := spConst_le hd hwN hwDec c βF βG hF hG
  have hsp0 : 0 ≤ spConst d wN wDec c βF βG := by
    unfold spConst; positivity
  calc (C * ENNReal.ofReal J1 * ENNReal.ofReal (spConst d wN wDec c βF βG)) * (C' * ENNReal.ofReal J2 * ENNReal.ofReal 1)
      = (C * C') * ENNReal.ofReal (J1 * spConst d wN wDec c βF βG * J2) := by
        rw [ENNReal.ofReal_mul (mul_nonneg h1 hsp0), ENNReal.ofReal_mul h1, ENNReal.ofReal_one, mul_one]
        ring
    _ ≤ (K0 * K0) * ENNReal.ofReal (Ksp d * (J1 * J2 * (|c| * βF * βG))) := by
        refine mul_le_mul' (mul_le_mul' hC hC') (ENNReal.ofReal_le_ofReal ?_)
        calc J1 * spConst d wN wDec c βF βG * J2 = (J1 * J2) * spConst d wN wDec c βF βG := by ring
          _ ≤ (J1 * J2) * (Ksp d * (|c| * βF * βG)) := mul_le_mul_of_nonneg_left hsp (by positivity)
          _ = Ksp d * (J1 * J2 * (|c| * βF * βG)) := by ring
    _ = K0 * K0 * ENNReal.ofReal (Ksp d) * ENNReal.ofReal (J1 * J2 * (|c| * βF * βG)) := by
        rw [ENNReal.ofReal_mul (le_trans zero_le_one (one_le_Ksp hd))]; ring

/-- A product `(C · ofReal a · ofReal u) (C' · ofReal b · ofReal 1)` (remainder times separated shape). -/
theorem bnd_R {C C' K0 : ℝ≥0∞} (hC : C ≤ K0) (hC' : C' ≤ K0) (a u b : ℝ) (ha : 0 ≤ a) (hu : 0 ≤ u) (hb : 0 ≤ b) :
    (C * ENNReal.ofReal a * ENNReal.ofReal u) * (C' * ENNReal.ofReal b * ENNReal.ofReal 1) ≤
      K0 * K0 * ENNReal.ofReal (a * u * b) := by
  calc (C * ENNReal.ofReal a * ENNReal.ofReal u) * (C' * ENNReal.ofReal b * ENNReal.ofReal 1)
      = (C * C') * ENNReal.ofReal (a * u * b) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul ha, ENNReal.ofReal_one, mul_one]
        ring
    _ ≤ K0 * K0 * ENNReal.ofReal (a * u * b) := mul_le_mul' (mul_le_mul' hC hC') le_rfl

/-- A product `(C · ofReal a) (C' · ofReal b)`. -/
theorem bnd_RR {C C' K0 : ℝ≥0∞} (hC : C ≤ K0) (hC' : C' ≤ K0) (a b : ℝ) (ha : 0 ≤ a) :
    (C * ENNReal.ofReal a) * (C' * ENNReal.ofReal b) ≤ K0 * K0 * ENNReal.ofReal (a * b) := by
  calc (C * ENNReal.ofReal a) * (C' * ENNReal.ofReal b) = (C * C') * ENNReal.ofReal (a * b) := by
        rw [ENNReal.ofReal_mul ha]; ring
    _ ≤ K0 * K0 * ENNReal.ofReal (a * b) := mul_le_mul' (mul_le_mul' hC hC') le_rfl

/-- A product `(C · ofReal a · ofReal b) · ofReal 1`. -/
theorem bnd_RP {C K0 : ℝ≥0∞} (hC : C ≤ K0) (hK : 1 ≤ K0) (a b : ℝ) (ha : 0 ≤ a) :
    (C * ENNReal.ofReal a * ENNReal.ofReal b) * ENNReal.ofReal 1 ≤ K0 * K0 * ENNReal.ofReal (a * b) := by
  rw [ENNReal.ofReal_one, mul_one, mul_assoc, ← ENNReal.ofReal_mul ha]
  calc C * ENNReal.ofReal (a * b) ≤ K0 * ENNReal.ofReal (a * b) := mul_le_mul' hC le_rfl
    _ ≤ K0 * K0 * ENNReal.ofReal (a * b) := mul_le_mul' (le_mul_of_one_le_left' hK) le_rfl

/-- The window of the clock of the layer selector `s` (`false`: the low window `L₄`, `true`: the high window `Lₕ`). -/
def Wsel (q4 qh : ℝ) (s : Bool) : Set ℝ := if s then Set.Ioo qh (qh + 1) else Set.Ioo q4 (q4 + 1)

/-- The uniform constant of the row-size products. -/
noncomputable def Kall (d : ℕ) (K0 : ℝ≥0∞) : ℝ≥0∞ := K0 * K0 * ENNReal.ofReal (Ksp d) * ENNReal.ofReal (Ksp d)

theorem Kall_ne_top (d : ℕ) {K0 : ℝ≥0∞} (h : K0 ≠ ⊤) : Kall d K0 ≠ ⊤ := by
  unfold Kall
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top h h) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top

theorem one_le_ofReal_Ksp {d : ℕ} (hd : 1 ≤ d) : 1 ≤ ENNReal.ofReal (Ksp d) := by
  rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (one_le_Ksp hd)

theorem K0_le_Kall {d : ℕ} (hd : 1 ≤ d) (K0 : ℝ≥0∞) (x : ℝ) :
    K0 * K0 * ENNReal.ofReal x ≤ Kall d K0 * ENNReal.ofReal x := by
  unfold Kall
  refine mul_le_mul' ?_ le_rfl
  have h1 := one_le_ofReal_Ksp hd
  calc K0 * K0 = K0 * K0 * 1 * 1 := by simp
    _ ≤ K0 * K0 * ENNReal.ofReal (Ksp d) * ENNReal.ofReal (Ksp d) := mul_le_mul' (mul_le_mul' le_rfl h1) h1

theorem Ksp_le_Kall {d : ℕ} (hd : 1 ≤ d) (K0 : ℝ≥0∞) (Z SZ : ℝ) (hZ : Z ≤ Ksp d * SZ) (hs : 0 ≤ SZ) :
    K0 * K0 * ENNReal.ofReal (Ksp d) * ENNReal.ofReal Z ≤ Kall d K0 * ENNReal.ofReal SZ := by
  unfold Kall
  calc K0 * K0 * ENNReal.ofReal (Ksp d) * ENNReal.ofReal Z
      ≤ K0 * K0 * ENNReal.ofReal (Ksp d) * ENNReal.ofReal (Ksp d * SZ) := mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hZ)
    _ = K0 * K0 * ENNReal.ofReal (Ksp d) * ENNReal.ofReal (Ksp d) * ENNReal.ofReal SZ := by
        rw [ENNReal.ofReal_mul (le_trans zero_le_one (one_le_Ksp hd))]; ring

/-- The factor of a piece: a unit constant times `1` (kind `0`) or `‖r‖` (kind `1`). -/
def FacOK {d : ℕ} {T : Type*} (kind : ℕ) (fac : (T → ℝ) → Mom d → ℂ) : Prop :=
  ∃ s : ℂ, ‖s‖ = 1 ∧ ∀ τ r, fac τ r = s * (if kind = 1 then ((‖r‖ : ℝ) : ℂ) else 1)

/-- A product `(C · ofReal a · ofReal u) (C' · ofReal b)` (separated times remainder). -/
theorem bnd_R' {C C' K0 : ℝ≥0∞} (hC : C ≤ K0) (hC' : C' ≤ K0) (a u b : ℝ) (ha : 0 ≤ a) (hu : 0 ≤ u) :
    (C * ENNReal.ofReal a * ENNReal.ofReal u) * (C' * ENNReal.ofReal b) ≤ K0 * K0 * ENNReal.ofReal (a * u * b) := by
  calc (C * ENNReal.ofReal a * ENNReal.ofReal u) * (C' * ENNReal.ofReal b) = (C * C') * ENNReal.ofReal (a * u * b) := by
        rw [ENNReal.ofReal_mul (mul_nonneg ha hu), ENNReal.ofReal_mul ha]; ring
    _ ≤ K0 * K0 * ENNReal.ofReal (a * u * b) := mul_le_mul' (mul_le_mul' hC hC') le_rfl

theorem K0_le_Kall_of_le {d : ℕ} (hd : 1 ≤ d) (K0 : ℝ≥0∞) (Z SZ : ℝ) (hZ : Z ≤ Ksp d * SZ) (hs : 0 ≤ SZ) :
    K0 * K0 * ENNReal.ofReal Z ≤ Kall d K0 * ENNReal.ofReal SZ := by
  refine le_trans ?_ (Ksp_le_Kall hd K0 Z SZ hZ hs)
  have h1 := one_le_ofReal_Ksp hd
  calc K0 * K0 * ENNReal.ofReal Z = K0 * K0 * 1 * ENNReal.ofReal Z := by simp
    _ ≤ K0 * K0 * ENNReal.ofReal (Ksp d) * ENNReal.ofReal Z := mul_le_mul' (mul_le_mul' le_rfl h1) le_rfl

namespace CertSrc
variable {P : WTParams} {β : Type*} {S : SepTerms β P.d} {q2 q4 qh : ℝ} (src : CertSrc P S q2 q4 qh)



theorem szQ_nonneg {b : β} (h1 : 0 ≤ src.CJq b) (h2 : 0 ≤ src.CMq b) : 0 ≤ src.szQ b :=
  mul_nonneg (mul_nonneg (abs_nonneg _) h1) h2

theorem szT_nonneg {b : β} (h1 : 0 ≤ src.CJt b) (h2 : 0 ≤ src.CMt b) : 0 ≤ src.szT b :=
  mul_nonneg (mul_nonneg (abs_nonneg _) h1) h2

theorem winq_sel {b : β} (hb : src.good b) (i : Fin (S.mQ b)) (s : Bool) :
    WinOK (src.cq s b i).V (src.cq s b i).Bc (Wsel q4 qh s) (Set.Ioo q2 (q2 + 1)) false := by
  cases s
  · simpa [Wsel] using (src.win_q b hb i).1
  · simpa [Wsel] using (src.win_q b hb i).2

theorem wint_sel {b : β} (hb : src.good b) (j : Fin (S.mT b)) (s : Bool) :
    WinOK (src.ct s b j).V (src.ct s b j).Bc (Wsel q4 qh s) (Set.Ioo q2 (q2 + 1)) true := by
  cases s
  · simpa [Wsel] using (src.win_t b hb j).1
  · simpa [Wsel] using (src.win_t b hb j).2

end CertSrc

namespace Src
variable {P : WTParams} {β : Type*} {S : SepTerms β P.d} {RQ RT : β → ℝ → ℝ → Mom P.d → ℂ} {q2 q4 qh : ℝ}
  (src : Src P S RQ RT q2 q4 qh)

theorem winrq_sel {b : β} (hb : src.good b) (s : Bool) :
    WinOK Set.univ (src.rq s b).Bc (Wsel q4 qh s) (Set.Ioo q2 (q2 + 1)) false := by
  cases s
  · simpa [Wsel] using (src.win_rq b hb).1
  · simpa [Wsel] using (src.win_rq b hb).2

theorem winrt_sel {b : β} (hb : src.good b) (s : Bool) :
    WinOK Set.univ (src.rt s b).Bc (Wsel q4 qh s) (Set.Ioo q2 (q2 + 1)) true := by
  cases s
  · simpa [Wsel] using (src.win_rt b hb).1
  · simpa [Wsel] using (src.win_rt b hb).2

end Src

end WaveTurbulence.VineEstS5C.P4.W2
