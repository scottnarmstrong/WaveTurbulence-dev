/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.WPF
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.PieceBound

/-! # P4-W3 (WP-F): the engine bound of a term in the literal form `Λ (Nₛ√δ)^{n₍₂₎} L^{-η⁸(M₀+M₁) - η²b + η⁷} leaf`

A per-term certificate (P2 `termBoundR_of_piece`, W2 `termBoundW`) bounds a recentered term by
`‖c^M ζ‖ · ((ccη+1) · mass · engineConst3(η, |Row|) · maxPar^{η⁶} · sumintRHS0(P, D) · ∏_ρ L^{w g_ρ}) · ∏_ρ b_ρ`
(`Amb.pre`/`AmbW.pre` times the row sizes), at the engine parameters `P` (`C₁ = c₀`).  `engine_rhs` turns it into the literal form
used by `wpF_top`, with the explicit constant `engNs η c₀ Km Kr` (depending on `η`, `c₀` and the row/mass constants only), from:

* the shape: `D.S.M = M ≥ 1`, `|Row D| = 2M`, `M + 2 Sₙ = n₍₂₎`, `b = #{nor = false}`;
* the gain bookkeeping: `M₀ˢ + M₁ˢ ≤ D.M₀ + D.M₁` (`M₀ˢ, M₁ˢ` the numbers of the statement: `cohmolIndex`, `step3D.M₁`);
* `mass ≤ Km^{M+1}`, `maxPar D^{η⁶} ≤ Λ` (R58: `(1+|λ|)^{6η⁶}`; `1` for `λ = 0`);
* the rows: `∏_ρ b_ρ ≤ Kr^{2M} (2c₀²δ)^{Sₙ} L^{-w M₁(D)} leaf` (the exceptional orders of a twisted state equal those of the start,
  `zp_sizes`; the remainder rows carry their `L^{-w}` in `M₁(D)`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W13
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar MeasureTheory Finset
open scoped ENNReal

/-- The engine-level constant of the literal form. -/
noncomputable def engNs (η c Km Kr : ℝ) : ℝ :=
  (ccη η + 1).toReal * Km * ((2 : ℝ) ^ (2 * η ^ 8) * Real.sqrt 2 ^ (η ^ 6)) * c *
    (Km * ((Real.sqrt 2 ^ 3) ^ (2 * η ^ 8) * (Real.sqrt 2 ^ 3) ^ (η ^ 6) * (8 : ℝ) ^ (η ^ 6)) ^ 2 * Kr ^ 2 * c) * Real.sqrt 2

theorem one_le_ccηPar (η : ℝ) : 1 ≤ (ccη η + 1).toReal := VineEstS3.one_le_ccη_toReal η

theorem ccηPar_ne_top (η : ℝ) : ccη η + 1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨(VineEstS3.ccη_lt_top η).ne, ENNReal.one_ne_top⟩

section
variable {P : WTParams} {D : SumintPar.SumintDatum P.d}

theorem sum_rowG_par : ∑ ρ : Row D, (rowG D ρ) = D.M₁ := by
  unfold Row rowG SumintPar.SumintDatum.M₁
  rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]; rfl

theorem prod_rpow_rowG_par {L : ℝ} (hL : 0 < L) (c : ℝ) :
    ∏ ρ : Row D, L ^ (c * (rowG D ρ : ℝ)) = L ^ (c * (D.M₁ : ℝ)) := by
  rw [← Real.rpow_sum_of_pos hL, ← Finset.mul_sum]
  congr 2
  exact_mod_cast sum_rowG_par

theorem card_Row_par : Fintype.card (Row D) = 2 * D.S.M := by
  unfold Row
  rw [Fintype.card_sum, Sumint.card_vector_index]; ring

/-- The algebraic identity of the engine bound (coupling, sumint prefactor and row weights). -/
theorem engine_alg {M Sn : ℕ} {s u T mass e0 ee mp c Le Lw Lw' Kr X lf : ℝ} (hs : 0 < s) (hu : 0 < u) :
    (s ^ 2 / (2 * u)) ^ M * (T * (mass * (e0 * ee ^ (2 * M) * mp * (c * (c * s⁻¹) ^ M * (u ^ M * Le)) * Lw)) *
      (Kr ^ (2 * M) * X ^ Sn * Lw' * lf)) =
    (T * mass * e0 * c * mp) * (ee ^ 2 * Kr ^ 2 * (c * s / 2)) ^ M * X ^ Sn * Le * lf * (Lw * Lw') := by
  have hsu : (s ^ 2 / (2 * u)) * (c * s⁻¹) * u = c * s / 2 := by field_simp
  calc (s ^ 2 / (2 * u)) ^ M * (T * (mass * (e0 * ee ^ (2 * M) * mp * (c * (c * s⁻¹) ^ M * (u ^ M * Le)) * Lw)) *
        (Kr ^ (2 * M) * X ^ Sn * Lw' * lf))
      = (T * mass * e0 * c * mp) * ((s ^ 2 / (2 * u)) * (c * s⁻¹) * u) ^ M * (ee ^ 2 * Kr ^ 2) ^ M *
        X ^ Sn * Le * lf * (Lw * Lw') := by
        rw [mul_pow, mul_pow, pow_mul, pow_mul]; ring
    _ = _ := by rw [hsu, ← mul_pow]; ring

/-- The numerical absorption of the engine bound into `Λ (Nₛ s)^{n₂} Lfin lf`. -/
theorem engine_num {M Sn n2 : ℕ} {T mass e0 ee mp c s δ Km Kr Λ Ns Le Lfin lf : ℝ}
    (hM1 : 1 ≤ M) (hn2 : M + 2 * Sn = n2) (hT1 : 1 ≤ T) (hKm : 1 ≤ Km) (he01 : 1 ≤ e0) (hee1 : 1 ≤ ee) (hC : 1 ≤ c)
    (hKr : 1 ≤ Kr) (hs0 : 0 < s) (hsδ : s ^ 2 = δ) (hmass0 : 0 ≤ mass) (hmass : mass ≤ Km * Km ^ M)
    (hmp0 : 0 ≤ mp) (hmp : mp ≤ Λ) (hLe0 : 0 ≤ Le) (hLe : Le ≤ Lfin) (hlf : 0 ≤ lf)
    (hNsE : Ns = (T * Km * e0 * c) * (Km * ee ^ 2 * Kr ^ 2 * c) * Real.sqrt 2) :
    (T * mass * e0 * c * mp) * (ee ^ 2 * Kr ^ 2 * (c * s / 2)) ^ M * (2 * c ^ 2 * δ) ^ Sn * Le * lf ≤
      Λ * ((Ns * s) ^ n2 * Lfin * lf) := by
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  set A := T * Km * e0 * c with hA
  set Bk := Km * ee ^ 2 * Kr ^ 2 * c with hBk
  have hA1 : 1 ≤ A := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hT1 hKm) he01) hC
  have hee2 : 1 ≤ ee ^ 2 := one_le_pow₀ hee1
  have hKr2 : 1 ≤ Kr ^ 2 := one_le_pow₀ hKr
  have hKe : 1 ≤ Km * ee ^ 2 * Kr ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hKm hee2) hKr2
  have hB1 : 1 ≤ Bk := one_le_mul_of_one_le_of_one_le hKe hC
  have hAB0 : 1 ≤ A * Bk := one_le_mul_of_one_le_of_one_le hA1 hB1
  have hAB : A * Bk ≤ Ns := by rw [hNsE]; exact le_mul_of_one_le_right (by linarith) hs2
  have hcB : c ≤ Bk := by rw [hBk]; exact le_mul_of_one_le_left (by linarith) hKe
  have hcN : Real.sqrt 2 * c ≤ Ns := by
    rw [hNsE, mul_comm (A * Bk)]
    refine mul_le_mul_of_nonneg_left (hcB.trans (le_mul_of_one_le_left (by linarith) hA1)) (by positivity)
  have hNs0 : 0 ≤ Ns := le_trans (by linarith) hAB
  have hX0 : 0 ≤ Ns * s := mul_nonneg hNs0 hs0.le
  have hP1 : (T * mass * e0 * c * mp) * (ee ^ 2 * Kr ^ 2 * (c * s / 2)) ^ M ≤ Λ * (Ns * s) ^ M := by
    have h1 : T * mass * e0 * c * mp ≤ Λ * (A * Km ^ M) := by
      have hTec : 0 ≤ T * e0 * c := by positivity
      calc T * mass * e0 * c * mp = (T * e0 * c) * mass * mp := by ring
        _ ≤ (T * e0 * c) * (Km * Km ^ M) * Λ := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hmass hTec) hmp hmp0 (by positivity)
        _ = Λ * (A * Km ^ M) := by rw [hA]; ring
    have hle : A ≤ A ^ M := by
      calc A = A ^ 1 := (pow_one _).symm
        _ ≤ A ^ M := pow_le_pow_right₀ hA1 hM1
    have hx : Km * (ee ^ 2 * Kr ^ 2 * (c * s / 2)) ≤ Bk * s := by
      have : Km * (ee ^ 2 * Kr ^ 2 * (c * s / 2)) = Bk * s / 2 := by rw [hBk]; ring
      rw [this]; linarith [mul_pos (lt_of_lt_of_le one_pos hB1) hs0]
    have h2 : A * Km ^ M * (ee ^ 2 * Kr ^ 2 * (c * s / 2)) ^ M ≤ (Ns * s) ^ M := by
      calc A * Km ^ M * (ee ^ 2 * Kr ^ 2 * (c * s / 2)) ^ M = A * (Km * (ee ^ 2 * Kr ^ 2 * (c * s / 2))) ^ M := by
            rw [mul_pow]; ring
        _ ≤ A ^ M * (Bk * s) ^ M := mul_le_mul hle (pow_le_pow_left₀ (by positivity) hx M) (by positivity) (by positivity)
        _ = (A * Bk * s) ^ M := by rw [mul_assoc A Bk s, ← mul_pow]
        _ ≤ (Ns * s) ^ M := pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hAB hs0.le) M
    have hy0 : 0 ≤ (ee ^ 2 * Kr ^ 2 * (c * s / 2)) ^ M := by positivity
    calc (T * mass * e0 * c * mp) * (ee ^ 2 * Kr ^ 2 * (c * s / 2)) ^ M
        ≤ Λ * (A * Km ^ M) * (ee ^ 2 * Kr ^ 2 * (c * s / 2)) ^ M := mul_le_mul_of_nonneg_right h1 hy0
      _ = Λ * (A * Km ^ M * (ee ^ 2 * Kr ^ 2 * (c * s / 2)) ^ M) := by ring
      _ ≤ Λ * (Ns * s) ^ M := mul_le_mul_of_nonneg_left h2 (hmp0.trans hmp)
  have hδ0 : 0 ≤ 2 * c ^ 2 * δ := by rw [← hsδ]; positivity
  have hP2 : (2 * c ^ 2 * δ) ^ Sn ≤ (Ns * s) ^ (2 * Sn) := by
    rw [pow_mul]
    refine pow_le_pow_left₀ hδ0 ?_ Sn
    have : 2 * c ^ 2 * δ = (Real.sqrt 2 * c * s) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), hsδ]
    rw [this]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hcN hs0.le) 2
  have hn : (Ns * s) ^ n2 = (Ns * s) ^ M * (Ns * s) ^ (2 * Sn) := by rw [← pow_add, hn2]
  have hΛ0 : 0 ≤ Λ := hmp0.trans hmp
  calc (T * mass * e0 * c * mp) * (ee ^ 2 * Kr ^ 2 * (c * s / 2)) ^ M * (2 * c ^ 2 * δ) ^ Sn * Le * lf
      ≤ (Λ * (Ns * s) ^ M) * (Ns * s) ^ (2 * Sn) * Lfin * lf := by
        have := mul_le_mul hP1 hP2 (pow_nonneg hδ0 _) (by nlinarith [hmp0.trans hmp, pow_nonneg hX0 M])
        have := mul_le_mul this hLe hLe0 (by positivity)
        exact mul_le_mul_of_nonneg_right this hlf
    _ = Λ * ((Ns * s) ^ n2 * Lfin * lf) := by rw [hn]; ring

/-- **The engine bound of a term in the literal form.** -/
theorem engine_rhs (mass : ℝ) (Rb : Row D → ℝ≥0∞) (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    {M Sn n2 bb M0s M1s : ℕ} {Λ Km Kr lf : ℝ}
    (hM : D.S.M = M) (hM1 : 1 ≤ M) (hn2 : M + 2 * Sn = n2)
    (hb : (Finset.univ.filter fun i => D.S.nor i = false).card = bb)
    (hnum : M0s + M1s ≤ D.M₀ + D.M₁)
    (hmass0 : 0 ≤ mass) (hmass : mass ≤ Km ^ (M + 1)) (hKm : 1 ≤ Km)
    (hpar : maxPar D ^ (P.η ^ 6) ≤ Λ)
    (hrows : ∏ ρ, Rb ρ ≤ ENNReal.ofReal (Kr ^ (2 * M) * (2 * P.C₁ ^ 2 * P.δ) ^ Sn *
      P.L ^ (-(weightExp P.d P.γ P.η) * (D.M₁ : ℝ)) * lf))
    (hKr : 1 ≤ Kr) (hlf : 0 ≤ lf) (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hC : 1 ≤ P.C₁) (hη0 : 0 < P.η) (hη1 : P.η ≤ 1) :
    ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ M * ζ‖ₑ *
      ((ccη P.η + 1) * ENNReal.ofReal (mass * (engineConst3 P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) *
        sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * rowG D ρ))) * ∏ ρ, Rb ρ) ≤
    ENNReal.ofReal (Λ * ((engNs P.η P.C₁ Km Kr * Real.sqrt P.δ) ^ n2 *
      P.L ^ (-(P.η ^ 8 * ((M0s + M1s : ℕ) : ℝ)) - P.η ^ 2 * (bb : ℝ) + P.η ^ 7) * lf)) := by
  have hT1 : 1 ≤ (ccη P.η + 1).toReal := one_le_ccηPar P.η
  have hTe : ccη P.η + 1 = ENNReal.ofReal (ccη P.η + 1).toReal := (ENNReal.ofReal_toReal (ccηPar_ne_top P.η)).symm
  have hL0 : 0 < P.L := by linarith
  have hs0 : 0 < Real.sqrt P.δ := Real.sqrt_pos.2 hδ
  have hu0 : 0 < P.L ^ ((P.d : ℝ) - P.γ) := Real.rpow_pos_of_pos hL0 _
  set e1 : ℝ := -(P.η ^ 2 * (((Finset.univ.filter fun i => D.S.nor i = false).card : ℕ) + (D.M₁ : ℝ))) -
    P.η ^ 8 * (D.M₀ : ℝ) + P.η ^ 7 with he1
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  set e0 : ℝ := (2 : ℝ) ^ (2 * P.η ^ 8) * Real.sqrt 2 ^ (P.η ^ 6) with he0
  set ee : ℝ := (Real.sqrt 2 ^ 3) ^ (2 * P.η ^ 8) * (Real.sqrt 2 ^ 3) ^ (P.η ^ 6) * (8 : ℝ) ^ (P.η ^ 6) with hee
  have he01 : 1 ≤ e0 := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by norm_num) (by positivity))
    (Real.one_le_rpow hs2 (by positivity))
  have hee1 : 1 ≤ ee := by
    have hs3 : (1 : ℝ) ≤ Real.sqrt 2 ^ 3 := one_le_pow₀ hs2
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hs3 (by positivity))
      (Real.one_le_rpow hs3 (by positivity))) (Real.one_le_rpow (by norm_num) (by positivity))
  have hE3 : engineConst3 P.η (Fintype.card (Row D)) = e0 * ee ^ (2 * M) := by
    unfold engineConst3; rw [card_Row_par, hM]
  have hpr : ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)) = P.L ^ (weightExp P.d P.γ P.η * (D.M₁ : ℝ)) :=
    prod_rpow_rowG_par hL0 _
  have hS0 : sumintRHS0 P D = P.C₁ * (P.C₁ * (Real.sqrt P.δ)⁻¹) ^ M * ((P.L ^ ((P.d : ℝ) - P.γ)) ^ M * P.L ^ e1) := by
    unfold sumintRHS0
    rw [hM]
    have hsq : P.δ ^ (-(1 : ℝ) / 2) = (Real.sqrt P.δ)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hδ.le]; congr 1; ring
    rw [hsq]
    have hexp : (M : ℝ) * ((P.d : ℝ) - P.γ) - P.η ^ 2 * (((Finset.univ.filter fun i => D.S.nor i = false).card : ℕ) +
        (D.M₁ : ℝ)) - P.η ^ 8 * (D.M₀ : ℝ) + P.η ^ 7 = ((P.d : ℝ) - P.γ) * (M : ℝ) + e1 := by rw [he1]; ring
    rw [hexp, Real.rpow_add hL0, Real.rpow_mul hL0.le, Real.rpow_natCast]
  have hcpl0 : 0 ≤ coupling P.d P.L P.γ P.δ := by unfold coupling; positivity
  have hcplN : ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ M * ζ‖ₑ = ENNReal.ofReal (coupling P.d P.L P.γ P.δ ^ M) := by
    rw [← ofReal_norm, norm_mul, hζ, mul_one, norm_pow, Complex.norm_real, Real.norm_of_nonneg hcpl0]
  have hcp : coupling P.d P.L P.γ P.δ = Real.sqrt P.δ ^ 2 / (2 * P.L ^ ((P.d : ℝ) - P.γ)) := by
    rw [Real.sq_sqrt hδ.le]; rfl
  have hmp0 : 0 ≤ maxPar D ^ (P.η ^ 6) := by
    unfold maxPar
    exact Real.rpow_nonneg (Real.iSup_nonneg fun v => (VineEstS3.Eng.Jb_pos _).le) _
  have hLe : P.L ^ e1 ≤ P.L ^ (-(P.η ^ 8 * ((M0s + M1s : ℕ) : ℝ)) - P.η ^ 2 * (bb : ℝ) + P.η ^ 7) := by
    apply Real.rpow_le_rpow_of_exponent_le hL
    rw [he1, hb]
    have h8 : P.η ^ 8 ≤ P.η ^ 2 := pow_le_pow_of_le_one hη0.le hη1 (by norm_num)
    have hnumR : ((M0s + M1s : ℕ) : ℝ) ≤ (D.M₀ : ℝ) + (D.M₁ : ℝ) := by exact_mod_cast hnum
    have hM1' : (0 : ℝ) ≤ (D.M₁ : ℝ) := Nat.cast_nonneg _
    have hη8 : 0 ≤ P.η ^ 8 := by positivity
    nlinarith
  have hLw : P.L ^ (weightExp P.d P.γ P.η * (D.M₁ : ℝ)) * P.L ^ (-(weightExp P.d P.γ P.η) * (D.M₁ : ℝ)) = 1 := by
    rw [← Real.rpow_add hL0]; simp
  have hC0 : 0 ≤ P.C₁ := by linarith
  have hQ0 : 0 ≤ mass * (e0 * ee ^ (2 * M) * maxPar D ^ (P.η ^ 6) *
      (P.C₁ * (P.C₁ * (Real.sqrt P.δ)⁻¹) ^ M * ((P.L ^ ((P.d : ℝ) - P.γ)) ^ M * P.L ^ e1)) *
      P.L ^ (weightExp P.d P.γ P.η * (D.M₁ : ℝ))) := by positivity
  have hR0 : 0 ≤ Kr ^ (2 * M) * (2 * P.C₁ ^ 2 * P.δ) ^ Sn * P.L ^ (-(weightExp P.d P.γ P.η) * (D.M₁ : ℝ)) * lf := by
    positivity
  rw [hE3, hS0, hpr, hcplN, hTe]
  refine (mul_le_mul' le_rfl (mul_le_mul' le_rfl hrows)).trans ?_
  rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (mul_nonneg (by linarith) hQ0),
    ← ENNReal.ofReal_mul (pow_nonneg hcpl0 _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hcp, engine_alg hs0 hu0, hLw, mul_one]
  exact engine_num hM1 hn2 hT1 hKm he01 hee1 hC hKr hs0 (Real.sq_sqrt hδ.le) hmass0
    (by rw [pow_succ] at hmass; linarith) hmp0 hpar (Real.rpow_nonneg hL0.le _) hLe hlf (by unfold engNs; ring)
end

end WaveTurbulence.VineEstS5C.P4.W13
