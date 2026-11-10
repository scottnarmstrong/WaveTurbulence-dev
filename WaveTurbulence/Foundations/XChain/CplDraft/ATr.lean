/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CplDraft.CoupleLimit
public import WaveTurbulence.Foundations.XChain.CplDraft.RapidTransfer
public import WaveTurbulence.Foundations.XChain.CmattrEnvelopeBound
public import WaveTurbulence.Foundations.XChain.CoupleTailEnvelopeBound
public import WaveTurbulence.Foundations.XChain.GraftStageEnvelope
public import WaveTurbulence.Foundations.XChain.GraftInputErrorAbsorption
public import WaveTurbulence.Foundations.XChain.GraftTailAbsorption
public import WaveTurbulence.Foundations.XChain.InductWidthRange
public import WaveTurbulence.Foundations.XChain.ClippedInputs
public import WaveTurbulence.Foundations.XChain.AnsatzInputFunctionBound
public import WaveTurbulence.Foundations.XChain.AssemblySizeNumbers
public import WaveTurbulence.Foundations.XChain.UniformPhiWeights
public import WaveTurbulence.Foundations.XChain.UniformSchwartzBracket
public import WaveTurbulence.Foundations.XChain.SmallDeltaChoice
public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Couple

/-!
# CPL-1: the `a^tr` clause of O-X3-CPL

**Statement** (`wtprefix_cplATr : WTPrefix (OX3CplBodyV .aTr)`). For `L` large after `(d, 𝔇)`:
- `|a^tr_n(t)|²` is integrable on `F_p`;
- `|𝔼_p|a^tr_n(t)|² − ∑_{N ≤ N_{p+1}^4} coupleSum_N(t,n)| ≤ ⟨n⟩^{-4Λ_{p+1}} e^{-101N_{p+1}}`.

Here `OX3CplBodyV v` is `OX3CplBody` (`flower/X2-Couple.lean`) for one couple quantity `v`.
`OX3CplBody_of_forall` reassembles the four quantities.

**Proof** (`cplATr_body`).
1. Replace `F_p` by `F_p ∩ {rapid data}` and `R` by `R` clipped above `p`. Neither changes any integral or
   kernel (`ansatzAt_rapidFev`, `ansatzAt_clip`, `truncSum_clip`).
2. CPL step 3 gives `𝔼_p|a^tr|² = ∑_{N ≤ N_{p+1}^4} truncSum_N + tail + cmattrError` (INDUCT's identity).
   `truncSum_N = coupleSum_N` by `coupleSum_tr`.
3. Bound both remaining terms:
   - INDUCT's envelope bounds give `tail ≤ env (δ^{ν/2})^{N^4+1−2N} W` and `cmattrError ≤ env e^{−N_p} W`;
   - `env ≤ e^{10⁶N^4}` (`stage_graftEnvelope_bound`);
   - `W = ⟨n⟩^{-Λ_p/2} ≤ ⟨n⟩^{-4Λ_{p+1}}`;
   - the final step `≤ e^{−102N}` each is done here (`env_mul_input_error_le`, `env_mul_tail_le`).
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.Cpl

open Finset MeasureTheory Set Filter Topology Induct
open scoped ENNReal

universe u

/-! ## The body of O-X3-CPL for one quantity -/

/-- `OX3CplBody` for the couple quantity `v`. -/
def OX3CplBodyV (v : CplVar) (P : WTParams) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
  ∀ p : ℕ, p < P.D →
  ∀ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
    (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
    (∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q) →
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ (n : Fin P.d → ℤ),
    Integrable (fun ω => ‖cplRand P (a ω p) p v t n‖ ^ 2) (μ.restrict (Fev p)) ∧
    ‖(((∫ ω in Fev p, ‖cplRand P (a ω p) p v t n‖ ^ 2 ∂μ : ℝ)) : ℂ) -
        ∑ N ∈ Finset.range (P.N (p + 1) ^ 4 + 1),
          coupleSum P (inputsF P R) p N v.kind v.dt t (latticePoint P.L n)‖ ≤
      jbr (latticePoint P.L n) ^ (-(4 * P.Lambda (p + 1) : ℝ)) * Real.exp (-(101 * P.N (p + 1) : ℝ))

theorem OX3CplBody_of_forall {P : WTParams} (h : ∀ v, OX3CplBodyV.{u} v P) : OX3CplBody.{u} P :=
  fun Ω _ μ _ g hg p hp a Fev R E Et ha t ht n v => h v Ω μ g hg p hp a Fev R E Et ha t ht n

/-! ## Clipping the remainder above `p` -/

theorem truncSum_clip (P : WTParams) (R : ℕ → Mom P.d → ℝ) {p q : ℕ} (hq : q ≤ p + 1) (N : ℕ) {w : ℕ}
    (t : ℝ) (ζ : Fin w → ℤˣ) (n : Fin w → (Fin P.d → ℤ)) :
    truncSum P (inputsF P (clipRemainder p R)) q N t ζ n = truncSum P (inputsF P R) q N t ζ n := by
  unfold truncSum
  refine finsum_congr fun LG => finsum_congr fun h => ?_
  apply KG_clip_inputs P R LG _ t n
  intro x
  cases q with
  | zero => exact False.elim h.1
  | succ q => exact (Canon.layer_le_of_isCanonGC h.1 x).trans (by omega)

theorem ansatzAt_clip (P : WTParams) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : (Fin P.d → ℤ) → Ω → ℂ) (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom P.d → ℝ) (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ) (p : ℕ)
    (ha : AnsatzAt P μ g a Fev R E Et p) : AnsatzAt P μ g a Fev (clipRemainder p R) E Et p := by
  have h1 : clipRemainder p R p = R p := clipRemainder_eq R le_rfl
  have h2 (N : ℕ) {w : ℕ} (t : ℝ) (ζ : Fin w → ℤˣ) (n : Fin w → (Fin P.d → ℤ)) :
      truncSum P (inputsF P (clipRemainder p R)) p N t ζ n = truncSum P (inputsF P R) p N t ζ n :=
    truncSum_clip P R (by omega) N t ζ n
  obtain ⟨h1', ⟨hS, hE, hcov⟩, h2', h3, h4⟩ := ha
  refine ⟨h1', ⟨by rw [h1]; exact hS, hE, fun n n' => by rw [h1]; exact hcov n n'⟩, h2', ?_, ?_⟩
  · intro m hm hmR ζ hζ n
    simp only [h2]
    exact h3 m hm hmR ζ hζ n
  · intro m hm hmR ζ hζ n N hN
    simp only [h2]
    exact h4 m hm hmR ζ hζ n N hN

/-! ## The final absorptions (`e^{−102 N}`) -/

theorem quartic_add_le_pow {N e : ℕ} (hN : 2000000 ≤ N) (he : 6 ≤ e) :
    1000000 * N ^ 4 + 102 * N ≤ N ^ e := by
  have hN1 : 1 ≤ N := by omega
  have h4 : N ≤ N ^ 4 := le_self_pow₀ hN1 (by decide)
  have h2 : 2000000 ≤ N ^ 2 := hN.trans (le_self_pow₀ hN1 (by decide))
  have h6 : 1000000 * N ^ 4 + 102 * N ≤ N ^ 6 := by
    have h := Nat.mul_le_mul_right (N ^ 4) h2
    rw [show 6 = 2 + 4 from rfl, pow_add]
    nlinarith
  exact h6.trans (Nat.pow_le_pow_right (by omega) he)

theorem env_mul_input_error_le (P : WTParams) (hd : 1 ≤ P.d) {p : ℕ} (hp : p < P.D)
    (hN : 2000000 ≤ P.N (p + 1)) {E : ℝ} (hE : E ≤ Real.exp (1000000 * (P.N (p + 1) : ℝ) ^ 4)) :
    E * Real.exp (-(P.N p : ℝ)) ≤ Real.exp (-(102 * (P.N (p + 1) : ℝ))) := by
  have hk : 6 ≤ (40 * P.d) * (40 * P.d) := by nlinarith
  have h := quartic_add_le_pow hN hk
  rw [← N_succ_relation P hp] at h
  have hr : 1000000 * (P.N (p + 1) : ℝ) ^ 4 + 102 * P.N (p + 1) ≤ (P.N p : ℝ) := by exact_mod_cast h
  have hm := mul_le_mul_of_nonneg_right hE (Real.exp_pos (-(P.N p : ℝ))).le
  rw [← Real.exp_add] at hm
  exact hm.trans (Real.exp_le_exp.mpr (by linarith))

theorem env_mul_tail_le {N : ℕ} (hN : 20 ≤ N) {E q : ℝ} (hE : E ≤ Real.exp (1000000 * (N : ℝ) ^ 4))
    (hq : 0 ≤ q) (hq' : q ≤ Real.exp (-4000000)) :
    E * q ^ ((N ^ 4 + 1) - 2 * N) ≤ Real.exp (-(102 * (N : ℝ))) := by
  set J := (N ^ 4 + 1) - 2 * N with hJ
  have hpow : q ^ J ≤ Real.exp (-4000000 * (J : ℝ)) := by
    have h := pow_le_pow_left₀ hq hq' J
    simpa only [← Real.exp_nat_mul, mul_comm (J : ℝ)] using h
  have hprod := mul_le_mul hE hpow (pow_nonneg hq _) (Real.exp_pos _).le
  rw [← Real.exp_add] at hprod
  have hJN := total_order_tail_cutoff_large (w := 2) hN (by omega)
  have h1 : (N : ℝ) ≤ (N : ℝ) ^ 4 := le_self_pow₀ (by exact_mod_cast (by omega : 1 ≤ N)) (by decide)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  exact hprod.trans (Real.exp_le_exp.mpr (by rw [← hJ] at hJN; nlinarith))

theorem pair_weight_le (P : WTParams) (hd : 1 ≤ P.d) {p : ℕ} (hp : p < P.D) (n : Fin P.d → ℤ) :
    (∏ _j : Fin 2, jbr (latticePoint P.L n)) ^ (-((P.Lambda p : ℝ) / 4)) ≤
      jbr (latticePoint P.L n) ^ (-(4 * P.Lambda (p + 1) : ℝ)) := by
  have hj := one_le_jbr (latticePoint P.L n)
  rw [Fin.prod_univ_two, Real.mul_rpow (jbr_pos _).le (jbr_pos _).le, ← Real.rpow_add (jbr_pos _)]
  apply Real.rpow_le_rpow_of_exponent_le hj
  have h := lambda_quarter_ge_twice_succ P hd hp
  linarith

/-! ## The size conditions -/

/-- The parameter conditions used by CPL-1. -/
structure CplSizes (P : WTParams) (C : ℝ) : Prop where
  dim : 1 ≤ P.d
  delta_pos : 0 < P.δ
  delta_le : P.δ ≤ 1
  gamma_le : P.γ ≤ (P.d : ℝ)
  small_delta : P.δ ^ (P.ν / 2) ≤ Real.exp (-4000000)
  L_exp : Real.exp 2 ≤ P.L
  C_ge : 2 ≤ C
  C_le : C ≤ P.L
  base : baseLatticeSum P.d ≤ P.L
  phi : ∀ p, p < P.D → ∀ k, |P.φ (P.δ * p) k| ≤ (C - 1) * jbr k ^ (-(P.Lambda p : ℝ))
  stage : ∀ p, p < P.D → 2000000 ≤ P.N (p + 1) ∧ 2 * P.d + 4 ≤ P.N (p + 1) ∧
    (P.Lambda p : ℝ) / 4 ≤ P.N (p + 1)

/-! ## CPL-1 -/

/-- **CPL-1, deterministic parameters.** -/
theorem cplATr_body (P : WTParams) (C : ℝ) (hS : CplSizes P C) : OX3CplBodyV.{u} .aTr P := by
  classical
  intro Ω _ μ _ g hG p hp a Fev R E Et ha t ht n
  obtain ⟨hd, hδ, hδ1, hγ, hq, hLexp, hC, hCL, hbase, hφ, hstage⟩ := hS
  obtain ⟨hN, hNdim, hbN⟩ := hstage p hp
  have hsmall := small_delta_consequences hδ hq
  have hL1 : 1 ≤ P.L := (by linarith [Real.add_one_le_exp (2 : ℝ)] : (1 : ℝ) ≤ Real.exp 2).trans hLexp
  have hL0 : 0 < P.L := zero_lt_one.trans_le hL1
  -- the modified events and remainder
  let Fev' := rapidFev P g Fev
  let R' := clipRemainder p R
  have ha' : AnsatzAt P μ g a Fev' R' E Et p :=
    ansatzAt_clip P μ g a Fev' R E Et p (ansatzAt_rapidFev μ g hG hL0 a Fev R E Et p (ha p le_rfl))
  have hrapid' : ∀ ω ∈ Fev' p, IsRapidDecay (initialCoeff P.L P.φin g ω) := rapid_of_mem_rapidFev g Fev p
  have hres : μ.restrict (Fev' p) = μ.restrict (Fev p) := restrict_rapidFev μ g hG hL0 Fev p
  have hF : ∀ k, |inputsF P R' p (latticePoint P.L k)| ≤
      C * jbr (latticePoint P.L k) ^ (-(P.Lambda p : ℝ)) := by
    have h := ansatz_inputsF_bracket_bound P μ g a Fev' R' E Et p ha' hL1 (C - 1) (hφ p hp)
    simpa only [sub_add_cancel] using fun k => h (latticePoint P.L k)
  have hRB : RemainderBound P R p := fun q hq => (ha q hq).2.1.1
  have hsumF := summable_clipped_inputs P R p hp.le hd hL1 hRB
  have hΛ4 := lambda_quarter_ge_dimension P hd hp
  have hΛ : (P.d : ℝ) + 1 ≤ (P.Lambda p : ℝ) / 2 := by
    have : (0 : ℝ) ≤ P.Lambda p := Nat.cast_nonneg _
    linarith
  have hR1 : 1 ≤ P.R (p + 1) := by
    by_contra h0
    have hR0 : P.R (p + 1) = 0 := by omega
    have : P.N (p + 1) = 0 := by
      simp only [WTParams.N, hR0, zero_pow (by omega : 40 * P.d ≠ 0)]
    omega
  have hw2 : 2 ≤ 100 * P.R (p + 1) := by omega
  have hNR := top_leaf_count_le_previous_range P hd hp (by omega) hw2
  have hpt : (p : ℝ) ≤ t := ht.1.le
  have htp : t ≤ (p : ℝ) + 1 := ht.2.le
  -- the identity
  have hid := integral_norm_aTr_sq_eq P μ g hG a Fev' R' E Et p ha' hrapid' hL1 hδ hsmall.2.1 C hC hF
    hsumF hΛ hNR (P.N (p + 1) ^ 4) t hpt htp n
  have hint : (∫ ω in Fev' p, ‖aTr P.L P.γ P.δ p (P.N (p + 1)) (a ω p) t n‖ ^ 2 ∂μ) =
      ∫ ω in Fev p, ‖aTr P.L P.γ P.δ p (P.N (p + 1)) (a ω p) t n‖ ^ 2 ∂μ := by rw [hres]
  rw [hint] at hid
  have hcs (N' : ℕ) : coupleSum P (inputsF P R) p N' .tr false t (latticePoint P.L n) =
      truncSum P (inputsF P R') (p + 1) N' t ![1, -1] (fun _ => n) := by
    rw [FlowerProbes.coupleSum_tr, ← Canon.truncSum_couple_eq_truncSumC]
    exact (truncSum_clip P R le_rfl N' t ![1, -1] (fun _ => n)).symm
  refine ⟨?_, ?_⟩
  · have h := integrable_norm_aTr_sq P μ g hG a Fev' R' E Et p ha' hrapid' hL1 hδ hsmall.2.1 C hC hF hΛ
      (P.N (p + 1)) hNR t n
    rw [hres] at h
    exact h
  · change ‖(((∫ ω in Fev p, ‖aTr P.L P.γ P.δ p (P.N (p + 1)) (a ω p) t n‖ ^ 2 ∂μ : ℝ)) : ℂ) -
        ∑ N ∈ Finset.range (P.N (p + 1) ^ 4 + 1),
          coupleSum P (inputsF P R) p N .tr false t (latticePoint P.L n)‖ ≤ _
    simp only [hcs]
    rw [hid]
    set M := ∑ N ∈ range (P.N (p + 1) ^ 4 + 1), truncSum P (inputsF P R') (p + 1) N t ![1, -1] (fun _ => n)
    set T := ∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧
          LG.IsTrunc p (P.N (p + 1)) (P.N p)},
          if P.N (p + 1) ^ 4 < LG.1.garden.order then
            KG P.L P.γ P.δ (inputsF P R') LG.1 t (fun _ => n) else 0
    set Er := cmattrError (μ.restrict (Fev' p)) P.L P.γ P.δ (inputsF P R') ![1, -1] (fun ω => a ω p) p
          (P.N (p + 1)) (P.N p) t (fun _ => n)
    have he : M + T + Er - M = T + Er := by ring
    rw [he]
    have hC0 : 0 ≤ C := by linarith
    have henv := stage_graftEnvelope_bound P hd p hLexp C ((P.Lambda p : ℝ) / 4) hC0 hCL hΛ4 hbN hbase
      hNdim hw2
    have hW := pair_weight_le P hd hp n
    have hW0 : 0 ≤ (∏ _j : Fin 2, jbr (latticePoint P.L n)) ^ (-((P.Lambda p : ℝ) / 4)) :=
      Real.rpow_nonneg (prod_nonneg fun _ _ => (jbr_pos _).le) _
    have hTb := couple_tail_envelope_bound P μ g a Fev' R' E Et p ha' hδ hsmall.1 hL1 C hC hF hsumF
      (fun _ => n) hd hp (P.N (p + 1)) (P.N (p + 1) ^ 4) hNR hγ hδ1 t hpt htp
    have hErb := cmattr_error_envelope_bound P μ g hG a Fev' R' E Et p ha' hrapid' hδ hsmall.2.1 hL1 C hC hF
      ![1, -1] (fun _ => n) hd hp (P.N (p + 1)) hNR hγ hδ1 t hpt htp
    have hT' : ‖T‖ ≤ Real.exp (-(102 * (P.N (p + 1) : ℝ))) *
        jbr (latticePoint P.L n) ^ (-(4 * P.Lambda (p + 1) : ℝ)) := by
      refine hTb.trans ?_
      have h := env_mul_tail_le (by omega) henv (Real.rpow_nonneg hδ.le _) hq
      exact mul_le_mul h hW hW0 (Real.exp_pos _).le
    have hEr' : ‖Er‖ ≤ Real.exp (-(102 * (P.N (p + 1) : ℝ))) *
        jbr (latticePoint P.L n) ^ (-(4 * P.Lambda (p + 1) : ℝ)) := by
      refine hErb.trans ?_
      have h := env_mul_input_error_le P hd hp hN henv
      exact mul_le_mul h hW hW0 (Real.exp_pos _).le
    have hexp : 2 * Real.exp (-(102 * (P.N (p + 1) : ℝ))) ≤ Real.exp (-(101 * (P.N (p + 1) : ℝ))) := by
      have h2 : (2 : ℝ) ≤ Real.exp (P.N (p + 1) : ℝ) := by
        have : (1 : ℝ) ≤ P.N (p + 1) := by exact_mod_cast (by omega : 1 ≤ P.N (p + 1))
        linarith [Real.add_one_le_exp (P.N (p + 1) : ℝ)]
      calc 2 * Real.exp (-(102 * (P.N (p + 1) : ℝ)))
          ≤ Real.exp (P.N (p + 1) : ℝ) * Real.exp (-(102 * (P.N (p + 1) : ℝ))) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = Real.exp (-(101 * (P.N (p + 1) : ℝ))) := by rw [← Real.exp_add]; ring_nf
    have hj0 : 0 ≤ jbr (latticePoint P.L n) ^ (-(4 * P.Lambda (p + 1) : ℝ)) :=
      Real.rpow_nonneg (jbr_pos _).le _
    calc ‖T + Er‖ ≤ ‖T‖ + ‖Er‖ := norm_add_le _ _
      _ ≤ 2 * Real.exp (-(102 * (P.N (p + 1) : ℝ))) *
            jbr (latticePoint P.L n) ^ (-(4 * P.Lambda (p + 1) : ℝ)) := by linarith
      _ ≤ Real.exp (-(101 * (P.N (p + 1) : ℝ))) *
            jbr (latticePoint P.L n) ^ (-(4 * P.Lambda (p + 1) : ℝ)) :=
          mul_le_mul_of_nonneg_right hexp hj0
      _ = jbr (latticePoint P.L n) ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
            Real.exp (-(101 * (P.N (p + 1) : ℝ))) := mul_comm _ _

end WaveTurbulence.Cpl
