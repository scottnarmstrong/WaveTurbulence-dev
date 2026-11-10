/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CplDraft.ATr
public import WaveTurbulence.Foundations.XChain.CplDraft.L0Kind
public import WaveTurbulence.Foundations.XChain.CplDraft.FamBounds

/-!
# CPL-2: the `ℒ₀` clause of O-X3-CPL

**Statement** (`wtprefix_cplL0 : WTPrefix (OX3CplBodyV .L0)`). For `L` large after `(d, 𝔇)`:
- `|ℒ₀(t)_n|²` is integrable on `F_p`;
- `|𝔼_p|ℒ₀(t)_n|² − ∑_{N ≤ N_{p+1}^4} coupleSum_N(t,n)| ≤ ⟨n⟩^{-4Λ_{p+1}} e^{-101N_{p+1}}`.

Here `coupleSum_N` has kind `ℒ₀` and no `∂_t`.

**Proof** (`cplL0_body`). The same parameters as CPL-1 (`CplSizes`); set `N = N_{p+1}`, `M = 3N + 1`.
1. `ℒ₀ = ∑_{𝒯 ∈ l0Trees N} 𝒥_𝒯` (step 1), a family in `truncatedTrees M`.
2. Step 2 gives `𝔼_p|ℒ₀|² = famKernelExpansion + famError`, on `F_p ∩ {rapid data}` with `R` clipped above
   `p`, as in CPL-1.
3. Step 3 gives `famKernelExpansion = ∑_{N' ≤ N^4} (weighted garden sum of order N') + tail`. Step 4 identifies
   the weighted garden sum of order `N'` with `coupleSum_{N'}` of kind `ℒ₀`.
4. Step 5 bounds `tail` and `famError` by `graftEnvelope d 2 M` times `(δ^{ν/2})^{N^4+1−2M}` and `e^{-N_p}`.
   Since `graftEnvelope d 2 (3N+1) = 9 graftEnvelope d 6 N ≤ 9e^{10⁶N^4}` (INDUCT
   `stage_graftEnvelope_bound`, width 6), each is `≤ e^{-102N}`.
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.Cpl

open Finset MeasureTheory Set Filter Topology Induct
open scoped ENNReal Classical

universe u

/-! ## Envelope arithmetic for `M = 3N + 1` -/

theorem graftEnvelope_three (d N : ℕ) (L b C : ℝ) :
    graftEnvelope d 2 (3 * N + 1) L b C = 9 * graftEnvelope d 6 N L b C := by
  unfold graftEnvelope
  have hH : 2 * (2 * (3 * N + 1) + 1) = 6 * (2 * N + 1) := by ring
  simp only [hH]
  have h3 : ((3 : ℝ) ^ (3 * (3 * N + 1) + 1)) ^ 2 = 9 * ((3 : ℝ) ^ (3 * N + 1)) ^ 6 := by ring
  rw [h3]
  ring

theorem quartic_add_le_pow' {N e : ℕ} (hN : 2000000 ≤ N) (he : 6 ≤ e) :
    1000000 * N ^ 4 + 102 * N + 4 ≤ N ^ e := by
  have hN1 : 1 ≤ N := by omega
  have h4 : N ≤ N ^ 4 := le_self_pow₀ hN1 (by decide)
  have h2 : 2000000 ≤ N ^ 2 := hN.trans (le_self_pow₀ hN1 (by decide))
  have h6 : 1000000 * N ^ 4 + 102 * N + 4 ≤ N ^ 6 := by
    have h := Nat.mul_le_mul_right (N ^ 4) h2
    rw [show 6 = 2 + 4 from rfl, pow_add]
    nlinarith
  exact h6.trans (Nat.pow_le_pow_right (by omega) he)

theorem env9_mul_input_error_le (P : WTParams) (hd : 1 ≤ P.d) {p : ℕ} (hp : p < P.D)
    (hN : 2000000 ≤ P.N (p + 1)) {E : ℝ} (hE : E ≤ 9 * Real.exp (1000000 * (P.N (p + 1) : ℝ) ^ 4)) :
    E * Real.exp (-(P.N p : ℝ)) ≤ Real.exp (-(102 * (P.N (p + 1) : ℝ))) := by
  have hk : 6 ≤ (40 * P.d) * (40 * P.d) := by nlinarith
  have h := quartic_add_le_pow' hN hk
  rw [← N_succ_relation P hp] at h
  have hr : 1000000 * (P.N (p + 1) : ℝ) ^ 4 + 102 * P.N (p + 1) + 4 ≤ (P.N p : ℝ) := by
    exact_mod_cast h
  have h9 : (9 : ℝ) ≤ Real.exp 4 := by
    have h3 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h16 : (2 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he1 4
    rw [h3]
    norm_num at h16
    linarith
  have hE' : E ≤ Real.exp (1000000 * (P.N (p + 1) : ℝ) ^ 4 + 4) := by
    rw [Real.exp_add]
    calc E ≤ 9 * Real.exp (1000000 * (P.N (p + 1) : ℝ) ^ 4) := hE
      _ ≤ Real.exp 4 * Real.exp (1000000 * (P.N (p + 1) : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_right h9 (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  have hm := mul_le_mul_of_nonneg_right hE' (Real.exp_pos (-(P.N p : ℝ))).le
  rw [← Real.exp_add] at hm
  exact hm.trans (Real.exp_le_exp.mpr (by linarith))

theorem env9_mul_tail_le {N : ℕ} (hN : 20 ≤ N) {E q : ℝ}
    (hE : E ≤ 9 * Real.exp (1000000 * (N : ℝ) ^ 4)) (hq : 0 ≤ q) (hq' : q ≤ Real.exp (-4000000)) :
    E * q ^ ((N ^ 4 + 1) - 2 * (3 * N + 1)) ≤ Real.exp (-(102 * (N : ℝ))) := by
  set J := (N ^ 4 + 1) - 2 * (3 * N + 1) with hJ
  have hpow : q ^ J ≤ Real.exp (-4000000 * (J : ℝ)) := by
    have h := pow_le_pow_left₀ hq hq' J
    simpa only [← Real.exp_nat_mul, mul_comm (J : ℝ)] using h
  have hJN : (N : ℝ) ^ 4 / 2 ≤ (J : ℝ) := by
    have hpow2 : 400 ≤ N ^ 2 := by
      have h := Nat.pow_le_pow_left hN 2
      norm_num at h ⊢
      exact h
    have h4 : 200 * N ^ 2 ≤ N ^ 4 := by
      have h := Nat.mul_le_mul_right (N ^ 2) hpow2
      rw [show 4 = 2 + 2 from rfl, pow_add]
      nlinarith
    have hNN : 20 * N ≤ N ^ 2 := by nlinarith
    have hJ' : N ^ 4 ≤ 2 * J := by omega
    have hr : (N : ℝ) ^ 4 ≤ 2 * (J : ℝ) := by exact_mod_cast hJ'
    linarith
  have h9 : (9 : ℝ) ≤ Real.exp 4 := by
    have h3 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h16 : (2 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he1 4
    rw [h3]
    norm_num at h16
    linarith
  have hE' : E ≤ Real.exp (1000000 * (N : ℝ) ^ 4 + 4) := by
    rw [Real.exp_add]
    calc E ≤ 9 * Real.exp (1000000 * (N : ℝ) ^ 4) := hE
      _ ≤ Real.exp 4 * Real.exp (1000000 * (N : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_right h9 (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  have hprod := mul_le_mul hE' hpow (pow_nonneg hq _) (Real.exp_pos _).le
  rw [← Real.exp_add] at hprod
  have h1 : (N : ℝ) ≤ (N : ℝ) ^ 4 := le_self_pow₀ (by exact_mod_cast (by omega : 1 ≤ N)) (by decide)
  have h20 : (20 : ℝ) ≤ N := by exact_mod_cast hN
  exact hprod.trans (Real.exp_le_exp.mpr (by nlinarith))

/-! ## CPL-2 -/

/-- **CPL-2, deterministic parameters.** -/
theorem cplL0_body (P : WTParams) (C : ℝ) (hS : CplSizes P C) : OX3CplBodyV.{u} .L0 P := by
  intro Ω _ μ _ g hG p hp a Fev R E Et ha t ht n
  obtain ⟨hd, hδ, hδ1, hγ, hq, hLexp, hC, hCL, hbase, hφ, hstage⟩ := hS
  obtain ⟨hN, hNdim, hbN⟩ := hstage p hp
  have hsmall := small_delta_consequences hδ hq
  have hL1 : 1 ≤ P.L := (by linarith [Real.add_one_le_exp (2 : ℝ)] : (1 : ℝ) ≤ Real.exp 2).trans hLexp
  have hL0 : 0 < P.L := zero_lt_one.trans_le hL1
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
  have hw6 : 6 ≤ 100 * P.R (p + 1) := by omega
  have hNR6 := top_leaf_count_le_previous_range P hd hp (by omega) hw6
  have hNR : 2 * (2 * (3 * P.N (p + 1) + 1) + 1) ≤ 2 * P.R p := by omega
  have hpt : (p : ℝ) ≤ t := ht.1.le
  have htp : t ≤ (p : ℝ) + 1 := ht.2.le
  have hsub := l0Trees_subset (P.N (p + 1))
  -- `ℒ₀ = famTerm` almost surely
  have hcsF := ansatz_input_summable (ha p le_rfl) hL0
  have hae : (fun ω => ‖cplRand P (a ω p) p .L0 t n‖ ^ 2) =ᵐ[μ.restrict (Fev p)]
      fun ω => ‖famTerm P.L P.γ P.δ p (3 * P.N (p + 1) + 1) (l0Trees (P.N (p + 1))) (a ω p) t n‖ ^ 2 := by
    filter_upwards [hcsF] with ω hω
    change ‖Lop P.L P.γ P.δ p (P.N (p + 1)) (a ω p) 0 (fun _ _ => 0) t n‖ ^ 2 = _
    rw [Lop_zero_eq_sum_l0Trees P.L P.γ P.δ p (P.N (p + 1)) hω hpt n, famTerm_eq_sum _ _ _ p _ hsub]
  have hint : (∫ ω in Fev p, ‖cplRand P (a ω p) p .L0 t n‖ ^ 2 ∂μ) =
      ∫ ω in Fev' p, ‖famTerm P.L P.γ P.δ p (3 * P.N (p + 1) + 1) (l0Trees (P.N (p + 1))) (a ω p) t n‖ ^ 2 ∂μ := by
    rw [integral_congr_ae hae, hres]
  refine ⟨?_, ?_⟩
  · have h := integrable_norm_famTerm_sq P μ g hG a Fev' R' E Et p ha' hrapid' hL1 hδ hsmall.2.1 C hC hF hΛ
      (3 * P.N (p + 1) + 1) (l0Trees (P.N (p + 1))) hNR t n
    rw [hres] at h
    exact h.congr hae.symm
  · have hid := integral_norm_famTerm_sq_eq P μ g hG a Fev' R' E Et p ha' hrapid' hL1 hδ hsmall.2.1 C hC hF
      hsumF hΛ (3 * P.N (p + 1) + 1) (l0Trees (P.N (p + 1))) hNR t hpt htp n
    rw [← famKernelExpansion_eq_finsum P.L P.γ P.δ (inputsF P R') _ (P.N p) _ t hpt htp _ hsumF,
      famGarden_eq_sum_orders_add_tail P (inputsF P R') p _ (P.N p) _ (P.N (p + 1) ^ 4) t,
      famGarden_tail_eq P.L P.γ P.δ (inputsF P R') _ (P.N p) _ t hpt htp _ hsumF] at hid
    have hcs (N' : ℕ) : coupleSum P (inputsF P R) p N' .L0 false t (latticePoint P.L n) =
        ∑ᶠ LG : {LG : LayeredGarden 2 // (IsCanonC (p + 1) LG ∧
            LG.IsTrunc p (3 * P.N (p + 1) + 1) (P.N p)) ∧ LG.garden.order = N'},
          if ∀ j, layerCutForest LG.1 p j ∈ l0Trees (P.N (p + 1)) then
            KG P.L P.γ P.δ (inputsF P R') LG.1 t (fun _ => n) else 0 := by
      rw [coupleSum_L0_eq]
      refine finsum_congr fun LG => ?_
      split_ifs
      · exact (KG_clip_inputs P R LG.1 (Canon.layer_le_of_isCanonC LG.2.1.1) t _).symm
      · rfl
    change ‖(((∫ ω in Fev p, ‖cplRand P (a ω p) p .L0 t n‖ ^ 2 ∂μ : ℝ)) : ℂ) -
        ∑ N ∈ Finset.range (P.N (p + 1) ^ 4 + 1),
          coupleSum P (inputsF P R) p N .L0 false t (latticePoint P.L n)‖ ≤ _
    rw [hint, hid]
    simp only [hcs]
    set A := ∑ N ∈ range (P.N (p + 1) ^ 4 + 1), ∑ᶠ LG : {LG : LayeredGarden 2 //
          (IsCanonC (p + 1) LG ∧ LG.IsTrunc p (3 * P.N (p + 1) + 1) (P.N p)) ∧ LG.garden.order = N},
          if ∀ j, layerCutForest LG.1 p j ∈ l0Trees (P.N (p + 1)) then
            KG P.L P.γ P.δ (inputsF P R') LG.1 t (fun _ => n) else 0
    set T := ∑ top : Fin 2 → TrTree (3 * P.N (p + 1) + 1),
        if ∀ j, (top j).1 ∈ l0Trees (P.N (p + 1)) then
          (∏ j, zpowSign (![1, -1] j) (SysAPI.treePrefactor P.L P.γ P.δ P.d (top j).1)) *
            ∑ Q : {Q : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
                TopPartitionIrreducible (fun j => (top j).1) Q},
              lowerOrderTail P.L P.γ P.δ (inputsF P R') ![1, -1] (fun j => (top j).1) Q.1 p (P.N p)
                ((P.N (p + 1) ^ 4 + 1) - ∑ j, (top j).1.order) t (fun _ => n)
          else 0
    set Er := famError P.L P.γ P.δ (μ.restrict (Fev' p)) (inputsF P R') ![1, -1] (fun ω => a ω p) p
      (3 * P.N (p + 1) + 1) (P.N p) (l0Trees (P.N (p + 1))) t (fun _ => n)
    have he : A + T + Er - A = T + Er := by ring
    rw [he]
    have hC0 : 0 ≤ C := by linarith
    have henv6 := stage_graftEnvelope_bound P hd p hLexp C ((P.Lambda p : ℝ) / 4) hC0 hCL hΛ4 hbN hbase
      hNdim hw6
    have henv : graftEnvelope P.d 2 (3 * P.N (p + 1) + 1) P.L ((P.Lambda p : ℝ) / 4) C ≤
        9 * Real.exp (1000000 * (P.N (p + 1) : ℝ) ^ 4) := by
      rw [graftEnvelope_three]
      linarith
    have hW := pair_weight_le P hd hp n
    have hW0 : 0 ≤ (∏ _j : Fin 2, jbr (latticePoint P.L n)) ^ (-((P.Lambda p : ℝ) / 4)) :=
      Real.rpow_nonneg (prod_nonneg fun _ _ => (jbr_pos _).le) _
    have hTb := famTail_envelope_bound P μ g a Fev' R' E Et p ha' hδ hL1 C hC hF hd hp hγ hδ1 hsmall.1
      (3 * P.N (p + 1) + 1) (l0Trees (P.N (p + 1))) (fun _ => n) hNR t hpt htp (P.N (p + 1) ^ 4)
    have hErb := famError_envelope_bound P μ g hG a Fev' R' E Et p ha' hrapid' hδ hL1 C hC hF hd hp hγ
      hδ1 hsmall.2.1 (3 * P.N (p + 1) + 1) (l0Trees (P.N (p + 1))) ![1, -1] (fun _ => n) hNR t hpt htp
    have hT' : ‖T‖ ≤ Real.exp (-(102 * (P.N (p + 1) : ℝ))) *
        jbr (latticePoint P.L n) ^ (-(4 * P.Lambda (p + 1) : ℝ)) := by
      refine hTb.trans ?_
      have h := env9_mul_tail_le (by omega) henv (Real.rpow_nonneg hδ.le _) hq
      exact mul_le_mul h hW hW0 (Real.exp_pos _).le
    have hEr' : ‖Er‖ ≤ Real.exp (-(102 * (P.N (p + 1) : ℝ))) *
        jbr (latticePoint P.L n) ^ (-(4 * P.Lambda (p + 1) : ℝ)) := by
      refine hErb.trans ?_
      have h := env9_mul_input_error_le P hd hp hN henv
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

/-- The parameters of CPL-1 (`wtprefix_cplATr`) give the sizes. -/
theorem wtprefix_cplSizes : WTPrefix fun P => ∃ C, CplSizes P C := by
  intro d hd γ hγ
  refine ⟨1, one_pos, fun η hη φin hφin τstar hτ φ hsol => ?_⟩
  refine ⟨1, le_rfl, 1, one_pos, fun ν hν => ?_⟩
  let δ₀ := min (1 / 2) (Real.exp (-8000000 / ν))
  have hδ₀ : 0 < δ₀ := lt_min (by norm_num) (Real.exp_pos _)
  refine ⟨δ₀, hδ₀, fun δ hδ D hD htime => ?_⟩
  have hδparts : δ ≤ 1 / 2 ∧ δ ≤ Real.exp (-8000000 / ν) := by simpa only [δ₀, le_min_iff] using hδ.2
  let P0 : WTParams := ⟨d, γ, η, φin, τstar, φ, 1, ν, δ, D, 1, 1⟩
  obtain ⟨B, hB, hφB⟩ := uniform_schwartz_bracket_bound τstar φ hsol.1 (4 * P0.Lambda 0)
  let C := B + 1
  refine ⟨1, le_rfl, max 2 (assemblySizeThreshold P0 C 0), le_max_left _ _, fun L hL => ?_⟩
  let P : WTParams := ⟨d, γ, η, φin, τstar, φ, 1, ν, δ, D, 1, L⟩
  have hd1 : 1 ≤ P.d := by change 1 ≤ d; omega
  have hsize : assemblySizeThreshold P C 0 ≤ P.L := by
    change assemblySizeThreshold P0 C 0 ≤ L
    exact (le_max_right _ _).trans hL
  obtain ⟨hLexp, hCL, hbase, hst⟩ := assembly_stage_sizes P hd1 hη.1 C 0 hsize
  have htime' : P.δ * P.D ≤ P.τstar := by
    change δ * D ≤ τstar
    rw [htime, mul_comm]
  have hφ0 : ∀ t ∈ Icc 0 P.τstar, ∀ k, |P.φ t k| ≤ B * jbr k ^ (-(4 * P.Lambda 0 : ℝ)) := by
    simpa only [P, P0, WTParams.Lambda, Nat.sub_zero, Nat.cast_mul, Nat.cast_ofNat] using hφB
  refine ⟨C, hd1, hδ.1, hδparts.1.trans (by norm_num), ?_,
    delta_half_power_le_of_threshold hδ.1 hν.1 hδparts.2, hLexp, ?_, hCL, hbase, ?_, ?_⟩
  · have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    exact hγ.2.le.trans (by change (1 : ℝ) ≤ d; linarith)
  · change 2 ≤ B + 1
    linarith
  · intro p hp k
    have h := uniform_phi_stage_weight P hd1 hδ.1.le htime' B (zero_le_one.trans hB) hφ0 hp.le
      ⟨Nat.cast_nonneg p, le_rfl⟩
    have h' := phi_stage_input_weight P p B (zero_le_one.trans hB) h k
    change |P.φ (P.δ * p) k| ≤ (B + 1 - 1) * jbr k ^ (-(P.Lambda p : ℝ))
    rw [add_sub_cancel_right]
    exact h'
  · intro p hp
    obtain ⟨h1, h2, h3, -⟩ := hst p hp
    exact ⟨h1, h2, h3⟩

end WaveTurbulence.Cpl
