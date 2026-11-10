/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.CplDraft.L0
public import WaveTurbulence.Foundations.XChain.CplDraft.DtBounds
public import WaveTurbulence.Foundations.XChain.CplDraft.GenFamilyId

/-!
# CPL-3: the `∂_t a^tr` and `∂_t ℒ₀` clauses of O-X3-CPL, and O-X3-CPL

**Statements.**
- `wtprefix_cplATrDt : WTPrefix (OX3CplBodyV .aTrDt)` and `wtprefix_cplL0Dt : WTPrefix (OX3CplBodyV .L0Dt)`. For
  `L` large after `(d, 𝔇)`: `|∂_t a^tr(t)_n|²` (resp. `|∂_t ℒ₀(t)_n|²`) is integrable on `F_p`, and
  `|𝔼_p|·|² − ∑_{N ≤ N_{p+1}^4} coupleSum_N(t,n)| ≤ ⟨n⟩^{-4Λ_{p+1}} e^{-101N_{p+1}}`. Here `coupleSum_N` has kind
  `tr` (resp. `ℒ₀`) and `∂_t`.
- `oX3Cpl : OX3Cpl`: O-X3-CPL, from the four clauses (CPL-1, CPL-2 and the two above).

**Proof.** The parameters are those of CPL-1 (`CplSizes`); set `N = N_{p+1}`.
1. `∂_t a^tr = ∑_{𝒯 ∈ truncatedTrees N, 𝒯 ≠ •} ∂_t 𝒥_𝒯` and `∂_t ℒ₀ = ∑_{𝒯 ∈ l0Trees N} ∂_t 𝒥_𝒯`
   (`aTrDt_eq_famGenTerm_erase`, `L0Dt_eq_famGenTerm`): families with the coefficients `dtCoef`, `|dtCoef| ≤ 1`.
2. `famGen_dt_moment_bound`: for such a family of non-trivial trees, the generic identity
   (`integral_norm_famGenTerm_sq_eq`), the garden form of its kernel series (`famGenKernelExpansion_dt_eq_finsum`),
   the order split and the tail (`famGenGarden_dt_tail_eq`) leave the tail and the input error, bounded by
   `famGenTail_envelope_bound` and `famGenError_envelope_bound`.
3. The weighted garden sum of order `N'` is `coupleSum_{N'}` with `∂_t` (`coupleSum_trDt_eq`,
   `coupleSum_L0Dt_eq`; snapshot 8's `dt` clause).
4. The arithmetic is that of CPL-1 (`M = N`) and CPL-2 (`M = 3N + 1`).
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.Cpl

open Finset MeasureTheory Set Filter Topology Induct
open scoped ENNReal Classical

universe u

/-! ## Inputs above `p` -/

theorem kernelKgen_congr_inputs {d w : ℕ} (L γ δ : ℝ) {F F' : ℕ → Mom d → ℝ} (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (h : ∀ a : GNode LG.garden.tree, F (LG.layer a) = F' (LG.layer a)) :
    kernelKgen L γ δ F LG fix off wt up k₀ nroot nfl = kernelKgen L γ δ F' LG fix off wt up k₀ nroot nfl := by
  unfold kernelKgen
  simp only [h]

theorem kernelKgen_clip_inputs (P : WTParams) (R : ℕ → Mom P.d → ℝ) {w p : ℕ} (LG : LayeredGarden w)
    (hl : ∀ a : GNode LG.garden.tree, LG.layer a ≤ p) (fix : GBranch LG.garden.tree → Option ℝ)
    (off : Finset (GBranch LG.garden.tree)) (wt : (GNode LG.garden.tree → Mom P.d) → ℝ)
    (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom P.d) (nroot : Fin w → (Fin P.d → ℤ)) (nfl : Fin P.d → ℤ) :
    kernelKgen P.L P.γ P.δ (inputsF P (clipRemainder p R)) LG fix off wt up k₀ nroot nfl =
      kernelKgen P.L P.γ P.δ (inputsF P R) LG fix off wt up k₀ nroot nfl :=
  kernelKgen_congr_inputs P.L P.γ P.δ LG fix off wt up k₀ nroot nfl (fun a => inputsF_clip_eq P R (hl a))

/-! ## The generic `∂_t` moment bound -/

section

variable (P : WTParams) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ) (hG : IsGaussianData μ g)
    (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
    (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ) (p : ℕ)
    (ha : AnsatzAt P μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff P.L P.φin g ω))
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hsmall : P.δ ^ P.ν ≤ 1 / 2) (hsmall' : P.δ ^ (P.ν / 2) ≤ 1 / 2)
    (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF P R p (latticePoint P.L n)| ≤
      C * jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ)))
    (hsumF : ∀ q, Summable fun m : Fin P.d → ℤ => |inputsF P R q (latticePoint P.L m)|)
    (hΛ : (P.d : ℝ) + 1 ≤ (P.Lambda p : ℝ) / 2) (hd : 1 ≤ P.d) (hp : p < P.D)

include hG ha hrapid hL hδ hsmall hsmall' hC hF hsumF hΛ hd hp in
/-- **The `∂_t` moment bound for a family of non-trivial trees.** The second moment of `∑_{𝒯 ∈ 𝒮} ∂_t 𝒥_𝒯`
minus the root-fixed garden sums of orders `≤ Ncut` is at most the tail envelope plus the input-error envelope. -/
theorem famGen_dt_moment_bound (M : ℕ) (𝒮 : Finset TTree) (h𝒮 : ∀ T ∈ 𝒮, T ≠ .leaf)
    (hNR : 2 * (2 * M + 1) ≤ 2 * P.R p) {t : ℝ} (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (hcoef : ∀ T κ, ‖dtCoef (d := P.d) P.L P.γ P.δ p t T κ‖ ≤ 1) (n : Fin P.d → ℤ) (Ncut : ℕ) :
    ‖(((∫ ω in Fev p, ‖famGenTerm M 𝒮 (dtCoef P.L P.γ P.δ p t) (a ω p) n‖ ^ 2 ∂μ : ℝ)) : ℂ) -
        ∑ N ∈ range (Ncut + 1), ∑ᶠ LG : {LG : LayeredGarden 2 //
          (IsCanonC (p + 1) LG ∧ LG.IsTrunc p M (P.N p)) ∧ LG.garden.order = N},
          if ∀ j, layerCutForest LG.1 p j ∈ 𝒮 then
            kernelKgen P.L P.γ P.δ (inputsF P R) LG.1 (rootFix t) ∅ (fun _ => 1) (fun _ => t) 0 (fun _ => n) 0
          else 0‖ ≤
      graftEnvelope P.d 2 M P.L ((P.Lambda p : ℝ) / 4) C * (P.δ ^ (P.ν / 2)) ^ ((Ncut + 1) - 2 * M) *
          (∏ _j : Fin 2, jbr (latticePoint P.L n)) ^ (-((P.Lambda p : ℝ) / 4)) +
        graftEnvelope P.d 2 M P.L ((P.Lambda p : ℝ) / 4) C * Real.exp (-(P.N p : ℝ)) *
          (∏ _j : Fin 2, jbr (latticePoint P.L n)) ^ (-((P.Lambda p : ℝ) / 4)) := by
  have hid := integral_norm_famGenTerm_sq_eq P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ M 𝒮
    (dtCoef P.L P.γ P.δ p t) hcoef hNR n
  rw [← famGenKernelExpansion_dt_eq_finsum P.L P.γ P.δ M (P.N p) 𝒮 h𝒮 (inputsF P R) hpt htp (fun _ => n) hsumF,
    gardenSum_eq_sum_orders_add_tail p M (P.N p) (fun LG => if ∀ j, layerCutForest LG p j ∈ 𝒮 then
      kernelKgen P.L P.γ P.δ (inputsF P R) LG (rootFix t) ∅ (fun _ => 1) (fun _ => t) 0 (fun _ => n) 0 else 0)
      Ncut,
    famGenGarden_dt_tail_eq P.L P.γ P.δ (inputsF P R) M (P.N p) 𝒮 h𝒮 hpt htp (fun _ => n) hsumF Ncut] at hid
  rw [hid]
  have key : ∀ A T Er : ℂ, ‖A + T + Er - A‖ ≤ ‖T‖ + ‖Er‖ := fun A T Er => by
    rw [show A + T + Er - A = T + Er by ring]
    exact norm_add_le _ _
  refine (key _ _ _).trans (add_le_add ?_ ?_)
  · exact famGenTail_envelope_bound P μ g a Fev R E Et p ha hδ hL C hC hF hd hp hsmall' M 𝒮
      (dtCoef P.L P.γ P.δ p t) hcoef (fun _ => n) hNR Ncut
  · exact famGenError_envelope_bound P μ g hG a Fev R E Et p ha hrapid hδ hL C hC hF hd hp hsmall M 𝒮
      (dtCoef P.L P.γ P.δ p t) hcoef ![1, -1] (fun _ => n) hNR

end

/-! ## The two clauses -/

theorem two_exp_neg_102_le {N : ℕ} (hN : 1 ≤ N) :
    2 * Real.exp (-(102 * (N : ℝ))) ≤ Real.exp (-(101 * (N : ℝ))) := by
  have h2 : (2 : ℝ) ≤ Real.exp (N : ℝ) := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith [Real.add_one_le_exp (N : ℝ)]
  calc 2 * Real.exp (-(102 * (N : ℝ)))
      ≤ Real.exp (N : ℝ) * Real.exp (-(102 * (N : ℝ))) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp (-(101 * (N : ℝ))) := by rw [← Real.exp_add]; ring_nf

theorem add_le_of_two_exp {N : ℕ} (hN : 1 ≤ N) {X Y j : ℝ} (hj : 0 ≤ j)
    (hX : X ≤ Real.exp (-(102 * (N : ℝ))) * j) (hY : Y ≤ Real.exp (-(102 * (N : ℝ))) * j) :
    X + Y ≤ j * Real.exp (-(101 * (N : ℝ))) := by
  have h := mul_le_mul_of_nonneg_right (two_exp_neg_102_le hN) hj
  linarith

/-- **CPL-3, `∂_t a^tr`, deterministic parameters.** -/
theorem cplATrDt_body (P : WTParams) (C : ℝ) (hS : CplSizes P C) : OX3CplBodyV.{u} .aTrDt P := by
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
  have hw2 : 2 ≤ 100 * P.R (p + 1) := by omega
  have hNR : 2 * (2 * P.N (p + 1) + 1) ≤ 2 * P.R p :=
    top_leaf_count_le_previous_range P hd hp (by omega) hw2
  have hpt : (p : ℝ) ≤ t := ht.1.le
  have htp : t ≤ (p : ℝ) + 1 := ht.2.le
  have hcoupling := abs_coupling_le_one hL1 hγ hδ.le hδ1
  have hcoef : ∀ T κ, ‖dtCoef (d := P.d) P.L P.γ P.δ p t T κ‖ ≤ 1 :=
    fun T κ => norm_dtCoef_le P.L P.γ P.δ p hcoupling hpt htp T κ
  have h𝒮 : ∀ T ∈ (truncatedTrees (P.N (p + 1))).erase .leaf, T ≠ .leaf := fun T hT => ne_of_mem_erase hT
  -- `∂_t a^tr = famGenTerm` almost surely
  have hcsF := ansatz_input_summable (ha p le_rfl) hL0
  have hae : (fun ω => ‖cplRand P (a ω p) p .aTrDt t n‖ ^ 2) =ᵐ[μ.restrict (Fev p)]
      fun ω => ‖famGenTerm (P.N (p + 1)) ((truncatedTrees (P.N (p + 1))).erase .leaf)
        (dtCoef P.L P.γ P.δ p t) (a ω p) n‖ ^ 2 := by
    filter_upwards [hcsF] with ω hω
    change ‖aTrDt P.L P.γ P.δ p (P.N (p + 1)) (a ω p) t n‖ ^ 2 = _
    rw [aTrDt_eq_famGenTerm_erase P.L P.γ P.δ p _ hω t n]
  have hint : (∫ ω in Fev p, ‖cplRand P (a ω p) p .aTrDt t n‖ ^ 2 ∂μ) =
      ∫ ω in Fev' p, ‖famGenTerm (P.N (p + 1)) ((truncatedTrees (P.N (p + 1))).erase .leaf)
        (dtCoef P.L P.γ P.δ p t) (a ω p) n‖ ^ 2 ∂μ := by
    rw [integral_congr_ae hae, hres]
  refine ⟨?_, ?_⟩
  · have h := integrable_norm_famGenTerm_sq P μ g hG a Fev' R' E Et p ha' hrapid' hL1 hδ hsmall.2.1 C hC hF hΛ
      (P.N (p + 1)) ((truncatedTrees (P.N (p + 1))).erase .leaf) (dtCoef P.L P.γ P.δ p t) hcoef hNR n
    rw [hres] at h
    exact h.congr hae.symm
  · have hcs (N' : ℕ) : coupleSum P (inputsF P R) p N' .tr true t (latticePoint P.L n) =
        ∑ᶠ LG : {LG : LayeredGarden 2 // (IsCanonC (p + 1) LG ∧
            LG.IsTrunc p (P.N (p + 1)) (P.N p)) ∧ LG.garden.order = N'},
          if ∀ j, layerCutForest LG.1 p j ∈ (truncatedTrees (P.N (p + 1))).erase .leaf then
            kernelKgen P.L P.γ P.δ (inputsF P R') LG.1 (rootFix t) ∅ (fun _ => 1) (fun _ => t) 0
              (fun _ => n) 0 else 0 := by
      rw [coupleSum_trDt_eq]
      refine finsum_congr fun LG => ?_
      split_ifs
      · exact (kernelKgen_clip_inputs P R LG.1 (Canon.layer_le_of_isCanonC LG.2.1.1) _ _ _ _ _ _ _).symm
      · rfl
    change ‖(((∫ ω in Fev p, ‖cplRand P (a ω p) p .aTrDt t n‖ ^ 2 ∂μ : ℝ)) : ℂ) -
        ∑ N ∈ Finset.range (P.N (p + 1) ^ 4 + 1),
          coupleSum P (inputsF P R) p N .tr true t (latticePoint P.L n)‖ ≤ _
    rw [hint]
    simp only [hcs]
    refine (famGen_dt_moment_bound P μ g hG a Fev' R' E Et p ha' hrapid' hL1 hδ hsmall.2.1 hsmall.1 C hC hF
      hsumF hΛ hd hp (P.N (p + 1)) _ h𝒮 hNR hpt htp hcoef n (P.N (p + 1) ^ 4)).trans ?_
    have hC0 : 0 ≤ C := by linarith
    have henv := stage_graftEnvelope_bound P hd p hLexp C ((P.Lambda p : ℝ) / 4) hC0 hCL hΛ4 hbN hbase
      hNdim hw2
    have hW := pair_weight_le P hd hp n
    have hW0 : 0 ≤ (∏ _j : Fin 2, jbr (latticePoint P.L n)) ^ (-((P.Lambda p : ℝ) / 4)) :=
      Real.rpow_nonneg (prod_nonneg fun _ _ => (jbr_pos _).le) _
    have hT := mul_le_mul (env_mul_tail_le (by omega) henv (Real.rpow_nonneg hδ.le _) hq) hW hW0
      (Real.exp_pos _).le
    have hEr := mul_le_mul (env_mul_input_error_le P hd hp hN henv) hW hW0 (Real.exp_pos _).le
    exact add_le_of_two_exp (by omega) (Real.rpow_nonneg (jbr_pos _).le _) hT hEr

/-- **CPL-3, `∂_t ℒ₀`, deterministic parameters.** -/
theorem cplL0Dt_body (P : WTParams) (C : ℝ) (hS : CplSizes P C) : OX3CplBodyV.{u} .L0Dt P := by
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
  have hcoupling := abs_coupling_le_one hL1 hγ hδ.le hδ1
  have hcoef : ∀ T κ, ‖dtCoef (d := P.d) P.L P.γ P.δ p t T κ‖ ≤ 1 :=
    fun T κ => norm_dtCoef_le P.L P.γ P.δ p hcoupling hpt htp T κ
  have h𝒮 : ∀ T ∈ l0Trees (P.N (p + 1)), T ≠ .leaf := fun T hT => ne_leaf_of_mem_l0Trees hT
  -- `∂_t ℒ₀ = famGenTerm` almost surely
  have hcsF := ansatz_input_summable (ha p le_rfl) hL0
  have hae : (fun ω => ‖cplRand P (a ω p) p .L0Dt t n‖ ^ 2) =ᵐ[μ.restrict (Fev p)]
      fun ω => ‖famGenTerm (3 * P.N (p + 1) + 1) (l0Trees (P.N (p + 1)))
        (dtCoef P.L P.γ P.δ p t) (a ω p) n‖ ^ 2 := by
    filter_upwards [hcsF] with ω hω
    change ‖L0Dt P.L P.γ P.δ p (P.N (p + 1)) (a ω p) t n‖ ^ 2 = _
    rw [L0Dt_eq_famGenTerm P.L P.γ P.δ p _ hω t n]
  have hint : (∫ ω in Fev p, ‖cplRand P (a ω p) p .L0Dt t n‖ ^ 2 ∂μ) =
      ∫ ω in Fev' p, ‖famGenTerm (3 * P.N (p + 1) + 1) (l0Trees (P.N (p + 1)))
        (dtCoef P.L P.γ P.δ p t) (a ω p) n‖ ^ 2 ∂μ := by
    rw [integral_congr_ae hae, hres]
  refine ⟨?_, ?_⟩
  · have h := integrable_norm_famGenTerm_sq P μ g hG a Fev' R' E Et p ha' hrapid' hL1 hδ hsmall.2.1 C hC hF hΛ
      (3 * P.N (p + 1) + 1) (l0Trees (P.N (p + 1))) (dtCoef P.L P.γ P.δ p t) hcoef hNR n
    rw [hres] at h
    exact h.congr hae.symm
  · have hcs (N' : ℕ) : coupleSum P (inputsF P R) p N' .L0 true t (latticePoint P.L n) =
        ∑ᶠ LG : {LG : LayeredGarden 2 // (IsCanonC (p + 1) LG ∧
            LG.IsTrunc p (3 * P.N (p + 1) + 1) (P.N p)) ∧ LG.garden.order = N'},
          if ∀ j, layerCutForest LG.1 p j ∈ l0Trees (P.N (p + 1)) then
            kernelKgen P.L P.γ P.δ (inputsF P R') LG.1 (rootFix t) ∅ (fun _ => 1) (fun _ => t) 0
              (fun _ => n) 0 else 0 := by
      rw [coupleSum_L0Dt_eq]
      refine finsum_congr fun LG => ?_
      split_ifs
      · exact (kernelKgen_clip_inputs P R LG.1 (Canon.layer_le_of_isCanonC LG.2.1.1) _ _ _ _ _ _ _).symm
      · rfl
    change ‖(((∫ ω in Fev p, ‖cplRand P (a ω p) p .L0Dt t n‖ ^ 2 ∂μ : ℝ)) : ℂ) -
        ∑ N ∈ Finset.range (P.N (p + 1) ^ 4 + 1),
          coupleSum P (inputsF P R) p N .L0 true t (latticePoint P.L n)‖ ≤ _
    rw [hint]
    simp only [hcs]
    refine (famGen_dt_moment_bound P μ g hG a Fev' R' E Et p ha' hrapid' hL1 hδ hsmall.2.1 hsmall.1 C hC hF
      hsumF hΛ hd hp (3 * P.N (p + 1) + 1) _ h𝒮 hNR hpt htp hcoef n (P.N (p + 1) ^ 4)).trans ?_
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
    have hT := mul_le_mul (env9_mul_tail_le (by omega) henv (Real.rpow_nonneg hδ.le _) hq) hW hW0
      (Real.exp_pos _).le
    have hEr := mul_le_mul (env9_mul_input_error_le P hd hp hN henv) hW hW0 (Real.exp_pos _).le
    exact add_le_of_two_exp (by omega) (Real.rpow_nonneg (jbr_pos _).le _) hT hEr

/-- **O-X3-CPL**: all four couple-moment clauses, with the parameters of CPL-1. -/
theorem oX3Cpl : OX3Cpl.{u} :=
  wtprefix_cplSizes.mono fun P ⟨C, hS⟩ => OX3CplBody_of_forall fun v => by
    cases v
    · exact cplATr_body P C hS
    · exact cplL0_body P C hS
    · exact cplATrDt_body P C hS
    · exact cplL0Dt_body P C hS

end WaveTurbulence.Cpl
