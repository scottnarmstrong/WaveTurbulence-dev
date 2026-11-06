/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerSums
public import WaveTurbulence.Foundations.XChain.CplDraft.L0
public import WaveTurbulence.Foundations.XChain.CplDraft.Dt
public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Est
public import WaveTurbulence.Foundations.XChain.InductLogSize

/-!
# X2E-4: O-X2-EXP without cutoffs

`OX2ExpNoCutBody`: the body of O-X2-EXP (`flower/X2-Est.lean`) for `cut1 = cut2 = none`, verbatim otherwise.

**Statements.**
- `env_mul_tail_le_w`: the envelope times the order tail `q^{N^4 + 1 − wN}` is `≤ e^{−102 N}` (`w ≤ 100 N`);
- `X2Sizes`: CPL's size conditions, `1 ≤ P` and `e^{9P} ≤ L`; `wtprefixP_x2Sizes`;
- `flowerSum_clip`: the flower sums see the inputs in layers `≤ p` only;
- `ox2ExpNoCut_body`, **`oX2ExpNoCut : WTPrefixP OX2ExpNoCutBody`**.
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.X2E

open Finset MeasureTheory Set Induct SysAPI Cpl
open scoped Classical

/-- **The body of O-X2-EXP without cutoffs.** -/
def OX2ExpNoCutBody.{u} (Pm : ℕ) (P : WTParams) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
  ∀ p : ℕ, p < P.D →
  ∀ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
    (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
    (∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q) →
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
  ∀ (kind : FlowerKind) (pat : FixPat) (dagger : Option (Fin 3 → Mom P.d)),
    (pat = .plain ∨ pat = .dRoot) →
    Integrable (fun ω => ‖randK P a p kind pat dagger none none ζ t s n n' ω‖ ^ (2 * Pm))
      (μ.restrict (Fev p)) ∧
    ‖(((∫ ω in Fev p, ‖randK P a p kind pat dagger none none ζ t s n n' ω‖ ^ (2 * Pm) ∂μ : ℝ)) : ℂ) -
        ∑ N ∈ Finset.range (P.N (p + 1) ^ 4 + 1),
          flowerSumP P (inputsF P R) p N (w := 2 * Pm) kind (fun _ => pat) (dagger.map fun c _ => c)
            none none ζ t s n n'‖ ≤
      x2Bound P Pm p ζ n n' (fun _ : Fin (2 * Pm) => pat) none none *
        Real.exp (-(101 * P.N (p + 1) : ℝ))

/-- O-X2-EXP without cutoffs. -/
def OX2ExpNoCut.{u} : Prop := WTPrefixP OX2ExpNoCutBody.{u}

/-! ## Arithmetic -/

theorem env_mul_tail_le_w {N w : ℕ} (hN : 20 ≤ N) (hw : w ≤ 100 * N) {E q : ℝ}
    (hE : E ≤ Real.exp (1000000 * (N : ℝ) ^ 4)) (hq : 0 ≤ q) (hq' : q ≤ Real.exp (-4000000)) :
    E * q ^ ((N ^ 4 + 1) - w * N) ≤ Real.exp (-(102 * (N : ℝ))) := by
  set J := (N ^ 4 + 1) - w * N with hJ
  have hpow : q ^ J ≤ Real.exp (-4000000 * (J : ℝ)) := by
    have h := pow_le_pow_left₀ hq hq' J
    simpa only [← Real.exp_nat_mul, mul_comm (J : ℝ)] using h
  have hprod := mul_le_mul hE hpow (pow_nonneg hq _) (Real.exp_pos _).le
  rw [← Real.exp_add] at hprod
  have hJN := total_order_tail_cutoff_large hN hw
  have h1 : (N : ℝ) ≤ (N : ℝ) ^ 4 := le_self_pow₀ (by exact_mod_cast (by omega : 1 ≤ N)) (by decide)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  exact hprod.trans (Real.exp_le_exp.mpr (by rw [← hJ] at hJN; nlinarith))

theorem two_exp_le (N : ℕ) (hN : 1 ≤ N) :
    2 * Real.exp (-(102 * (N : ℝ))) ≤ Real.exp (-(101 * (N : ℝ))) := by
  have h2 : (2 : ℝ) ≤ Real.exp (N : ℝ) := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith [Real.add_one_le_exp (N : ℝ)]
  calc 2 * Real.exp (-(102 * (N : ℝ))) ≤ Real.exp (N : ℝ) * Real.exp (-(102 * (N : ℝ))) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp (-(101 * (N : ℝ))) := by rw [← Real.exp_add]; ring_nf

/-- The bracket of `x2Bound`. -/
theorem bracketW_le (P : WTParams) {p : ℕ} (ζ : ℤˣ) (n n' : Fin P.d → ℤ) (Pm : ℕ) (b : ℝ)
    (hb : 2 * (P.Lambda (p + 1) : ℝ) ≤ b) :
    bracketW P ζ n n' Pm b ≤
      jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^ (-(4 * P.Lambda (p + 1) * Pm : ℝ)) := by
  have hlin : latticePoint P.L (n - (ζ : ℤ) • n') = latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n' := by
    rw [← latticePoint_units_smul]
    exact map_sub (latticePointAddHom P.L) n ((ζ : ℤ) • n')
  unfold bracketW
  rw [prod_const, card_univ, Fintype.card_fin, hlin, ← Real.rpow_natCast,
    ← Real.rpow_mul (jbr_pos _).le]
  apply Real.rpow_le_rpow_of_exponent_le (one_le_jbr _)
  have hPm : (0 : ℝ) ≤ Pm := Nat.cast_nonneg _
  push_cast
  nlinarith

theorem jbr_le_x2Bound (P : WTParams) (hL : 1 ≤ P.L) (Pm p : ℕ) (ζ : ℤˣ) (n n' : Fin P.d → ℤ) (pat : FixPat) :
    jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^ (-(4 * P.Lambda (p + 1) * Pm : ℝ)) ≤
      x2Bound P Pm p ζ n n' (fun _ : Fin (2 * Pm) => pat) none none := by
  unfold x2Bound
  simp only [Option.elim, mul_one]
  have h1 : 1 ≤ P.L ^ ((if ∀ _j : Fin (2 * Pm), pat = .plain then (1 : ℝ) else 2) * (100 * P.d : ℝ) ^ 3 * Pm) :=
    Real.one_le_rpow hL (by positivity)
  exact le_mul_of_one_le_right (Real.rpow_nonneg (jbr_pos _).le _) h1

/-! ## Sizes -/

/-- **The size conditions of X2E**: CPL's, `1 ≤ P`, `e^{9P} ≤ L` and `(8/δ)² ≤ L`. -/
structure X2Sizes (Pm : ℕ) (P : WTParams) (C : ℝ) : Prop where
  cpl : CplSizes P C
  pm : 1 ≤ Pm
  L_pm : Real.exp (9 * Pm) ≤ P.L
  L_delta : (8 / P.δ) ^ 2 ≤ P.L
  gamma_nonneg : 0 ≤ P.γ

theorem wtprefixP_x2Sizes : WTPrefixP fun Pm P => ∃ C, X2Sizes Pm P C := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := wtprefix_cplSizes d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
  refine ⟨1, fun Pm hPm => ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
  refine ⟨C₂, hC₂, max (max L₀ (Real.exp (9 * Pm))) ((8 / δ) ^ 2), hL₀.trans ((le_max_left _ _).trans
    (le_max_left _ _)), fun L hL => ?_⟩
  obtain ⟨C, hS⟩ := H L (((le_max_left _ _).trans (le_max_left _ _)).trans hL)
  exact ⟨C, hS, hPm, ((le_max_right _ _).trans (le_max_left _ _)).trans hL, (le_max_right _ _).trans hL, hγ.1.le⟩

/-- The sizes at a layer. -/
theorem x2Sizes_stage {Pm : ℕ} {P : WTParams} {C : ℝ} (hS : X2Sizes Pm P C) {p : ℕ} (hp : p < P.D) :
    9 * Pm ≤ P.R (p + 1) ∧ 9 * Pm ≤ P.N (p + 1) ∧
      (2 * Pm) * (2 * (3 * P.N (p + 1) + 1) + 1) ≤ 2 * P.R p := by
  have hd := hS.cpl.dim
  have hLexp := hS.cpl.L_exp
  have hL0 : 0 < P.L := (Real.exp_pos 2).trans_le hLexp
  have hlog : (9 * Pm : ℝ) ≤ Real.log P.L := (Real.le_log_iff_exp_le hL0).mpr (by exact_mod_cast hS.L_pm)
  have hR : (9 * Pm : ℝ) ≤ P.R (p + 1) := hlog.trans (log_le_Rdown P hd hLexp _)
  have hR' : 9 * Pm ≤ P.R (p + 1) := by exact_mod_cast hR
  have hN : 9 * Pm ≤ P.N (p + 1) := hR'.trans (R_le_N P hd (p + 1))
  refine ⟨hR', hN, ?_⟩
  rw [R_succ_relation P hp]
  set N := P.N (p + 1)
  have hN1 : 1 ≤ N := by have := hS.pm; omega
  have h2 : N ^ 2 ≤ N ^ (40 * P.d) := Nat.pow_le_pow_right hN1 (by omega)
  have h3 : Pm * (2 * (3 * N + 1) + 1) ≤ N ^ 2 := by
    have : Pm * (2 * (3 * N + 1) + 1) ≤ Pm * (9 * N) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have h4 : (2 * Pm) * (2 * (3 * N + 1) + 1) = 2 * (Pm * (2 * (3 * N + 1) + 1)) := by ring
  rw [h4]
  omega

/-! ## The flower sums and the clipped inputs -/

theorem flowerSum_clip (P : WTParams) (R : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ} (kind : FlowerKind)
    (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ) (ζ : ℤˣ) (t s : ℝ)
    (n n' : Fin P.d → ℤ) :
    flowerSumP P (inputsF P (clipRemainder p R)) p N kind pat dagger cut1 cut2 ζ t s n n' =
      flowerSumP P (inputsF P R) p N kind pat dagger cut1 cut2 ζ t s n n' := by
  unfold flowerSumP
  refine finsum_congr fun LG => finsum_congr fun h => ?_
  exact kernelKgen_clip_inputs P R LG (fun a => Canon.layer_le_of_isCanonH h.1 a) _ _ _ _ _ _ _

/-! ## The body -/

/-- **The core estimate**: with identified cutoff weights and a coefficient weight `(b, K)`, the error of the
expansion is `≤ e^{−101N_{p+1}} K (∏_j ⟨n − ζ n'⟩)^{−b}`. -/
theorem x2_core.{u} (Pm : ℕ) (P : WTParams) (C : ℝ) (hS : X2Sizes Pm P C) (Ω : Type u) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : (Fin P.d → ℤ) → Ω → ℂ) (hG : IsGaussianData μ g) (p : ℕ)
    (hp : p < P.D) (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
    (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ)
    (ha : ∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q) (t : ℝ) (ht : t ∈ Ioo (p : ℝ) (p + 1)) (s : ℝ)
    (hs : s ∈ Ioo (p : ℝ) t) (n n' : Fin P.d → ℤ) (ζ : ℤˣ) (kind : FlowerKind) (pat : FixPat)
    (dagger : Option (Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ) (hpat : pat = .plain ∨ pat = .dRoot)
    (hcut : ∀ x : FlIdx (P.N p) (P.N (p + 1)) pat kind ζ Pm p, CutWeightsOK P.L (d := P.d)
      (fun j => ne_flower_of_mem_kernelTrees pat (x.1 j).2) (mkFlowerAt x.2.1.1 x.2.1.2 x.2.2)
      (fun j => kernelTrees_sign (P.N (p + 1)) pat kind ζ (x.1 j).2) cut1 cut2)
    (b K : ℝ) (hb : (P.d : ℝ) + 1 ≤ b) (hbN : b ≤ (P.N (p + 1) : ℝ)) (hK : 0 ≤ K)
    (hcw : CoefW P p kind pat dagger cut1 cut2 ζ t s Pm b K) :
    Integrable (fun ω => ‖randK P a p kind pat dagger cut1 cut2 ζ t s n n' ω‖ ^ (2 * Pm)) (μ.restrict (Fev p)) ∧
    ‖(((∫ ω in Fev p, ‖randK P a p kind pat dagger cut1 cut2 ζ t s n n' ω‖ ^ (2 * Pm) ∂μ : ℝ)) : ℂ) -
        ∑ N ∈ Finset.range (P.N (p + 1) ^ 4 + 1),
          flowerSumP P (inputsF P R) p N (w := 2 * Pm) kind (fun _ => pat) (dagger.map fun c _ => c)
            cut1 cut2 ζ t s n n'‖ ≤
      Real.exp (-(101 * P.N (p + 1) : ℝ)) * (K * bracketW P ζ n n' Pm b) := by
  classical
  obtain ⟨hd, hδ, hδ1, hγ, hq, hLexp, hC, hCL, hbase, hφ, hstage⟩ := hS.cpl
  obtain ⟨hN, hNdim, hbN'⟩ := hstage p hp
  obtain ⟨hRpm, hNpm, hNR⟩ := x2Sizes_stage hS hp
  have hPm1 := hS.pm
  have hsmall := small_delta_consequences hδ hq
  have hL1 : 1 ≤ P.L := (by linarith [Real.add_one_le_exp (2 : ℝ)] : (1 : ℝ) ≤ Real.exp 2).trans hLexp
  have hL0 : 0 < P.L := zero_lt_one.trans_le hL1
  let Fev' := rapidFev P g Fev
  let R' := clipRemainder p R
  have ha' : AnsatzAt P μ g a Fev' R' E Et p :=
    ansatzAt_clip P μ g a Fev' R E Et p (ansatzAt_rapidFev μ g hG hL0 a Fev R E Et p (ha p le_rfl))
  have hrapid' : ∀ ω ∈ Fev' p, IsRapidDecay (initialCoeff P.L P.φin g ω) := rapid_of_mem_rapidFev g Fev p
  have hres : μ.restrict (Fev' p) = μ.restrict (Fev p) := restrict_rapidFev μ g hG hL0 Fev p
  have hF : ∀ k, |inputsF P R' p (latticePoint P.L k)| ≤ C * jbr (latticePoint P.L k) ^ (-(P.Lambda p : ℝ)) := by
    have h := ansatz_inputsF_bracket_bound P μ g a Fev' R' E Et p ha' hL1 (C - 1) (hφ p hp)
    simpa only [sub_add_cancel] using fun k => h (latticePoint P.L k)
  have hRB : RemainderBound P R p := fun q hq => (ha q hq).2.1.1
  have hsumF := summable_clipped_inputs P R p hp.le hd hL1 hRB
  have hΛ4 := lambda_quarter_ge_dimension P hd hp
  have hΛ : (P.d : ℝ) + 1 ≤ (P.Lambda p : ℝ) / 2 := by
    have : (0 : ℝ) ≤ P.Lambda p := Nat.cast_nonneg _
    linarith
  have hc : |coupling P.d P.L P.γ P.δ| ≤ 1 := abs_coupling_le_one hL1 hγ hδ.le hδ1
  have hpt : (p : ℝ) ≤ t := ht.1.le
  have hps : (p : ℝ) ≤ s := hs.1.le
  have hNR' : (Pm + Pm) * (2 * (3 * P.N (p + 1) + 1) + 1) ≤ 2 * P.R p := by rw [← two_mul]; exact hNR
  refine ⟨?_, ?_⟩
  · have h := integrable_norm_randK_pow P μ g hG a Fev' R' E Et p ha' hrapid' hL1 hδ hsmall.2.1 C hC hF hΛ hc kind
      pat dagger cut1 cut2 ζ t s n n' Pm hPm1 hNR'
    rw [hres] at h
    exact h
  · have hid := integral_norm_randK_pow_eq_flowerSum P μ g hG a Fev' R' E Et p ha' hrapid' hL1 hδ hsmall.2.1 C hC
      hF hsumF hΛ hc kind pat hpat dagger cut1 cut2 ζ t s hpt hps n n' Pm hPm1 hNR hcut (P.N (p + 1) ^ 4)
    have hint : (∫ ω in Fev' p, ‖randK P a p kind pat dagger cut1 cut2 ζ t s n n' ω‖ ^ (2 * Pm) ∂μ) =
        ∫ ω in Fev p, ‖randK P a p kind pat dagger cut1 cut2 ζ t s n n' ω‖ ^ (2 * Pm) ∂μ := by rw [hres]
    rw [hint] at hid
    have hcl : ∀ N, flowerSumP P (inputsF P R') p N (w := 2 * Pm) kind (fun _ => pat) (dagger.map fun c _ => c)
        cut1 cut2 ζ t s n n' = flowerSumP P (inputsF P R) p N (w := 2 * Pm) kind (fun _ => pat)
          (dagger.map fun c _ => c) cut1 cut2 ζ t s n n' := fun N =>
      flowerSum_clip P R p N kind (fun _ => pat) (dagger.map fun c _ => c) cut1 cut2 ζ t s n n'
    simp only [hcl] at hid
    rw [hid]
    set M := ∑ N ∈ range (P.N (p + 1) ^ 4 + 1),
      flowerSumP P (inputsF P R) p N (w := 2 * Pm) kind (fun _ => pat) (dagger.map fun c _ => c) cut1 cut2
        ζ t s n n'
    set T := flowerTail P (inputsF P R') p kind pat dagger cut1 cut2 ζ t s n n' Pm (P.N (p + 1) ^ 4)
    set Er := flowerErr P μ a Fev' R' p kind pat dagger cut1 cut2 ζ t s n n' Pm
    have he : M + T + Er - M = T + Er := by ring
    rw [he]
    have hC0 : 0 ≤ C := by linarith
    have hw : 12 * Pm ≤ 100 * P.R (p + 1) := by omega
    have henv := stage_graftEnvelope_bound P hd p hLexp C b hC0 hCL hb hbN hbase hNdim hw
    have hq0 : 0 ≤ P.δ ^ (P.ν / 2) := Real.rpow_nonneg hδ.le _
    have hq1 : P.δ ^ (P.ν / 2) ≤ 1 := hsmall.1.trans (by norm_num)
    have hW0 : 0 ≤ K * bracketW P ζ n n' Pm b := mul_nonneg hK (bracketW_nonneg P ζ n n' Pm b)
    have hTb := norm_flowerTail_le P μ g a Fev' R' E Et p ha' hL1 hδ hsmall.1 C hC hF hsumF kind pat hpat
      dagger cut1 cut2 ζ t s hpt hps n n' Pm hNR hcut b K hb hK hcw (P.N (p + 1) ^ 4)
    have hErb := norm_flowerErr_le P μ g hG a Fev' R' E Et p ha' hrapid' hL1 hδ hsmall.2.1 C hC hF kind
      pat dagger cut1 cut2 ζ t s n n' Pm hNR b K hb hK hcw
    have hexpo : (P.N (p + 1) ^ 4 + 1) - 8 * Pm * P.N (p + 1) ≤
        (P.N (p + 1) ^ 4 + 1) - 2 * Pm * (3 * P.N (p + 1) + 1) := by
      have : 2 * Pm * (3 * P.N (p + 1) + 1) ≤ 8 * Pm * P.N (p + 1) := by nlinarith
      omega
    have hT' : ‖T‖ ≤ Real.exp (-(102 * (P.N (p + 1) : ℝ))) * (K * bracketW P ζ n n' Pm b) := by
      refine hTb.trans (mul_le_mul_of_nonneg_right ?_ hW0)
      have hmono := pow_le_pow_of_le_one hq0 hq1 hexpo
      have h := env_mul_tail_le_w (w := 8 * Pm) (by omega) (by omega) henv hq0 hq
      exact (mul_le_mul_of_nonneg_left hmono (graftEnvelope_nonneg _ _ _ _ _ _ hC0)).trans h
    have hEr' : ‖Er‖ ≤ Real.exp (-(102 * (P.N (p + 1) : ℝ))) * (K * bracketW P ζ n n' Pm b) :=
      hErb.trans (mul_le_mul_of_nonneg_right (env_mul_input_error_le P hd hp hN henv) hW0)
    calc ‖T + Er‖ ≤ ‖T‖ + ‖Er‖ := norm_add_le _ _
      _ ≤ 2 * Real.exp (-(102 * (P.N (p + 1) : ℝ))) * (K * bracketW P ζ n n' Pm b) := by linarith
      _ ≤ Real.exp (-(101 * (P.N (p + 1) : ℝ))) * (K * bracketW P ζ n n' Pm b) :=
          mul_le_mul_of_nonneg_right (two_exp_le _ (by omega)) hW0
      _ = _ := by ring

theorem ox2ExpNoCut_body.{u} (Pm : ℕ) (P : WTParams) (C : ℝ) (hS : X2Sizes Pm P C) : OX2ExpNoCutBody.{u} Pm P := by
  classical
  intro Ω _ μ _ g hG p hp a Fev R E Et ha t ht s hs n n' ζ kind pat dagger hpat
  obtain ⟨hd, hδ, hδ1, hγ, hq, hLexp, hC, hCL, hbase, hφ, hstage⟩ := hS.cpl
  obtain ⟨hN, hNdim, hbN⟩ := hstage p hp
  have hL1 : 1 ≤ P.L := (by linarith [Real.add_one_le_exp (2 : ℝ)] : (1 : ℝ) ≤ Real.exp 2).trans hLexp
  have hc : |coupling P.d P.L P.γ P.δ| ≤ 1 := abs_coupling_le_one hL1 hγ hδ.le hδ1
  have hcut : ∀ x : FlIdx (P.N p) (P.N (p + 1)) pat kind ζ Pm p, CutWeightsOK P.L (d := P.d)
      (fun j => ne_flower_of_mem_kernelTrees pat (x.1 j).2) (mkFlowerAt x.2.1.1 x.2.1.2 x.2.2)
      (fun j => kernelTrees_sign (P.N (p + 1)) pat kind ζ (x.1 j).2) none none :=
    fun x => cutWeightsOK_none P.L _ _ _
  have hcw : CoefW P p kind pat dagger none none ζ t s Pm ((P.Lambda p : ℝ) / 4) 1 := by
    intro tops κ
    have h1 := norm_topCoefK_le P p pat dagger none none t s hc κ (tops := fun j => (tops j).1)
    have hexp : -(2 * ((P.Lambda p : ℝ) / 4)) = -(P.Lambda p : ℝ) / 2 := by ring
    rw [hexp, one_mul]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (prod_nonneg fun _ _ => (jbr_pos _).le) _) h1
  obtain ⟨hint, hbd⟩ := x2_core Pm P C hS Ω μ g hG p hp a Fev R E Et ha t ht s hs n n' ζ kind pat dagger none none
    hpat hcut ((P.Lambda p : ℝ) / 4) 1 (lambda_quarter_ge_dimension P hd hp) hbN zero_le_one hcw
  refine ⟨hint, hbd.trans ?_⟩
  have hB := (bracketW_le P ζ n n' Pm _ (lambda_quarter_ge_twice_succ P hd hp)).trans
    (jbr_le_x2Bound P hL1 Pm p ζ n n' pat)
  rw [one_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le

/-- **O-X2-EXP without cutoffs.** -/
theorem oX2ExpNoCut.{u} : OX2ExpNoCut.{u} :=
  wtprefixP_x2Sizes.mono fun Pm P ⟨C, hS⟩ => ox2ExpNoCut_body Pm P C hS

end WaveTurbulence.X2E
