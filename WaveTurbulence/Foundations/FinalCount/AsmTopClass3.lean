/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTopClass2
public import WaveTurbulence.Foundations.FinalCount.AsmEx1U
/-! **FINALCOUNT-ASSEMBLY (top level): `reg_class_bound`.**  `chain_cover` + `hterm_main` + the uniform `Ex1A/Ex1N` at the initial state, with the
numerics (`exists_N`, polylog absorption).  Named inputs: `HmemAt`, `HendAt` (Step 1) and the class hypotheses. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountG8
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

theorem one_add_le_sq {x : ℝ} (h : 2 ≤ x) : 1 + x ≤ x ^ 2 := by nlinarith

theorem Nmul_aux {B : ℝ} (hB : 1 ≤ B) (m : ℕ) {N X X' : ℝ} (hN : N ≤ 4096 * (2 * B ^ (m + 1)) ^ 13) (hX : 0 ≤ X)
    (hXX : X ≤ X' * B ^ m) (hX' : 0 ≤ X') : N * X ≤ 4096 * 2 ^ 13 * X' * B ^ (13 * (m + 1) + m) := by
  have hBm : 0 ≤ B ^ m := by positivity
  calc N * X ≤ (4096 * (2 * B ^ (m + 1)) ^ 13) * (X' * B ^ m) := by
        apply mul_le_mul hN hXX hX (by positivity)
    _ = 4096 * 2 ^ 13 * X' * B ^ (13 * (m + 1) + m) := by ring

theorem reg_class_bound {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (1 / 2 : ℝ) 1) {η : ℝ} (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hsm2 : (d : ℝ) * η ≤ (2 * γ - 1) / 1000) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
      ∀ {V : Type} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {M₀ : Molecule V D₀} {Rn : ℕ}
        {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {crit Tm : V → Prop},
        SubHyp Rn M₀ → M₀.IsMolecule → LadderHered M₀ P → (∀ S, 0 ≤ P S) →
        PinnedM0 (fun k => k ∈ A0) L (0 : Mom d) M₀ →
        (∀ κ ∈ A0, SubproOblG C L γ η (0 : Mom d) κ) → TripleDesig C →
        (∀ κ ∈ A0, C.UnselOK L γ η (0 : Mom d) κ (Un κ)) →
        (∀ κ ∈ A0, DegenSGT M₀ L γ η (0 : Mom d) κ Tm) →
        (∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 →
          ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0) →
        (∀ k0 ∈ A0, ∀ v ∈ M₀.atoms, Tm v → ∀ x y, M₀.atom x = v → M₀.atom y = v → k0 x = k0 y) →
        (∀ k0 ∈ A0, ∀ x, k0 (M₀.mate x) = k0 x) →
        (∀ v ∈ M₀.atoms, Tm v → M₀.deg v < 4 → ∃ k, ∀ k0 ∈ A0, ∀ x, M₀.atom x = v → k0 x = k) →
        (∀ κ ∈ A0, ∀ a, crit a → SGat M₀ L γ η (0 : Mom d) κ a) →
        (((2 * M₀.atoms.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m) →
        (∀ k ∈ A0, SourceLadderGaps M₀ L (0 : Mom d) P k) →
        (∀ k ∈ A0, ∃ c0, M₀.IsDecoration L (0 : Mom d) c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0) →
        HmemAt M₀ Rn C L γ η (0 : Mom d) A0 Un Fst crit →
        HendAt M₀ Rn C L γ η (0 : Mom d) A0 Un Fst (2 * (Rn : ℝ) - 1) →
        M₀.countA L γ δ C1 (0 : Mom d) (fun k => k ∈ A0) P ≤
          ENNReal.ofReal (L ^ (-4 * η ^ 6 * ((M₀.rho : ℝ) + ((M₀.atoms.filter crit).card : ℝ))) *
            L ^ (((Rn : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4)) := by
  have hγ0 : 0 < γ := by linarith [hγ.1]
  have hγ1 : γ < 1 := hγ.2
  have hγI : γ ∈ Ioo (0 : ℝ) 1 := ⟨hγ0, hγ1⟩
  have hd1 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg0 : min γ (1 - γ) ≤ γ := min_le_left _ _
  have hg0' : 0 < min γ (1 - γ) := lt_min hγ0 (by linarith)
  have hη40 : η ≤ 1 / 40 := by nlinarith
  have hη1 : η < 1 := by linarith
  have hηγ : η ≤ γ := by nlinarith
  have hηsmall : 200 * η ≤ min γ (1 - γ) := by nlinarith
  have hη8 : 8 * η ≤ 2 * γ - 1 := by nlinarith
  obtain ⟨Ch, hCh1, hT⟩ := hterm_main.{0, 0} hd hγ hη hsm hsm2 hηs
  obtain ⟨CsA, hCsA, C2A, hC2A, hExAall⟩ := ex1A_uniform WaveTurbulence.Vine.Param.vineparam hd hγI
  obtain ⟨CsN, C2N, hCsN, hC2N, hExNall⟩ := ex1N_uniform WaveTurbulence.Vine.Param.vineparam hd hγI
  refine ⟨max Ch (max C2A C2N), le_trans hCh1 (le_max_left _ _), fun m C1 hC1 δ hδ => ?_⟩
  have hC1Ch : Ch ≤ C1 := le_trans (le_max_left _ _) hC1
  have hC1A : C2A ≤ C1 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC1
  have hC1N : C2N ≤ C1 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC1
  have hC11 : 1 ≤ C1 := le_trans hCh1 hC1Ch
  obtain ⟨LA, hLA, hExA⟩ := hExAall δ hδ
  obtain ⟨LN, hLN, hExN⟩ := hExNall δ hδ
  obtain ⟨Rh, hRh1, hTT⟩ := hT m C1 hC1Ch δ hδ
  have hη3 : η ^ 3 ≤ 1 / 64000 := by
    have : η ^ 3 ≤ (1 / 40) ^ 3 := pow_le_pow_left₀ hη.le hη40 3
    linarith
  have hεpos : ∀ k : ℝ, 0 ≤ k → k ≤ 100 → 0 < η ^ 3 - 4 * η ^ 6 * k := by
    intro k hk0 hk1
    have h6 : η ^ 6 = η ^ 3 * η ^ 3 := by ring
    have h3 : 0 < η ^ 3 := by positivity
    rw [h6]
    nlinarith [mul_pos h3 h3]
  have hε5 : 0 < (η ^ 5 - 4 * η ^ 6) / 4 := by
    have h5 : 4 * η ^ 6 < η ^ 5 := by
      have : η ^ 6 = η ^ 5 * η := by ring
      rw [this]; nlinarith [pow_pos hη 5]
    linarith
  set CAc : ℝ := (CsA * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13)) * (1 + δ⁻¹) with hCAc
  set KNc : ℝ := CsN * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8) with hKNc
  have hdel : 0 ≤ δ⁻¹ := inv_nonneg.2 hδ.1.le
  have hden1 : 0 ≤ 2 * η - η ^ 3 := by nlinarith [pow_pos hη 3]
  have hden2 : 0 ≤ η ^ 2 - η ^ 3 := by nlinarith [pow_pos hη 3, pow_pos hη 2]
  have hCAc0 : 0 ≤ CAc := by rw [hCAc]; positivity
  have hKNc0 : 0 ≤ KNc := by rw [hKNc]; positivity
  obtain ⟨L1, hL1, h1⟩ := polylog_absorb (4096 * 2 ^ 13 * (CAc + KNc)) (13 * (m + 1) + m)
    (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) (hεpos _ (by positivity) (by norm_num))
  obtain ⟨L2, hL2, h2⟩ := polylog_absorb (4096 * 2 ^ 13 * ghostConst d (2 * m) η δ) (13 * (m + 1) + m)
    (η ^ 3 - 4 * η ^ 6 * (((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))) (hεpos _ (by positivity) (by norm_num))
  obtain ⟨L3, hL3, h3⟩ := polylog_absorb (4096 * 2 ^ 13 * max (cAlpha d γ η) (cBeta η (2 * m))) (13 * (m + 1) + m)
    (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) (hεpos _ (by positivity) (by norm_num))
  obtain ⟨L4, hL4, h4⟩ := polylog_absorb (4096 * 2 ^ 13 * cBeta η (2 * m)) (13 * (m + 1) + m)
    (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) (hεpos _ (by positivity) (by norm_num))
  obtain ⟨L5, hL5, h5⟩ := polylog_absorb ((4096 * 2 ^ 13) ^ 4) (52 * (m + 1)) ((η ^ 5 - 4 * η ^ 6) / 4) hε5
  obtain ⟨L6, hL6, h6⟩ := polylog_absorb 2 0 (1 - γ) (by linarith)
  have a1 : 0 ≤ LA := le_trans (Real.exp_pos 1).le hLA
  have a2 : 0 ≤ LN := le_trans (Real.exp_pos 1).le hLN
  have a3 : 0 ≤ Rh := by linarith
  have e2 := Real.exp_pos 2
  refine ⟨LA + LN + Rh + L1 + L2 + L3 + L4 + L5 + L6 + Real.exp 2, ?_, fun L hL => ?_⟩
  · linarith
  have hexp1 : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.2 (by norm_num)
  have hLA' : LA ≤ L := by linarith
  have hLN' : LN ≤ L := by linarith
  have hRh' : Rh ≤ L := by linarith
  have hL1' : L1 ≤ L := by linarith
  have hL2' : L2 ≤ L := by linarith
  have hL3' : L3 ≤ L := by linarith
  have hL4' : L4 ≤ L := by linarith
  have hL5' : L5 ≤ L := by linarith
  have hL6' : L6 ≤ L := by linarith
  have hLe2 : Real.exp 2 ≤ L := by linarith
  have hLe : Real.exp 1 ≤ L := le_trans hexp1 hLe2
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) hLe
  have hL0 : 0 < L := by linarith
  have hlog2 : 2 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 2) hLe2
    rwa [Real.log_exp] at this
  have hB1 : 1 ≤ 1 + Real.log L := by linarith
  have hh2 : 2 / L ≤ L ^ (-γ + η) := by
    have h6' := h6 L hL6'
    simp only [pow_zero, mul_one] at h6'
    have h7 : 2 / L ≤ L ^ (-γ) := by
      rw [div_le_iff₀ hL0]
      calc (2 : ℝ) ≤ L ^ (1 - γ) := h6'
        _ = L ^ (-γ) * L := by rw [show 1 - γ = -γ + 1 by ring, Real.rpow_add hL0, Real.rpow_one]
    exact le_trans h7 (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  intro V _ _ D₀ _ _ M₀ Rn P A0 C Un Fst crit Tm hS hMol0 hP hP0 hp0 hobl hT3 hU hdeg h0 hTame hmate hfix hcrit hcard hSrc hdec hmem hend
  have hc4 : Fintype.card D₀ ≤ 4 * M₀.atoms.card := by
    have h1 := card_darts_eq_two_bonds M₀
    have h2 := hS.count
    omega
  obtain ⟨N, hN1, hN2, hN3, hN4, hNle⟩ := exists_N M₀.atoms.card (Fintype.card D₀) m hLe hcard hc4
  have hν1 : 1 ≤ (1 + Real.log L) ^ m := one_le_pow₀ hB1
  have hExA' := hExA L hLA' C1 η hC1A hη hη1 hηγ (0 : Mom d) M₀ P hP0 hP hMol0
  have hExN' := hExN L hLN' C1 η ((1 + Real.log L) ^ m) hC1N hη hη1 hν1 (0 : Mom d) M₀ P hP0 hP hMol0
  have hterm := hTT L hRh' (Fst := Fst) hS hP hP0 hobl hT3 hU hdeg h0 hTame hmate hfix hcrit hcard
    (fun A h hA hLC a => maxGap_comp hMol0 hP hdec hSrc hA hLC a)
    (fun A h hA hLC a => maxGap_comp_op5 hMol0 hP hdec hSrc hA hLC a)
  have hBm : 0 ≤ (1 + Real.log L) ^ m := by positivity
  have hCN0 : 0 ≤ CsN * (1 + Real.log L) ^ m * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8) := by
    have : CsN * (1 + Real.log L) ^ m * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8) =
        KNc * (1 + Real.log L) ^ m := by rw [hKNc]; ring
    rw [this]; exact mul_nonneg hKNc0 hBm
  have hmax : max CAc (CsN * (1 + Real.log L) ^ m * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)) ≤
      (CAc + KNc) * (1 + Real.log L) ^ m := by
    have e : CsN * (1 + Real.log L) ^ m * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8) =
        KNc * (1 + Real.log L) ^ m := by rw [hKNc]; ring
    rw [e]
    apply max_le
    · have h1' := mul_le_mul_of_nonneg_left hν1 hCAc0
      calc CAc = CAc * 1 := by ring
        _ ≤ CAc * (1 + Real.log L) ^ m := h1'
        _ ≤ (CAc + KNc) * (1 + Real.log L) ^ m := by rw [add_mul]; linarith [mul_nonneg hKNc0 hBm]
    · exact mul_le_mul_of_nonneg_right (by linarith) hBm
  have hNC1 : (N : ℝ) * max CAc (CsN * (1 + Real.log L) ^ m * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)) ≤
      L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) :=
    le_trans (Nmul_aux hB1 m hNle (le_trans hCAc0 (le_max_left _ _)) hmax (by positivity)) (h1 L hL1')
  have hK2 : 0 ≤ ghostConst d (2 * m) η δ := (triConst_nonneg d (2 * m) hη hδ.1).trans (ghostConst_ge_triConst d (2 * m) hη hδ.1)
  have hcAl : 0 ≤ cAlpha d γ η := by
    unfold cAlpha
    have : 0 < 1 - γ := by linarith
    positivity
  have hcBe : 0 ≤ cBeta η (2 * m) := by
    unfold cBeta
    exact mul_nonneg (by norm_num) (pow_nonneg (div_nonneg (by positivity) hden2) _)
  have hK3 : 0 ≤ max (cAlpha d γ η) (cBeta η (2 * m)) := le_trans hcAl (le_max_left _ _)
  have hNC2 : (N : ℝ) * ghostConst d (2 * m) η δ ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))) :=
    le_trans (Nmul_aux hB1 m hNle hK2 (le_mul_of_one_le_right hK2 hν1) hK2) (h2 L hL2')
  have hNC3 : (N : ℝ) * max (cAlpha d γ η) (cBeta η (2 * m)) ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) :=
    le_trans (Nmul_aux hB1 m hNle hK3 (le_mul_of_one_le_right hK3 hν1) hK3) (h3 L hL3')
  have hNC4 : (N : ℝ) * cBeta η (2 * m) ≤ L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) :=
    le_trans (Nmul_aux hB1 m hNle hcBe (le_mul_of_one_le_right hcBe hν1) hcBe) (h4 L hL4')
  have hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ (2 * m) := by
    refine le_trans hcard ?_
    rw [pow_mul]
    exact pow_le_pow_left₀ (by linarith) (one_add_le_sq hlog2) m
  have hY0 : 0 ≤ L ^ (eraseA γ η * (Rn : ℝ) + 4 * η * ((Rn : ℝ) - 1) - (η ^ 5 - 4 * η ^ 6) / 2) := by positivity
  have hap : ApPos (HSt.init M₀).s := by
    intro a _ R kp hcl
    change FinalCountG3.Cls.eps = FinalCountG3.Cls.alpha R kp at hcl
    cases hcl
  have hInit : Inv1 M₀ Rn C Un Fst L γ η 0 A0 A0 (HSt.init M₀) :=
    ⟨subset_rfl, Or.inr ⟨UCtx.init hS, hap, fun κ _ => Relation.ReflTransGen.refl⟩⟩
  have key := chain_cover (H := ⟨hd, hγ0, hγ1, hη, le_trans hηsmall (min_le_left _ _), le_trans hηsmall (min_le_right _ _), hLe, hδ.1, hδ.2, hC11⟩) hS hp0 hP hP0 (2 * m) hnc hobl
    hExA' hExN' hcard hSrc hdec h0 hh2 hη8 N hN1 hN2 hN3 hN4 hY0 hCAc0 hCN0 hNC1 hK2 hNC2 hK3 hNC3 hcBe hNC4
    hg0'.le hmem hend hterm (HSt.init M₀) A0 hInit
  have hAdm : AdmS (fun k => k ∈ A0) (HSt.init M₀).s = fun k => k ∈ A0 := by
    funext k; apply propext; constructor
    · rintro ⟨k0, hk0, rfl⟩; exact hk0
    · intro hk; exact ⟨k, hk, rfl⟩
  have hq : QS L γ δ C1 0 P (HSt.init M₀) A0 = M₀.countA L γ δ C1 0 (fun k => k ∈ A0) P := by
    unfold QS; rw [hAdm]; rfl
  rw [hq, WPot_init_eq hS hL0 crit] at key
  refine key.trans ?_
  have hN4' : (N : ℝ) ^ 4 ≤ L ^ ((η ^ 5 - 4 * η ^ 6) / 4) := by
    calc (N : ℝ) ^ 4 ≤ (4096 * (2 * (1 + Real.log L) ^ (m + 1)) ^ 13) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hNle 4
      _ = (4096 * 2 ^ 13) ^ 4 * (1 + Real.log L) ^ (52 * (m + 1)) := by ring
      _ ≤ _ := h5 L hL5'
  have hRn : (1 : ℝ) ≤ Rn := by exact_mod_cast hS.one_le
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact init_exp_le hd hγ0 hγ1 hη hη40 hRn hL1 hN4'

end WaveTurbulence.FinalCountAsm
