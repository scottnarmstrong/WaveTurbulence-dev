/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTopClass3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase1b
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmTopClass2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmInputsProved
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Statement
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAdm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCoords
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCDict
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCExcess
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCFlow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCGain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCInj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCLadProd
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCScale
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCSource
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCStmt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmEx1ULow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmTopClass3`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (top level): `reg_class_bound`.**  `chain_cover` + `hterm_main` + the uniform `Ex1A/Ex1N` at the initial state, with the
numerics (`exists_N`, polylog absorption).  Named inputs: `HmemAt`, `HendAt` (Step 1) and the class hypotheses. 

**Low-range change (L6-HASM).** `reg_class_bound`: `γ ∈ (1/2, 1)` → `γ ∈ (0, 1/2]`, `hsm2` deleted, `[Src.AsmInputs]`
added; Prop 9.6 through `hterm_main` (AsmProp96Low), Step 1 through `AsmEx1ULow.ex1A_uniform`/`ex1N_uniform` (no
VINEPARAM). The ghost step is the class field `Src.AsmInputs.chainCover` (`AsmChainLow.ChainCoverLow'`, wt-orch
DECISION + RULING R194: main's `chain_cover` without `hη8 : 8η ≤ 2γ − 1`, root form, with the Op-1 creation cone
`hExC` and the constant (f′) split budget `Ghost.splitK`). So `hη8` is gone; the Phase-2 constant is
`ghostConstChain d (2m) η δ`; the common Step-1 constant `CAc` uses `max CsA CsC` (`ex1A_uniform`, `ex1C_uniform`,
raised by `Ex1A.mono` / `Ex1Cone.mono`); `hNC1'`, `hNC2'`, `hNC3'` carry the factor `splitK` (and `3·5^d`), absorbed by
`polylog_absorb` (`nc_split_const`). The tail after the root bound is `reg_final` (heartbeat budget). The ghost
step is PROVED (wt-l6ghost, `Ghost.chainCoverLow'_holds`; instance `Src.asmInputs_proved` of `AsmInputsProved`), so
`reg_class_bound` and everything above it carry no named input. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountG8
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

/-- The (f′) split budget with a constant number `K` of classes per node (`Ghost.splitK`, R194 (3) in the form agreed
with wt-l6ghost): `N · (K · X) ≤ 4096·2^13 · (K·A) · B^(13(m+1)+m)` from `X ≤ A · B^m`. -/
theorem nc_split_const {B : ℝ} (hB : 1 ≤ B) (m : ℕ) {N K X A : ℝ} (hN : N ≤ 4096 * (2 * B ^ (m + 1)) ^ 13)
    (hK : 0 ≤ K) (hX0 : 0 ≤ X) (hX : X ≤ A * B ^ m) (hA : 0 ≤ A) :
    N * (K * X) ≤ 4096 * 2 ^ 13 * (K * A) * B ^ (13 * (m + 1) + m) := by
  refine Nmul_aux hB m hN (mul_nonneg hK hX0) ?_ (mul_nonneg hK hA)
  calc K * X ≤ K * (A * B ^ m) := mul_le_mul_of_nonneg_left hX hK
    _ = K * A * B ^ m := by ring

/-- The last step of `reg_class_bound` (split off to keep the main proof within the heartbeat budget): the root bound
of the ghost step `ChainCoverLow'` at `(HSt.init M₀, A0)` gives the stated `countA` bound (main's lines after `key`). -/
theorem reg_final {V : Type} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ} (hd : 3 ≤ d)
    {γ η L δ C1 : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η) (hη40 : η ≤ 1 / 40) (hL1 : 1 ≤ L)
    {M₀ : Molecule V D₀} {Rn : ℕ} (hS : SubHyp Rn M₀) {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))}
    {crit : V → Prop} {N : ℕ} {m : ℕ}
    (hNle : (N : ℝ) ≤ 4096 * (2 * (1 + Real.log L) ^ (m + 1)) ^ 13)
    (h5 : (4096 * 2 ^ 13) ^ 4 * (1 + Real.log L) ^ (52 * (m + 1)) ≤ L ^ ((η ^ 5 - 4 * η ^ 6) / 4))
    (key : QS L γ δ C1 (0 : Mom d) P (HSt.init M₀) A0 ≤ (N : ℝ≥0∞) ^ 4 *
      WPot L γ η (L ^ (eraseA γ η * (Rn : ℝ) + 4 * η * ((Rn : ℝ) - 1) - (η ^ 5 - 4 * η ^ 6) / 2))
        (g1 γ η crit (2 * (Rn : ℝ) - 1)) (HSt.init M₀)) :
    M₀.countA L γ δ C1 (0 : Mom d) (fun k => k ∈ A0) P ≤
      ENNReal.ofReal (L ^ (-4 * η ^ 6 * ((M₀.rho : ℝ) + ((M₀.atoms.filter crit).card : ℝ))) *
        L ^ (((Rn : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4)) := by
  have hL0 : 0 < L := by linarith
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
      _ ≤ _ := h5
  have hRn : (1 : ℝ) ≤ Rn := by exact_mod_cast hS.one_le
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact init_exp_le hd hγ0 hγ1 hη hη40 hRn hL1 hN4'

theorem reg_class_bound {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioc (0 : ℝ) (1 / 2)) {η : ℝ}
    (hη : 0 < η) (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
      ∀ {V : Type} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {M₀ : Molecule V D₀} {Rn : ℕ}
        {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)} {crit Tm : V → Prop},
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
  have hγ0 : 0 < γ := hγ.1
  have hγ1 : γ < 1 := by linarith [hγ.2]
  have hγI : γ ∈ Ioo (0 : ℝ) 1 := ⟨hγ0, hγ1⟩
  have hd1 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg0 : min γ (1 - γ) ≤ γ := min_le_left _ _
  have hg0' : 0 < min γ (1 - γ) := lt_min hγ0 (by linarith)
  have hη40 : η ≤ 1 / 40 := by nlinarith
  have hη1 : η < 1 := by linarith
  have hηγ : η ≤ γ := by nlinarith
  have hηsmall : 200 * η ≤ min γ (1 - γ) := by nlinarith
  obtain ⟨Ch, hCh1, hT⟩ := hterm_main.{0, 0} hd hγ hη hsm hηs
  obtain ⟨CsA, hCsA, C2A, hC2A, hExAall⟩ := ex1A_uniform hd hγI
  obtain ⟨CsN, C2N, hCsN, hC2N, hExNall⟩ := ex1N_uniform hd hγI
  obtain ⟨CsC, hCsC, C2C, hC2C, hExCall⟩ := ex1C_uniform hd hγI
  refine ⟨max Ch (max (max C2A C2C) C2N), le_trans hCh1 (le_max_left _ _), fun m C1 hC1 δ hδ => ?_⟩
  have hC1Ch : Ch ≤ C1 := le_trans (le_max_left _ _) hC1
  have hC1A : C2A ≤ C1 :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hC1
  have hC1C : C2C ≤ C1 :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hC1
  have hC1N : C2N ≤ C1 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC1
  have hC11 : 1 ≤ C1 := le_trans hCh1 hC1Ch
  obtain ⟨LA, hLA, hExA⟩ := hExAall δ hδ
  obtain ⟨LN, hLN, hExN⟩ := hExNall δ hδ
  obtain ⟨LC, hLC, hExC⟩ := hExCall δ hδ
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
  have hCsM : 0 ≤ max CsA CsC := le_trans hCsA (le_max_left _ _)
  set CAc : ℝ := (max CsA CsC * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13)) * (1 + δ⁻¹) with hCAc
  set KNc : ℝ := CsN * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8) with hKNc
  have hdel : 0 ≤ δ⁻¹ := inv_nonneg.2 hδ.1.le
  have hden1 : 0 ≤ 2 * η - η ^ 3 := by nlinarith [pow_pos hη 3]
  have hden2 : 0 ≤ η ^ 2 - η ^ 3 := by nlinarith [pow_pos hη 3, pow_pos hη 2]
  have hCAc0 : 0 ≤ CAc := by rw [hCAc]; positivity
  have hKNc0 : 0 ≤ KNc := by rw [hKNc]; positivity
  obtain ⟨L1, hL1, h1⟩ := polylog_absorb (4096 * 2 ^ 13 * ((Ghost.splitK : ℝ) * (3 * 5 ^ d) * (CAc + KNc))) (13 * (m + 1) + m)
    (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) (hεpos _ (by positivity) (by norm_num))
  obtain ⟨L2, hL2, h2⟩ := polylog_absorb (4096 * 2 ^ 13 * ((Ghost.splitK : ℝ) * ghostConstChain d (2 * m) η δ)) (13 * (m + 1) + m)
    (η ^ 3 - 4 * η ^ 6 * (((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))) (hεpos _ (by positivity) (by norm_num))
  obtain ⟨L3, hL3, h3⟩ := polylog_absorb (4096 * 2 ^ 13 * ((Ghost.splitK : ℝ) * (3 * 5 ^ d) * max (cAlpha d γ η) (cBeta η (2 * m))))
    (13 * (m + 1) + m)
    (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) (hεpos _ (by positivity) (by norm_num))
  obtain ⟨L4, hL4, h4⟩ := polylog_absorb (4096 * 2 ^ 13 * cBeta η (2 * m)) (13 * (m + 1) + m)
    (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) (hεpos _ (by positivity) (by norm_num))
  obtain ⟨L5, hL5, h5⟩ := polylog_absorb ((4096 * 2 ^ 13) ^ 4) (52 * (m + 1)) ((η ^ 5 - 4 * η ^ 6) / 4) hε5
  obtain ⟨L6, hL6, h6⟩ := polylog_absorb 2 0 (1 - γ) (by linarith)
  have a1 : 0 ≤ LA := le_trans (Real.exp_pos 1).le hLA
  have a2 : 0 ≤ LN := le_trans (Real.exp_pos 1).le hLN
  have a4 : 0 ≤ LC := le_trans (Real.exp_pos 1).le hLC
  have a3 : 0 ≤ Rh := by linarith
  have e2 := Real.exp_pos 2
  refine ⟨LA + LN + LC + Rh + L1 + L2 + L3 + L4 + L5 + L6 + Real.exp 2, ?_, fun L hL => ?_⟩
  · linarith
  have hexp1 : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.2 (by norm_num)
  have hLA' : LA ≤ L := by linarith
  have hLN' : LN ≤ L := by linarith
  have hLC' : LC ≤ L := by linarith
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
  have hY13 : 0 ≤ 2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13 := by positivity
  have hδ1 : 0 ≤ 1 + δ⁻¹ := by positivity
  have hExA' : Ex1A L γ η δ C1 (0 : Mom d) M₀ P CAc :=
    Ex1A.mono (mul_nonneg (mul_nonneg hCsA hY13) hδ1)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hY13) hδ1)
      (hExA L hLA' C1 η hC1A hη hη1 hηγ (0 : Mom d) M₀ P hP0 hP hMol0)
  have hExC' : Ex1Cone L γ η δ C1 (0 : Mom d) M₀ P CAc :=
    Ex1Cone.mono (mul_nonneg (mul_nonneg hCsC hY13) hδ1)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hY13) hδ1)
      (hExC L hLC' C1 η hC1C hη hη1 hηγ (le_trans hηsmall (min_le_left _ _))
        (le_trans hηsmall (min_le_right _ _)) (0 : Mom d) M₀ P hP0 hP hMol0)
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
  have hsK : (0 : ℝ) ≤ (Ghost.splitK : ℝ) * (3 * 5 ^ d) := by positivity
  have hNC1' : (N : ℝ) * ((Ghost.splitK : ℝ) * (3 * 5 ^ d) *
      max CAc (CsN * (1 + Real.log L) ^ m * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8))) ≤
      L ^ (η ^ 3 - 4 * η ^ 6 * (((86 : ℕ) : ℝ) + ((2 : ℕ) : ℝ))) :=
    le_trans (nc_split_const hB1 m hNle hsK (le_trans hCAc0 (le_max_left _ _)) hmax (add_nonneg hCAc0 hKNc0))
      (h1 L hL1')
  have hK2 : 0 ≤ ghostConstChain d (2 * m) η δ := ghostConstChain_nonneg d (2 * m) hη hδ.1
  have hcAl : 0 ≤ cAlpha d γ η := by
    unfold cAlpha
    have : 0 < 1 - γ := by linarith
    positivity
  have hcBe : 0 ≤ cBeta η (2 * m) := by
    unfold cBeta
    exact mul_nonneg (by norm_num) (pow_nonneg (div_nonneg (by positivity) hden2) _)
  have hK3 : 0 ≤ max (cAlpha d γ η) (cBeta η (2 * m)) := le_trans hcAl (le_max_left _ _)
  have hNC2' : (N : ℝ) * ((Ghost.splitK : ℝ) * ghostConstChain d (2 * m) η δ) ≤
      L ^ (η ^ 3 - 4 * η ^ 6 * (((9 : ℕ) : ℝ) + ((3 : ℕ) : ℝ))) :=
    le_trans (nc_split_const hB1 m hNle (Nat.cast_nonneg _) hK2 (le_mul_of_one_le_right hK2 hν1) hK2) (h2 L hL2')
  have hNC3' : (N : ℝ) * ((Ghost.splitK : ℝ) * (3 * 5 ^ d) * max (cAlpha d γ η) (cBeta η (2 * m))) ≤
      L ^ (η ^ 3 - 4 * η ^ 6 * (((1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ))) :=
    le_trans (nc_split_const hB1 m hNle hsK hK3 (le_mul_of_one_le_right hK3 hν1) hK3) (h3 L hL3')
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
  have hcc : ChainCoverLow' := Src.AsmInputs.chainCover
  unfold ChainCoverLow' at hcc
  have key := hcc (H := ⟨hd, hγ0, hγ1, hη, le_trans hηsmall (min_le_left _ _), le_trans hηsmall (min_le_right _ _), hLe, hδ.1, hδ.2, hC11⟩) hS hp0 hP hP0 (2 * m) hnc hobl
    hExA' hExN' hExC' hcard hSrc hdec h0 hh2 N hN1 hN2 hN3 hN4 hY0 hCAc0 hCN0 hNC1' hK2 hNC2' hK3 hNC3' hcBe hNC4
    hg0'.le hmem hend hterm hInit
  exact reg_final hd hγ0 hγ1 hη hη40 hL1 hS hNle (h5 L hL5') key

end WaveTurbulence.GammaLow.FinalCount.H
