/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKFine.Budget
import Mathlib.Tactic

/-! # C4b FINE-PIN: the bound of one counting choice

For one counting choice `C` with `C.subpro = Cs` (o73 (18.5), o75 row 12, `FinalCountAtMK`):

  `‖c^n‖ₑ · ∑'_{z ∈ carrier_C} ‖amp · B_MK(α z)‖ₑ ≤ fineConst · (C₀^n · scaleCost^{ρ + p_C})⁻¹`,

with `fineConst = (2L+1)^{d·#X} · ((N+1)L)^{4|E|} · L^{2m} · C₁ exp(…)` (`X` = darts at `E`, FL-FIBER).
The count `countE · 𝔛 = countA / norm` is bounded by `FinalCountAtMK`; the pinned box sum by `LadderFourierAtMK`;
the prefactor by `rawPrefactorMK_mul_choiceScale_le` (`q = #hinges ≤ p = numCriticalSGMK`). -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs
  WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical ENNReal

variable {w d : ℕ}

theorem encard_localizedTuples_le {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) (c : ι → Mom d) :
    ((FlFiber.localizedTuples L c).encard : ℝ≥0∞) ≤ ENNReal.ofReal ((2 * L + 1) ^ (Fintype.card ι * d)) := by
  have hfin := FlFiber.finite_localizedTuples hL c
  have h := FlFiber.ncard_localizedTuples_le hL c
  rw [← hfin.cast_ncard_eq]
  have e : (((FlFiber.localizedTuples L c).ncard : ℕ∞) : ℝ≥0∞) =
      ENNReal.ofReal ((FlFiber.localizedTuples L c).ncard : ℝ) := by
    rw [ENNReal.ofReal_natCast]
    simp
  rw [e]
  exact ENNReal.ofReal_le_ofReal h

theorem ennreal_rearrange {a e t t' q x l r : ℝ≥0∞} (ht : t ≤ t') (hel : e * l ≤ r) :
    a * (e * (t * (q * (x * l)))) ≤ a * t' * q * x * r := by
  calc a * (e * (t * (q * (x * l)))) = a * t * q * x * (e * l) := by ring
    _ ≤ a * t' * q * x * r := by gcongr

/-- The constant of the fine bound before the final simplification. -/
noncomputable def fineConst (P : WTParams) {R : ℕ} (G : Garden (2 * R)) (E : Finset (GBranch G.tree)) (m q : ℕ) :
    ℝ :=
  (2 * P.L + 1) ^ ((exDarts G E).card * P.d) * (((G.order : ℝ) + 1) * P.L) ^ (4 * E.card) *
    P.L ^ (2 * (m : ℝ)) *
    (P.C₁ * Real.exp (G.order * (Real.log P.C₁ - 10 * P.ν * Real.log P.δ) +
      (-P.η ^ 6 * (G.molecule.rho + q) - ((R : ℝ) - 1) * (1 / 4 + 1 / 50)) * Real.log P.L))

theorem fineConst_nonneg (P : WTParams) {R : ℕ} (G : Garden (2 * R)) (E : Finset (GBranch G.tree)) (m q : ℕ)
    (hL : 0 ≤ P.L) (hC₁ : 0 ≤ P.C₁) : 0 ≤ fineConst P G E m q := by
  unfold fineConst
  have h1 : 0 ≤ P.L ^ (2 * (m : ℝ)) := Real.rpow_nonneg hL _
  positivity

/-- **One counting choice.** -/
theorem perChoice_le (P : WTParams) (hLF : LadderFourierAtMK P) (hFC : FinalCountAtMK P)
    (hL : 2 ≤ P.L) (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁) (hδ1 : P.δ ≤ 1)
    (ha : P.δ ^ (5 * P.ν) ≤ P.η ^ 6)
    (hb : Real.log (Real.log P.L / Real.log 2 + 2) ≤ P.η ^ 6 * Real.log P.L)
    (hsmall : Real.log P.C₁ + Real.log (((3 ^ 16 * 17 : ℕ) : ℝ)) + 5 * P.ν * Real.log P.δ ≤ 0)
    {p R : ℕ} (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1))
    (G : Garden (2 * R)) (hplain : G.IsPlain) (hirred : G.Irreducible) (hbal : IsBalancedSig G.sig)
    (hn : 1 ≤ G.order) (hnmax : G.order ≤ P.N (p + 1) ^ 4)
    (D : SplicedKernelDataMK G P.d) (Cs : SubproChoices G) (S : SurvivorData G) (E : Finset (GBranch G.tree))
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData) (hlayer : ∀ v, D.layer v ≤ p)
    (hfilt : ∀ a q, D.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ D.ind k ∧ D.ind k ≤ 1)
    (hfixE : ∀ b, (D.fix b).isSome → b ∈ E)
    (hfixT : ∀ b t, D.fix b = some t → (D.layer b : ℝ) ≤ t ∧ t ≤ D.layer b + 1)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (hgeo : SplicedGeomPremises G)
    (hS : SubproConclusionsMK G D.toSplicedKernelData Cs S P.L P.γ P.η base roots)
    (C : CountingChoices G P.d) (hsub : C.subpro = Cs)
    (hfix : C.fixedRoots = Finset.univ.image (fun i => base + latticePoint P.L (roots i))) :
    ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ G.order‖ₑ *
        ∑' z : carrierMK G D C S P.L P.γ P.η base roots,
          ‖ampMK G D P.L P.γ P.η base z.1.1 * splicedFourierBMK G D.layer D.rootTime D.fix
            (splicedFrequency G D.toSplicedKernelData P.L P.γ P.δ base z.1.1)‖ₑ ≤
      ENNReal.ofReal (fineConst P G E S.m Cs.hinges.card *
        ((((3 ^ 16 * 17 : ℕ) : ℝ)) ^ G.order *
          (Real.log P.L / Real.log 2 + 2) ^ (G.molecule.rho + numCriticalSGMK C S))⁻¹) := by
  subst hsub
  by_cases hne : (carrierMK G D C S P.L P.γ P.η base roots).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : (∑' z : carrierMK G D C S P.L P.γ P.η base roots,
        ‖ampMK G D P.L P.γ P.η base z.1.1 * splicedFourierBMK G D.layer D.rootTime D.fix
          (splicedFrequency G D.toSplicedKernelData P.L P.γ P.δ base z.1.1)‖ₑ) = 0 := by
      rw [hne]
      exact tsum_empty
    rw [h0, mul_zero]
    exact zero_le
  obtain ⟨z0, hz0⟩ := hne
  have hL1 : 1 < P.L := by linarith
  have hL0 : 0 < P.L := by linarith
  have hC₁0 : 0 < P.C₁ := by linarith
  have hgeom : CountingGeometry G C :=
    countingGeometry_of_admissibleMK G hgeo D.toSplicedKernelData C S base roots hS hfix _ hz0.2
  have hq : C.subpro.hinges.card ≤ numCriticalSGMK C S := hinges_card_le_numCriticalSGMK hgeom hS.survivors
  have hLFj := fun β => hLF p hp R hR hRmax G hplain hirred hbal hn hnmax D.toSplicedKernelData D.fix E
    C.ladderScale hlayer hD hfixE hfixT base roots β
  have hcnt := tsum_carrierMK_le G hplain D hD hfilt hind C S E hL0 hδ P.γ P.η base roots _ hLFj
  have hFCj := hFC p hp R hR hRmax G hplain hirred hbal hn hnmax D.toSplicedKernelData C S hS.hinges hgeom
    hS.survivors hS.chainOrder base roots _ (fun _ h => h)
  have hceq := countE_mul_ladderWeight_eq_countA_div G.molecule hL0 hδ hC₁0 P.γ base
    (splicedCountingAdmissibleMK G D.toSplicedKernelData C S P.L P.γ P.η base roots) C.ladderScale
  have hnorm := molecularCountNormalization_pos G.molecule P.d hL0 hδ hC₁0 P.γ
  have hcoupling : 0 ≤ coupling P.d P.L P.γ P.δ := by unfold coupling; positivity
  have hc : ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ G.order‖ₑ =
      ENNReal.ofReal ((coupling P.d P.L P.γ P.δ) ^ G.order) := by
    rw [← ofReal_norm, norm_pow, Complex.norm_real, Real.norm_of_nonneg hcoupling]
  have hTb := encard_localizedTuples_le hL0 (exCenters G E D.toSplicedKernelData base)
  rw [Fintype.card_coe] at hTb
  have hsc : 0 < Real.log P.L / Real.log 2 + 2 := by
    have : 0 ≤ Real.log P.L / Real.log 2 :=
      div_nonneg (Real.log_nonneg hL1.le) (Real.log_nonneg (by norm_num))
    linarith
  have hC₀ : (0 : ℝ) < ((3 ^ 16 * 17 : ℕ) : ℝ) := by positivity
  have hLm : 0 ≤ P.L ^ (2 * (S.m : ℝ)) := Real.rpow_nonneg hL0.le _
  have hsc : 0 < Real.log P.L / Real.log 2 + 2 := by
    have : 0 ≤ Real.log P.L / Real.log 2 :=
      div_nonneg (Real.log_nonneg hL1.le) (Real.log_nonneg (by norm_num))
    linarith
  have hC₀ : (0 : ℝ) < ((3 ^ 16 * 17 : ℕ) : ℝ) := by positivity
  have hLm : 0 ≤ P.L ^ (2 * (S.m : ℝ)) := Real.rpow_nonneg hL0.le _
  have hQ : 0 ≤ (((G.order : ℝ) + 1) * P.L) ^ (4 * E.card) := by positivity
  have hA : 0 ≤ P.C₁ * (P.C₁ * P.δ ^ (-1 / 2 - 5 * P.ν)) ^ G.order *
      P.L ^ (P.δ ^ (5 * P.ν) * G.molecule.rho) := by positivity
  have hTb0 : 0 ≤ (2 * P.L + 1) ^ ((exDarts G E).card * P.d) := by positivity
  -- the real inequality
  have habs := rawPrefactorMK_mul_choiceScale_le G hgeo P.d (numCriticalSGMK C S) C.subpro.hinges.card hq hn hR
    hL1 hδ hδ1 hC₁ hC₀ hsc ha hb hsmall P.γ
  have hraw : rawPrefactorMK G P.d (numCriticalSGMK C S) P.L P.γ P.η P.δ P.C₁ P.ν ≤
      P.C₁ * Real.exp (G.order * (Real.log P.C₁ - 10 * P.ν * Real.log P.δ) +
        (-P.η ^ 6 * (G.molecule.rho + C.subpro.hinges.card) - ((R : ℝ) - 1) * (1 / 4 + 1 / 50)) * Real.log P.L) *
      ((((3 ^ 16 * 17 : ℕ) : ℝ)) ^ G.order *
        (Real.log P.L / Real.log 2 + 2) ^ (G.molecule.rho + numCriticalSGMK C S))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← mul_assoc]
    exact habs
  have hreal : (coupling P.d P.L P.γ P.δ) ^ G.order * (2 * P.L + 1) ^ ((exDarts G E).card * P.d) *
      (((G.order : ℝ) + 1) * P.L) ^ (4 * E.card) *
      (P.C₁ * (P.C₁ * P.δ ^ (-1 / 2 - 5 * P.ν)) ^ G.order * P.L ^ (P.δ ^ (5 * P.ν) * G.molecule.rho)) *
      ((P.L ^ (2 * (S.m : ℝ)) * P.L ^ (-4 * P.η ^ 6 * (G.molecule.rho + numCriticalSGMK C S)) *
          P.L ^ (((R : ℝ) - 1) * ((P.d : ℝ) - P.γ - 1 / 4 - 1 / 40))) /
        molecularCountNormalization G.molecule P.d P.L P.γ P.δ P.C₁) ≤
      fineConst P G E S.m C.subpro.hinges.card *
        ((((3 ^ 16 * 17 : ℕ) : ℝ)) ^ G.order *
          (Real.log P.L / Real.log 2 + 2) ^ (G.molecule.rho + numCriticalSGMK C S))⁻¹ := by
    have e : (coupling P.d P.L P.γ P.δ) ^ G.order * (2 * P.L + 1) ^ ((exDarts G E).card * P.d) *
        (((G.order : ℝ) + 1) * P.L) ^ (4 * E.card) *
        (P.C₁ * (P.C₁ * P.δ ^ (-1 / 2 - 5 * P.ν)) ^ G.order * P.L ^ (P.δ ^ (5 * P.ν) * G.molecule.rho)) *
        ((P.L ^ (2 * (S.m : ℝ)) * P.L ^ (-4 * P.η ^ 6 * (G.molecule.rho + numCriticalSGMK C S)) *
            P.L ^ (((R : ℝ) - 1) * ((P.d : ℝ) - P.γ - 1 / 4 - 1 / 40))) /
          molecularCountNormalization G.molecule P.d P.L P.γ P.δ P.C₁) =
        (2 * P.L + 1) ^ ((exDarts G E).card * P.d) * (((G.order : ℝ) + 1) * P.L) ^ (4 * E.card) *
          P.L ^ (2 * (S.m : ℝ)) * rawPrefactorMK G P.d (numCriticalSGMK C S) P.L P.γ P.η P.δ P.C₁ P.ν := by
      unfold rawPrefactorMK
      ring
    rw [e]
    unfold fineConst
    calc (2 * P.L + 1) ^ ((exDarts G E).card * P.d) * (((G.order : ℝ) + 1) * P.L) ^ (4 * E.card) *
          P.L ^ (2 * (S.m : ℝ)) * rawPrefactorMK G P.d (numCriticalSGMK C S) P.L P.γ P.η P.δ P.C₁ P.ν
        ≤ (2 * P.L + 1) ^ ((exDarts G E).card * P.d) * (((G.order : ℝ) + 1) * P.L) ^ (4 * E.card) *
          P.L ^ (2 * (S.m : ℝ)) * (P.C₁ * Real.exp (G.order * (Real.log P.C₁ - 10 * P.ν * Real.log P.δ) +
            (-P.η ^ 6 * (G.molecule.rho + C.subpro.hinges.card) -
              ((R : ℝ) - 1) * (1 / 4 + 1 / 50)) * Real.log P.L) *
          ((((3 ^ 16 * 17 : ℕ) : ℝ)) ^ G.order *
            (Real.log P.L / Real.log 2 + 2) ^ (G.molecule.rho + numCriticalSGMK C S))⁻¹) :=
          mul_le_mul_of_nonneg_left hraw (by positivity)
      _ = _ := by ring
  -- the extended-real chain
  have hcountle : (G.molecule.countE P.L P.γ P.δ base
        (splicedCountingAdmissibleMK G D.toSplicedKernelData C S P.L P.γ P.η base roots) : ℝ≥0∞) *
      ENNReal.ofReal (∏ S' ∈ G.molecule.maximalLadders,
        Molecule.ladderWeight P.L P.γ P.δ (C.ladderScale S') ^ Molecule.ladderLength S') ≤
      ENNReal.ofReal ((P.L ^ (2 * (S.m : ℝ)) * P.L ^ (-4 * P.η ^ 6 * (G.molecule.rho + numCriticalSGMK C S)) *
          P.L ^ (((R : ℝ) - 1) * ((P.d : ℝ) - P.γ - 1 / 4 - 1 / 40))) /
        molecularCountNormalization G.molecule P.d P.L P.γ P.δ P.C₁) := by
    rw [hceq, ENNReal.ofReal_div_of_pos hnorm, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hFCj zero_le
  have hcn : 0 ≤ (coupling P.d P.L P.γ P.δ) ^ G.order := by positivity
  have hR4 : ∀ a b c e f : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ e →
      ENNReal.ofReal (a * b * c * e * f) =
        ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c * ENNReal.ofReal e * ENNReal.ofReal f := by
    intro a b c e f ha hb hc he
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul ha]
  rw [hc]
  refine (mul_le_mul_of_nonneg_left hcnt zero_le).trans ?_
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal hreal)
  rw [hR4 _ _ _ _ _ hcn hTb0 hQ hA, ENNReal.ofReal_mul hQ, ENNReal.ofReal_mul hA]
  exact ennreal_rearrange hTb hcountle

end WaveTurbulence.Flower.FinalMKFine
