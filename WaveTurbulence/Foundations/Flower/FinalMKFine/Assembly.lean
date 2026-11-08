/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKFine.PerChoice
public import WaveTurbulence.Foundations.Flower.FinalMKFine.LBPin
import Mathlib.Tactic

/-! # C4b FINE-PIN: `FineSplicedAtMK` at fixed parameters

`fineSplicedAtMK_of_gates`: from `LadderFourierAtMK P` (C4a), `FinalCountAtMK P` (C1) and the numerical
conditions of main's `fine_spliced_of_subpro_choices` (plus `81 ≤ L` for FL-FIBER's `(3L)^{4d} ≤ L^{5d}`):
1. `splicedKernelMK = c^n ∑' z, ampMK z · B_MK(α z)` and `‖∑'‖ₑ ≤ ∑' ‖·‖ₑ` (no cancellation is used);
2. the cover with survivors (`exists_cover_choiceMK`) puts every nonzero summand in some `carrierMK`;
3. each carrier is bounded by `perChoice_le`, and the reciprocal weights sum to `≤ 1` (`tsum_weightMK_le_one`);
4. `(2L+1)^{d·#X} ≤ ((N+1)L)^{5d|E|}` (`#X ≤ 4|E|`, o75 row 12) and main's `exp_form_eq_fine`.
Ruling R187: steps 1–4 are `fineSplicedAtMK_of_gates_nolb` (data without lower bounds); a lower-bounded atom is
exceptional, so `LBPin.norm_kernelMK_le_of_pinLB` (pin it, integrate over a window of length `≤ 1`) gives the
general case. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs
  WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical ENNReal

variable {w d : ℕ}

theorem fullChoiceMK_tag_subpro (G : Garden w) (hM : G.molecule.IsMolecule) (Cs : SubproChoices G)
    (S : SurvivorData G) (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (t : Cover.Tag G)
    (s : ScalesMK (tagChoiceMK G hM Cs S L γ η base roots t) S L γ η) :
    (fullChoiceMK (tagChoiceMK G hM Cs S L γ η base roots t) S s).subpro = Cs := by
  unfold fullChoiceMK tagChoiceMK
  rfl

theorem fullChoiceMK_tag_fixedRoots (G : Garden w) (hM : G.molecule.IsMolecule) (Cs : SubproChoices G)
    (S : SurvivorData G) (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (t : Cover.Tag G)
    (s : ScalesMK (tagChoiceMK G hM Cs S L γ η base roots t) S L γ η) :
    (fullChoiceMK (tagChoiceMK G hM Cs S L γ η base roots t) S s).fixedRoots =
      Finset.univ.image (fun i => base + latticePoint L (roots i)) := by
  unfold fullChoiceMK tagChoiceMK
  rfl

/-- The exceptional tuples and the Fourier factor: `(2L+1)^{d·#X} · ((N+1)L)^{4|E|} ≤ ((N+1)L)^{(5d+4)|E|}`. -/
theorem tuples_mul_le {w : ℕ} (G : Garden w) (E : Finset (GBranch G.tree)) (d n : ℕ) {L : ℝ} (hL : 81 ≤ L) :
    (2 * L + 1) ^ ((exDarts G E).card * d) * (((n : ℝ) + 1) * L) ^ (4 * E.card) ≤
      (((n : ℝ) + 1) * L) ^ ((5 * d + 4) * E.card) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (2 * L + 1) ^ ((exDarts G E).card * d) ≤ (2 * L + 1) ^ (4 * E.card * d) :=
    pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_right d (card_exDarts_le G E))
  have h2 : (2 * L + 1) ^ (4 * E.card * d) ≤ (3 * L) ^ (4 * E.card * d) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hLn : L ≤ ((n : ℝ) + 1) * L := le_mul_of_one_le_left (by linarith) (by linarith)
  have h3 : (3 * L) ^ 4 ≤ (((n : ℝ) + 1) * L) ^ 5 := by
    calc (3 * L) ^ 4 = 81 * L ^ 4 := by ring
      _ ≤ L * L ^ 4 := by gcongr
      _ = L ^ 5 := by ring
      _ ≤ (((n : ℝ) + 1) * L) ^ 5 := pow_le_pow_left₀ (by linarith) hLn 5
  have h4 : (3 * L) ^ (4 * E.card * d) ≤ (((n : ℝ) + 1) * L) ^ (5 * d * E.card) := by
    rw [show 4 * E.card * d = 4 * (E.card * d) by ring, pow_mul (3 * L) 4 (E.card * d),
      show 5 * d * E.card = 5 * (E.card * d) by ring, pow_mul (((n : ℝ) + 1) * L) 5 (E.card * d)]
    exact pow_le_pow_left₀ (by positivity) h3 _
  calc (2 * L + 1) ^ ((exDarts G E).card * d) * (((n : ℝ) + 1) * L) ^ (4 * E.card)
      ≤ (((n : ℝ) + 1) * L) ^ (5 * d * E.card) * (((n : ℝ) + 1) * L) ^ (4 * E.card) :=
        mul_le_mul_of_nonneg_right (h1.trans (h2.trans h4)) (by positivity)
    _ = (((n : ℝ) + 1) * L) ^ ((5 * d + 4) * E.card) := by
        rw [← pow_add]
        congr 1
        ring

/-- **`FineSplicedAtMK` at fixed parameters for data without lower bounds** (o73 Prop 18.1 inside main's fine
bound, with survivors). -/
theorem fineSplicedAtMK_of_gates_nolb (P : WTParams) (hLF : LadderFourierAtMK P) (hFC : FinalCountAtMK P)
    (hL : 81 ≤ P.L) (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁) (hδ1 : P.δ ≤ 1)
    (hcap : 2 * P.L⁻¹ ≤ P.L ^ (-P.γ + P.η)) (hb1 : P.L ^ (-P.γ + P.η) ≤ 1)
    (ha : P.δ ^ (5 * P.ν) ≤ P.η ^ 6)
    (hb : Real.log (Real.log P.L / Real.log 2 + 2) ≤ P.η ^ 6 * Real.log P.L)
    (hsmall : Real.log P.C₁ + Real.log (((3 ^ 16 * 17 : ℕ) : ℝ)) + 5 * P.ν * Real.log P.δ ≤ 0) :
    ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
    ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
      1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
    ∀ (D : SplicedKernelDataMK G P.d) (Cs : SubproChoices G) (S : SurvivorData G) (E : Finset (GBranch G.tree)),
      SplicedAmplitudeBounds G D.toSplicedKernelData → (∀ v, D.layer v ≤ p) →
      (∀ a q, D.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) → (∀ k, 0 ≤ D.ind k ∧ D.ind k ≤ 1) →
      (∀ b, (D.fix b).isSome → b ∈ E) → (∀ b t, D.fix b = some t → (D.layer b : ℝ) ≤ t ∧ t ≤ D.layer b + 1) →
      D.lb = (fun _ => none) →
    ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
      SplicedGeomPremises G → SubproConclusionsMK G D.toSplicedKernelData Cs S P.L P.γ P.η base roots →
      ‖splicedKernelMK G D P.L P.γ P.η P.δ base roots‖ ≤
        P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order * P.L ^ (2 * (S.m : ℝ)) *
          (((G.order : ℝ) + 1) * P.L) ^ ((5 * P.d + 4) * E.card) *
          P.L ^ (-P.η ^ 6 * (G.molecule.rho + D.hinges.card)) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)) := by
  intro p hp R hR hRmax G hplain hirred hbal hn hnmax D Cs S E hD hlayer hfilt hind hfixE hfixT hlb base roots
    hgeo hS
  have hL2 : 2 ≤ P.L := by linarith
  have hL1 : 1 ≤ P.L := by linarith
  have hL0 : 0 < P.L := by linarith
  have hC₁0 : 0 < P.C₁ := by linarith
  have hF0 := fineConst_nonneg P G E S.m Cs.hinges.card hL0.le hC₁0.le
  have hcov : ∀ z : GenDecoration G P.d roots 0,
      ‖ampMK G D P.L P.γ P.η base z.1 * splicedFourierBMK G D.layer D.rootTime D.fix
          (splicedFrequency G D.toSplicedKernelData P.L P.γ P.δ base z.1)‖ₑ ≤
        ∑' j : (Σ t : Cover.Tag G, ScalesMK (tagChoiceMK G hgeo.molecule Cs S P.L P.γ P.η base roots t) S
            P.L P.γ P.η),
          (carrierMK G D (fullChoiceMK _ S j.2) S P.L P.γ P.η base roots).indicator
            (fun z => ‖ampMK G D P.L P.γ P.η base z.1 * splicedFourierBMK G D.layer D.rootTime D.fix
              (splicedFrequency G D.toSplicedKernelData P.L P.γ P.δ base z.1)‖ₑ) z := by
    intro z
    by_cases hz : ampMK G D P.L P.γ P.η base z.1 = 0
    · simp [hz]
    · obtain ⟨t, s, hadm⟩ := exists_cover_choiceMK G hplain hgeo.molecule D hD Cs S hL2 P.γ P.η hcap base
        roots hS z hz
      refine le_trans ?_ (ENNReal.le_tsum (⟨t, s⟩ : (Σ t : Cover.Tag G,
        ScalesMK (tagChoiceMK G hgeo.molecule Cs S P.L P.γ P.η base roots t) S P.L P.γ P.η)))
      rw [Set.indicator_of_mem (show z ∈ carrierMK G D (fullChoiceMK _ S s) S P.L P.γ P.η base roots
        from ⟨hz, hadm⟩)]
  have hper : ∀ j : (Σ t : Cover.Tag G, ScalesMK (tagChoiceMK G hgeo.molecule Cs S P.L P.γ P.η base roots t) S
      P.L P.γ P.η),
      ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ G.order‖ₑ *
        ∑' z : carrierMK G D (fullChoiceMK _ S j.2) S P.L P.γ P.η base roots,
          ‖ampMK G D P.L P.γ P.η base z.1.1 * splicedFourierBMK G D.layer D.rootTime D.fix
            (splicedFrequency G D.toSplicedKernelData P.L P.γ P.δ base z.1.1)‖ₑ ≤
        ENNReal.ofReal (fineConst P G E S.m Cs.hinges.card *
          (weightMK G hgeo.molecule Cs S P.L P.γ P.η base roots (((3 ^ 16 * 17 : ℕ) : ℝ)) j.1)⁻¹) := by
    intro j
    have h := perChoice_le P hLF hFC hL2 hδ hC₁ hδ1 ha hb hsmall hp hR hRmax G hplain hirred hbal hn hnmax
      D Cs S E hD hlayer hfilt hind hfixE hfixT base roots hgeo hS (fullChoiceMK _ S j.2)
      (fullChoiceMK_tag_subpro G hgeo.molecule Cs S P.L P.γ P.η base roots j.1 j.2)
      (fullChoiceMK_tag_fixedRoots G hgeo.molecule Cs S P.L P.γ P.η base roots j.1 j.2)
    rw [fullChoiceMK_numCritical] at h
    exact h
  have hK : ‖splicedKernelMK G D P.L P.γ P.η P.δ base roots‖ₑ ≤
      ENNReal.ofReal (fineConst P G E S.m Cs.hinges.card) := by
    rw [splicedKernelMK_eq G D hlb, enorm_mul]
    calc ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ G.order‖ₑ *
          ‖∑' z : GenDecoration G P.d roots 0, ampMK G D P.L P.γ P.η base z.1 *
            splicedFourierBMK G D.layer D.rootTime D.fix
              (splicedFrequency G D.toSplicedKernelData P.L P.γ P.δ base z.1)‖ₑ
        ≤ ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ G.order‖ₑ *
          ∑' z : GenDecoration G P.d roots 0, ‖ampMK G D P.L P.γ P.η base z.1 *
            splicedFourierBMK G D.layer D.rootTime D.fix
              (splicedFrequency G D.toSplicedKernelData P.L P.γ P.δ base z.1)‖ₑ :=
          mul_le_mul_of_nonneg_left enorm_tsum_le_tsum_enorm zero_le
      _ ≤ ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ G.order‖ₑ *
          ∑' j : (Σ t : Cover.Tag G, ScalesMK (tagChoiceMK G hgeo.molecule Cs S P.L P.γ P.η base roots t) S
            P.L P.γ P.η),
          ∑' z : carrierMK G D (fullChoiceMK _ S j.2) S P.L P.γ P.η base roots,
            ‖ampMK G D P.L P.γ P.η base z.1.1 * splicedFourierBMK G D.layer D.rootTime D.fix
              (splicedFrequency G D.toSplicedKernelData P.L P.γ P.δ base z.1.1)‖ₑ := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          refine (ENNReal.tsum_le_tsum hcov).trans (le_of_eq ?_)
          rw [ENNReal.tsum_comm]
          congr 1
          funext j
          exact (_root_.tsum_subtype _ _).symm
      _ = ∑' j : (Σ t : Cover.Tag G, ScalesMK (tagChoiceMK G hgeo.molecule Cs S P.L P.γ P.η base roots t) S
            P.L P.γ P.η),
          ‖(coupling P.d P.L P.γ P.δ : ℂ) ^ G.order‖ₑ *
          ∑' z : carrierMK G D (fullChoiceMK _ S j.2) S P.L P.γ P.η base roots,
            ‖ampMK G D P.L P.γ P.η base z.1.1 * splicedFourierBMK G D.layer D.rootTime D.fix
              (splicedFrequency G D.toSplicedKernelData P.L P.γ P.δ base z.1.1)‖ₑ :=
          ENNReal.tsum_mul_left.symm
      _ ≤ ∑' j : (Σ t : Cover.Tag G, ScalesMK (tagChoiceMK G hgeo.molecule Cs S P.L P.γ P.η base roots t) S
            P.L P.γ P.η),
          ENNReal.ofReal (fineConst P G E S.m Cs.hinges.card) *
            ENNReal.ofReal (weightMK G hgeo.molecule Cs S P.L P.γ P.η base roots
              (((3 ^ 16 * 17 : ℕ) : ℝ)) j.1)⁻¹ := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          rw [← ENNReal.ofReal_mul hF0]
          exact hper j
      _ = ENNReal.ofReal (fineConst P G E S.m Cs.hinges.card) *
          ∑' j : (Σ t : Cover.Tag G, ScalesMK (tagChoiceMK G hgeo.molecule Cs S P.L P.γ P.η base roots t) S
            P.L P.γ P.η),
            ENNReal.ofReal (weightMK G hgeo.molecule Cs S P.L P.γ P.η base roots
              (((3 ^ 16 * 17 : ℕ) : ℝ)) j.1)⁻¹ := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (fineConst P G E S.m Cs.hinges.card) * 1 :=
          mul_le_mul_of_nonneg_left (tsum_weightMK_le_one G hgeo.molecule Cs S hL1 P.γ P.η hb1 base roots
            _ le_rfl) zero_le
      _ = _ := mul_one _
  have hnorm : ‖splicedKernelMK G D P.L P.γ P.η P.δ base roots‖ ≤ fineConst P G E S.m Cs.hinges.card := by
    rw [← ofReal_norm] at hK
    exact (ENNReal.ofReal_le_ofReal_iff hF0).mp hK
  refine hnorm.trans ?_
  have hT := tuples_mul_le G E P.d G.order hL
  have hLm : 0 ≤ P.L ^ (2 * (S.m : ℝ)) := Real.rpow_nonneg hL0.le _
  unfold fineConst
  rw [Cover.exp_form_eq_fine G P hL0 hC₁0 hδ, hS.hinges]
  have hrest : 0 ≤ P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order *
      P.L ^ (-P.η ^ 6 * (G.molecule.rho + Cs.hinges.card)) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)) := by
    have := Real.rpow_nonneg hL0.le (-P.η ^ 6 * (G.molecule.rho + Cs.hinges.card))
    have := Real.rpow_nonneg hL0.le (-((R : ℝ) - 1) * (1 / 4 + 1 / 50))
    have := Real.rpow_nonneg hδ.le (-10 * P.ν)
    positivity
  calc (2 * P.L + 1) ^ ((exDarts G E).card * P.d) * (((G.order : ℝ) + 1) * P.L) ^ (4 * E.card) *
        P.L ^ (2 * (S.m : ℝ)) *
        (P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order *
          P.L ^ (-P.η ^ 6 * (G.molecule.rho + Cs.hinges.card)) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)))
      ≤ (((G.order : ℝ) + 1) * P.L) ^ ((5 * P.d + 4) * E.card) * P.L ^ (2 * (S.m : ℝ)) *
        (P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order *
          P.L ^ (-P.η ^ 6 * (G.molecule.rho + Cs.hinges.card)) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hT hLm) hrest
    _ = _ := by ring

/-- **`FineSplicedAtMK` at fixed parameters** (o73 Prop 18.1 inside main's fine bound, with survivors; ruling R187:
lower-bounded atoms are exceptional and are reduced to pins by `norm_kernelMK_le_of_pinLB`). -/
theorem fineSplicedAtMK_of_gates (P : WTParams) (hLF : LadderFourierAtMK P) (hFC : FinalCountAtMK P)
    (hL : 81 ≤ P.L) (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁) (hδ1 : P.δ ≤ 1)
    (hcap : 2 * P.L⁻¹ ≤ P.L ^ (-P.γ + P.η)) (hb1 : P.L ^ (-P.γ + P.η) ≤ 1)
    (ha : P.δ ^ (5 * P.ν) ≤ P.η ^ 6)
    (hb : Real.log (Real.log P.L / Real.log 2 + 2) ≤ P.η ^ 6 * Real.log P.L)
    (hsmall : Real.log P.C₁ + Real.log (((3 ^ 16 * 17 : ℕ) : ℝ)) + 5 * P.ν * Real.log P.δ ≤ 0) :
    FineSplicedAtMK P := by
  intro p hp R hR hRmax G hplain hirred hbal hn hnmax D Cs S E hD hlayer hfilt hind hfixE hfixT hlbE base roots
    hgeo hS
  have hL0 : 0 < P.L := by linarith
  refine norm_kernelMK_le_of_pinLB hplain hL0 P.γ P.η P.δ base roots _ D hD fun fix' hpins => ?_
  refine fineSplicedAtMK_of_gates_nolb P hLF hFC hL hδ hC₁ hδ1 hcap hb1 ha hb hsmall p hp R hR hRmax G hplain
    hirred hbal hn hnmax (pinData D fix') Cs S E hD hlayer hfilt hind (fun b hb => ?_) (fun b t ht => ?_) rfl base
    roots hgeo hS
  · by_cases hl : D.lb b = none
    · have e : (pinData D fix').fix b = D.fix b := hpins.1 b hl
      rw [e] at hb; exact hfixE b hb
    · exact hlbE b (Option.isSome_iff_ne_none.2 hl)
  · by_cases hl : D.lb b = none
    · have e : (pinData D fix').fix b = D.fix b := hpins.1 b hl
      rw [e] at ht; exact hfixT b t ht
    · rcases hpins.2 b (Option.isSome_iff_ne_none.2 hl) with e | ⟨r, hr, h1, h2⟩
      · have e' : (pinData D fix').fix b = D.fix b := e
        rw [e'] at ht; exact hfixT b t ht
      · have e' : (pinData D fix').fix b = some r := hr
        rw [e'] at ht; cases ht; exact ⟨h1, h2⟩

end WaveTurbulence.Flower.FinalMKFine
