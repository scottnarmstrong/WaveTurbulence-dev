/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKFine.CoverMK
import Mathlib.Tactic

/-! # C4b FINE-PIN: the choice budget with survivors and the raw prefactor arithmetic

Copy-thread of main's `CoverBudget` (scales only at `CriticalSGMK` atoms) and of `SplicedRawPrefactorLog`,
`SplicedChoiceScaleAbsorption` (the critical count `p` is a parameter, `q ≤ p`):
- `tsum_weightMK_le_one`: `∑_{(t,s)} (C₀^n ((log L/log 2)+2)^{ρ+p(t)})⁻¹ ≤ 1` over all tags and survivor scales;
- `rawPrefactorMK_mul_choiceScale_le`: main's absorption with `p = numCriticalSGMK`, `q = #hinges`. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs
  WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical ENNReal

variable {w d : ℕ}

theorem finite_scalesMK {G : Garden w} (B : CountingChoices G d) (S : SurvivorData G) {L : ℝ} (hL : 0 < L)
    (γ η : ℝ) (hb : L ^ (-γ + η) ≤ 1) : Finite (ScalesMK B S L γ η) := by
  have := finite_sourcePositiveLadderScale hL
  have : Finite (Cover.AtomScale L γ η) :=
    Finite.of_injective
      (fun P : Cover.AtomScale L γ η =>
        (⟨P.1, P.2.1, P.2.2.1, P.2.2.2.trans hb⟩ : SourcePositiveLadderScale L))
      (fun P Q h => Subtype.ext (by simpa using congrArg Subtype.val h))
  unfold ScalesMK Cover.LadderChoices
  infer_instance

theorem card_scalesMK_le {G : Garden w} (B : CountingChoices G d) (S : SurvivorData G) {L : ℝ} (hL : 1 ≤ L)
    (γ η : ℝ) (hb : L ^ (-γ + η) ≤ 1) :
    (Nat.card (ScalesMK B S L γ η) : ℝ) ≤
      (Real.log L / Real.log 2 + 2) ^ G.molecule.maximalLadders.card *
        (Real.log L / Real.log 2 + 1) ^ numCriticalSGMK B S := by
  have hlog : 0 ≤ Real.log L / Real.log 2 :=
    div_nonneg (Real.log_nonneg hL) (Real.log_nonneg (by norm_num))
  unfold ScalesMK
  rw [Nat.card_prod, Nat.cast_mul]
  have h1 := card_sourceLadderScaleFamilies_le (V := {S // S ∈ G.molecule.maximalLadders}) hL
  have hV : Nat.card {S // S ∈ G.molecule.maximalLadders} = G.molecule.maximalLadders.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hV] at h1
  have h2 : (Nat.card ({v // CriticalSGMK B S v} → Cover.AtomScale L γ η) : ℝ) ≤
      (Real.log L / Real.log 2 + 1) ^ numCriticalSGMK B S := by
    rw [Nat.card_fun, Nat.cast_pow]
    have hc : Nat.card {v // CriticalSGMK B S v} = numCriticalSGMK B S := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; rfl
    rw [hc]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (card_sourceAtomScales_le hL hb) _
  exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)

theorem scalesMK_weight_le {R : ℕ} (G : Garden (2 * R)) (B : CountingChoices G d) (S : SurvivorData G) {L : ℝ}
    (hL : 1 ≤ L) (γ η : ℝ) (hb : L ^ (-γ + η) ≤ 1) (C₀ : ℝ) (hC₀pos : 0 < C₀)
    [Fintype (ScalesMK B S L γ η)] :
    ∑ _x : ScalesMK B S L γ η, (C₀ ^ G.order * (Real.log L / Real.log 2 + 2) ^
        (G.molecule.rho + numCriticalSGMK B S))⁻¹ ≤ (C₀ ^ G.order)⁻¹ := by
  set s : ℝ := Real.log L / Real.log 2 + 2 with hs
  have hlog : 0 ≤ Real.log L / Real.log 2 :=
    div_nonneg (Real.log_nonneg hL) (Real.log_nonneg (by norm_num))
  have hs1 : 1 ≤ s := by rw [hs]; linarith
  have hq : G.molecule.maximalLadders.card ≤ G.molecule.rho := source_numLadders_le_rho G
  have hcard := card_scalesMK_le B S hL γ η hb
  have hcard' : (Fintype.card (ScalesMK B S L γ η) : ℝ) ≤ s ^ (G.molecule.rho + numCriticalSGMK B S) := by
    rw [← Nat.card_eq_fintype_card]
    refine hcard.trans ?_
    calc (Real.log L / Real.log 2 + 2) ^ G.molecule.maximalLadders.card *
          (Real.log L / Real.log 2 + 1) ^ numCriticalSGMK B S
        ≤ s ^ G.molecule.maximalLadders.card * s ^ numCriticalSGMK B S := by
          apply mul_le_mul le_rfl (pow_le_pow_left₀ (by linarith) (by rw [hs]; linarith) _)
            (by positivity) (by positivity)
      _ = s ^ (G.molecule.maximalLadders.card + numCriticalSGMK B S) := (pow_add _ _ _).symm
      _ ≤ s ^ (G.molecule.rho + numCriticalSGMK B S) :=
          pow_le_pow_right₀ hs1 (Nat.add_le_add_right hq _)
  rw [sum_const, card_univ, nsmul_eq_mul]
  have hpos : 0 < C₀ ^ G.order * s ^ (G.molecule.rho + numCriticalSGMK B S) := by positivity
  calc (Fintype.card (ScalesMK B S L γ η) : ℝ) *
        (C₀ ^ G.order * s ^ (G.molecule.rho + numCriticalSGMK B S))⁻¹
      ≤ s ^ (G.molecule.rho + numCriticalSGMK B S) *
          (C₀ ^ G.order * s ^ (G.molecule.rho + numCriticalSGMK B S))⁻¹ :=
        mul_le_mul_of_nonneg_right hcard' (inv_nonneg.mpr hpos.le)
    _ = (C₀ ^ G.order)⁻¹ := by
        rw [mul_inv, mul_comm (C₀ ^ G.order)⁻¹, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- The weight of a (tag, survivor scales) index. -/
noncomputable def weightMK {R : ℕ} (G : Garden (2 * R)) (hM : G.molecule.IsMolecule) (Cs : SubproChoices G)
    (S : SurvivorData G) (L γ η : ℝ) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ)) (C₀ : ℝ)
    (t : Cover.Tag G) : ℝ :=
  C₀ ^ G.order * (Real.log L / Real.log 2 + 2) ^
    (G.molecule.rho + numCriticalSGMK (tagChoiceMK G hM Cs S L γ η base roots t) S)

theorem weightMK_pos {R : ℕ} (G : Garden (2 * R)) (hM : G.molecule.IsMolecule) (Cs : SubproChoices G)
    (S : SurvivorData G) {L : ℝ} (hL : 1 ≤ L) (γ η : ℝ) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ))
    {C₀ : ℝ} (hC₀ : 0 < C₀) (t : Cover.Tag G) : 0 < weightMK G hM Cs S L γ η base roots C₀ t := by
  have hlog : 0 ≤ Real.log L / Real.log 2 :=
    div_nonneg (Real.log_nonneg hL) (Real.log_nonneg (by norm_num))
  unfold weightMK
  positivity

/-- **The budget with survivors**: the reciprocal weights of all tags and survivor scales sum to at most one. -/
theorem tsum_weightMK_le_one {R : ℕ} (G : Garden (2 * R)) (hM : G.molecule.IsMolecule) (Cs : SubproChoices G)
    (S : SurvivorData G) {L : ℝ} (hL : 1 ≤ L) (γ η : ℝ) (hb : L ^ (-γ + η) ≤ 1) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (C₀ : ℝ) (hC₀ : ((3 ^ 16 * 17 : ℕ) : ℝ) ≤ C₀) :
    ∑' j : (Σ t : Cover.Tag G, ScalesMK (tagChoiceMK G hM Cs S L γ η base roots t) S L γ η),
      ENNReal.ofReal (weightMK G hM Cs S L γ η base roots C₀ j.1)⁻¹ ≤ 1 := by
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le (by positivity) hC₀
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let _ : ∀ t : Cover.Tag G, Fintype (ScalesMK (tagChoiceMK G hM Cs S L γ η base roots t) S L γ η) :=
    fun t => @Fintype.ofFinite _ (finite_scalesMK _ S hL0 γ η hb)
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
    inv_nonneg.mpr (weightMK_pos G hM Cs S hL γ η base roots hC₀pos j.1).le)]
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [Fintype.sum_sigma]
  have hper : ∀ t : Cover.Tag G,
      ∑ x : ScalesMK (tagChoiceMK G hM Cs S L γ η base roots t) S L γ η,
        (weightMK G hM Cs S L γ η base roots C₀ t)⁻¹ ≤ (C₀ ^ G.order)⁻¹ := fun t =>
    scalesMK_weight_le G (tagChoiceMK G hM Cs S L γ η base roots t) S hL γ η hb C₀ hC₀pos
  calc ∑ t : Cover.Tag G, ∑ x : ScalesMK (tagChoiceMK G hM Cs S L γ η base roots t) S L γ η,
        (weightMK G hM Cs S L γ η base roots C₀ (⟨t, x⟩ : (Σ t : Cover.Tag G,
          ScalesMK (tagChoiceMK G hM Cs S L γ η base roots t) S L γ η)).1)⁻¹
      ≤ ∑ _t : Cover.Tag G, (C₀ ^ G.order)⁻¹ := sum_le_sum (fun t _ => hper t)
    _ = (Fintype.card (Cover.Tag G) : ℝ) * (C₀ ^ G.order)⁻¹ := by simp
    _ ≤ 1 := by
        have hT : (Fintype.card (Cover.Tag G) : ℝ) ≤ ((3 ^ 16 * 17 : ℕ) : ℝ) ^ G.order := by
          have hT' : Fintype.card (Cover.Tag G) ≤ (3 ^ 16 * 17) ^ G.order := by
            unfold Cover.Tag
            rw [Fintype.card_prod, mul_pow]
            exact Nat.mul_le_mul (card_sourceGapTables_le G) (card_sourcePairTables_le G)
          exact_mod_cast hT'
        have hpow : ((3 ^ 16 * 17 : ℕ) : ℝ) ^ G.order ≤ C₀ ^ G.order :=
          pow_le_pow_left₀ (by positivity) hC₀ _
        have hcp : 0 < C₀ ^ G.order := by positivity
        calc (Fintype.card (Cover.Tag G) : ℝ) * (C₀ ^ G.order)⁻¹ ≤ C₀ ^ G.order * (C₀ ^ G.order)⁻¹ :=
              mul_le_mul_of_nonneg_right (hT.trans hpow) (inv_nonneg.mpr hcp.le)
          _ = 1 := mul_inv_cancel₀ hcp.ne'

/-! ### The raw prefactor with a parameter critical count -/

/-- Main's `splicedRawPrefactor` with the critical count `p` as a parameter. -/
noncomputable def rawPrefactorMK {R : ℕ} (G : Garden (2 * R)) (d p : ℕ) (L γ η δ C₁ ν : ℝ) : ℝ :=
  (coupling d L γ δ) ^ G.order *
    (C₁ * (C₁ * δ ^ (-1 / 2 - 5 * ν)) ^ G.order * L ^ (δ ^ (5 * ν) * G.molecule.rho)) *
    ((L ^ (-4 * η ^ 6 * (G.molecule.rho + p)) *
      L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40))) /
      molecularCountNormalization G.molecule d L γ δ C₁)

theorem rawPrefactorMK_pos {R : ℕ} (G : Garden (2 * R)) (d p : ℕ) {L δ C₁ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hC₁ : 0 < C₁) (γ η ν : ℝ) : 0 < rawPrefactorMK G d p L γ η δ C₁ ν := by
  have ht := molecularCountNormalization_pos G.molecule d hL hδ hC₁ γ
  unfold rawPrefactorMK coupling
  positivity

theorem circuitRank_of_geom {R : ℕ} (G : Garden (2 * R)) (h : SplicedGeomPremises G) (hn : 1 ≤ G.order) :
    G.molecule.circuitRank = (G.order : ℤ) - R + 1 := by
  have hnonempty : G.molecule.atoms.Nonempty := by
    apply Finset.card_pos.mp
    rw [h.atom_count]
    omega
  have hcomp := WaveTurbulence.Mole.numComponents_eq_one G.molecule hnonempty h.connected
  have hE : (G.molecule.bonds.card : ℤ) + R = 2 * (G.order : ℤ) := by
    exact_mod_cast h.bond_count
  unfold Molecule.circuitRank
  rw [h.atom_count, hcomp]
  norm_num only [Nat.cast_one]
  omega

theorem log_rawPrefactorMK {R : ℕ} (G : Garden (2 * R)) (hgeo : SplicedGeomPremises G) (d p : ℕ)
    (hn : 1 ≤ G.order) {L δ C₁ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hC₁ : 0 < C₁) (γ η ν : ℝ) :
    Real.log (rawPrefactorMK G d p L γ η δ C₁ ν) =
      Real.log C₁ + G.order * (2 * Real.log C₁ - 5 * ν * Real.log δ - Real.log 2) +
        ((R : ℝ) - 1) * (Real.log δ / 2 - Real.log C₁) +
        (-4 * η ^ 6 * (G.molecule.rho + p) + δ ^ (5 * ν) * G.molecule.rho -
          ((R : ℝ) - 1) * (1 / 4 + 1 / 40)) * Real.log L := by
  have ht := molecularCountNormalization_pos G.molecule d hL hδ hC₁ γ
  have hc : 0 < coupling d L γ δ := by unfold coupling; positivity
  unfold rawPrefactorMK
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_mul hC₁.ne' (Real.rpow_pos_of_pos hδ _).ne',
    Real.log_rpow hδ, Real.log_rpow hL, Real.log_div (by positivity) ht.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hL, Real.log_rpow hL,
    log_molecularCountNormalization G.molecule d hL hδ hC₁ γ]
  unfold coupling
  rw [Real.log_div hδ.ne' (by positivity), Real.log_mul (by norm_num) (by positivity), Real.log_rpow hL]
  rw [circuitRank_of_geom G hgeo hn]
  push_cast
  ring

/-- Main's `splicedRawPrefactor_mul_choiceScale_le` with critical count `p` and hinge count `q ≤ p`. -/
theorem rawPrefactorMK_mul_choiceScale_le {R : ℕ} (G : Garden (2 * R)) (hgeo : SplicedGeomPremises G)
    (d p q : ℕ) (hq : q ≤ p) (hn : 1 ≤ G.order) (hR : 1 ≤ R)
    {L δ C₁ C₀ η ν scaleCost : ℝ} (hL : 1 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC₁ : 1 ≤ C₁) (hC₀ : 0 < C₀) (hscale : 0 < scaleCost)
    (ha : δ ^ (5 * ν) ≤ η ^ 6)
    (hb : Real.log scaleCost ≤ η ^ 6 * Real.log L)
    (hsmall : Real.log C₁ + Real.log C₀ + 5 * ν * Real.log δ ≤ 0) (γ : ℝ) :
    rawPrefactorMK G d p L γ η δ C₁ ν * C₀ ^ G.order * scaleCost ^ (G.molecule.rho + p) ≤
      C₁ * Real.exp (G.order * (Real.log C₁ - 10 * ν * Real.log δ) +
        (-η ^ 6 * (G.molecule.rho + q) - ((R : ℝ) - 1) * (1 / 4 + 1 / 50)) * Real.log L) := by
  have hL0 := zero_lt_one.trans hL
  have hC₁0 := zero_lt_one.trans_le hC₁
  have hlogL : 0 < Real.log L := Real.log_pos hL
  have hpref := rawPrefactorMK_pos G d p hL0 hδ hC₁0 γ η ν
  have hleft : 0 < rawPrefactorMK G d p L γ η δ C₁ ν * C₀ ^ G.order *
      scaleCost ^ (G.molecule.rho + p) := by positivity
  have hright : 0 < C₁ * Real.exp (G.order * (Real.log C₁ - 10 * ν * Real.log δ) +
        (-η ^ 6 * (G.molecule.rho + q) - ((R : ℝ) - 1) * (1 / 4 + 1 / 50)) * Real.log L) := by
    positivity
  apply (Real.log_le_log_iff hleft hright).mp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hpref.ne' (by positivity),
    Real.log_pow, Real.log_pow, Real.log_mul hC₁0.ne' (Real.exp_pos _).ne', Real.log_exp,
    log_rawPrefactorMK G hgeo d p hn hL0 hδ hC₁0 γ η ν]
  have hq' : (q : ℝ) ≤ p := by exact_mod_cast hq
  have hh := spliced_counting_exponent_le (R := (R : ℝ)) (ρ := (G.molecule.rho : ℝ))
    (p := (p : ℝ)) (q := (q : ℝ)) (n := (G.order : ℝ))
    (Real.log_nonneg hC₁) (Real.log_nonpos hδ.le hδ1)
    hlogL.le (by positivity : 0 ≤ η ^ 6) (Nat.cast_nonneg G.order)
    (by exact_mod_cast hR) (Nat.cast_nonneg G.molecule.rho) (Nat.cast_nonneg p)
    hq' ha hb hsmall
  have htwo : 0 ≤ (G.order : ℝ) * Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  push_cast
  linarith

end WaveTurbulence.Flower.FinalMKFine
