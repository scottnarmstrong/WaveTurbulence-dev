/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Top.Assembly
public import WaveTurbulence.Foundations.Flower.Cases.Top

/-! # FLOWER-LOW (packet L8), item B (2/6): the flower cases from the two families, `0 < γ ≤ 1/2`

Main's `Flower.Cases.*` γ-carrying declarations copied by source, `1 / 2 < P.γ` ↦ `P.γ ≤ 1 / 2`, names suffixed
`Low`. One change beyond the carrier: main's `layergardenFlower_v3_of_families` takes the couple clause from main's
γ > 1/2 LG spine (`FlowerTop.coupleHalf_of_spine …`); `flower_low_of_families` takes it as the named input
`CoupleClauseLowInput` (PLAN-L8 item D). -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Cases
open scoped Classical
open Set WaveTurbulence.Flower.FamilyW

/-- **Input 1 (filtered family).** -/
def FlowerFiltFamilyAtLow (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (Pm : ℕ) (P : WTParams) : Prop :=
  P.γ ≤ 1 / 2 → ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
    ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
      (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (j : ℕ) (σ : Fin (2 * Pm) → Option ℕ),
    ((∃ i, σ i ≠ none) → ((2 : ℝ) ^ j * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) →
    UniformFlowerFamilyW P (inputsF P R) p N kind pat dagger ζ t s n n'
      (fun LG k => stemFilter LG P.L σ k)
      (2 ^ j * P.L) ((2 ^ j * P.L) / (4 * (2 * N + 1 : ℕ)))
      (fun _ => FC23.extractionRadius (40 * P.d) N (C P.d) (U {P with L := 1} p) (2 ^ j * P.L))
      (familyBudget Pm P p ζ n n' pat N Pm)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Cases
open scoped Classical
open Set WaveTurbulence.Flower.FamilyW

/-- **Input 2 (gain family).** Plain patterns, positive cut2 shell, frozen `M₂` gain. -/
def FlowerGainFamilyAtLow (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (Pm : ℕ) (P : WTParams) : Prop :=
  P.γ ≤ 1 / 2 → ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
    ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind)
      (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (j j₂ : ℕ), 0 < j₂ →
    ((2 : ℝ) ^ j * P.L) ^ 10 ≤ ‖latticePoint P.L n‖ →
    UniformFlowerFamilyW P (inputsF P R) p N kind (fun _ => .plain) dagger ζ t s n n'
      (fun LG k => LG.cutWeight2P P.L j₂ k)
      (2 ^ j * P.L) ((2 ^ j * P.L) / (4 * (2 * N + 1 : ℕ)))
      (fun _ => FC23.extractionRadius (40 * P.d) N (C P.d) (U {P with L := 1} p) (2 ^ j * P.L))
      (familyBudget Pm P p ζ n n' (fun _ => .plain) N 0 * ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ)))

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Cases
open scoped Classical
open Set Induct WaveTurbulence.FC23 WaveTurbulence.Flower.FamilyW

/-- The filtered family at a fixed parameter set gives the cut1 bound with the stem filter. -/
theorem filt_cut1Low (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d) (hU : ∀ P p, 0 < U P p)
    {Pm : ℕ} {P : WTParams} (hF : FlowerFiltFamilyAtLow C U Pm P)
    {p N : ℕ} (hnum : Numerics C U Pm P p N) (hγ : P.γ ≤ 1 / 2) (hp : p < P.D)
    (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p)
    (t : ℝ) (ht : t ∈ Ioo (p : ℝ) (p + 1)) (s : ℝ) (hs : s ∈ Ioo (p : ℝ) t) (n n' : Fin P.d → ℤ)
    (ζ : ℤˣ) (hN : N ≤ P.N (p + 1) ^ 4) (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
    (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (j : ℕ) (σ : Fin (2 * Pm) → Option ℕ)
    (hσ : (∃ i, σ i ≠ none) → ((2 : ℝ) ^ j * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) :
    ‖flowerWeighted P (inputsF P R) p N kind pat dagger
        (fun LG k => stemFilter LG P.L σ k * LG.cutWeight1P p P.L j k) ζ t s n n'‖ ≤
      FC23.flowerRootBudget Pm P p ζ n n' *
        P.L ^ (FC23.flowerLExponent Pm P pat - (Pm : ℝ)) * P.δ ^ (2 * P.ν * N) *
        (2 ^ j * P.L) ^ (-((((40 * P.d) * (2 * Pm) : ℕ) : ℝ))) := by
  have H := hF hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger j σ hσ
  have hroot : 0 ≤ FC23.flowerRootBudget Pm P p ζ n n' := by
    unfold FC23.flowerRootBudget
    exact Real.rpow_nonneg (by unfold jbr; positivity) _
  refine cut1W_flower C U hC hU hnum hp.le R hR kind pat dagger ζ t s n n'
    (fun LG k => stemFilter LG P.L σ k) (fun LG k => stemFilter_abs_le_one LG P.L σ k)
    _ _ hroot j ?_
  convert H using 2
  unfold familyBudget
  have e1 : FC23.flowerLExponent Pm P pat - (Pm : ℝ) - (((40 * P.d) * (2 * Pm) : ℕ) : ℝ) -
      ((2 * Pm : ℕ) : ℝ) = FC23.flowerLExponent Pm P pat - (((40 * P.d) * (2 * Pm) : ℕ) : ℝ) -
      ((2 * Pm : ℕ) : ℝ) - (Pm : ℝ) := by ring
  have e2 : (2 + 2 : ℝ) = 4 := by norm_num
  rw [e1, e2]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Cases
open scoped Classical
open Set Induct WaveTurbulence.FC23 WaveTurbulence.Flower.FamilyW

/-- The gain family at a fixed parameter set (plain patterns, positive shell). -/
theorem gain_cut1Low (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d) (hU : ∀ P p, 0 < U P p)
    {Pm : ℕ} {P : WTParams} (hG : FlowerGainFamilyAtLow C U Pm P)
    {p N : ℕ} (hnum : Numerics C U Pm P p N) (hγ : P.γ ≤ 1 / 2) (hp : p < P.D)
    (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p)
    (t : ℝ) (ht : t ∈ Ioo (p : ℝ) (p + 1)) (s : ℝ) (hs : s ∈ Ioo (p : ℝ) t) (n n' : Fin P.d → ℤ)
    (ζ : ℤˣ) (hN : N ≤ P.N (p + 1) ^ 4) (kind : FlowerKind)
    (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (j j₂ : ℕ) (hj₂ : 0 < j₂)
    (hj : ((2 : ℝ) ^ j * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) :
    ‖flowerWeighted P (inputsF P R) p N kind (fun _ => .plain) dagger
        (fun LG k => LG.cutWeight2P P.L j₂ k * LG.cutWeight1P p P.L j k) ζ t s n n'‖ ≤
      (FC23.flowerRootBudget Pm P p ζ n n' * ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ))) *
        P.L ^ (FC23.flowerLExponent Pm P (fun _ => .plain)) * P.δ ^ (2 * P.ν * N) *
        (2 ^ j * P.L) ^ (-((((40 * P.d) * (2 * Pm) : ℕ) : ℝ))) := by
  have H := hG hγ p hp R hR t ht s hs n n' ζ N hN kind dagger j j₂ hj₂ hj
  have hL0 : 0 < P.L := by have := hnum.2.2.2.2.1; linarith
  have hroot : 0 ≤ FC23.flowerRootBudget Pm P p ζ n n' * ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ)) := by
    refine mul_nonneg ?_ (Real.rpow_nonneg (by positivity) _)
    unfold FC23.flowerRootBudget
    exact Real.rpow_nonneg (by unfold jbr; positivity) _
  refine cut1W_flower C U hC hU hnum hp.le R hR kind (fun _ => .plain) dagger ζ t s n n'
    (fun LG k => LG.cutWeight2P P.L j₂ k)
    (fun LG k => cutWeight2P_abs_le_one LG P.L j₂ k) _ (FC23.flowerLExponent Pm P (fun _ => .plain)) hroot j ?_
  have e2 : (2 + 2 : ℝ) = 4 := by norm_num
  have hB : familyBudget Pm P p ζ n n' (fun _ => .plain) N 0 * ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ)) =
      (FC23.flowerRootBudget Pm P p ζ n n' * ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ))) *
        P.L ^ (FC23.flowerLExponent Pm P (fun _ => .plain) - (((40 * P.d) * (2 * Pm) : ℕ) : ℝ) -
          ((2 * Pm : ℕ) : ℝ)) * P.δ ^ ((2 + 2) * P.ν * N) := by
    unfold familyBudget
    rw [e2, sub_zero]
    ring
  rw [hB] at H
  exact H

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Cases
open scoped Classical
open Set Induct WaveTurbulence.FC23 WaveTurbulence.Flower.FamilyW WaveTurbulence.FlowerTop LGSpine

/-- `FlowerCaseAtLow` with an extra restriction on the pattern. -/
def FlowerCasePatAtLow (case : Option ℕ → Option ℕ → Prop)
    (patOK : ∀ {Pm : ℕ}, (Fin (2 * Pm) → FixPat) → Prop) (Pm : ℕ) (P : WTParams) : Prop :=
  P.γ ≤ 1 / 2 → ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
    ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
      (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ),
      case cut1 cut2 → patOK pat →
      (∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) →
      FlowerBoundAt P R p N Pm kind pat dagger cut1 cut2 ζ t s n n'

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Cases
open scoped Classical
open Set Induct WaveTurbulence.FC23 WaveTurbulence.Flower.FamilyW WaveTurbulence.FlowerTop LGSpine

theorem flowerCasePatAt_largeConstantMonotoneLow (case : Option ℕ → Option ℕ → Prop)
    (patOK : ∀ {Pm : ℕ}, (Fin (2 * Pm) → FixPat) → Prop) (Pm : ℕ) :
    LargeConstantMonotone (FlowerCasePatAtLow case patOK Pm) := by
  intro P c₁ c₂ _ _ _ _ _ _ h hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hpat hcut
  rw [N_largeConstants] at hN
  have H := h hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hpat hcut
  have hF : inputsF {P with C₁ := c₁, C₂ := c₂} R = inputsF P R := rfl
  unfold FlowerBoundAt at H ⊢
  rw [hF, flowerSumP_largeConstants]
  simpa only [N_largeConstants, WTParams.Lambda] using H

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Cases
open scoped Classical
open Set Induct WaveTurbulence.FC23 WaveTurbulence.Flower.FamilyW WaveTurbulence.FlowerTop LGSpine

theorem caseAt_of_pat_splitLow {case : Option ℕ → Option ℕ → Prop} {Pm : ℕ} {P : WTParams}
    (h1 : FlowerCasePatAtLow case PatPlain Pm P) (h2 : FlowerCasePatAtLow case PatNonplain Pm P) :
    FlowerCaseAtLow case Pm P := by
  intro hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hcut
  by_cases hpl : ∀ j, pat j = .plain
  · exact h1 hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hpl hcut
  · exact h2 hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hpl hcut

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Cases
open scoped Classical
open Set Induct WaveTurbulence.FC23 WaveTurbulence.Flower.FamilyW WaveTurbulence.FlowerTop LGSpine

/-- Plain clause from the filtered family at `σ ≡ none`, by letting the scale tend to infinity. -/
theorem casePlain_of_filtLow (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d)
    (hU : ∀ P p, 0 < U P p) {Pm : ℕ} {P : WTParams} (hF : FlowerFiltFamilyAtLow C U Pm P)
    (hnum : NumericsAll C U Pm P) :
    FlowerCaseAtLow CasePlain Pm P := by
  intro hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc _
  obtain ⟨rfl, rfl⟩ := hc
  obtain ⟨hd, hν, hδ, hδ1, hL4, -⟩ := hnum p hp N hN
  have hL : 1 ≤ P.L := by linarith
  have hL0 : 0 < P.L := zero_lt_one.trans_le hL
  have hsum := summable_clipped_inputs P R p hp.le hd hL hR
  have hH : ∀ j : ℕ, UniformFlowerFamilyW P (inputsF P (clipRemainder p R)) p N kind pat dagger ζ t s n n'
      (fun LG k => stemFilter LG P.L (fun _ => none) k)
      (2 ^ j * P.L) ((2 ^ j * P.L) / (4 * (2 * N + 1 : ℕ)))
      (fun _ => extractionRadius (40 * P.d) N (C P.d) (U {P with L := 1} p) (2 ^ j * P.L))
      (familyBudget Pm P p ζ n n' pat N Pm) := by
    intro j tail small z hz
    rw [flowerWeighted_clip]
    exact hF hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger j (fun _ => none)
      (fun h => absurd h (by simp)) tail small z hz
  have hle := plain_of_familyW P (inputsF P (clipRemainder p R)) p N kind pat dagger ζ t s n n'
    (fun LG k => stemFilter LG P.L (fun _ => none) k) hL0 hsum
    (fun LG k => stemFilter_abs_le_one LG P.L _ k)
    (fun j _ => extractionRadius (40 * P.d) N (C P.d) (U {P with L := 1} p) (2 ^ j * P.L))
    (fun j _ => (extractionRadius_pos (40 * P.d) N (hC P.d) (hU _ _)
      (by positivity : 0 < (2 : ℝ) ^ j * P.L)).le) _ hH
  have key : flowerSumP P (inputsF P R) p N kind pat dagger none none ζ t s n n' =
      flowerWeighted P (inputsF P (clipRemainder p R)) p N kind pat dagger
        (fun LG k => stemFilter LG P.L (fun _ => none) k) ζ t s n n' := by
    rw [flowerWeighted_clip, flowerSumP_eq_weighted]
    exact flowerWeighted_congr_weight P _ p N kind pat dagger ζ t s n n' fun LG k => by
      simp [stemFilter_none]
  unfold FlowerBoundAt
  rw [key]
  simp only [Option.elim, mul_one]
  refine hle.trans ?_
  have hroot := rootBudget_nonneg Pm P p ζ n n'
  unfold familyBudget flowerRootBudget flowerLExponent at *
  refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ hroot) ?_ (by positivity) (by unfold jbr; positivity)
  · refine Real.rpow_le_rpow_of_exponent_le hL ?_
    have : (0 : ℝ) ≤ (((40 * P.d) * (2 * Pm) : ℕ) : ℝ) + ((2 * Pm : ℕ) : ℝ) + (Pm : ℝ) := by positivity
    linarith
  · refine Real.rpow_le_rpow_of_exponent_ge hδ hδ1 ?_
    have : (0 : ℝ) ≤ P.ν * N := by positivity
    nlinarith

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Cases
open scoped Classical
open Set Induct WaveTurbulence.FC23 WaveTurbulence.Flower.FamilyW WaveTurbulence.FlowerTop LGSpine

theorem cut1_clause_of_filtLow (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d)
    (hU : ∀ P p, 0 < U P p) {Pm : ℕ} {P : WTParams} (hF : FlowerFiltFamilyAtLow C U Pm P)
    (hnum : NumericsAll C U Pm P) : FlowerCaseAtLow CaseCut1 Pm P := by
  intro hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc _
  obtain ⟨hs1, rfl⟩ := hc
  obtain ⟨j, rfl⟩ := Option.isSome_iff_exists.mp hs1
  have hn := hnum p hp N hN
  have hδ : 0 < P.δ := hn.2.2.1
  have hL1 : 1 ≤ P.L := by linarith [hn.2.2.2.2.1]
  have hb := filt_cut1Low C U hC hU hF hn hγ hp R hR t ht s hs n n' ζ hN kind pat dagger j
    (fun _ => none) (fun h => absurd h (by simp))
  have key : flowerSumP P (inputsF P R) p N kind pat dagger (some j) none ζ t s n n' =
      flowerWeighted P (inputsF P R) p N kind pat dagger
        (fun LG k => stemFilter LG P.L (fun _ => none) k * LG.cutWeight1P p P.L j k) ζ t s n n' := by
    rw [flowerSumP_eq_weighted]
    exact flowerWeighted_congr_weight P _ p N kind pat dagger ζ t s n n' fun LG k => by
      simp [stemFilter_none]
  unfold FlowerBoundAt
  rw [key]
  simp only [Option.elim, mul_one]
  rw [Sw_eq] at hb
  have hroot := rootBudget_nonneg Pm P p ζ n n'
  unfold flowerRootBudget flowerLExponent at hb
  unfold flowerRootBudget at hroot
  refine hb.trans ?_
  exact mul4_le hroot (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [(Nat.cast_nonneg Pm : (0 : ℝ) ≤ Pm)]))
    (Real.rpow_nonneg hδ.le _) (Real.rpow_nonneg (by positivity) _)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Cases
open scoped Classical
open Set Induct WaveTurbulence.FC23 WaveTurbulence.Flower.FamilyW WaveTurbulence.FlowerTop LGSpine

theorem cut2zero_clause_of_filtLow (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d)
    (hU : ∀ P p, 0 < U P p) {Pm : ℕ} {P : WTParams} (hF : FlowerFiltFamilyAtLow C U Pm P)
    (hnum : NumericsAll C U Pm P) : FlowerCaseAtLow CaseCut2Zero Pm P := by
  intro hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hcut
  subst hc
  obtain ⟨j₁, hm, hj₁⟩ := hcut 0 rfl
  have hm' : cut1 = some j₁ := Option.mem_def.mp hm
  subst hm'
  have hn := hnum p hp N hN
  have hδ : 0 < P.δ := hn.2.2.1
  have hL1 : 1 ≤ P.L := by linarith [hn.2.2.2.2.1]
  have hb := filt_cut1Low C U hC hU hF hn hγ hp R hR t ht s hs n n' ζ hN kind pat dagger j₁
    (fun _ => some 0) (fun _ => hj₁)
  have key : flowerSumP P (inputsF P R) p N kind pat dagger (some j₁) (some 0) ζ t s n n' =
      flowerWeighted P (inputsF P R) p N kind pat dagger
        (fun LG k => stemFilter LG P.L (fun _ => some 0) k * LG.cutWeight1P p P.L j₁ k) ζ t s n n' := by
    rw [flowerSumP_eq_weighted]
    exact flowerWeighted_congr_weight P _ p N kind pat dagger ζ t s n n' fun LG k => by
      simp only [Option.elim, cutWeight2P_zero]
      ring
  unfold FlowerBoundAt
  rw [key]
  simp only [Option.elim]
  rw [Sw_eq] at hb
  have hroot := rootBudget_nonneg Pm P p ζ n n'
  unfold flowerRootBudget flowerLExponent at hb
  unfold flowerRootBudget at hroot
  have hPm : (0 : ℝ) ≤ Pm := Nat.cast_nonneg Pm
  have hD : 0 ≤ P.δ ^ (2 * P.ν * N) := Real.rpow_nonneg hδ.le _
  have hM : 0 ≤ ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ)) := Real.rpow_nonneg (by positivity) _
  by_cases hpl : ∀ j, pat j = .plain
  · simp only [if_pos hpl] at hb ⊢
    have hB : P.L ^ ((1 : ℝ) * (100 * P.d : ℝ) ^ 3 * Pm - Pm) ≤
        P.L ^ ((1 : ℝ) * (100 * P.d : ℝ) ^ 3 * Pm) * ((2 : ℝ) ^ 0 * P.L) ^ (-(Pm / 9 : ℝ)) := by
      simp only [pow_zero, one_mul]
      rw [← Real.rpow_add (by linarith : (0 : ℝ) < P.L)]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    exact hb.trans ((mul4_le hroot hB hD hM).trans (le_of_eq (by ring)))
  · simp only [if_neg hpl, mul_one] at hb ⊢
    have hB : P.L ^ ((2 : ℝ) * (100 * P.d : ℝ) ^ 3 * Pm - Pm) ≤
        P.L ^ ((2 : ℝ) * (100 * P.d : ℝ) ^ 3 * Pm) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    exact hb.trans (mul4_le hroot hB hD hM)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Cases
open scoped Classical
open Set Induct WaveTurbulence.FC23 WaveTurbulence.Flower.FamilyW WaveTurbulence.FlowerTop LGSpine

theorem cut2pos_plain_of_gainLow (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d)
    (hU : ∀ P p, 0 < U P p) {Pm : ℕ} {P : WTParams} (hG : FlowerGainFamilyAtLow C U Pm P)
    (hnum : NumericsAll C U Pm P) : FlowerCasePatAtLow CaseCut2Pos PatPlain Pm P := by
  intro hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hpat hcut
  obtain ⟨j₂, rfl, hj₂⟩ := hc
  obtain ⟨j₁, hm, hj₁⟩ := hcut j₂ rfl
  have hm' : cut1 = some j₁ := Option.mem_def.mp hm
  subst hm'
  have hpat' : pat = fun _ => FixPat.plain := funext hpat
  subst hpat'
  have hn := hnum p hp N hN
  have hδ : 0 < P.δ := hn.2.2.1
  have hL1 : 1 ≤ P.L := by linarith [hn.2.2.2.2.1]
  have hb := gain_cut1Low C U hC hU hG hn hγ hp R hR t ht s hs n n' ζ hN kind dagger j₁ j₂ hj₂ hj₁
  have key : flowerSumP P (inputsF P R) p N kind (fun _ => .plain) dagger (some j₁) (some j₂) ζ t s n n' =
      flowerWeighted P (inputsF P R) p N kind (fun _ => .plain) dagger
        (fun LG k => LG.cutWeight2P P.L j₂ k * LG.cutWeight1P p P.L j₁ k) ζ t s n n' := by
    rw [flowerSumP_eq_weighted]
    exact flowerWeighted_congr_weight P _ p N kind _ dagger ζ t s n n' fun LG k => by
      simp only [Option.elim]
      ring
  unfold FlowerBoundAt
  rw [key]
  have hpl : ∀ j : Fin (2 * Pm), ((fun _ => FixPat.plain : Fin (2 * Pm) → FixPat) j = .plain) :=
    fun _ => rfl
  simp only [Option.elim, hpl, implies_true, ite_true]
  rw [Sw_eq] at hb
  unfold flowerRootBudget flowerLExponent at hb
  simp only [hpl, implies_true, ite_true] at hb
  refine hb.trans (le_of_eq ?_)
  ring

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Cases
open scoped Classical
open Set Induct WaveTurbulence.FC23 WaveTurbulence.Flower.FamilyW WaveTurbulence.FlowerTop LGSpine

theorem cut2pos_nonplain_of_filtLow (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d)
    (hU : ∀ P p, 0 < U P p) {Pm : ℕ} {P : WTParams} (hF : FlowerFiltFamilyAtLow C U Pm P)
    (hnum : NumericsAll C U Pm P) : FlowerCasePatAtLow CaseCut2Pos PatNonplain Pm P := by
  intro hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hpat hcut
  obtain ⟨j₂, rfl, hj₂⟩ := hc
  obtain ⟨j₁, hm, hj₁⟩ := hcut j₂ rfl
  have hm' : cut1 = some j₁ := Option.mem_def.mp hm
  subst hm'
  have hn := hnum p hp N hN
  have hδ : 0 < P.δ := hn.2.2.1
  have hL4 : 4 ≤ P.L := hn.2.2.2.2.1
  have hL1 : 1 ≤ P.L := by linarith
  have hd : 1 ≤ P.d := hn.1
  have hsum := summable_clipped_inputs P R p hp.le hd hL1 hR
  have hterm : ∀ ε : Fin (2 * Pm) → Bool,
      ‖flowerWeighted P (inputsF P (clipRemainder p R)) p N kind pat dagger
        (fun LG k => stemFilter LG P.L (fun i => some (if ε i then j₂ - 1 else j₂)) k *
          LG.cutWeight1P p P.L j₁ k) ζ t s n n'‖ ≤
      flowerRootBudget Pm P p ζ n n' * P.L ^ (flowerLExponent Pm P pat - (Pm : ℝ)) *
        P.δ ^ (2 * P.ν * N) * (2 ^ j₁ * P.L) ^ (-((((40 * P.d) * (2 * Pm) : ℕ) : ℝ))) := fun ε => by
    rw [flowerWeighted_clip]
    exact filt_cut1Low C U hC hU hF hn hγ hp R hR t ht s hs n n' ζ hN kind pat dagger j₁
      (fun i => some (if ε i then j₂ - 1 else j₂)) (fun _ => hj₁)
  have key : flowerSumP P (inputsF P R) p N kind pat dagger (some j₁) (some j₂) ζ t s n n' =
      ∑ ε : Fin (2 * Pm) → Bool, ((∏ i, if ε i then (-1 : ℝ) else 1 : ℝ) : ℂ) *
        flowerWeighted P (inputsF P (clipRemainder p R)) p N kind pat dagger
          (fun LG k => stemFilter LG P.L (fun i => some (if ε i then j₂ - 1 else j₂)) k *
            LG.cutWeight1P p P.L j₁ k) ζ t s n n' := by
    have hlin := flowerWeighted_finset_sum P (inputsF P (clipRemainder p R)) p N kind pat dagger ζ t s n n'
      (Finset.univ : Finset (Fin (2 * Pm) → Bool))
      (fun ε : Fin (2 * Pm) → Bool => ∏ i, if ε i then (-1 : ℝ) else 1)
      (fun (ε : Fin (2 * Pm) → Bool) LG k =>
        stemFilter LG P.L (fun i => some (if ε i then j₂ - 1 else j₂)) k * LG.cutWeight1P p P.L j₁ k)
      (fun ε LG k => by
        rw [abs_mul]
        exact mul_le_one₀ (stemFilter_abs_le_one _ _ _ _) (abs_nonneg _) (cutWeight1P_abs_le_one _ _ _ _ _))
      hsum
    rw [← hlin, flowerWeighted_clip, flowerSumP_eq_weighted]
    exact flowerWeighted_congr_weight P _ p N kind pat dagger ζ t s n n' fun LG k => by
      simp only [Option.elim]
      rw [cutWeight2P_expand LG P.L j₂ k hj₂, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ε _ => by ring
  have hc1 : ∀ ε : Fin (2 * Pm) → Bool, ‖((∏ i, if ε i then (-1 : ℝ) else 1 : ℝ) : ℂ)‖ = 1 := by
    intro ε
    rw [Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
    exact Finset.prod_eq_one fun i _ => by split_ifs <;> simp
  unfold FlowerBoundAt
  rw [key]
  have hpl : ¬ ∀ j, pat j = .plain := hpat
  simp only [Option.elim, if_neg hpl, mul_one]
  rw [Sw_eq] at hterm
  have hroot := rootBudget_nonneg Pm P p ζ n n'
  unfold flowerRootBudget flowerLExponent at hterm
  unfold flowerRootBudget at hroot
  simp only [if_neg hpl] at hterm
  have hD : 0 ≤ P.δ ^ (2 * P.ν * N) := Real.rpow_nonneg hδ.le _
  have hM : 0 ≤ ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ)) := Real.rpow_nonneg (by positivity) _
  refine (sum_norm_bound _ _ hc1 _ hterm).trans ?_
  have hcard : ((Fintype.card (Fin (2 * Pm) → Bool) : ℕ) : ℝ) = (2 : ℝ) ^ (2 * Pm) := by simp
  rw [hcard]
  rw [show ∀ r B D M : ℝ, (2 : ℝ) ^ (2 * Pm) * (r * B * D * M) = r * ((2 : ℝ) ^ (2 * Pm) * B) * D * M from
    fun _ _ _ _ => by ring]
  exact mul4_le hroot (two_pow_mul_rpow_le P.L hL4 _ Pm) hD hM

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Cases
open scoped Classical
open Set Filter Induct WaveTurbulence.FC23 WaveTurbulence.Flower.FamilyW WaveTurbulence.FlowerTop LGSpine

/-- **`layergardenFlower_v3` from the two core families** (PLAN §1.4). -/
theorem flower_low_of_families (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ)
    (hC : ∀ d, 0 < C d) (hU : ∀ P p, 0 < U P p)
    (hFilt : WTPrefixP (FlowerFiltFamilyAtLow C U))
    (hGain : WTPrefixP (FlowerGainFamilyAtLow C U)) (hCouple : CoupleClauseLowInput) : LayergardenFlowerLowGate := by
  have hF := prefix_with_numerics C U hC hU hFilt
  have hG := prefix_with_numerics C U hC hU hGain
  have hPlain : WTPrefixP (FlowerCaseAtLow CasePlain) :=
    prefixP_map hF fun _ _ h => casePlain_of_filtLow C U hC hU h.1 h.2
  have hCut1 : WTPrefixP (FlowerCaseAtLow CaseCut1) :=
    prefixP_map hF fun _ _ h => cut1_clause_of_filtLow C U hC hU h.1 h.2
  have hCut2Zero : WTPrefixP (FlowerCaseAtLow CaseCut2Zero) :=
    prefixP_map hF fun _ _ h => cut2zero_clause_of_filtLow C U hC hU h.1 h.2
  have hNon : WTPrefixP (FlowerCasePatAtLow CaseCut2Pos PatNonplain) :=
    prefixP_map hF fun _ _ h => cut2pos_nonplain_of_filtLow C U hC hU h.1 h.2
  have hPl : WTPrefixP (FlowerCasePatAtLow CaseCut2Pos PatPlain) :=
    prefixP_map hG fun _ _ h => cut2pos_plain_of_gainLow C U hC hU h.1 h.2
  have hCut2 : WTPrefixP (FlowerCaseAtLow CaseCut2Pos) :=
    prefixP_map (prefixP_and hPl hNon
      (fun Pm => flowerCasePatAt_largeConstantMonotoneLow _ _ Pm)
      (fun Pm => flowerCasePatAt_largeConstantMonotoneLow _ _ Pm))
      fun _ _ h => caseAt_of_pat_splitLow h.1 h.2
  exact flower_low_of_inputs hPlain hCut1 hCut2 hCut2Zero
    (prefixP_map (prefixP_lift hCouple) fun _ _ h => h)

end

end WaveTurbulence.GammaLow.Flower
