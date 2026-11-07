/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Cases.Core
/-! # The five flower clauses at a fixed parameter set, from the two family inputs. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Cases
open Set Induct WaveTurbulence.FC23 WaveTurbulence.Flower.FamilyW WaveTurbulence.FlowerTop LGSpine

/-- `FlowerCaseAt` with an extra restriction on the pattern. -/
def FlowerCasePatAt (case : Option ℕ → Option ℕ → Prop)
    (patOK : ∀ {Pm : ℕ}, (Fin (2 * Pm) → FixPat) → Prop) (Pm : ℕ) (P : WTParams) : Prop :=
  1 / 2 < P.γ → ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
    ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
      (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ),
      case cut1 cut2 → patOK pat →
      (∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) →
      FlowerBoundAt P R p N Pm kind pat dagger cut1 cut2 ζ t s n n'

theorem flowerCasePatAt_largeConstantMonotone (case : Option ℕ → Option ℕ → Prop)
    (patOK : ∀ {Pm : ℕ}, (Fin (2 * Pm) → FixPat) → Prop) (Pm : ℕ) :
    LargeConstantMonotone (FlowerCasePatAt case patOK Pm) := by
  intro P c₁ c₂ _ _ _ _ _ _ h hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hpat hcut
  rw [N_largeConstants] at hN
  have H := h hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hpat hcut
  have hF : inputsF {P with C₁ := c₁, C₂ := c₂} R = inputsF P R := rfl
  unfold FlowerBoundAt at H ⊢
  rw [hF, flowerSumP_largeConstants]
  simpa only [N_largeConstants, WTParams.Lambda] using H

/-- Plain patterns / non-plain patterns. -/
def PatPlain {Pm : ℕ} (pat : Fin (2 * Pm) → FixPat) : Prop := ∀ j, pat j = .plain
def PatNonplain {Pm : ℕ} (pat : Fin (2 * Pm) → FixPat) : Prop := ¬ ∀ j, pat j = .plain

theorem caseAt_of_pat_split {case : Option ℕ → Option ℕ → Prop} {Pm : ℕ} {P : WTParams}
    (h1 : FlowerCasePatAt case PatPlain Pm P) (h2 : FlowerCasePatAt case PatNonplain Pm P) :
    FlowerCaseAt case Pm P := by
  intro hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hcut
  by_cases hpl : ∀ j, pat j = .plain
  · exact h1 hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hpl hcut
  · exact h2 hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hpl hcut

theorem flowerWeighted_congr_weight (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ)
    {w₁ w₂ : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ}
    (h : ∀ LG k, w₁ LG k = w₂ LG k) :
    flowerWeighted P F p N kind pat dagger w₁ ζ t s n n' =
      flowerWeighted P F p N kind pat dagger w₂ ζ t s n n' := by
  have : w₁ = w₂ := funext fun LG => funext fun k => h LG k
  rw [this]

theorem flowerSumP_eq_weighted (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (cut1 cut2 : Option ℕ) (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) :
    flowerSumP P F p N kind pat dagger cut1 cut2 ζ t s n n' =
      flowerWeighted P F p N kind pat dagger
        (fun LG k => (cut1.elim 1 fun j₁ => LG.cutWeight1P p P.L j₁ k) *
          (cut2.elim 1 fun j₂ => LG.cutWeight2P P.L j₂ k)) ζ t s n n' := rfl

theorem rootBudget_nonneg (Pm : ℕ) (P : WTParams) (p : ℕ) (ζ : ℤˣ) (n n' : Fin P.d → ℤ) :
    0 ≤ flowerRootBudget Pm P p ζ n n' := by
  unfold flowerRootBudget
  exact Real.rpow_nonneg (by unfold jbr; positivity) _

theorem Sw_eq (P : WTParams) (Pm : ℕ) :
    (((40 * P.d) * (2 * Pm) : ℕ) : ℝ) = 80 * P.d * Pm := by push_cast; ring

/-- Fixed-parameter numerics at every admissible `(p, N)`. -/
def NumericsAll (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (Pm : ℕ) (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ N, N ≤ P.N (p + 1) ^ 4 → Numerics C U Pm P p N

/-- Plain clause from the filtered family at `σ ≡ none`, by letting the scale tend to infinity. -/
theorem casePlain_of_filt (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d)
    (hU : ∀ P p, 0 < U P p) {Pm : ℕ} {P : WTParams} (hF : FlowerFiltFamilyAt C U Pm P)
    (hnum : NumericsAll C U Pm P) :
    FlowerCaseAt CasePlain Pm P := by
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

end WaveTurbulence.Flower.Cases
