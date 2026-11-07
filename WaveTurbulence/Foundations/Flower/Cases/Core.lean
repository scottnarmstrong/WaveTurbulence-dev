/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Cases.ScaleAt
public import WaveTurbulence.Foundations.Flower.Cases.Shell
public import WaveTurbulence.Foundations.Flower.Cases.Linear
public import WaveTurbulence.Foundations.Flower.FamilyW.Plain
public import WaveTurbulence.Foundations.FlowerTop.PlainOfFamily
/-! # Fixed-parameter consequences of the two family inputs: cut1 bounds with an extra weight. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Cases
open Set Induct WaveTurbulence.FC23 WaveTurbulence.Flower.FamilyW

/-- The numerical side conditions at fixed `(P, p, N)`. -/
def Numerics (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (Pm : ℕ) (P : WTParams) (p N : ℕ) : Prop :=
  1 ≤ P.d ∧ 0 < P.ν ∧ 0 < P.δ ∧ P.δ ≤ 1 ∧ 4 ≤ P.L ∧
  (4 * Real.exp 1) ^ (2 * (2 * Pm)) * P.δ ^ (2 * P.ν) ≤ 1 ∧
  4 * ((2 * N + 1 : ℕ) : ℝ) ≤ P.L ∧
  C P.d * ((2 * N + 1 : ℕ) : ℝ) * U {P with L := 1} p *
    (4 * ((2 * N + 1 : ℕ) : ℝ)) ^ (40 * P.d) ≤ P.L ^ (40 * P.d) ∧
  3 * (4 * Real.exp 1) * 4 ^ (40 * P.d) * C P.d * U {P with L := 1} p *
    ((2 * N + 1 : ℕ) : ℝ) ^ (40 * P.d + 2) ≤ P.L

/-- Clipped cut1 scale bound for a `W`-weighted family, at one cut1 index. -/
theorem cut1W_flower (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d) (hU : ∀ P p, 0 < U P p)
    {Pm : ℕ} {P : WTParams} {p N : ℕ} (hnum : Numerics C U Pm P p N)
    (hpd : p ≤ P.D) (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p)
    (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
    (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ)
    (W : ∀ LG : LayeredGarden (2 * Pm), (GNode LG.garden.tree → Mom P.d) → ℝ)
    (hW : ∀ LG k, |W LG k| ≤ 1) (J b : ℝ) (hJ : 0 ≤ J) (j : ℕ)
    (H : UniformFlowerFamilyW P (inputsF P R) p N kind pat dagger ζ t s n n' W
      (2 ^ j * P.L) ((2 ^ j * P.L) / (4 * (2 * N + 1 : ℕ)))
      (fun _ => extractionRadius (40 * P.d) N (C P.d) (U {P with L := 1} p) (2 ^ j * P.L))
      (J * P.L ^ (b - ((40 * P.d) * (2 * Pm) : ℕ) - ((2 * Pm : ℕ) : ℝ)) *
        P.δ ^ ((2 + 2) * P.ν * N))) :
    ‖flowerWeighted P (inputsF P R) p N kind pat dagger
        (fun LG k => W LG k * LG.cutWeight1P p P.L j k) ζ t s n n'‖ ≤
      J * P.L ^ b * P.δ ^ (2 * P.ν * N) * (2 ^ j * P.L) ^ (-((((40 * P.d) * (2 * Pm) : ℕ) : ℝ))) := by
  obtain ⟨hd, hν, hδ, hδ1, hL4, hsmall, hA, hρ, hcost⟩ := hnum
  have hL1 : 1 ≤ P.L := by linarith
  have hsum := summable_clipped_inputs P R p hpd hd hL1 hR
  have H' : UniformFlowerFamilyW P (inputsF P (clipRemainder p R)) p N kind pat dagger ζ t s n n' W
      (2 ^ j * P.L) ((2 ^ j * P.L) / (4 * (2 * N + 1 : ℕ)))
      (fun _ => extractionRadius (40 * P.d) N (C P.d) (U {P with L := 1} p) (2 ^ j * P.L))
      (J * P.L ^ (b - ((40 * P.d) * (2 * Pm) : ℕ) - ((2 * Pm : ℕ) : ℝ)) *
        P.δ ^ ((2 + 2) * P.ν * N)) := by
    intro tail small z hz
    rw [flowerWeighted_clip]
    exact H tail small z hz
  have := cut1_scale_bound_W_at P (inputsF P (clipRemainder p R)) p N kind pat dagger ζ t s n n' W
    (40 * P.d) (C P.d) (U {P with L := 1} p) J b 2 (hC _) (hU _ _) hL1 hδ hδ1 hν.le hJ
    (by norm_num) hsmall hA hρ hcost hsum hW j H'
  rwa [flowerWeighted_clip] at this

/-- The filtered family at a fixed parameter set gives the cut1 bound with the stem filter. -/
theorem filt_cut1 (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d) (hU : ∀ P p, 0 < U P p)
    {Pm : ℕ} {P : WTParams} (hF : FlowerFiltFamilyAt C U Pm P)
    {p N : ℕ} (hnum : Numerics C U Pm P p N) (hγ : 1 / 2 < P.γ) (hp : p < P.D)
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

/-- The gain family at a fixed parameter set (plain patterns, positive shell). -/
theorem gain_cut1 (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (hC : ∀ d, 0 < C d) (hU : ∀ P p, 0 < U P p)
    {Pm : ℕ} {P : WTParams} (hG : FlowerGainFamilyAt C U Pm P)
    {p N : ℕ} (hnum : Numerics C U Pm P p N) (hγ : 1 / 2 < P.γ) (hp : p < P.D)
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

end WaveTurbulence.Flower.Cases
