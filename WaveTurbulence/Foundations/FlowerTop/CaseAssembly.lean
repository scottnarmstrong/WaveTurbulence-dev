/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FC23.Cut1PrefixInterface
public import WaveTurbulence.Foundations.Spine.PrefixConjunction
public import WaveTurbulence.Foundations.Spine.SourceLargeConstantBounds

/-! Case split of the frozen v3 flower clause by the cutoff indices (main world, frozen definitions).
Each case is a distinctly named clause; `FlowerCaseAt top` is the frozen flower half. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop
open LGSpine Set

theorem flowerSumP_largeConstants (P : WTParams) (c₁ c₂ : ℝ) (R : ℕ → Mom P.d → ℝ) (p N : ℕ)
    {w : ℕ} (kind : FlowerKind) (pat : Fin w → FixPat)
    (dagger : Option (Fin w → Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ) (ζ : ℤˣ) (t s : ℝ)
    (n n' : Fin P.d → ℤ) :
    flowerSumP ({P with C₁ := c₁, C₂ := c₂} : WTParams) (inputsF P R) p N kind pat dagger cut1 cut2 ζ t s n n' =
      flowerSumP P (inputsF P R) p N kind pat dagger cut1 cut2 ζ t s n n' := by
  simp only [flowerSumP, N_largeConstants]

/-- The frozen flower-half conclusion, as a bound on one `flowerSumP`. -/
def FlowerBoundAt (P : WTParams) (R : ℕ → Mom P.d → ℝ) (p N Pm : ℕ) (kind : FlowerKind)
    (pat : Fin (2 * Pm) → FixPat) (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d))
    (cut1 cut2 : Option ℕ) (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) : Prop :=
  ‖flowerSumP P (inputsF P R) p N kind pat dagger cut1 cut2 ζ t s n n'‖ ≤
    jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^
        (-(4 * P.Lambda (p + 1) * Pm : ℝ)) *
      P.L ^ ((if ∀ j, pat j = .plain then 1 else 2) * (100 * P.d : ℝ) ^ 3 * Pm) *
      P.δ ^ (2 * P.ν * N) *
      (cut1.elim 1 fun j₁ => ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ))) *
      (cut2.elim 1 fun j₂ =>
        if ∀ j, pat j = .plain then ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ)) else 1)

/-- The flower half of frozen v3, restricted to the cutoff indices selected by `case`. -/
def FlowerCaseAt (case : Option ℕ → Option ℕ → Prop) (Pm : ℕ) (P : WTParams) : Prop :=
  1 / 2 < P.γ → ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
    ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
      (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ),
      case cut1 cut2 →
      (∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) →
      FlowerBoundAt P R p N Pm kind pat dagger cut1 cut2 ζ t s n n'

/-- Case: no cutoff. -/
def CasePlain (c1 c2 : Option ℕ) : Prop := c1 = none ∧ c2 = none
/-- Case: cut1 present, cut2 absent. -/
def CaseCut1 (c1 c2 : Option ℕ) : Prop := c1.isSome ∧ c2 = none
/-- Case: cut2 present with positive index. -/
def CaseCut2Pos (_c1 c2 : Option ℕ) : Prop := ∃ j, c2 = some j ∧ 0 < j
/-- Case: cut2 present with index zero. -/
def CaseCut2Zero (_c1 c2 : Option ℕ) : Prop := c2 = some 0

/-- The four cases together are the frozen flower half. -/
theorem flowerCase_top {Pm : ℕ} {P : WTParams}
    (h0 : FlowerCaseAt CasePlain Pm P) (h1 : FlowerCaseAt CaseCut1 Pm P)
    (h2 : FlowerCaseAt CaseCut2Pos Pm P) (h3 : FlowerCaseAt CaseCut2Zero Pm P) :
    FlowerCaseAt (fun _ _ => True) Pm P := by
  intro hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 _ hcut
  rcases cut2 with _ | j
  · rcases cut1 with _ | j₁
    · exact h0 hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger none none ⟨rfl, rfl⟩ hcut
    · exact h1 hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger (some j₁) none ⟨rfl, rfl⟩ hcut
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact h3 hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 (some 0) rfl hcut
    · exact h2 hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 (some j) ⟨j, rfl, hj⟩ hcut

theorem flowerCase_largeConstantMonotone (case : Option ℕ → Option ℕ → Prop) (Pm : ℕ) :
    LargeConstantMonotone (FlowerCaseAt case Pm) := by
  intro P c₁ c₂ _ _ _ _ _ _ h hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hcut
  rw [N_largeConstants] at hN
  have H := h hγ p hp R hR t ht s hs n n' ζ N hN kind pat dagger cut1 cut2 hc hcut
  have hF : inputsF {P with C₁ := c₁, C₂ := c₂} R = inputsF P R := rfl
  unfold FlowerBoundAt at H ⊢
  rw [hF, flowerSumP_largeConstants]
  simpa only [N_largeConstants, WTParams.Lambda] using H

end WaveTurbulence.FlowerTop
