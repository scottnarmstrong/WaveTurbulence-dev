/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FamilyW.Family
public import WaveTurbulence.Foundations.FlowerTop.ThreeInputs
/-! # FL-CASES definitions: stem filters and the two core family statements (PLAN §1.4). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Cases
open Set WaveTurbulence.Flower.FamilyW

/-- Stem set of tree `j`: stem branching nodes other than the flower parent (as in `cutWeight2P`). -/
def stemSet {w : ℕ} (LG : LayeredGarden w) (j : Fin w) : Finset (GBranch LG.garden.tree) :=
  Finset.univ.filter fun b : GBranch LG.garden.tree =>
    b.1.1 = j ∧ LG.OnStem b.toNode ∧ ¬ LG.garden.IsFlowerParent b

/-- Per-tree low-pass stem-resonance filter at scale `2^{σ j} L` (`none`: no filter). -/
def stemFilter {w d : ℕ} (LG : LayeredGarden w) (L : ℝ) (σ : Fin w → Option ℕ)
    (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ j : Fin w, (σ j).elim 1 fun i =>
    prodDyadicCut (2 ^ i * L) 0 (stemSet LG j) (fun b => |omegaNode LG.garden k b|)

/-- The family budget: FC23 shape with explicit extra `L`-slack `e` and `δ^{4νN}`. -/
def familyBudget (Pm : ℕ) (P : WTParams) (p : ℕ) (ζ : ℤˣ) (n n' : Fin P.d → ℤ)
    (pat : Fin (2 * Pm) → FixPat) (N : ℕ) (e : ℝ) : ℝ :=
  FC23.flowerRootBudget Pm P p ζ n n' *
    P.L ^ (FC23.flowerLExponent Pm P pat - ((40 * P.d) * (2 * Pm) : ℕ) - (2 * Pm : ℕ) - e) *
    P.δ ^ (4 * P.ν * N)

/-- **Input 1 (filtered family).** -/
def FlowerFiltFamilyAt (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (Pm : ℕ) (P : WTParams) : Prop :=
  1 / 2 < P.γ → ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
    ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
      (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (j : ℕ) (σ : Fin (2 * Pm) → Option ℕ),
    ((∃ i, σ i ≠ none) → ((2 : ℝ) ^ j * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) →
    UniformFlowerFamilyW P (inputsF P R) p N kind pat dagger ζ t s n n'
      (fun LG k => stemFilter LG P.L σ k)
      (2 ^ j * P.L) ((2 ^ j * P.L) / (4 * (2 * N + 1 : ℕ)))
      (fun _ => FC23.extractionRadius (40 * P.d) N (C P.d) (U {P with L := 1} p) (2 ^ j * P.L))
      (familyBudget Pm P p ζ n n' pat N Pm)

/-- **Input 2 (gain family).** Plain patterns, positive cut2 shell, frozen `M₂` gain. -/
def FlowerGainFamilyAt (C : ℕ → ℝ) (U : WTParams → ℕ → ℝ) (Pm : ℕ) (P : WTParams) : Prop :=
  1 / 2 < P.γ → ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
    ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind)
      (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (j j₂ : ℕ), 0 < j₂ →
    ((2 : ℝ) ^ j * P.L) ^ 10 ≤ ‖latticePoint P.L n‖ →
    UniformFlowerFamilyW P (inputsF P R) p N kind (fun _ => .plain) dagger ζ t s n n'
      (fun LG k => LG.cutWeight2P P.L j₂ k)
      (2 ^ j * P.L) ((2 ^ j * P.L) / (4 * (2 * N + 1 : ℕ)))
      (fun _ => FC23.extractionRadius (40 * P.d) N (C P.d) (U {P with L := 1} p) (2 ^ j * P.L))
      (familyBudget Pm P p ζ n n' (fun _ => .plain) N 0 * ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ)))

end WaveTurbulence.Flower.Cases
