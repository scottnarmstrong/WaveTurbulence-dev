/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentObjects
public import WaveTurbulence.Foundations.Spine.AnchorTypes
/-! Source-level coherent approximation data and the assertions of TARGET Props 6.1–6.2.
These are proposition definitions, not proved source theorems or substitutes for layergarden.
The same approximation family must be used in the approximation and Taylor comparison assertions. -/
@[expose] public section
open WaveTurbulence.Induct
namespace WaveTurbulence.LGSpine
open Set
open scoped ENNReal Classical

/-- The two approximation functions in TARGET (layerregest2), L1099.
There are no analytic conclusions in this data structure. -/
structure CoherentAppData (d : ℕ) where
  couple : ℕ → ℕ → LayeredGarden 2 → (Fin 2 → ℝ) → Mom d → ℂ
  tree : ℕ → ℕ → LayeredGarden 1 → (Fin 2 → ℝ) → Mom d → ℂ

/-- TARGET L1103–1110, (layerregest4–6): at most 2^n separated terms, with the stated
one-time-factor norm and spatial-factor norm. The weight is 30d for couples and 0 for trees. -/
def HasCoherentSeparation (P : WTParams) (n W : ℕ) (B : Set (Fin 2 → ℝ))
    (f : (Fin 2 → ℝ) → Mom P.d → ℂ) : Prop :=
  ∃ (m : ℕ) (J : Fin m → (Fin 2 → ℝ) → ℂ) (M : Fin m → Mom P.d → ℂ),
    m ≤ 2 ^ n ∧
    (∀ ts ∈ B, ∀ k, f ts k = ∑ i, (P.δ ^ n : ℂ) * J i ts * M i k) ∧
    (∀ i, XNorm00Restr (V := Unit) (1 - P.η) B Set.univ (fun ts _ => J i ts) ≤
      ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) ∧
    ∀ i, SNorm (30 * P.d) W (M i) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n)

/-- TARGET Prop 6.1, L1097–1111. As in the literal B2.1/B2.2 anchors, the two remainder
norms in (layerregest3) are recorded separately with the common implicit constant C1.
Eligibility retains the ambient canonical embedding required at L951. -/
def CoherentApproximationBounds (P : WTParams) (p : ℕ) (R : ℕ → Mom P.d → ℝ)
    (A : CoherentAppData P.d) : Prop :=
  ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
    (∀ (Q : RegCpl) (LG : LayeredGarden 2) (q q' : ℕ),
      q' ≤ q → q ≤ p → Q.size = 2 * n → IsCoherentCoupleAt p q q' Q LG →
      (XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
        (fun ts k => KQstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k -
          A.couple q q' LG ts k) ≤ regBound P n 1) ∧
      (Q.dominant = false → ∀ ts ∈ timeBox q q', ∀ k, A.couple q q' LG ts k = 0) ∧
      HasCoherentSeparation P n (30 * P.d) (timeBox q q') (A.couple q q' LG)) ∧
    (∀ (X : RegChain) (LG : LayeredGarden 1) (q q' : ℕ),
      q' ≤ q → q ≤ p → X.size = 2 * n → IsCoherentTreeAt p q q' X LG →
      (XNormRestr P.η (30 * P.d) 0 (timeBoxGt q q') Set.univ
        (fun ts k => KTstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k -
          A.tree q q' LG ts k) ≤ regBound P n 1) ∧
      (X.dominant = false → ∀ ts ∈ timeBoxGt q q', ∀ k, A.tree q q' LG ts k = 0) ∧
      HasCoherentSeparation P n 0 (timeBoxGt q q') (A.tree q q' LG))

/-- TARGET Prop 6.2, L1112–1117, (layerregest7–8). The sum is the full regular-couple sum;
there is deliberately no top-tree truncation predicate in this source assertion. -/
def CoherentTaylorComparison (P : WTParams) (p : ℕ) (A : CoherentAppData P.d) : Prop :=
  ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k : Mom P.d,
    ‖(∑ᶠ (LG : LayeredGarden 2)
        (_ : IsRegularCouple LG.garden ∧ LG.garden.order = 2 * n ∧ ∀ a, LG.layer a = p),
        A.couple p p LG ![t, t] k) -
      (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)‖ ≤
      P.C₁ * (P.C₁ * P.δ) ^ n * jbr k ^ (-(30 * P.d : ℝ)) *
        P.L ^ (-(P.theta (p + 1) + 4 * P.theta p) / 5)

end WaveTurbulence.LGSpine
