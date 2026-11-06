/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SpineInputs
/-! Literal fixed-parameter bodies of the exported L3+L4 gates. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Finset
open scoped ENNReal Classical

/-- Exact body of CoherentApproximationGate at P; no premise is changed. -/
abbrev SourceCoherentApproximationAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ,
    (∀ r ≤ p, InputRemainder P (R r) r) →
  ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
    (∀ (Q : RegCpl) (LG : LayeredGarden 2) (q q' : ℕ),
      q' ≤ q → q ≤ p → Q.size = 2 * n → IsCoherentCoupleAt p q q' Q LG →
      (XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
        (fun ts k => KQstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k -
          SourceApp.couple P.δ (inputsF P R) LG Q q q' (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      (Q.dominant = false → ∀ ts ∈ timeBox q q', ∀ k,
        SourceApp.couple P.δ (inputsF P R) LG Q q q' (ts 0) (ts 1) k = 0) ∧
      SourceSeparated P n (30 * P.d) (timeBox q q')
        (fun ts k => SourceApp.couple P.δ (inputsF P R) LG Q q q' (ts 0) (ts 1) k)) ∧
    (∀ (X : RegChain) (LG : LayeredGarden 1) (q q' : ℕ),
      q' ≤ q → q ≤ p → X.size = 2 * n → IsCoherentTreeAt p q q' X LG →
      (XNormRestr P.η (30 * P.d) 0 (timeBoxGt q q') Set.univ
        (fun ts k => KTstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k -
          SourceApp.tree P.δ (inputsF P R) LG X q q' (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      (X.dominant = false → ∀ ts ∈ timeBoxGt q q', ∀ k,
        SourceApp.tree P.δ (inputsF P R) LG X q q' (ts 0) (ts 1) k = 0) ∧
      SourceSeparated P n 0 (timeBoxGt q q')
        (fun ts k => SourceApp.tree P.δ (inputsF P R) LG X q q' (ts 0) (ts 1) k))

theorem SourceCoherentApproximationAt_gate_eq : CoherentApproximationGate = WTPrefix SourceCoherentApproximationAt := rfl

/-- Exact body of CoherentTaylorGate at P; no premise is changed. -/
abbrev SourceCoherentTaylorAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ,
    (∀ r ≤ p, InputRemainder P (R r) r) →
  ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k : Mom P.d,
    ‖(∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n),
        Q.app P.δ p (inputsF P R p) t t k) -
      (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)‖ ≤
      P.C₁ * (P.C₁ * P.δ) ^ n * jbr k ^ (-(30 * P.d : ℝ)) *
        P.L ^ (-(P.theta (p + 1) + 4 * P.theta p) / 5)

theorem SourceCoherentTaylorAt_gate_eq : CoherentTaylorGate = WTPrefix SourceCoherentTaylorAt := rfl

/-- Exact body of CoherentRealityGate at P; no premise is changed. -/
abbrev SourceCoherentRealityAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ,
    (∀ r ≤ p, InputRemainder P (R r) r) →
  ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
    (∀ (Q Qbar : RegCpl) (LG LGbar : LayeredGarden 2) (q q' : ℕ),
      q ≤ p → q' ≤ p → Q.size = 2 * n →
      IsCoherentCoupleAt p q q' Q LG → IsCoherentCoupleAt p q' q Qbar LGbar →
      IsConjugateCouple LG LGbar → ∀ ts ∈ timeBox q' q, ∀ k : Mom P.d,
        (KQstar P.L P.γ P.δ (inputsF P R) LGbar (ts 0) (ts 1) k =
          star (KQstar P.L P.γ P.δ (inputsF P R) LG (ts 1) (ts 0) k)) ∧
        SourceApp.couple P.δ (inputsF P R) LGbar Qbar q' q (ts 0) (ts 1) k =
          star (SourceApp.couple P.δ (inputsF P R) LG Q q q' (ts 1) (ts 0) k)) ∧
    (∀ (X Xbar : RegChain) (LG LGbar : LayeredGarden 1) (q q' : ℕ),
      q' ≤ q → q ≤ p → X.size = 2 * n →
      IsCoherentTreeAt p q q' X LG → IsCoherentTreeAt p q q' Xbar LGbar →
      IsConjugateTree LG LGbar → ∀ ts ∈ timeBoxGt q q', ∀ k : Mom P.d,
        (KTstar P.L P.γ P.δ (inputsF P R) LGbar (ts 0) (ts 1) k =
          star (KTstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k)) ∧
        SourceApp.tree P.δ (inputsF P R) LGbar Xbar q q' (ts 0) (ts 1) k =
          star (SourceApp.tree P.δ (inputsF P R) LG X q q' (ts 0) (ts 1) k)) ∧
    (∀ q q' : ℕ, q' ≤ q → q ≤ p → ∀ b : Option ℕ,
      ∀ ts ∈ timeBoxGt q q', ∀ k : Mom P.d,
        (∑ᶠ (Q : RegCpl) (X : RegChain) (LQ : LayeredGarden 2) (LX : LayeredGarden 1)
          (_ : CoherentPairCarrier p q q' n b Q X LQ LX),
          SourceApp.couple P.δ (inputsF P R) LQ Q q q' (ts 0) (ts 1) k *
            star (SourceApp.tree P.δ (inputsF P R) LX X q q' (ts 0) (ts 1) k)).im = 0)

theorem SourceCoherentRealityAt_gate_eq : CoherentRealityGate = WTPrefix SourceCoherentRealityAt := rfl

end WaveTurbulence.LGSpine
