/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.AnchorTypes
public import WaveTurbulence.Foundations.Spine.ExplicitCoherentApps
public import WaveTurbulence.Foundations.Spine.SourceSeparation
public import WaveTurbulence.Foundations.Spine.CoherentConjugacyData
/-! Exported literal source interfaces for LG-SPINE consumers and producer packets.
No theorem is assumed here, and no arbitrary approximation functions occur in these input types.
The full minimal conjunction is added only after every source interface is stated. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Finset
open scoped ENNReal Classical

/-- TARGET Prop 6.1, L1097–1111, with explicit products (prooflayer1-1–2), L1241–1246,
and the B2 single-layer functions (regref1-3), L1156–1160. The eligible objects are precisely
coherent regular objects embedded in a canonical garden, as required at L951 and layerreg1.
All approximation functions below are the fixed definitions SourceApp.couple / SourceApp.tree.
R33 F-DERIV (supersedes the 2026-11-04 order-zero correction; F80 fixed the measurability): the literal norm
`XNormRestr eta 30d 30d` (couples) / `XNormRestr eta 30d 0` (trees), as in layerregest3. -/
abbrev CoherentApproximationGate : Prop := WTPrefix fun P =>
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

/-- TARGET Prop 6.2, L1112–1117 (layerregest7–8), with the explicit uniform-layer approximation
(regref1-3), L1156–1160: RegCpl.app. The regular-couple sum uses its unique well-formed structure
code (TARGET propstructure; proved REG-STRUCT). Non-dominant app terms are zero by definition.
Standing input hypothesis: TARGET L951, with Lambda replaced by 40d, exactly as in B2.1/B2.2.
This is the exported L3 statement; it has no free approximation-family argument. -/
abbrev CoherentTaylorGate : Prop := WTPrefix fun P =>
  ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ,
    (∀ r ≤ p, InputRemainder P (R r) r) →
  ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k : Mom P.d,
    ‖(∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n),
        Q.app P.δ p (inputsF P R p) t t k) -
      (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)‖ ≤
      P.C₁ * (P.C₁ * P.δ) ^ n * jbr k ^ (-(30 * P.d : ℝ)) *
        P.L ^ (-(P.theta (p + 1) + 4 * P.theta p) / 5)

/-- TARGET Prop 6.3, L1118–1125 (layerregest9–10), with the same explicit source approximations
as Prop 6.1. The conjugate relation is exactly deftree/defgarden, with all layers preserved.
The Option-valued branching count combines the unrestricted and fixed-count conclusions. -/
abbrev CoherentRealityGate : Prop := WTPrefix fun P =>
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

end WaveTurbulence.LGSpine
