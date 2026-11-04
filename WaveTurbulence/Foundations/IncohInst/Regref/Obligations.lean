/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB2
public import WaveTurbulence.Foundations.Fourier.MixedNorm

/-!
# RA2 REGREF: the named obligations from RA1 (DH23 Prop 6.1)

TARGET's proof of Props `regref1`–`regref3` (L1171–L1173) cites DH23 Prop 6.1 (single layer `0`, times in `[0,1]`)
and then makes two remarks: the kernels are invariant under translating all times by `r`, and the inputs
`F_r = φ(δr) + R_r` are real and bounded in a regularity class "more than enough" for DH23's proof. Packet RA1
(wt-ansob) proves DH23 Prop 6.1 on the Wave B objects; it has not yet published a source-level statement. Until it
lands, RA2 takes it as the named obligations below, stated **in layer `0`** (DH23's setting) with the inputs
quantified by an explicit `𝔖^{40d,40d}` bound and every constant in the order of TARGET's parameter prefix:

* `RA1Couple`: DH23 Prop 6.1 for regular couples. For every well-formed code `𝒬` of order `2n ≤ 2(log L)^A` and
  every layered couple decoded by it with all nodes in layer `0`:
  `‖K*_𝒬 − (K*_𝒬)_app‖_{𝔛^{η,30d,30d}([0,1]²)} ≤ C(Cδ)^n L^{-(γ₁−√η)}` (DH23 (remainderbd): `(C⁺δ)^n L^{-γ₁+2η}`,
  and `2η ≤ √η` for `η ≤ 1/4`); for dominant codes the factor bounds of DH23 (kqtermsest),
  `‖𝒥ℬ*_𝒬‖_{𝔛^{1−η}([0,1]²)} ≤ C·C^n` and `‖ℳ*_{(𝒬,Z)}‖_{𝔖^{30d,30d}} ≤ C·C^n`.
* `RA1Tree`: the same for regular trees of either sign (lone leaf in layer `0`, box `{0 ≤ s < t ≤ 1}`), with
  `𝔛^{η,30d,0}` and `𝔖^{30d,0}`. The remainder bound is stated in the **landed** TARGET (normX) restriction norm
  `Fourier.mixedRestrictionNorm` (WAVE-B §2.6: smoothness of `k ↦ F̂(λ, k)` for almost every `λ`), which bounds B2's
  `XNormRestr` (`XNormRestr_le_mixedRestrictionNorm`). Reason: the `q' < r` case of B2.1 item (2) needs a trace
  estimate, which differentiates under the frequency integral; B2's guard (integrand `⊤` off the smooth
  frequencies) only controls the non-smooth frequencies in inner measure, the landed guard in measure.

`(K*)_app` is B2's leading term (`RegCpl.app`, `RegChain.app`, F61 weight, F66 lower limit). The order of the
quantifiers is that of `WTPrefix`: `η₀` after `(d, γ)`, the constant `C` after `η` and the input bound `B`, the
step bound `δ₁` after `C`, `L₀` after everything.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Regref

open TTree

/-- `γ₁ = min(2γ, 1, 2(d−1)(1−γ))` (T (defgamma1); `WTParams.gamma1`). -/
noncomputable def gam1 (d : ℕ) (γ : ℝ) : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ)))

theorem gamma1_eq (P : WTParams) : P.gamma1 = gam1 P.d P.γ := rfl

/-- **Named obligation RA1, couples** (DH23 Prop 6.1, `regcpltreeasymp`, L920–L934, couple part; packet RA1). -/
def RA1Couple : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η ∈ Ioc 0 η₀ →
  ∀ B : ℝ, ∃ C : ℝ, 1 ≤ C ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, δ ∈ Ioc 0 δ₁ → ∀ A : ℝ, ∃ L₀ : ℝ,
  ∀ L : ℝ, L₀ ≤ L → ∀ F : Mom d → ℝ, SNormR (40 * d) (40 * d) F ≤ ENNReal.ofReal B →
  ∀ n : ℕ, (n : ℝ) ≤ Real.log L ^ A →
    (∀ Q : RegCpl, Q.wf = true → Q.size = 2 * n → ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
      (∀ a, LG.layer a = 0) →
      XNormRestr η (30 * d) (30 * d) (timeBox 0 0) Set.univ
        (fun ts k => KQstar L γ δ (fun _ => F) LG (ts 0) (ts 1) k - Q.app δ 0 F (ts 0) (ts 1) k) ≤
        ENNReal.ofReal (C * (C * δ) ^ n * L ^ (-(gam1 d γ - Real.sqrt η)))) ∧
    (∀ Q : RegCpl, Q.wf = true → Q.dominant = true → Q.size = 2 * n →
      XNorm00Restr (V := Unit) (1 - η) (timeBox 0 0) Set.univ
          (fun ts _ => (Q.JB 0 (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (C * C ^ n) ∧
        ∀ Z ∈ specialSets Q.links,
          SNormR (30 * d) (30 * d) (Q.Mstar F Z (0, []) (1, [])) ≤ ENNReal.ofReal (C * C ^ n))

/-- **Named obligation RA1, trees** (DH23 Prop 6.1, tree part; packet RA1). Layer `0` for every node, including the
lone leaf; the box `{0 ≤ s < t ≤ 1}`; the remainder in the landed restriction norm `Fourier.mixedRestrictionNorm`. -/
def RA1Tree : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η ∈ Ioc 0 η₀ →
  ∀ B : ℝ, ∃ C : ℝ, 1 ≤ C ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, δ ∈ Ioc 0 δ₁ → ∀ A : ℝ, ∃ L₀ : ℝ,
  ∀ L : ℝ, L₀ ≤ L → ∀ F : Mom d → ℝ, SNormR (40 * d) (40 * d) F ≤ ENNReal.ofReal B →
  ∀ n : ℕ, (n : ℝ) ≤ Real.log L ^ A →
    (∀ X : RegChain, X.wf = true → X.size = 2 * n → ∀ LG : LayeredGarden 1, X.DecodesTree LG.garden →
      (∀ a, LG.layer a = 0) →
      Fourier.mixedRestrictionNorm η (30 * d) 0 (timeBoxGt 0 0) Set.univ
        (fun ts k => KTstar L γ δ (fun _ => F) LG (ts.1 0) (ts.1 1) k.1 -
          X.app δ 0 F (LG.garden.sig 0) (ts.1 0) (ts.1 1) k.1) ≤
        ENNReal.ofReal (C * (C * δ) ^ n * L ^ (-(gam1 d γ - Real.sqrt η)))) ∧
    (∀ X : RegChain, X.wf = true → X.dominant = true → X.size = 2 * n → ∀ ζ : ℤˣ,
      XNorm00Restr (V := Unit) (1 - η) (timeBoxGt 0 0) Set.univ
          (fun ts _ => (X.JBtree 0 (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (C * C ^ n) ∧
        ∀ Z ∈ specialSets (X.treeLinks ζ),
          SNormR (30 * d) 0 (X.Nstar F Z ζ (0, [])) ≤ ENNReal.ofReal (C * C ^ n))

end WaveTurbulence.Regref
