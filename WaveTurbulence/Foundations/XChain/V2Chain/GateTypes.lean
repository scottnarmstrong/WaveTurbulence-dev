/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.XChain.GateTypes
public import WaveTurbulence.Frozen.Defs.IsASolution
public import WaveTurbulence.Frozen.Defs.ZNormOn
public import WaveTurbulence.Frozen.Defs.SNormR
public import WaveTurbulence.Frozen.Defs.WkeTaylorTerm
public import WaveTurbulence.Frozen.Defs.IsSmoothNLSSolution
public import WaveTurbulence.Frozen.Defs.TorusFourierCoeff
public import WaveTurbulence.Frozen.Defs.KineticTime
public import WaveTurbulence.Frozen.Defs.Jbr
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# V2-CHAIN: the successor statements as `Prop`s

Each abbreviation is, token for token, the type of the corresponding frozen anchor of
`WaveTurbulence.Frozen.Theorems.*` (`layergarden_v2`, `fixedpoint_v2`, `propansatz_v2`, `wkeTaylor`,
`layergardenFlower_v2`, `nlsAkBridge`): the type text is extracted mechanically from the frozen file
(`tools/gen_gates.py`). They are used only as the hypotheses and conclusions of the conditional assembly theorems.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence.V2Chain

abbrev LayergardenV2Gate : Prop :=
  WTPrefix fun P => 1 / 2 < P.γ →
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioc (p : ℝ) (p + 1), ∀ N ≤ P.N (p + 1) ^ 4,
      (∀ m : ℕ, 2 ≤ m → m ≤ 10 * P.R (p + 1) → ∀ ζ : Fin (2 * m) → ℤˣ, IsBalancedSig ζ →
        ∀ n : Fin (2 * m) → (Fin P.d → ℤ),
          ‖truncSum P (inputsF P R) (p + 1) N t ζ n‖ ≤
            jbrProd P.L n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-((m : ℝ) - 1) / 4) *
              P.δ ^ (2 * P.ν * N)) ∧
      (∀ n : Fin 2 → (Fin P.d → ℤ), n 0 ≠ n 1 →
        truncSum P (inputsF P R) (p + 1) N t ![1, -1] n = 0) ∧
      SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1)) (coupleRemainder P R p N t) ≤
        ENNReal.ofReal (P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5) * P.δ ^ (2 * P.ν * N))

abbrev FixedpointV2Gate.{u} : Prop :=
  WTPrefix fun P => 1 / 2 < P.γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
    ∀ p : ℕ, p < P.D →
    ∀ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
      (E : ℕ → (Fin P.d → ℤ) → ℝ)
      (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
      (∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q) →
    ∃ F' : Set Ω, F' ⊆ Fev p ∧ MeasurableSet F' ∧ IsSymmetricEvent P.L P.φin g F' ∧
      μ.real (Fev p \ F') ≤ Real.exp (-(4 * P.N (p + 1) : ℝ)) ∧
      ∀ ω ∈ F',
        let Ntr := P.N (p + 1)
        let Λ : ℝ := 5 / 4 * P.Lambda (p + 1)
        let ℒ : ℕ → (Icc (p : ℝ) (p + 1) → (Fin P.d → ℤ) → ℂ) →
            Icc (p : ℝ) (p + 1) → (Fin P.d → ℤ) → ℂ :=
          fun j b t n => Lop P.L P.γ P.δ p Ntr (a ω p) j b t n
        let Zs := ZSpace (d := P.d) P.L Λ p
        (∀ t ∈ Icc (p : ℝ) (p + 1), ∀ n,
          ‖aTr P.L P.γ P.δ p Ntr (a ω p) t n‖ ≤
            jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) *
              Real.exp (3 * Ntr)) ∧
        (∀ (b : Icc (p : ℝ) (p + 1) → (Fin P.d → ℤ) → ℂ) (t : Icc (p : ℝ) (p + 1)) (n),
          ‖ℒ 0 b t n‖ ≤ jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) *
            Real.exp (-(20 * Ntr : ℝ))) ∧
        (∀ b ∈ Zs, b - ℒ 1 b ∈ Zs) ∧
        (∀ c ∈ Zs, ∃! b, b ∈ Zs ∧ b - ℒ 1 b = c) ∧
        (∀ b ∈ Zs, ZNorm P.L Λ b ≤ ENNReal.ofReal (Real.exp (3 * Ntr)) * ZNorm P.L Λ (b - ℒ 1 b)) ∧
        (∀ b ∈ Zs, ZNorm P.L Λ b ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ))) →
          ∃ c ∈ Zs, c - ℒ 1 c = ℒ 0 b + ℒ 2 b + ℒ 3 b ∧
            ZNorm P.L Λ c ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ)))) ∧
        (∀ b ∈ Zs, ∀ b' ∈ Zs, ∀ c ∈ Zs, ∀ c' ∈ Zs,
          ZNorm P.L Λ b ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ))) →
          ZNorm P.L Λ b' ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ))) →
          c - ℒ 1 c = ℒ 0 b + ℒ 2 b + ℒ 3 b → c' - ℒ 1 c' = ℒ 0 b' + ℒ 2 b' + ℒ 3 b' →
          ZNorm P.L Λ (c - c') ≤ 2⁻¹ * ZNorm P.L Λ (b - b'))

abbrev PropansatzV2Gate.{u} : Prop :=
  WTPrefix fun P => 1 / 2 < P.γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
    ∃ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
      (E : ℕ → (Fin P.d → ℤ) → ℝ)
      (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
      ∀ p ≤ P.D, AnsatzAt P μ g a Fev R E Et p

abbrev WkeTaylorGate : Prop := Induct.WkeTaylorGate

open Classical in
abbrev LayergardenFlowerV2Gate : Prop :=
  WTPrefixP fun Pm P => 1 / 2 < P.γ →
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
      ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
        (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ),
        (∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) →
        ‖flowerSum P (inputsF P R) p N kind pat dagger cut1 cut2 ζ t s n n'‖ ≤
          jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^
              (-(4 * P.Lambda (p + 1) * Pm : ℝ)) *
            P.L ^ ((if ∀ j, pat j = .plain then 1 else 2) * (100 * P.d : ℝ) ^ 3 * Pm) *
            P.δ ^ (2 * P.ν * N) *
            (cut1.elim 1 fun j₁ => ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ))) *
            (cut2.elim 1 fun j₂ =>
              if ∀ j, pat j = .plain then ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ)) else 1)) ∧
    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ k : Mom P.d, ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : TreeKind)
        (dt : Bool), (kind = .tr → dt = true) →
        ‖coupleSum P (inputsF P R) p N kind dt t k‖ ≤
          jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (P.ν * N))

abbrev NlsAkBridgeGate.{u} : Prop :=
  ∀ {d : ℕ} (hd : 1 ≤ d) (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (D : ℕ)
    (hD : 1 ≤ D) (α T : ℝ) (hα : α = L ^ (-γ)) (hT : T = D * δ * kineticTime α),
    -- (1) forward
    (∀ (c : (Fin d → ℤ) → ℂ) (u : ℝ → (Fin d → ℝ) → ℂ), IsSmoothNLSSolution L α T c u →
      let M : ℝ := (L ^ d)⁻¹ * ∑' n, ‖c n‖ ^ 2
      let a : ℝ → (Fin d → ℤ) → ℂ := fun t n =>
        Complex.exp (-(Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L n‖ ^ 2 * t : ℝ) *
          Complex.I) *
        Complex.exp (-(2 * α * M * δ * kineticTime α * t : ℝ) * Complex.I) *
        torusFourierCoeff L (u (δ * kineticTime α * t)) n
      IsASolution L γ δ D c a ∧ (∀ Λ : ℝ, ZNormOn L Λ (Icc 0 D) a < ⊤) ∧
        ∀ t ∈ Icc (0 : ℝ) D, ∀ n,
          ‖a t n‖ = ‖torusFourierCoeff L (u (δ * kineticTime α * t)) n‖) ∧
    -- (2) backward
    (∀ (c : (Fin d → ℤ) → ℂ) (a : ℝ → (Fin d → ℤ) → ℂ),
      (∀ s : ℝ, ∃ C, ∀ n, jbr (latticePoint L n) ^ s * ‖c n‖ ≤ C) →
      IsASolution L γ δ D c a →
      ∃ u : ℝ → (Fin d → ℝ) → ℂ, IsSmoothNLSSolution L α T c u ∧
        ∀ t ∈ Icc 0 T, ∀ n, ‖torusFourierCoeff L (u t) n‖ = ‖a (t / (δ * kineticTime α)) n‖) ∧
    -- (3) uniqueness
    (∀ (c : (Fin d → ℤ) → ℂ) (u u' : ℝ → (Fin d → ℝ) → ℂ),
      IsSmoothNLSSolution L α T c u → IsSmoothNLSSolution L α T c u' → ∀ t ∈ Icc 0 T, u t = u' t) ∧
    -- (4) measurability
    (∀ (Ω : Type u) [MeasurableSpace Ω] (c : Ω → (Fin d → ℤ) → ℂ), Measurable c →
      MeasurableSet {ω | ∃ v, IsSmoothNLSSolution L α T (c ω) v} ∧
      ∀ U : Ω → ℝ → (Fin d → ℝ) → ℂ,
        (∀ ω, (∃ v, IsSmoothNLSSolution L α T (c ω) v) → IsSmoothNLSSolution L α T (c ω) (U ω)) →
        ∀ t ∈ Icc 0 T, ∀ n, Measurable fun ω =>
          {ω | ∃ v, IsSmoothNLSSolution L α T (c ω) v}.indicator
            (fun ω => ‖torusFourierCoeff L (U ω t) n‖ ^ 2) ω)

end WaveTurbulence.V2Chain
