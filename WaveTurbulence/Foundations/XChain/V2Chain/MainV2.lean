/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.V2Chain.GateTypes
public import WaveTurbulence.Foundations.XChain.MainAssembly

/-!
# V2-CHAIN 3: `main_v2` from `propansatz_v2` and `nlsAkBridge`

`main_v2_of_propansatz` is MAIN-ASSEMBLY's `main_of_propansatz_nlsAkBridge` re-run for the successor: the hypothesis
`propansatz_v2` supplies the ansatz for `1/2 < γ`, and the binder `hγ : γ ∈ Ioo (1/2) 1` of `main_v2` supplies the
restriction. The second hypothesis is the body of the sealed `nlsAkBridge`. Conditional helper.
-/

public section
namespace WaveTurbulence.MainGlue
open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace SchwartzMap ENNReal
universe u

/-- The successor bodies `propansatz_v2` and `nlsAkBridge` compose to the body of `main_v2` (ruling D9/D10). -/
theorem main_v2_of_propansatz
    (hpropansatz : V2Chain.PropansatzV2Gate.{u}) (hnlsAkBridge : V2Chain.NlsAkBridgeGate.{u})
    (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ θ > (0 : ℝ), ∀ φin : 𝓢(Mom d, ℝ), (∀ k, 0 ≤ φin k) →
      ∀ τstar > (0 : ℝ), ∀ φ : ℝ → 𝓢(Mom d, ℝ), IsWKESolution φin τstar φ →
      ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ α T : ℝ, α = L ^ (-γ) → T = τstar * kineticTime α →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (g : (Fin d → ℤ) → Ω → ℂ),
        (∀ n, Measurable (g n)) → iIndepFun g P → (∀ n, P.map (g n) = stdComplexGaussian) →
        MeasurableSet (solvableEvent L α T φin g) ∧
        1 - Real.exp (-(Real.log L ^ (40 * d))) ≤ P.real (solvableEvent L α T φin g) ∧
        ∀ U : Ω → ℝ → (Fin d → ℝ) → ℂ,
          (∀ ω ∈ solvableEvent L α T φin g,
            IsSmoothNLSSolution L α T (initialCoeff L φin g ω) (U ω)) →
          ∀ t ∈ Icc 0 T, ∀ n : Fin d → ℤ,
            |(∫ ω, (solvableEvent L α T φin g).indicator
                  (fun ω => ‖torusFourierCoeff L (U ω t) n‖ ^ 2) ω ∂P)
              - φ (t / kineticTime α) (latticePoint L n)| ≤ L ^ (-θ) := by
  obtain ⟨η₀, hη₀, hηgate⟩ := hpropansatz d hd γ ⟨hγ.1.trans' (by norm_num), hγ.2⟩
  refine ⟨η₀ ^ 20, pow_pos hη₀ _, ?_⟩
  intro φin hφ τstar hτ φ hsol
  obtain ⟨C₁, _, ν₀, hν₀, hνgate⟩ := hηgate η₀ ⟨hη₀, le_rfl⟩ φin hφ τstar hτ φ hsol
  obtain ⟨δ₀, hδ₀, hδgate⟩ := hνgate ν₀ ⟨hν₀, le_rfl⟩
  let D : ℕ := ⌈τstar / δ₀⌉₊
  let δ : ℝ := τstar / D
  obtain ⟨hD, hδ, hδle, hτeq⟩ := ceiling_subdivision hτ hδ₀
  obtain ⟨C₂, _, Lbase, hLbase, hLgate⟩ := hδgate δ ⟨hδ, hδle⟩ D hD hτeq
  obtain ⟨C, hC, hCbound⟩ := schwartz_lattice_sum_le φin
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Lprob, _, hprob⟩ := eventually_final_exponent hd1
  obtain ⟨Labs, _, habs⟩ := induction_error_absorption hd1 hη₀ hC D
  refine ⟨max Lbase (max Lprob Labs), ?_⟩
  intro L hL α T hα hT Ω _ μ _ g hg hind hmap
  have hLb : Lbase ≤ L := (le_max_left _ _).trans hL
  have hLp : Lprob ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLa : Labs ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hL1 : 1 ≤ L := (by linarith only [hLbase] : (1 : ℝ) ≤ Lbase).trans hLb
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  let Q : WTParams := ⟨d, γ, η₀, φin, τstar, φ, C₁, ν₀, δ, D, C₂, L⟩
  have hTQ : T = Q.δ * kineticTime α * Q.D := by
    dsimp only [Q]
    rw [hT, hτeq]
    ring
  obtain ⟨a, Fev, R, E, Et, hA⟩ := hLgate L hLb hγ.1 Ω μ g ⟨hg, hind, hmap⟩
  have hAQ : ∀ p ≤ Q.D, AnsatzAt Q μ g a Fev R E Et p := hA
  have hlaw : ∀ n, HasLaw (g n) stdComplexGaussian μ :=
    fun n => hasLaw_stdComplexGaussian (hg n) (hmap n)
  have hN : Real.log L ^ (40 * d) ≤ (Q.N Q.D : ℝ) := by
    simpa only [Q, WTParams.N, WTParams.R, Nat.sub_self, WTParams.Rdown, Nat.cast_pow]
      using hprob L hLp
  have hmeas := gate_solvable_measurability (P := Q) hnlsAkBridge hd1 hLpos hδ hD hα hTQ hg
  have hpr := ansatz_solvable_probability (hAQ Q.D le_rfl) hLpos hδ hD hα hTQ hlaw
  have hsmall : 1 - Real.exp (-(Real.log L ^ (40 * d))) ≤ 1 - Real.exp (-(Q.N Q.D : ℝ)) :=
    sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg hN)) 1
  refine ⟨hmeas.1, hsmall.trans hpr, ?_⟩
  intro U hU t ht n
  have hkt : 0 < kineticTime α := by
    rw [hα]
    exact NLS.kineticTime_rpow_neg_pos hLpos γ
  have hσ : 0 < δ * kineticTime α := mul_pos hδ hkt
  have hs : t / (δ * kineticTime α) ∈ Icc (0 : ℝ) D := by
    refine ⟨div_nonneg ht.1 hσ.le, (div_le_iff₀' hσ).mpr ?_⟩
    rw [← hTQ]
    exact ht.2
  obtain ⟨p, hp1, hpD, hstep⟩ := exists_ansatz_step hD hs
  have herr := ansatz_observable_error hnlsAkBridge hd1 hAQ hLpos hδ hD hφ hα hTQ hg hlaw
    U hU ht hp1 hpD hstep n
  have htime : Q.δ * (t / (Q.δ * kineticTime α)) = t / kineticTime α := by
    dsimp only [Q]
    have hδne : δ ≠ 0 := hδ.ne'
    field_simp [hδne, hkt.ne']
  rw [htime] at herr
  have htail : 2 * Real.sqrt 2 * (∑' m, φin (latticePoint L m)) *
      Real.exp (-(Q.N Q.D : ℝ) / 2) ≤
      2 * Real.sqrt 2 * C * L ^ d * Real.exp (-(Q.N Q.D : ℝ) / 2) := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hCbound hL1) (by positivity : 0 ≤ 2 * Real.sqrt 2))
      (Real.exp_nonneg (-(Q.N Q.D : ℝ) / 2))
    simpa only [mul_assoc] using h
  apply herr.trans
  calc
    _ ≤ 2 * L ^ (-Q.theta p) + 2 * Real.sqrt 2 * C * L ^ d * Real.exp (-(Q.N Q.D : ℝ) / 2) :=
      add_le_add le_rfl htail
    _ ≤ _ := by
      simpa only [Q, WTParams.theta] using habs L hLa p hpD (Q.N Q.D : ℝ) hN

end WaveTurbulence.MainGlue
