/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ProperGardenZero
public import WaveTurbulence.Foundations.Spine.CoupleZeroRemainder
public import WaveTurbulence.Foundations.Spine.OffDiagonal
public import WaveTurbulence.Foundations.Spine.CoupleThreeContributionAssembly
public import WaveTurbulence.Foundations.Spine.RegularLegPrefix
public import WaveTurbulence.Foundations.Spine.ThreeContributionReserve
public import WaveTurbulence.Foundations.Spine.CoherentSmallParameters
/-! Assembly of B1.2 `layergarden` from the regular legs and ONE remaining estimate, the terms (a)
and (b) of TARGET L2236-L2255 (garden width >= 4, nonregular couples), `NonregularEstimateAt`.
That estimate is TARGET's finalprooffin2 after the weight/derivative reductions of L2062-L2067, i.e.
the content of the blueprint node T.plg.ab; it is proved in the later assembly modules from the Stage 1
inputs, never assumed in the final theorem. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set
open scoped ENNReal

/-- TARGET terms (a) and (b): clause (1) of B1.2 for every garden width `2m >= 4`, and the exact spatial
norm of the sum over nonregular couples (the term (b) of L2236), at every `t in [p, p+1]`. -/
abbrev NonregularEstimateAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ N : ℕ, N ≤ P.N (p + 1) ^ 4 → ∀ t ∈ Icc (p : ℝ) (p + 1),
    (∀ m : ℕ, 2 ≤ m → m ≤ 10 * P.R (p + 1) → ∀ ζ : Fin (2 * m) → ℤˣ, IsBalancedSig ζ →
        ∀ n : Fin (2 * m) → (Fin P.d → ℤ),
          ‖truncSum P (inputsF P R) (p + 1) N t ζ n‖ ≤
            jbrProd P.L n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-((m : ℝ) - 1) / 4) *
              P.δ ^ (2 * P.ν * N)) ∧
      SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1))
        (fun k => nonregularCoupleSum P (inputsF P R) (p + 1) N t k) ≤
        ENNReal.ofReal (P.δ ^ (2 * P.ν * N) *
          P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))

theorem R_largeConstants (P : WTParams) (C₁ C₂ : ℝ) (p : ℕ) :
    ({P with C₁ := C₁, C₂ := C₂} : WTParams).R p = P.R p := by
  simp only [WTParams.R, Rdown_largeConstants]

theorem truncSum_largeConstants (P : WTParams) (C₁ C₂ : ℝ) (F : ℕ → Mom P.d → ℝ) (q N : ℕ)
    {w : ℕ} (t : ℝ) (ζ : Fin w → ℤˣ) (n : Fin w → (Fin P.d → ℤ)) :
    truncSum ({P with C₁ := C₁, C₂ := C₂} : WTParams) F q N t ζ n = truncSum P F q N t ζ n := by
  unfold truncSum
  simp only [N_largeConstants]

theorem coupleCarrier_largeConstants (P : WTParams) (C₁ C₂ : ℝ) (q N : ℕ) :
    coupleCarrier ({P with C₁ := C₁, C₂ := C₂} : WTParams) q N = coupleCarrier P q N := by
  ext LG
  unfold coupleCarrier
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, N_largeConstants]

theorem nonregularCoupleSum_largeConstants (P : WTParams) (C₁ C₂ : ℝ) (F : ℕ → Mom P.d → ℝ)
    (q N : ℕ) (t : ℝ) :
    nonregularCoupleSum ({P with C₁ := C₁, C₂ := C₂} : WTParams) F q N t =
      nonregularCoupleSum P F q N t := by
  funext k
  unfold nonregularCoupleSum
  rw [coupleCarrier_largeConstants]

theorem nonregularEstimate_largeConstantMonotone : LargeConstantMonotone NonregularEstimateAt := by
  intro P C₁ C₂ hC hC₂ hδ hL h₁ h₂ h p hp R hRb N hNb t ht
  rw [N_largeConstants] at hNb
  simp only [R_largeConstants, truncSum_largeConstants,
    nonregularCoupleSum_largeConstants]
  exact h p hp R hRb N hNb t ht

theorem prefix_with_basic_parameters {Q : WTParams → Prop} (hQ : WTPrefix Q) :
    WTPrefix (fun P => Q P ∧ 3 ≤ P.d ∧ 0 < P.δ ∧ 2 ≤ P.L) := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hQ⟩ := hQ d hd γ hγ
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  obtain ⟨C₁, hC₁, ν₀, hν₀, hQ⟩ := hQ η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, ?_⟩
  intro ν hν
  obtain ⟨δ₀, hδ₀, hQ⟩ := hQ ν hν
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, L₀, hL₀, hQ⟩ := hQ δ hδ D hD htime
  refine ⟨C₂, hC₂, L₀, hL₀, ?_⟩
  intro L hL
  exact ⟨hQ L hL, hd, hδ.1, hL₀.trans hL⟩

theorem regularAnalyticSources_largeConstantMonotone :
    LargeConstantMonotone RegularAnalyticSourcesAt :=
  (((leafwiseCoherentApproximation_largeConstantMonotone.and
      sourceCoherentTaylor_largeConstantMonotone).and
    (taylorBound_largeConstantMonotone.and lowProfile_largeConstantMonotone)).and
    leafwiseIncoherentDecay_largeConstantMonotone)

/-- B1.2 from the three literal regular-leg inputs and the terms (a),(b). The legs (c),(d), the
off-diagonal clause and the carrier partition are proved here, not assumed. -/
theorem layergarden_of_nonregular
    (hLeaf : LeafwiseCoherentApproximationGate) (hTaylor : CoherentTaylorGate)
    (hDecay : LeafwiseIncoherentDecayGate) (hnr : WTPrefix NonregularEstimateAt) :
    LayergardenGate := by
  have hsource := prefix_and hnr (regular_analytic_sources_prefix hLeaf hTaylor hDecay)
    nonregularEstimate_largeConstantMonotone regularAnalyticSources_largeConstantMonotone
  have h1 := prefix_add_regular_comparisons hsource
  have h2 := prefix_with_three_contribution_reserve h1
  have h3 := prefix_with_basic_parameters h2
  refine prefix_map ?_ h3
  rintro P ⟨⟨⟨hnr', hcoh, hinc⟩, hres⟩, hd, hδ, hL⟩
  intro p hp R hR t ht N hN
  have htI : t ∈ Icc (p : ℝ) (p + 1) := ⟨ht.1.le, ht.2⟩
  obtain ⟨hgard, hnonreg⟩ := hnr' p hp R hR N hN t htI
  refine ⟨hgard, ?_, ?_⟩
  · intro n hn
    exact truncSum_pair_off_diagonal P (inputsF P R) (p + 1) N t n hn
  · exact coupleRemainder_bound_of_three_contributions P (by omega) (by linarith) hδ.le hcoh hinc
      hres hp hN R hR t htI hnonreg

end WaveTurbulence.LGSpine
