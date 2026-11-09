/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.Free
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.Glue
public import WaveTurbulence.Foundations.VineEst.VineEstS2.VineChainSumintForm
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.FreeRow
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.Free
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.FreeRow` (sha256 4ff606a0898bc275…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (N2): the free-domain dictionary from the row form

**N2(a), the phase.**  `engDatum_phase`: the phase of the engine datum `engDatum hM9 B hG W ..` (P2) is the `signedPhase` of the
source datum with the parameters and the bad kinds switched off (`W0 W`), times the parameter factor `paramFac W.param τ`
(`∏_v e^{πi p_v τ_v}`) and the kind-2 factor `k2c bk η τ` (`∏_i |t₁ⁱ - s₁ⁱ|^{1-3η}` over the kind-2 blocks).  With the R58 modulation
(the parameter `λ` at the clock of the lower joint `b`, `W.param = λ · 1_{v₀}`, `v₀ = t₀⁰` = `.inl ⟨⟨0, hI⟩, 0⟩`) the parameter factor is
`e^{πiλτ_b}` (`paramFac_single`, `clock_lowerJoint`).  The recentring factor `recFac` and the regional phase combine into the
`signedPhase` (`recFac_mul_regionalPhase`: `clLocalDecoration_phase_recenter`, then `assembly_regionalPhase_eq_signedPhase`).

**`freeDict_of_rowForm`.**  For a summand `ψ = e^{πiλu_b} ψ₀` with `ψ₀` in row form (`RowForm R ψ₀ Dm Qw Tw`, N1), the free-domain
dictionary `FreeDict` holds as soon as
* (`hMx`) the character mixture is the sign `ε` of the decoration,
* (`hsub`) a.e. on the engine time domain the row-form time condition holds, (`hvan`) a.e. where the row-form condition holds outside
  the engine domain the product of the row weights vanishes (the clock indicators of the twin-ordered pieces sit in their rows), and
* (`hrow`) a.e. on the engine time domain, the product of the row-form weights is `kind1Pref · k2c · ∏_ρ (engine row ρ)`.
The row matching (`hrow`, N2(b)) and the time domain (`hsub`, `hvan`, N2(c)) are separate modules.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
variable {kind : Bool}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS4
open scoped ENNReal

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The clock of the lower joint `b`: the first clock `t₀⁰` of the assembly. -/
theorem clock_lowerJointΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (tt : Fin 3 → ℝ)
    (τ : (assemblyShapeΓ hM9 B).TVar → ℝ) :
    clLocalClock R tt (assemblyClockEquivΓ hM9 B τ) b = τ (.inl ⟨⟨0, assemblyShape_I_posΓ hM9 B⟩, 0⟩) := by
  have := clLocalClock_slotΓ hM9 B tt τ (.inl ⟨⟨0, assemblyShape_I_posΓ hM9 B⟩, 0⟩)
  rwa [assemblyClockAtom_firstΓ hM9 B (assemblyShape_I_posΓ hM9 B)] at this

/-- **N2(a): the phase of the engine datum** is the source `signedPhase` without parameters and bad kinds, times the parameter
factor and the kind-2 factor. -/
theorem engDatum_phaseΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) (wN wDec : ℕ) (bk : Fin (assemblyShapeΓ hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) (g g' : (assemblyShapeΓ hM9 B).VIdx → ℕ)
    (L γ δ η : ℝ) (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) (r : Mom d) (t : ℝ) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ) :
    (engDatumΓ hM9 B hG W wN wDec bk cons g g').phase L γ δ η x r t τ =
      signedPhase (sourceSumintDatumΓ hM9 B hG (W0 W)) (assemblyCoreFirstSignΓ hM9 B) (assemblyCoreSignΓ hM9 B) L γ δ η x r t τ *
        (paramFac W.param τ * k2c bk η τ) := by
  have e1 : (engDatumΓ hM9 B hG W wN wDec bk cons g g').phase L γ δ η x r t τ =
      signedPhase (sourceSumintDatumΓ hM9 B hG { W with badKind := bk }) (assemblyCoreFirstSignΓ hM9 B) (assemblyCoreSignΓ hM9 B)
        L γ δ η x r t τ := rfl
  exact e1.trans ((signedPhase_split (sourceSumintDatumΓ hM9 B hG { W with badKind := bk }) (assemblyCoreFirstSignΓ hM9 B)
    (assemblyCoreSignΓ hM9 B) L γ δ η x r t τ).trans rfl)

/-- **N2(a): the recentring factor times the regional phase is the source `signedPhase`** (at `δ' = 2δ`, the frozen gap `E₀ - E₁`). -/
theorem recFac_mul_regionalPhaseΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
    (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)) (τ : (assemblyShapeΓ hM9 B).TVar → ℝ) :
    recFac (G.sign a.toNode) (G.sign a.toNode) L γ δ tt
        (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) *
      clRegionalPhase G U L γ δ
        (cosetDecoration G L base (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1))
        (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ)) =
    signedPhase (sourceSumintDatumΓ hM9 B hG (W0 W)) (assemblyCoreFirstSignΓ hM9 B) (assemblyCoreSignΓ hM9 B) L γ (2 * δ) η x
      (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
        sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1) (tt 0) τ := by
  have hrec := clLocalDecoration_phase_recenter B.isBlock R L γ δ base (fun j => base + latticePoint L (β j))
    ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x) (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ)) (tt 0)
  have hsp := assembly_regionalPhase_eq_signedPhaseΓ hM9 B hG (W0 W) (fun _ => rfl)
    (fun _ => show (0 : Fin 4) ≠ 2 by decide) hL base β hβ γ δ η x tt τ
  rw [sumintBoundary_gap_physical (L := L) (G.sign a.toNode) base β hβ, ← hsp]
  simp only [recFac, sumintBoundary_invol, clRegionalPhase]
  exact hrec

/-- **N2: the free-domain dictionary from the row form.**  `ψ = e^{πiλu_b} ψ₀` with `ψ₀` in row form; the modulation is the engine
parameter `λ` at the clock `t₀⁰` of `b` (`hpar`); `hMx` (the sign), `hsub`/`hvan` (time domain) and `hrow` (rows) as in the module docstring. -/
theorem freeDict_of_rowFormΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (base : Mom d)
    (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
    (ψ ψ0 : PsiT G d) (lam : ℝ)
    (hψ : ∀ x t u, ψ x t u = Complex.exp (((Real.pi * lam * u b : ℝ) : ℂ) * Complex.I) * ψ0 x t u)
    {Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop}
    {Qw : SourcePair G → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ}
    {Tw : GBranch G.tree → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ}
    (hR : RowForm hG R L γ δ base ψ0 Dm Qw Tw)
    (wN wDec : ℕ) (bk : Fin (assemblyShapeΓ hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar)) (g g' : (assemblyShapeΓ hM9 B).VIdx → ℕ)
    (Mx : CharMix (assemblyShapeΓ hM9 B) d) (cr : ClockedRows3 (engDatumΓ hM9 B hG W wN wDec bk cons g g'))
    (hpar : ∀ v, W.param v =
      if v = (.inl ⟨⟨0, assemblyShape_I_posΓ hM9 B⟩, 0⟩ : (assemblyShapeΓ hM9 B).TVar) then lam else 0)
    (hMx : ∀ x, Mx.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x =
      (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1) : ℂ))
    (hsub : ∀ᵐ τ : (assemblyShapeΓ hM9 B).TVar → ℝ,
      τ ∈ (engDatumΓ hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_posΓ hM9 B) (tt 0) (tt 1) (tt 2) →
        Dm tt (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ)))
    (hvan : ∀ x, ∀ᵐ τ : (assemblyShapeΓ hM9 B).TVar → ℝ, Dm tt (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ)) →
      τ ∉ (engDatumΓ hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_posΓ hM9 B) (tt 0) (tt 1) (tt 2) →
      (∏ p ∈ clRegionalPairs hG U, Qw p tt (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ))
          (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1)) *
        (∏ v ∈ U.erase a, Tw v tt (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ))
          (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1)) = 0)
    (hrow : ∀ x, ∀ᵐ τ : (assemblyShapeΓ hM9 B).TVar → ℝ,
      τ ∈ (engDatumΓ hM9 B hG W wN wDec bk cons g g').timeDom (assemblyShape_I_posΓ hM9 B) (tt 0) (tt 1) (tt 2) →
      (∏ p ∈ clRegionalPairs hG U, Qw p tt (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ))
          (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1)) *
        (∏ v ∈ U.erase a, Tw v tt (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ))
          (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1)) =
      ((kind1Pref (D := engDatumΓ hM9 B hG W wN wDec bk cons g g')
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) : ℝ) : ℂ) * k2c bk η τ *
        ∏ ρ, cr.W ρ (cr.clock τ tt ρ)
          (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 0 -
            sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)) 1)
          (rowMom (engDatumΓ hM9 B hG W wN wDec bk cons g g') L x
            (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) ρ)) :
    FreeDictΓ hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk cons g g' Mx cr := by
  classical
  intro x
  filter_upwards [hsub, hvan x, hrow x] with τ hd1 hd2 hr
  have hform := hR _ ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x) tt (clLocalClock R tt (assemblyClockEquivΓ hM9 B τ))
  have hm := hMx x
  have hrec := recFac_mul_regionalPhaseΓ hM9 B hG W hL γ δ η base β hβ tt x τ
  rw [hψ, clock_lowerJointΓ hM9 B tt τ]
  generalize clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1 = X0 at hform hm hd2 hr hrec ⊢
  rw [hform]
  exact dict_scalar _ τ _ _ _ _ _ _ _ _ _ _ _ _ hd1 hd2 hr
    (by simp only [clockedIntegrand3]; rw [engDatum_phaseΓ, paramFac_single _ lam _ τ hpar]) hm hrec

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
