/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.VineEst.VineSpaceK.StatementDefs
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.Free
public import WaveTurbulence.Foundations.Vine.DegenVine.MixAlgebra
/-! V5-SPACE: insert a certified input-lattice mixture in the existing single engine call. -/
@[expose] public section
noncomputable section
namespace WaveTurbulence.VineSpaceK
open MeasureTheory DegenVine DegenVinePar VineEstS5C VineEstS5C.P2 VineEstS5C.P3
  VineEstS5C.P4 VineEstS5C.P4.W2 VineEstS3Par.Eng RegRed Reg.Skeleton VineParamContract
  VineEstS2 VineEstS3 VineEstS4 VineEstS5A TTree
open scoped ENNReal

variable {A : ℝ} {P : WTParams} {D : SumintPar.SumintDatum P.d}

def addMix (Z : AmbW A P D) (N : CharMix D.S P.d) : AmbW A P D :=
  { Z with Mx := Z.Mx.mul N }

theorem addMix_pre (Z : AmbW A P D) (N : CharMix D.S P.d) :
    (addMix Z N).pre = ENNReal.ofReal N.mass * Z.pre := by
  unfold AmbW.pre addMix
  rw [CharMix.mass_mul]
  rw [mul_assoc, ENNReal.ofReal_mul Z.Mx.mass_nonneg,
    ENNReal.ofReal_mul N.mass_nonneg, ENNReal.ofReal_mul Z.Mx.mass_nonneg]
  ac_rfl

/-- The single existing engine estimate already handles the multiplied mixture. -/
theorem engine_mix_bound (Z : AmbW A P D) (N : CharMix D.S P.d)
    (Rw : ∀ ρ : Row D, RowData D (6 * P.η ^ 6) ρ) (hAe : ∀ ρ, (Rw ρ).Ae Z.hI) :
    XNorm00Restr (2 * P.η ^ 8) (outBox D) (outSet D P.L P.γ P.η)
      (fun tt E => clockedExprMul3 (Z.Mx.mul N) (allCR Rw) Z.hI P.L P.γ (2 * P.δ) P.η tt E) ≤
      ENNReal.ofReal N.mass * (Z.pre * ∏ ρ, (Rw ρ).b) := by
  have h := (addMix Z N).bound Rw hAe
  rw [addMix_pre, mul_assoc] at h
  exact h

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {R : CLRegionData G U a b} {n : ℕ}

theorem spatialMul_one (ψ : PsiT G d) : spatialMul (fun _ => 1) ψ = ψ := by
  funext x tt u
  exact one_mul _

/-- Pullback at the actual normalized coordinates. No norm estimate is part of this certificate. -/
theorem freeDict_mul (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (base : Mom d)
    (β : Fin 4 → Fin d → ℤ) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
    (ψ : PsiT G d) (m : (GNode G.tree → Fin d → ℤ) → ℂ)
    (wN wDec : ℕ) (bk : Fin (assemblyShape hM9 B).I → Fin 4)
    (cons : Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar))
    (g g' : (assemblyShape hM9 B).VIdx → ℕ)
    (Mx N : CharMix (assemblyShape hM9 B) d)
    (cr : ClockedRows3 (engDatum hM9 B hG W wN wDec bk cons g g'))
    (hdict : FreeDict hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk cons g g' Mx cr)
    (hpull : ∀ x, m (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) =
      N.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x) :
    FreeDict hM9 B hG W hL γ δ η base β hβ tt (spatialMul m ψ) wN wDec bk cons g g' (Mx.mul N) cr := by
  intro x
  filter_upwards [hdict x] with τ hτ
  simp only [spatialMul, hpull, CharMix.val_mul]
  calc _ = N.val L _ x * (recFac (G.sign a.toNode) (G.sign a.toNode) L γ δ tt _ *
      ψ (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) tt
        (clLocalClock R tt (assemblyClockEquiv hM9 B τ))) := by ring
    _ = _ := by rw [hτ]; ring
end WaveTurbulence.VineSpaceK
