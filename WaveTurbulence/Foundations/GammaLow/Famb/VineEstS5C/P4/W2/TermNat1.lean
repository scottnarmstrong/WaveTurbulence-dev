/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NatCert
public import WaveTurbulence.Foundations.VineEst.VineEstS3.EpsLabels
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Facts
public import WaveTurbulence.Foundations.Vine.DegenVine.Degenerate
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.TermNat1
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.NatFree
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.TermNat1` (sha256 ec222cdf365eb694…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 12, step 1a): the character mixture of the sign `ε` and the free-domain dictionary of a native term

`exists_mix_native`: a `CharMix` of mass `3^{|U|}` whose value at every integer boundary is the sign `clRegionalEpsilon` of the decoration
(`exists_eps_mix` + `clRegionalEpsilon_eq_epsOf`).  `freeDict_native_NE`: `freeDict_native` for an ARBITRARY term `ψ0` with the native row form
`RowFormNE .. ∅ ∅` on the native clock domain (the form is all that the proof used of `psiNat`). -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS4

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **The sign `ε` as a character mixture** of mass `3^{|U|}`. -/
theorem exists_mix_nativeΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShapeΓ hM9 B) d) {L : ℝ} (hL : L ≠ 0) (base : Mom d) :
    ∃ N : CharMix (assemblyShapeΓ hM9 B) d, N.mass = 3 ^ (clLocalOrder1 R + 1) ∧
      ∀ (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3)
        (x : (assemblyShapeΓ hM9 B).VIdx → (Fin d → ℤ)),
        N.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x =
          (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1) : ℂ) := by
  classical
  obtain ⟨N, hmass, hval⟩ := exists_eps_mix (ι := ↥U) (S := (assemblyShapeΓ hM9 B)) (L := L) hL
    (fun v : ↥U => WaveTurbulence.DegenVine.labelRef (sourceSumintDatumΓ hM9 B hG W) (childLabelΓ hM9 B hG v.1 0))
    (fun v : ↥U => WaveTurbulence.DegenVine.labelRef (sourceSumintDatumΓ hM9 B hG W) (childLabelΓ hM9 B hG v.1 1))
    (fun v : ↥U => WaveTurbulence.DegenVine.labelRef (sourceSumintDatumΓ hM9 B hG W) (childLabelΓ hM9 B hG v.1 2)) base
  refine ⟨N, by rw [hmass, card_U_eqΓ B], fun β hβ x => ?_⟩
  rw [hval (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))
    (fun k => ⟨β (sumintBoundaryPermutation (G.sign a.toNode) k), rfl⟩) x,
    clRegionalEpsilon_eq_epsOfΓ hM9 B hG W hL base β hβ x]
  unfold WaveTurbulence.DegenVine.epsOf
  congr 1
  exact Finset.prod_congr rfl fun i _ => by
    have h0 := WaveTurbulence.DegenVine.labelRef_val (sourceSumintDatumΓ hM9 B hG W) L x
      (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))
    exact congr (congr (congrArg epsMom (h0 _)) (h0 _)) (h0 _)

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
