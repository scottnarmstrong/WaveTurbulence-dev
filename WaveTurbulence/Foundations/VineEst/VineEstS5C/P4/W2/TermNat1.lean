/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.NatFree
public import WaveTurbulence.Foundations.VineEst.VineEstS3.EpsLabels
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Facts
public import WaveTurbulence.Foundations.Vine.DegenVine.Degenerate

/-! # P4-W2 (session 12, step 1a): the character mixture of the sign `ε` and the free-domain dictionary of a native term

`exists_mix_native`: a `CharMix` of mass `3^{|U|}` whose value at every integer boundary is the sign `clRegionalEpsilon` of the decoration
(`exists_eps_mix` + `clRegionalEpsilon_eq_epsOf`).  `freeDict_native_NE`: `freeDict_native` for an ARBITRARY term `ψ0` with the native row form
`RowFormNE .. ∅ ∅` on the native clock domain (the form is all that the proof used of `psiNat`). -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **The sign `ε` as a character mixture** of mass `3^{|U|}`. -/
theorem exists_mix_native (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) {L : ℝ} (hL : L ≠ 0) (base : Mom d) :
    ∃ N : CharMix (assemblyShape hM9 B) d, N.mass = 3 ^ (clLocalOrder1 R + 1) ∧
      ∀ (β : Fin 4 → (Fin d → ℤ)) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3)
        (x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ)),
        N.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x =
          (clRegionalEpsilon G U (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) : ℂ) := by
  classical
  obtain ⟨N, hmass, hval⟩ := exists_eps_mix (ι := ↥U) (S := (assemblyShape hM9 B)) (L := L) hL
    (fun v : ↥U => WaveTurbulence.DegenVine.labelRef (sourceSumintDatum hM9 B hG W) (childLabel hM9 B hG v.1 0))
    (fun v : ↥U => WaveTurbulence.DegenVine.labelRef (sourceSumintDatum hM9 B hG W) (childLabel hM9 B hG v.1 1))
    (fun v : ↥U => WaveTurbulence.DegenVine.labelRef (sourceSumintDatum hM9 B hG W) (childLabel hM9 B hG v.1 2)) base
  refine ⟨N, by rw [hmass, card_U_eq B], fun β hβ x => ?_⟩
  rw [hval (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))
    (fun k => ⟨β (sumintBoundaryPermutation (G.sign a.toNode) k), rfl⟩) x,
    clRegionalEpsilon_eq_epsOf hM9 B hG W hL base β hβ x]
  unfold WaveTurbulence.DegenVine.epsOf
  congr 1
  exact Finset.prod_congr rfl fun i _ => by
    have h0 := WaveTurbulence.DegenVine.labelRef_val (sourceSumintDatum hM9 B hG W) L x
      (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j)))
    exact congr (congr (congrArg epsMom (h0 _)) (h0 _)) (h0 _)

end WaveTurbulence.VineEstS5C.P4.W2
