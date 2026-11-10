/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.Glue
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Family

/-! # P4-W2 (N1): every unrolled term has a row form on its level's region

`rowForm_idx`: the row form does not depend on the region data of a fixed `(U, a, b)`.  `FrameShape BE X`: at operative members, every
summand of the bundle expansion is the frame `bundleFrame` (= `spartFrame` of the S-block at the exceptional pair `p₀`) times an
exceptional factor `X` (true for P4's `bundleFamOf`: `bundleTerm = bundleFrame · ν · bundlePt`, `frameShape_bundleExpOf`).
**`rowForm_terms`**: by `Lvl.terms_induction` and `rowForm_step`, every unrolled term of a level has a row form on the region of the level;
the terms ending in the bottom bundle `psiBot` are covered through the named input `hbot` (owner BOT-DECOMP, R60).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1

variable {w d : ℕ} {G : Garden w}

/-- The row form is independent of the region data of a fixed `(U, a, b)`. -/
theorem rowForm_idx (hG : G.IsPlain) {U U' : Finset (GBranch G.tree)} {a a' b b' : GBranch G.tree} (hU : U = U') (ha : a = a')
    (hb : b = b') (R : CLRegionData G U a b) (R' : CLRegionData G U' a' b') (L γ δ : ℝ) (base : Mom d) (ψ : PsiT G d)
    (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop)
    (Qw : SourcePair G → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ)
    (Tw : GBranch G.tree → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → (GNode G.tree → (Fin d → ℤ)) → ℂ)
    (h : RowForm hG R L γ δ base ψ Dm Qw Tw) : RowForm hG R' L γ δ base ψ Dm Qw Tw := by
  subst hU ha hb
  rw [regionData_subsingleton R' R]
  exact h

variable {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
variable {κ0 : KPar d} {hprime : IsPrimeGarden G}
variable (BE : BundleExpFam (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime)

end WaveTurbulence.VineEstS5C.P4.W2
