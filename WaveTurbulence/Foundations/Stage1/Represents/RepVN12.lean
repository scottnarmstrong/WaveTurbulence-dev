/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepH18
public import WaveTurbulence.Foundations.Stage1.Represents.RepH6
public import WaveTurbulence.Foundations.Stage1.Represents.RepVN11
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-D/E: the hinge data of every unit from VINEEST(λ)

`unitMass`: the VINEEST mass `M0 j` of a unit, without the modulation loss (independent of the centre: `M₁` is read from
`rowCoupleG`/`rowTreeG`).  `exists_hinge_data_units`: for every modulation `lam : J → ℤ`, hinge families `H` and masses
`Mh` for the units `j : J` (VINE-A/C data `U₀ a₀ b₀ R₀ B₀` over the skeleton `S`) with the hinge superposition property
and `Π_j Mh_j ≤ C^{|J|} Π_j M0_j Π_j (1 + |λ_j|)^{6η⁶}`.  Named inputs: `hcont` (V5-CONT, kind-generic: V5-KIND),
`G1`, `G2` (VINE-B♯ geometry).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C VineParamContract TTree WaveTurbulence.LGSpine
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3.FS
open scoped ENNReal

/-- The VINEEST mass of a unit (without the modulation loss). -/
noncomputable def unitMass (P : WTParams) {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (B₀ : ℝ) : ℝ :=
  (P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R)
          (fun _ => (0 : Mom P.d)) (0 : Mom P.d)).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 / 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀)

theorem step3D_M₁_const {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} {d : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (c c' : Fin 4 → Mom d) (wb wb' : Mom d) :
    (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) c wb).M₁ =
      (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) c' wb').M₁ :=
  rfl

/-- The `sumint` datum of the unit at the centre `centre` and offset `wBar`. -/
noncomputable abbrev unitD {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (centre : Fin 4 → Mom d) (wBar : Mom d) : SumintDatum d :=
  step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar

/-- The modulated class kernel of the unit, curried as in `outerValM`. -/
noncomputable def unitHk (P : WTParams) (p : ℕ) {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} (B : CLChainAssembly G R n)
    (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (h : ℕ → Mom P.d → ℝ) (wBar : Mom P.d) :
    ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ := fun lam t k =>
  WaveTurbulence.VineEstS5C.Cont.twistedRecenteredModC G a
    (canonFinsetK p (objKind w) (startState B RD hG layer hLayer) (chainStart B))
    P.L P.γ P.δ h wBar (lam : ℝ) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3)

end WaveTurbulence.Represents
