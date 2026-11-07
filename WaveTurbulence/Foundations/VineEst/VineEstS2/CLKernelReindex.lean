/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLClockReindex
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLNormalizedCoordinates

/-! # Exact lattice and clock change in the actual recentered regional kernel -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed Reg Reg.Skeleton MeasureTheory
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- TARGET Step2's actual regional kernel, with no epsilon replacement,
weight extraction, Fubini assumption, or source summand omitted. -/
theorem clLocalKernel_reindexed {L : ℝ} (hL : L ≠ 0)
    (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (D : ReconstructionData G) (hG : G.IsPlain)
    (γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
    (hβ : ((G.sign a.toNode : ℤ) • (β 0-β 1)) = β 2-β 3) (t : Fin 3 → ℝ) :
    clRecenteredLocalKernel D hG R L γ δ F layer hLayer base (t 0) (t 1) (t 2)
      (base+latticePoint L (β 0)) (base+latticePoint L (β 1))
      (base+latticePoint L (β 2)) (base+latticePoint L (β 3)) =
    (coupling d L γ δ : ℂ)^clLocalOrder1 R * clLocalZeta R *
      ∑' x : (assemblyShape hM9 B).VIdx → (Fin d → ℤ), ∫ τ : (assemblyShape hM9 B).TVar → ℝ,
        clLocalRecenteredSummand D hG R L γ δ F layer hLayer base
          (fun j => base+latticePoint L (β j)) t
          ((clNormalizedChainEquiv hL B base β hβ hM9).symm x) (assemblyClockEquiv hM9 B τ) := by
  let H := clLocalRecenteredSummand D hG R L γ δ F layer hLayer base
    (fun j => base+latticePoint L (β j)) t
  have hb : ![base+latticePoint L (β 0),base+latticePoint L (β 1),
      base+latticePoint L (β 2),base+latticePoint L (β 3)] = fun j => base+latticePoint L (β j) := by
    funext j
    fin_cases j <;> rfl
  have ht : ![t 0,t 1,t 2] = t := by funext j; fin_cases j <;> rfl
  have hsrc := clLocalKernel_recentered_formula B.isBlock D hG R L γ δ F layer hLayer base
    (t 0) (t 1) (t 2) (base+latticePoint L (β 0)) (base+latticePoint L (β 1))
      (base+latticePoint L (β 2)) (base+latticePoint L (β 3))
  generalize hbb : ![base+latticePoint L (β 0),base+latticePoint L (β 1),
      base+latticePoint L (β 2),base+latticePoint L (β 3)] = b at hsrc
  obtain rfl : b = fun j => base+latticePoint L (β j) := hbb.symm.trans hb
  simp only [ht] at hsrc
  have hs : (∑' κ, ∫ τ, H κ τ) =
      ∑' x, ∫ τ, H ((clNormalizedChainEquiv hL B base β hβ hM9).symm x) τ :=
    ((clNormalizedChainEquiv hL B base β hβ hM9).symm.tsum_eq (fun κ => ∫ τ, H κ τ)).symm
  calc
    _ = (coupling d L γ δ : ℂ)^clLocalOrder1 R * clLocalZeta R * (∑' κ, ∫ τ, H κ τ) := hsrc
    _ = _ := congrArg (fun z : ℂ => (coupling d L γ δ : ℂ)^clLocalOrder1 R * clLocalZeta R*z) hs
    _ = _ := by
      apply congrArg (fun z : ℂ => (coupling d L γ δ : ℂ)^clLocalOrder1 R * clLocalZeta R*z)
      apply tsum_congr
      intro x
      exact assemblyClock_integral hM9 B (H ((clNormalizedChainEquiv hL B base β hβ hM9).symm x))

end WaveTurbulence.VineEstS2
