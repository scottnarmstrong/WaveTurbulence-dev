/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainSplit
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainAssembly
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainAssembly` (sha256 dd5336d6096daab0…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Source-chain assembly with its derived current CL region data -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2
variable {γF : ℝ}
open TTree RegRed
variable {w : ℕ}

/-- A data-bearing copy of the actual source chain over `𝒱_γ` (main's `CLChainAssembly` with the ingredient family
`Src.IsSomeVine γF`, L6's carrier). Its proper prefix blocks and CL metadata are constructed from the source
theorem. The whole region is an index, so its four boundary nodes are preserved exactly. -/
inductive CLChainAssemblyΓ (γF : ℝ) (G : Garden w) :
    {U : Finset (GBranch G.tree)} → {a b : GBranch G.tree} → CLRegionData G U a b → ℕ → Type
  | single {U a b} (hV : FinalCount.Src.IsSomeVine γF G.molecule U a b) (R : CLRegionData G U a b) :
      CLChainAssemblyΓ γF G R 1
  | append {S T a b c n} {RP : CLRegionData G S a b}
      (B : CLChainAssemblyΓ γF G RP n) (hT : FinalCount.Src.IsSomeVine γF G.molecule T b c)
      (hi : S ∩ T = {b}) (hU : G.molecule.IsBlock (S ∪ T) a c) (R : CLRegionData G (S ∪ T) a c) :
      CLChainAssemblyΓ γF G R (n+1)

namespace CLChainAssemblyΓ
variable {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem isBlock (B : CLChainAssemblyΓ γF G R n) : G.molecule.IsBlock U a b := by
  cases B with
  | single hV _ => exact FinalCount.Src.isBlock_of_isSomeVine hV
  | append _ _ _ hU _ => exact hU

theorem toSourceChain (B : CLChainAssemblyΓ γF G R n) : FinalCount.Src.Chain γF G.molecule U a b n := by
  induction B with
  | single hV _ => exact .single hV
  | append _ hT hi hU _ ih => exact .append ih hT hi hU.2.2.2.1

theorem length_pos (B : CLChainAssemblyΓ γF G R n) : 1 ≤ n := by
  cases B <;> omega

end CLChainAssemblyΓ

end WaveTurbulence.GammaLow.Famb.VineEstS2
