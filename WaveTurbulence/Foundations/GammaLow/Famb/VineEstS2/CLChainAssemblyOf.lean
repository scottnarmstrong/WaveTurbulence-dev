/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainAssembly
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.ChainPrefixBlocks
-- L5b port of `nonempty_clChainAssembly`, `clChainAssembly` (`VineEst/VineEstS2/CLChainAssembly.lean`) and
-- `clChainPrefixRegion`, `clChainTerminalRegion` (`VineEst/VineEstS2/CLChainSplit.lean`) for L6's chains over 𝒱_γ;
-- see COPIED-SHA256SUMS.

/-! # Every source chain over `𝒱_γ` in a CL region has assembly data

The constructor API for consumers (Stage1′): a chain `FinalCount.Src.Chain γF G.molecule U a b n` (L6's carrier) that
is a block, with CL region data `R`, has a chain assembly `CLChainAssemblyΓ γF G R n`; prefix and ingredient CL geometry
are conclusions, never added premises (main's `nonempty_clChainAssembly`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {γF : ℝ}

/-- Current source-chain prefix data from the actual connected block and the proved split parent pattern. -/
noncomputable def clChainPrefixRegionΓ {S T : Finset (GBranch G.tree)} {a b c : GBranch G.tree} {n : ℕ}
    (hS : FinalCount.Src.Chain γF G.molecule S a b n) (hT : FinalCount.Src.IsSomeVine γF G.molecule T b c)
    (hi : S ∩ T = {b}) (hU : G.molecule.IsBlock (S ∪ T) a c) (R : CLRegionData G (S ∪ T) a c) :
    CLRegionData G S a b := by
  let hB := chain_prefix_currentBlockΓ G.molecule (Mole.garden_isMolecule G) hS hT hi hU
  exact clRegionData G hB (clBlockConcat_parentPatterns hB (memBlock hT) hi hU R).1

/-- **Every actual source VC over `𝒱_γ` in a CL region has assembly data.** -/
theorem nonempty_clChainAssemblyΓ {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {n : ℕ}
    (h : FinalCount.Src.Chain γF G.molecule U a b n) (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) :
    Nonempty (CLChainAssemblyΓ γF G R n) := by
  induction h with
  | single hV => exact ⟨.single hV R⟩
  | append hS hT hi _ ih =>
    have hB := chain_prefix_currentBlockΓ G.molecule (Mole.garden_isMolecule G) hS hT hi hU
    let RP := clChainPrefixRegionΓ hS hT hi hU R
    obtain ⟨B⟩ := ih hB RP
    exact ⟨.append B hT hi hU R⟩

/-- Canonical noncomputable selection of the proved source assembly data. -/
noncomputable def clChainAssemblyΓ {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {n : ℕ}
    (h : FinalCount.Src.Chain γF G.molecule U a b n) (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) :
    CLChainAssemblyΓ γF G R n := Classical.choice (nonempty_clChainAssemblyΓ h hU R)

end WaveTurbulence.GammaLow.Famb.VineEstS2
