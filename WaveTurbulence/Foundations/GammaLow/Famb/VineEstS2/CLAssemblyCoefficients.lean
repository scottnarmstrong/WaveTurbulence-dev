/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyChart
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyCoefficients
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyChart
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyCoefficients` (sha256 dcd71d77e4bc7a9d…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Unit free decoder coefficients for the actual triangular chain chart -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS2
open WaveTurbulence.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS2
variable {γF : ℝ}
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w}

/-- Recursive coefficients on literal bonds. Disjoint piece bonds prevent
addition of two free coefficients in any matrix entry. -/
noncomputable def chainDecodeFreeΓ (hM9 : NormalChartSupply γF)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) : Bond G.molecule U → chainInputIndexΓ hM9 B → ℤ := by
  induction B with
  | single hV R => exact (chosenVineChartΓ hM9 hV).decodeFree
  | append B hT hi hU R ih =>
    let C := chosenVineChartΓ hM9 hT
    let split := bondUnionEquiv (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU
    exact fun e => match split.symm e with
      | .inl eS => Sum.elim (C.decodeFree (B.terminalAnchor hT hi hU R)) (ih eS)
      | .inr eT => Sum.elim (C.decodeFree eT) (fun _ => 0)

noncomputable def chainDecodeGapΓ (hM9 : NormalChartSupply γF)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) : Bond G.molecule U → ℤ := by
  induction B with
  | single hV R => exact (chosenVineChartΓ hM9 hV).decodeGap
  | append B hT hi hU R ih =>
    let C := chosenVineChartΓ hM9 hT
    let split := bondUnionEquiv (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU
    exact fun e => match split.symm e with
      | .inl eS => C.decodeGap (B.terminalAnchor hT hi hU R) + ih eS
      | .inr eT => C.decodeGap eT

/-- Every free coefficient is 0 or a sign, uniformly in chain length. -/
theorem chainDecodeFree_unitΓ (hM9 : NormalChartSupply γF)
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (B : CLChainAssemblyΓ γF G R n) (e : Bond G.molecule U) (j : chainInputIndexΓ hM9 B) :
    chainDecodeFreeΓ hM9 B e j = 0 ∨ chainDecodeFreeΓ hM9 B e j = 1 ∨ chainDecodeFreeΓ hM9 B e j = -1 := by
  induction B with
  | single hV R => exact (chosenVineChartΓ hM9 hV).free_unit e j
  | append B hT hi hU R ih =>
    cases he : (bondUnionEquiv (Mole.garden_isMolecule G) B.isBlock (memBlock hT) hi hU).symm e <;>
      simp only [chainDecodeFreeΓ, he]
    · cases j with
      | inl j => exact (chosenVineChartΓ hM9 hT).free_unit _ j
      | inr j => exact ih _ j
    · cases j with
      | inl j => exact (chosenVineChartΓ hM9 hT).free_unit _ j
      | inr j => exact Or.inl rfl

end WaveTurbulence.GammaLow.Famb.VineEstS2
