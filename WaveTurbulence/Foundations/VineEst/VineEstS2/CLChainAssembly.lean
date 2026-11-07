/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainSplit

/-! # Source-chain assembly with its derived current CL region data -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ}

/-- A data-bearing copy of the actual source chain. Its proper prefix
blocks and CL metadata are constructed from the source theorem below. The
whole region is an index, so its four boundary nodes are preserved exactly. -/
inductive CLChainAssembly (G : Garden w) :
    {U : Finset (GBranch G.tree)} → {a b : GBranch G.tree} → CLRegionData G U a b → ℕ → Type
  | single {U a b X} (hV : G.molecule.IsVine X U a b) (R : CLRegionData G U a b) :
      CLChainAssembly G R 1
  | append {S T a b c n} {RP : CLRegionData G S a b}
      (B : CLChainAssembly G RP n) {X} (hT : G.molecule.IsVine X T b c)
      (hi : S ∩ T = {b}) (hU : G.molecule.IsBlock (S ∪ T) a c) (R : CLRegionData G (S ∪ T) a c) :
      CLChainAssembly G R (n+1)

namespace CLChainAssembly
variable {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem isBlock (B : CLChainAssembly G R n) : G.molecule.IsBlock U a b := by
  cases B with
  | single hV _ => exact hV.1
  | append _ _ _ hU _ => exact hU

theorem toSourceChain (B : CLChainAssembly G R n) : Vine.Chain G.molecule U a b n := by
  induction B with
  | single hV _ => exact Vine.Chain.single ⟨_,hV⟩
  | append _ hT hi hU _ ih =>
    exact Vine.Chain.append ih ⟨_,hT⟩ hi hU.2.2.2.1

theorem length_pos (B : CLChainAssembly G R n) : 1 ≤ n := Vine.chain_pos B.toSourceChain

end CLChainAssembly

/-- Every actual source VC in a CL region has such assembly data; prefix
and ingredient CL geometry is a conclusion, never an added source premise. -/
theorem nonempty_clChainAssembly {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {n : ℕ}
    (h : Vine.Chain G.molecule U a b n) (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) :
    Nonempty (CLChainAssembly G R n) := by
  induction h with
  | single hV => obtain ⟨X,hX⟩ := hV; exact ⟨.single hX R⟩
  | append hS hT hi _ ih =>
    obtain ⟨X,hX⟩ := hT
    have hB := chain_prefix_currentBlock G.molecule (Mole.garden_isMolecule G) hS hX hi hU
    let RP := clChainPrefixRegion hS hX hi hU R
    obtain ⟨B⟩ := ih hB RP
    exact ⟨.append B hX hi hU R⟩

/-- Canonical noncomputable selection of the proved source assembly data. -/
noncomputable def clChainAssembly {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {n : ℕ}
    (h : Vine.Chain G.molecule U a b n) (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) :
    CLChainAssembly G R n := Classical.choice (nonempty_clChainAssembly h hU R)

end WaveTurbulence.VineEstS2
