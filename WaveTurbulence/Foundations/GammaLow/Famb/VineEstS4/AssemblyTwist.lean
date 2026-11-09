/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainAssembly
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieces
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Region
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS4.AssemblyTwist
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyPieces
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainAssemblyOf
public import WaveTurbulence.Foundations.GammaLow.Famb.TVineIso
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS4.AssemblyTwist` (sha256 bca6f90cabbd48b9…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # The chain assembly of a twisted garden (V5 Step 4b, packet 2, P2.1)

`CLChainAssembly.twist P B ...`: the assembly of the twisted garden `unitTwistGarden G P` whose pieces are the twisted
pieces of `B` (same vine types, atoms/joints transported by `coreBranchEquiv`).  It is built by recursion on `B`; the prefix
CL regions are recovered from the whole region by `clChainPrefixRegion`.  `assemblyPieceAt_twist`: the pieces are exactly the
transported ones.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS4
open WaveTurbulence.VineEstS4
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.VineEstS2 WaveTurbulence.RegRed TTree WaveTurbulence.GammaLow.Famb.VineEstS2

variable {w : ℕ} {G : Garden w} (P : CorePlacement G)

/-- A member of `𝒱_γ` of the garden is a member of `𝒱_γ` of its unit twist (main's `isVine_twistedAtoms`, with the
T-vines by `TVineIso.iso_isSomeVine`). -/
theorem isSomeVine_twistedAtoms {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hV : FinalCount.Src.IsSomeVine γF G.molecule S a b) :
    FinalCount.Src.IsSomeVine γF (unitTwistGarden G P).molecule (twistedAtoms G P S) (coreBranchEquiv G P a)
      (coreBranchEquiv G P b) :=
  TVineIso.iso_isSomeVine G (unitTwistGarden G P) (unitTwistDirectedIso G P) hV

/-- A source chain over `𝒱_γ` of the garden is one of its unit twist (main's `chain_twistedAtoms`). -/
theorem chain_twistedAtomsΓ {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {n : ℕ}
    (h : FinalCount.Src.Chain γF G.molecule U a b n) :
    FinalCount.Src.Chain γF (unitTwistGarden G P).molecule (twistedAtoms G P U) (coreBranchEquiv G P a)
      (coreBranchEquiv G P b) n := by
  induction h with
  | single hV => exact .single (isSomeVine_twistedAtoms P hV)
  | append hS hT hi hac ih =>
    rw [twistedAtoms_union]
    exact .append ih (isSomeVine_twistedAtoms P hT) (twistedAtoms_inter_singleton P hi)
      (fun he => hac ((coreBranchEquiv G P).injective he))

/-- The assembly of the twisted garden with the transported pieces. -/
noncomputable def CLChainAssemblyΓ.twistΓ :
    {U : Finset (GBranch G.tree)} → {a b : GBranch G.tree} → {R : CLRegionData G U a b} → {n : ℕ} →
    CLChainAssemblyΓ γF G R n →
    (U' : Finset (GBranch (unitTwistGarden G P).tree)) → (a' b' : GBranch (unitTwistGarden G P).tree) →
    U' = twistedAtoms G P U → a' = coreBranchEquiv G P a → b' = coreBranchEquiv G P b →
    (R' : CLRegionData (unitTwistGarden G P) U' a' b') → CLChainAssemblyΓ γF (unitTwistGarden G P) R' n
  | _, _, _, _, _, .single hV _ => fun U' a' b' hU ha hb R' => by
    subst hU ha hb
    exact .single (isSomeVine_twistedAtoms P hV) R'
  | _, _, _, _, _, .append B hT hi hU R => fun U' a' b' hU' ha hb R' => by
    subst ha hb
    have hU2 : U' = twistedAtoms G P _ ∪ twistedAtoms G P _ := hU'.trans (twistedAtoms_union P _ _)
    subst hU2
    have hT' := isSomeVine_twistedAtoms P hT
    have hi' := twistedAtoms_inter_singleton P hi
    have hU'' : (unitTwistGarden G P).molecule.IsBlock (twistedAtoms G P _ ∪ twistedAtoms G P _) _ _ :=
      (twistedAtoms_union P _ _) ▸ isBlock_twistedAtoms G P hU
    have hS' := chain_twistedAtomsΓ P B.toSourceChain
    exact .append (CLChainAssemblyΓ.twistΓ B _ _ _ rfl rfl rfl
      (clChainPrefixRegionΓ hS' hT' hi' hU'' R')) hT' hi' hU'' R'

/-- The pieces of the twisted assembly are the transported pieces: atoms and joints transported by
`coreBranchEquiv` (main's statement also equates the drawn types; over `𝒱_γ` the correspondence of the pieces is
`AsmCorrΓ`, with bad-ness and cohmol groups). -/
theorem assemblyPieceAt_twistΓ {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
    {n : ℕ} (B : CLChainAssemblyΓ γF G R n) (U' : Finset (GBranch (unitTwistGarden G P).tree))
    (a' b' : GBranch (unitTwistGarden G P).tree) (hU : U' = twistedAtoms G P U)
    (ha : a' = coreBranchEquiv G P a) (hb : b' = coreBranchEquiv G P b)
    (R' : CLRegionData (unitTwistGarden G P) U' a' b') (i : Fin n) :
    (assemblyPieceAtΓ (CLChainAssemblyΓ.twistΓ P B U' a' b' hU ha hb R') i).atoms =
        twistedAtoms G P (assemblyPieceAtΓ B i).atoms ∧
      (assemblyPieceAtΓ (CLChainAssemblyΓ.twistΓ P B U' a' b' hU ha hb R') i).upper =
        coreBranchEquiv G P (assemblyPieceAtΓ B i).upper ∧
      (assemblyPieceAtΓ (CLChainAssemblyΓ.twistΓ P B U' a' b' hU ha hb R') i).lower =
        coreBranchEquiv G P (assemblyPieceAtΓ B i).lower := by
  induction B generalizing U' a' b' with
  | single hV R0 =>
    subst hU ha hb
    exact ⟨rfl, rfl, rfl⟩
  | append B hT hi hU0 R0 ih =>
    subst ha hb
    have hU2 : U' = twistedAtoms G P _ ∪ twistedAtoms G P _ := hU.trans (twistedAtoms_union P _ _)
    subst hU2
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨rfl, rfl, rfl⟩
    · exact ih _ _ _ rfl rfl rfl _ j

end WaveTurbulence.GammaLow.Famb.VineEstS4
