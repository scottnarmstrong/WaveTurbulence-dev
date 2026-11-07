/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLChainAssembly
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLAssemblyPieces
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Region

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
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.VineEstS2 WaveTurbulence.RegRed TTree

variable {w : ℕ} {G : Garden w} (P : CorePlacement G)

theorem twistedAtoms_union (S T : Finset (GBranch G.tree)) :
    twistedAtoms G P (S ∪ T) = twistedAtoms G P S ∪ twistedAtoms G P T := by
  apply Finset.ext
  intro x
  obtain ⟨v, rfl⟩ := (coreBranchEquiv G P).surjective x
  have h1 := mem_twistedAtoms G P (S ∪ T) v
  have h2 := mem_twistedAtoms G P S v
  have h3 := mem_twistedAtoms G P T v
  exact h1.trans (Finset.mem_union.trans ((or_congr h2.symm h3.symm).trans Finset.mem_union.symm))

theorem twistedAtoms_inter_singleton {S T : Finset (GBranch G.tree)} {b : GBranch G.tree} (h : S ∩ T = {b}) :
    twistedAtoms G P S ∩ twistedAtoms G P T = {coreBranchEquiv G P b} := by
  apply Finset.ext
  intro x
  obtain ⟨v, rfl⟩ := (coreBranchEquiv G P).surjective x
  have h2 := mem_twistedAtoms G P S v
  have h3 := mem_twistedAtoms G P T v
  have h4 : v ∈ S ∩ T ↔ v ∈ ({b} : Finset (GBranch G.tree)) := by rw [h]
  have h5 : v ∈ ({b} : Finset (GBranch G.tree)) ↔ coreBranchEquiv G P v = coreBranchEquiv G P b :=
    Finset.mem_singleton.trans (coreBranchEquiv G P).injective.eq_iff.symm
  exact Finset.mem_inter.trans ((and_congr h2 h3).trans (Finset.mem_inter.symm.trans (h4.trans
    (h5.trans Finset.mem_singleton.symm))))

/-- A vine chain of the garden is a vine chain of its unit twist. -/
theorem chain_twistedAtoms {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {n : ℕ}
    (h : Vine.Chain G.molecule U a b n) :
    Vine.Chain (unitTwistGarden G P).molecule (twistedAtoms G P U) (coreBranchEquiv G P a)
      (coreBranchEquiv G P b) n := by
  induction h with
  | single hV =>
    obtain ⟨X, hX⟩ := hV
    exact Vine.Chain.single ⟨X, isVine_twistedAtoms G P hX⟩
  | append hS hT hi hac ih =>
    obtain ⟨X, hX⟩ := hT
    rw [twistedAtoms_union]
    exact Vine.Chain.append ih ⟨X, isVine_twistedAtoms G P hX⟩ (twistedAtoms_inter_singleton P hi)
      (fun he => hac ((coreBranchEquiv G P).injective he))

/-- The assembly of the twisted garden with the transported pieces. -/
noncomputable def CLChainAssembly.twist :
    {U : Finset (GBranch G.tree)} → {a b : GBranch G.tree} → {R : CLRegionData G U a b} → {n : ℕ} →
    CLChainAssembly G R n →
    (U' : Finset (GBranch (unitTwistGarden G P).tree)) → (a' b' : GBranch (unitTwistGarden G P).tree) →
    U' = twistedAtoms G P U → a' = coreBranchEquiv G P a → b' = coreBranchEquiv G P b →
    (R' : CLRegionData (unitTwistGarden G P) U' a' b') → CLChainAssembly (unitTwistGarden G P) R' n
  | _, _, _, _, _, .single hV _ => fun U' a' b' hU ha hb R' => by
    subst hU ha hb
    exact .single (isVine_twistedAtoms G P hV) R'
  | _, _, _, _, _, .append B hT hi hU R => fun U' a' b' hU' ha hb R' => by
    subst ha hb
    have hU2 : U' = twistedAtoms G P _ ∪ twistedAtoms G P _ := hU'.trans (twistedAtoms_union P _ _)
    subst hU2
    have hT' := isVine_twistedAtoms G P hT
    have hi' := twistedAtoms_inter_singleton P hi
    have hU'' : (unitTwistGarden G P).molecule.IsBlock (twistedAtoms G P _ ∪ twistedAtoms G P _) _ _ :=
      (twistedAtoms_union P _ _) ▸ isBlock_twistedAtoms G P hU
    have hS' := chain_twistedAtoms P B.toSourceChain
    exact .append (CLChainAssembly.twist B _ _ _ rfl rfl rfl
      (clChainPrefixRegion hS' hT' hi' hU'' R')) hT' hi' hU'' R'

/-- The pieces of the twisted assembly are the transported pieces: same vine types, atoms and joints
transported by `coreBranchEquiv`. -/
theorem assemblyPieceAt_twist {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
    {n : ℕ} (B : CLChainAssembly G R n) (U' : Finset (GBranch (unitTwistGarden G P).tree))
    (a' b' : GBranch (unitTwistGarden G P).tree) (hU : U' = twistedAtoms G P U)
    (ha : a' = coreBranchEquiv G P a) (hb : b' = coreBranchEquiv G P b)
    (R' : CLRegionData (unitTwistGarden G P) U' a' b') (i : Fin n) :
    (assemblyPieceAt (CLChainAssembly.twist P B U' a' b' hU ha hb R') i).vineType =
        (assemblyPieceAt B i).vineType ∧
      (assemblyPieceAt (CLChainAssembly.twist P B U' a' b' hU ha hb R') i).atoms =
        twistedAtoms G P (assemblyPieceAt B i).atoms ∧
      (assemblyPieceAt (CLChainAssembly.twist P B U' a' b' hU ha hb R') i).upper =
        coreBranchEquiv G P (assemblyPieceAt B i).upper ∧
      (assemblyPieceAt (CLChainAssembly.twist P B U' a' b' hU ha hb R') i).lower =
        coreBranchEquiv G P (assemblyPieceAt B i).lower := by
  induction B generalizing U' a' b' with
  | single hV R0 =>
    subst hU ha hb
    exact ⟨rfl, rfl, rfl, rfl⟩
  | append B hT hi hU0 R0 ih =>
    subst ha hb
    have hU2 : U' = twistedAtoms G P _ ∪ twistedAtoms G P _ := hU.trans (twistedAtoms_union P _ _)
    subst hU2
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ih _ _ _ rfl rfl rfl _ j

end WaveTurbulence.VineEstS4
