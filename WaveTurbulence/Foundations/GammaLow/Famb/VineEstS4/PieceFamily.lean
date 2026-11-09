/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.VineMonotone
public import WaveTurbulence.Foundations.Molecule.TwistSourceFamily
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.Molecule.TwistSourceFamily
public import WaveTurbulence.Foundations.VineEst.VineEstS4.PieceFamily
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.VineMonotone
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS4.PieceFamily` (sha256 d6d5281648351b90…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # The source vine family of a chain assembly (V5 Step 4a)

The pieces of a (CL) vine chain `U` form a `Twist.SourceVineFamily` (TARGET Definition `lftwist`, L1429: "the
collection of (CL) vines `U`"): every piece is a vine with the CL parent pattern (`assemblyPiece_cl`) and distinct
pieces meet in at most the common joint (`S ∩ T = {b}` of the chain construction).  Its core members are the vines
twisted by the LF family machinery.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS4
open WaveTurbulence.VineEstS4
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.Twist TTree RegRed WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- Distinct pieces of a chain assembly have separated atom sets (they meet in at most one joint atom). -/
theorem assemblyPiece_separatedΓ (B : CLChainAssemblyΓ γF G R n) (i j : Fin n) (hij : i ≠ j) :
    SeparatedGroups (assemblyPieceAtΓ B i).atoms (assemblyPieceAtΓ B j).atoms := by
  induction B with
  | single hV R => exact absurd (Subsingleton.elim i j) hij
  | @append S T a' b' c' n' RP B hT hi hU R ih =>
    have key : ∀ k : Fin n', SeparatedGroups T (assemblyPieceAtΓ B k).atoms := by
      intro k x hx hx' y hy hy'
      have h1 : x ∈ S ∩ T := Finset.mem_inter.mpr ⟨assemblyPiece_subsetΓ B k hx', hx⟩
      have h2 : y ∈ S ∩ T := Finset.mem_inter.mpr ⟨assemblyPiece_subsetΓ B k hy', hy⟩
      rw [hi] at h1 h2
      exact (Finset.mem_singleton.mp h1).trans (Finset.mem_singleton.mp h2).symm
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩ <;> rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨l, rfl⟩
    · exact absurd rfl hij
    · exact key l
    · intro x hx hx' y hy hy'
      exact (key k y hy' hy x hx' hx).symm
    · exact ih k l (fun h => hij (congrArg Fin.succ h))

/-- The family of pieces of a chain assembly (terminal vine first). -/
noncomputable def assemblySourceFamilyΓ (B : CLChainAssemblyΓ γF G R n) : Twist.SourceVineFamilyΓ G n where
  kind i := (assemblyPieceAtΓ B i).label
  atoms i := (assemblyPieceAtΓ B i).atoms
  upper i := (assemblyPieceAtΓ B i).upper
  lower i := (assemblyPieceAtΓ B i).lower
  cl i := assemblyPiece_clΓ B i
  separated i j hij := assemblyPiece_separatedΓ B i j hij

end WaveTurbulence.GammaLow.Famb.VineEstS4
