/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.VineMonotone
public import WaveTurbulence.Foundations.Molecule.TwistSourceFamily

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
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.Twist TTree RegRed

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- Distinct pieces of a chain assembly have separated atom sets (they meet in at most one joint atom). -/
theorem assemblyPiece_separated (B : CLChainAssembly G R n) (i j : Fin n) (hij : i ≠ j) :
    SeparatedGroups (assemblyPieceAt B i).atoms (assemblyPieceAt B j).atoms := by
  induction B with
  | single hV R => exact absurd (Subsingleton.elim i j) hij
  | @append S T a' b' c' n' RP B X hT hi hU R ih =>
    have key : ∀ k : Fin n', SeparatedGroups T (assemblyPieceAt B k).atoms := by
      intro k x hx hx' y hy hy'
      have h1 : x ∈ S ∩ T := Finset.mem_inter.mpr ⟨assemblyPiece_subset B k hx', hx⟩
      have h2 : y ∈ S ∩ T := Finset.mem_inter.mpr ⟨assemblyPiece_subset B k hy', hy⟩
      rw [hi] at h1 h2
      exact (Finset.mem_singleton.mp h1).trans (Finset.mem_singleton.mp h2).symm
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩ <;> rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨l, rfl⟩
    · exact absurd rfl hij
    · exact key l
    · intro x hx hx' y hy hy'
      exact (key k y hy' hy x hx' hx).symm
    · exact ih k l (fun h => hij (congrArg Fin.succ h))

/-- The family of pieces of a chain assembly (terminal vine first). -/
noncomputable def assemblySourceFamily (B : CLChainAssembly G R n) : SourceVineFamily G n where
  kind i := (assemblyPieceAt B i).vineType
  atoms i := (assemblyPieceAt B i).atoms
  upper i := (assemblyPieceAt B i).upper
  lower i := (assemblyPieceAt B i).lower
  vine i := (assemblyPieceAt B i).vine
  cl i := assemblyPiece_cl B i
  separated i j hij := assemblyPiece_separated B i j hij

end WaveTurbulence.VineEstS4
