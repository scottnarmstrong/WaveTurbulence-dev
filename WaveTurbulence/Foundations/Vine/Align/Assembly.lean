/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG15
public import WaveTurbulence.Foundations.Vine.C.VCSigma
public import WaveTurbulence.Foundations.Vine.A.VineFineRecovery
/-! Exact source ingredients of the unit assemblies. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS2 VineEstS3 VineEstS4 VineA RedSplice Stage1 Twist RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}

/-- Each assembly piece is an ingredient of the actual source chain. -/
theorem assemblyPiece_ingredient (B : CLChainAssembly G R n) (i : Fin n) :
    Vine.ChainIngredient G.molecule U a b n (assemblyPieceAt B i).atoms
      (assemblyPieceAt B i).upper (assemblyPieceAt B i).lower := by
  induction B with
  | single hV R => exact .single ⟨_, hV⟩
  | append B hT hi hU R ih =>
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · exact .append_last B.toSourceChain ⟨_, hT⟩ hi hU.2.2.2.1
    · exact .append_left (ih k) ⟨_, hT⟩ hi hU.2.2.2.1

/-- A vine contained in an assembly is contained in one of its actual pieces. -/
theorem vine_subset_assemblyPiece (B : CLChainAssembly G R n)
    {A : Finset (GBranch G.tree)} {x y : GBranch G.tree} {X : VineType}
    (hA : G.molecule.IsVine X A x y) (hAU : A ⊆ U) :
    ∃ i, A ⊆ (assemblyPieceAt B i).atoms := by
  induction B with
  | single hV R => exact ⟨0, hAU⟩
  | append B hT hi hU R ih =>
    rcases Vine.vine_in_terminal_split G.molecule (Mole.garden_isMolecule G)
      hT.1 hU (Vine.chain_joints_mem B.toSourceChain).2 hA hAU with hAS | hAT
    · obtain ⟨i, hi⟩ := ih hAS
      exact ⟨i.succ, hi⟩
    · exact ⟨0, hAT⟩

/-- The CL vine of an actual assembly piece, with the source's ordered joints. -/
noncomputable def assemblyVine (B : CLChainAssembly G R n) (i : Fin n) : CLVine G where
  atoms := (assemblyPieceAt B i).atoms
  upper := (assemblyPieceAt B i).upper
  lower := (assemblyPieceAt B i).lower
  isVine := ⟨_, (assemblyPieceAt B i).vine⟩
  notParentUpper := (assemblyPiece_cl B i).1
  parentLower := (assemblyPiece_cl B i).2

/-- B1b (Mk-general form of `assemblyVine_mem`). -/
theorem assemblyVine_memMk {σ : Prescription G} {u : CLBlock G}
    {Mk : Set (Stage1.CLVine _)} (hu : u ∈ unitBlocks (Mk := Mk) G σ) {n : ℕ} (B : CLChainAssembly G (VineB.regionOf u) n) (i : Fin n) :
    assemblyVine B i ∈ vinesV0 (Mk := Mk) G σ := by
  have hi : (assemblyPieceAt B i).atoms ∈ unitIngredients (Mk := Mk) G σ :=
    ⟨u, hu, u.upper, u.lower, n, _, _, assemblyPiece_ingredient B i⟩
  obtain ⟨c, hc, he⟩ := (mem_unitIngredients_iffMk (Mk := Mk)).mp hi
  have hcv : c = assemblyVine B i := clVine_eq_of_atoms he
  exact hcv ▸ hc

end WaveTurbulence.VineAlign
