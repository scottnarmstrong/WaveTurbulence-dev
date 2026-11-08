/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkUnits.Defs
public import WaveTurbulence.Foundations.Flower.MkDefs.Intrinsic
public import WaveTurbulence.Foundations.Vine.A.VineUnitSelectedMK
public import WaveTurbulence.Foundations.VineEst.VineEstS3.VineMonotone
public import WaveTurbulence.Foundations.Molecule.BlockParent

/-! # B3s MK-SLOTS (integration): the admissibility predicate of the marked twist closure

B3 (`MkUnits`) proves its marked-unit results under main's `TwistClosedAdm p A Adm` and the admissibility of the
run assembly's start state `Adm (startAt a (mkAt mkF a))`. The consumer (B4) has `MarkedTwistClosed` at the concrete
marking rule `protSkOf` and a fine marking `mkF ⊇ markI`. With

`AdmP B := ∀ i, ∀ b ∈ B.family.atoms i, b ≠ B.family.upper i → ¬ protSkOf … B b`

(no protected vertex in the near region of a non-upper atom of a family member):

* `twistClosedAdm_of_marked`: `MarkedTwistClosed p A (protSkOf …)` is `TwistClosedAdm p A AdmP` (same body);
* `startAt_admP`: the start state of the run assembly at `mkAt mkF a` is admissible.

Proof of the second. The members of the start family are the pieces of the aligned chain assemblies of the units of
`unitBlocks G σ Mk` (`unitsStart`). The pieces of a chain assembly are the members of a spine of its region
(`assembly_exists_spine`); the spine of a block chain is unique (`RedSplice.Spine.unique`), and every unit has a
spine of `𝒱₀ \ Mk` vines (main's `unitBlocks_selected_spineMk`). So every piece has the atoms of a vine `c` of
`𝒱₀ \ Mk` (`alignedPiece_mem_vinesV0`), and a non-upper atom of the piece is a non-upper atom of `c` (parent flow:
an interior atom and the lower joint of a CL piece have their parent inside, the upper joint of `c` does not;
`ne_upper_of_piece`). A protected vertex in its near region marks `c` (`markI`, after transporting the protected set
along `sourceLayer_reconstructs`), so `c ∈ mkF a.prime ∩ 𝒱₀ = mkAt mkF a`, against `c ∉ Mk`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice (Prescription vinesV0 unitBlocks Spine)
open WaveTurbulence.VineEstS2 (CLChainAssembly assemblyPieceAt)
open WaveTurbulence.Represents (TwistClosedAdm)

namespace WaveTurbulence.Flower.MkSlots

/-! ## The admissibility predicate and the twist closure -/

/-- **The admissibility of a family reconstruction for the marked twist closure**: no non-upper atom of a family
member is protected (for the concrete rule `protSkOf` with the intrinsic capped pins and selection). -/
def AdmP (R : ℕ) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel : Fin (2 * R) → Option ℕ) : ∀ {ι : Type}, LFTwist.FamilyReconstruction (2 * R) ι → Prop :=
  fun {_ι} B => ∀ i, ∀ b ∈ B.family.atoms i, b ≠ B.family.upper i →
    ¬ protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel) B b

/-- **The marked twist closure is main's admissible twist closure at `AdmP`** (the two bodies coincide). -/
theorem twistClosedAdm_of_marked {R p : ℕ} {A : Finset (LayeredGarden (2 * R))} {J : Finset (Fin (2 * R))}
    {pat : Fin (2 * R) → FixPat} {t s : ℝ} {kSel : Fin (2 * R) → Option ℕ}
    (h : MarkedTwistClosed p A (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel))) :
    TwistClosedAdm p A (AdmP R J pat t s kSel) :=
  fun kind ι B L hp hc hA hadm => h kind ι B L hp hc hA hadm

/-! ## The pieces of a unit assembly are unmarked `𝒱₀` vines -/

section Chain
variable {w : ℕ}

/-- **The pieces of a chain assembly are the members of a spine of its region.** -/
theorem assembly_exists_spine {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : RegRed.CLRegionData G U a b} {n : ℕ} (B : CLChainAssembly G R n) :
    ∃ L, Spine G.molecule L U a b ∧ ∀ i, ((assemblyPieceAt B i).atoms, (assemblyPieceAt B i).upper,
      (assemblyPieceAt B i).lower) ∈ L := by
  induction B with
  | single hV R => exact ⟨_, Spine.one ⟨_, hV⟩, fun _ => List.mem_singleton_self _⟩
  | @append S T a' b' c' n' RP B X hT hi hU R ih =>
    obtain ⟨L, hL, hmem⟩ := ih
    refine ⟨L ++ [(T, b', c')], Spine.snoc hL ⟨X, hT⟩ hi hU.2.2.2.1, fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_left _ (hmem j)

/-- **Every piece of the aligned assembly of a unit has the atoms of a vine of `𝒱₀ \ Mk`.** The unit's spine of
`𝒱₀ \ Mk` vines (`unitBlocks_selected_spineMk`) is the spine of the assembly (`Spine.unique`). -/
theorem alignedPiece_mem_vinesV0 {G : Garden w} (σ : Prescription G) (Mk : Set (Stage1.CLVine G))
    (j : Fin (unitBlocks G σ Mk).length) (i : Fin (Represents.unitN σ j)) :
    ∃ c ∈ vinesV0 G σ Mk, c.atoms =
      (assemblyPieceAt (VineAlign.alignedAssemblyMk (Mole.garden_isMolecule G) σ Mk j) i).atoms := by
  obtain ⟨L, hL, hmem⟩ := assembly_exists_spine (VineAlign.alignedAssemblyMk (Mole.garden_isMolecule G) σ Mk j)
  have hu : VineB.unitBlkMk (Mole.garden_isMolecule G) σ Mk j ∈ unitBlocks G σ Mk := List.get_mem _ _
  obtain ⟨L', hL', hsel⟩ := VineA.unitBlocks_selected_spineMk hu
  have hLL : L = L' :=
    Spine.unique (Mole.garden_isMolecule G) hL hL' (VineB.unitBlkMk (Mole.garden_isMolecule G) σ Mk j).isBlock
  subst hLL
  obtain ⟨c, hc, he⟩ := hsel _ (hmem i)
  exact ⟨c, hc, he⟩

/-- **A non-upper atom of a piece is a non-upper atom of every CL vine with the atoms of the piece** (parent flow: an
interior atom of the piece and its lower joint have their parent inside it, the upper joint of a CL vine does not). -/
theorem ne_upper_of_piece {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : RegRed.CLRegionData G U a b} {n : ℕ} (B : CLChainAssembly G R n) (i : Fin n) (c : Stage1.CLVine G)
    (hc : c.atoms = (assemblyPieceAt B i).atoms) {v : GBranch G.tree} (hv : v ∈ (assemblyPieceAt B i).atoms)
    (hne : v ≠ (assemblyPieceAt B i).upper) : v ≠ c.upper := by
  rintro rfl
  apply c.notParentUpper
  rw [hc]
  by_cases hl : c.upper = (assemblyPieceAt B i).lower
  · rw [hl]
    exact (VineEstS3.assemblyPiece_cl B i).2
  · exact Mole.block_interior_has_parent G (assemblyPieceAt B i).vine.1 hv hne hl

/-- **Every non-upper atom of a member of the start family is a non-upper atom of a vine of `𝒱₀ \ Mk`.** -/
theorem startAt_nonUpper_vinesV0 (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton))
    (i : VineC.UnitsIndex (VineAlign.alignedAssemblyMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk))
    {b : GBranch a.prime.skeleton.tree} (hb : b ∈ (MkUnits.startAt a Mk).family.atoms i)
    (hbne : b ≠ (MkUnits.startAt a Mk).family.upper i) :
    ∃ c ∈ vinesV0 a.prime.skeleton a.totalSigma Mk, b ∈ c.atoms ∧ b ≠ c.upper := by
  obtain ⟨j, k⟩ := i
  obtain ⟨c, hc, hca⟩ := alignedPiece_mem_vinesV0 a.totalSigma Mk j k.1
  refine ⟨c, hc, ?_, ne_upper_of_piece _ k.1 c hca hb hbne⟩
  rw [hca]
  exact hb

end Chain

/-! ## The start state is admissible -/

/-- Transport of a protected vertex along an equality of layered gardens. -/
theorem exists_protI_of_layered_eq {w : ℕ} {LG LG' : LayeredGarden w} (h : LG = LG') (J : Finset (Fin w))
    (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ) (N : Set (Reg.Skeleton.Address w))
    (hx : ∃ x ∈ protectedSet LG J (fixCap LG J pat t s) (selSetCap LG J kSel), x.1 ∈ N) :
    ∃ x ∈ protI LG' J pat t s kSel, x.1 ∈ N := by
  subst h
  exact hx

/-- **The start state of the run assembly is admissible** at every marked set `Mk` containing the marked `𝒱₀`
vines (`markI ∩ 𝒱₀ ⊆ Mk`). -/
theorem startAt_admP_of_sub {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel : Fin (2 * R) → Option ℕ) (a : PrescribedPrimeGarden (2 * R)) (Mk : Set (Stage1.CLVine a.prime.skeleton))
    (hMk : ∀ c ∈ markI J pat t s kSel a.prime, c ∈ vinesV0 a.prime.skeleton a.totalSigma → c ∈ Mk) :
    AdmP R J pat t s kSel (MkUnits.startAt a Mk) := by
  intro i b hb hbne hprot
  obtain ⟨c, hc, hbc, hbu⟩ := startAt_nonUpper_vinesV0 a Mk i hb hbne
  obtain ⟨x, hx, hxn⟩ := hprot
  have hpx := exists_protI_of_layered_eq (VineAlign.sourceLayer_reconstructs a) J pat t s kSel _ ⟨x, hx, hxn⟩
  have hm : c ∈ markI J pat t s kSel a.prime :=
    ⟨RedSplice.vinesV0_subsetMk _ _ _ hc, b, hbc, hbu, hpx⟩
  exact (RedSplice.mem_vinesV0.mp hc).2 (hMk c hm (RedSplice.mem_vinesV0.mp hc).1)

/-- **The start state of the run assembly at `mkAt mkF a` is admissible** for every fine marking `mkF ⊇ markI`. -/
theorem startAt_admP {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel : Fin (2 * R) → Option ℕ) (a : PrescribedPrimeGarden (2 * R)) (mkF : Stage1Mk.MarkFn (2 * R))
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B) :
    AdmP R J pat t s kSel (MkUnits.startAt a (MkUnits.mkAt mkF a)) :=
  startAt_admP_of_sub J pat t s kSel a _ fun _ hm h0 => ⟨hsub a.prime hm, h0⟩

end WaveTurbulence.Flower.MkSlots
