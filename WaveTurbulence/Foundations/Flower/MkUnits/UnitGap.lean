/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.SigmaCrown
public import WaveTurbulence.Foundations.Stage1.Represents.RepNU7
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD3
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSurvMK2
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK4

/-! # MK-UNITS: the unit gap of every unit at a marking (G2 for runs)

Main's `unitGap_of_selOfN` / `unitGap_stStN` / `mem_outSet_of_gsbN` (RepNU4, RepNU7) prove the SG clause G2 for the
units of the unmarked splice; their proof goes through the single-skip `UnitSpec` chain of `groupUnitsOf`.  The units
at a marking are the units of the unmarked groups (main's statement applies) and the **runs** of the marked groups
(B2a's `MarkedGroupUnits.runs`).  For a run `u` the gap is read at its lower joint:

* the last member `(T, b', u.lower)` of the run's spine is an unmarked `𝒱`-ingredient of the group (`spine` field);
* B2b's `ingredient_blockGap_of_groupGapKind` gives an internal out/in pair of `T` at `u.lower` whose gap has the
  group's kind, which the σ-restriction `selOf` makes `SG`;
* internal pairs of `T ⊆ u.atoms` are internal pairs of `u`, so B2b's `crown_eq_blockGap` (the dictionary at a CL lower
  joint) identifies that gap with `±` the crown gap `β₂ − β₃` of `u`, and main's `boundary_diff_cases` /
  `unitGap_of_cases` conclude.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.MkUnits
open Finset TTree WaveTurbulence WaveTurbulence.Mole WaveTurbulence.RegRed WaveTurbulence.RedSplice
  WaveTurbulence.VineB WaveTurbulence.LGSpine WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS2
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3.Eng WaveTurbulence.Represents WaveTurbulence.Stage1

variable {w d : ℕ} {G : Garden w}

/-- The last member of a spine ends at the spine's lower joint. -/
theorem spine_last {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    {L : List (Finset V × V × V)} {U : Finset V} {a b : V} (h : Spine M L U a b) :
    ∃ T a', (T, a', b) ∈ L ∧ Vine.IsSomeVine M T a' b ∧ T ⊆ U := by
  cases h with
  | one hv => exact ⟨_, _, List.mem_singleton_self _, hv, subset_rfl⟩
  | snoc _ hT _ _ => exact ⟨_, _, List.mem_append_right _ (List.mem_singleton_self _), hT, Finset.subset_union_right⟩

/-- Internal pairs of a sub-block are internal pairs of the block. -/
theorem isBlockGap_mono {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    {L : ℝ} {base : Mom d} {κ : D → (Fin d → ℤ)} {T U : Finset V} (hTU : T ⊆ U) {j : V} {r : Mom d}
    (h : M.IsBlockGap L base κ T j r) : M.IsBlockGap L base κ U j r := by
  obtain ⟨x₁, x₂, h1, h2, hg1, hg2, ho1, ho2, hr⟩ := h
  exact ⟨x₁, x₂, h1, h2, ⟨hTU hg1.1, hTU hg1.2⟩, ⟨hTU hg2.1, hTU hg2.2⟩, ho1, ho2, hr⟩

/-- **G2 for a run of a marked SG group.** -/
theorem runGap_of_selOf (hM : G.molecule.IsMolecule) (hp : G.IsPlain) (σ : Prescription G) {Mk : Set (CLVine G)}
    {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0)
    (hsel : VineA.NormalizedSplice.selOf (VineA.NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base z.1)
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG)
    (hmk : markedGroup G Mk S) {u : CLBlock G} (hu : u ∈ (markedUnitsOfMK hmk).runs) :
    UnitGap L γ η (fun i => base + latticePoint L (z.1 (bnodes u i))) := by
  obtain ⟨Lsp, hsp, hLsp⟩ := (markedUnitsOfMK hmk).spine u hu
  obtain ⟨T, a', hTmem, hTv, hTU⟩ := spine_last hsp
  obtain ⟨c, -, -, hI, hcT⟩ := hLsp _ hTmem
  have hκ := spliced_molecule_decoration G hp hL base roots z
  have hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 →
      gardenSource G hp (fun i => base + latticePoint L (roots i)) v = 0 :=
    fun v _ hv => gardenSource_eq_zero_of_deg_four G hp _ v hv
  have hk : VineA.NormalizedSplice.groupGapKind G L γ η base (bondIndex G z.1) S = Molecule.GapKind.SG :=
    (hsel ⟨S, hS⟩).trans hσ
  obtain ⟨X, hX⟩ := hTv
  have hI' : IsIngredient G.molecule S T := by
    rw [show T = c.atoms from hcT.symm]
    exact hI
  obtain ⟨r, hr, hkr⟩ := Flower.MkMark.ingredient_blockGap_of_groupGapKind hM L γ η base _ _ hκ hc0 hS hk hI'
    (Flower.MkMark.isBlock_swap hX.1)
  have hrU : G.molecule.IsBlockGap L base (bondIndex G z.1) u.atoms u.lower r := isBlockGap_mono hTU hr
  have hcr := Flower.MkMark.crown_eq_blockGap (regionOf u) L base base z.1 z.2.1 hrU
  refine unitGap_of_cases L γ η _ r hkr ?_ (boundary_diff_cases u L base z.1 z.2.1)
  have e2 : bnodes u 2 = u.lower.child (regionOf u).positive := rfl
  have e3 : bnodes u 3 = u.lower.child (regionOf u).negative := rfl
  simp only [e2, e3]
  simp only [cosetDecoration] at hcr
  rcases hcr with e | e
  · exact Or.inr (Or.inr (Or.inl e.symm))
  · right; right; right
    rw [← neg_sub, e, neg_neg]

/-- **G2 at a marking**: under the σ-restriction every unit of `unitBlocks G σ Mk` (a run of a marked group or a unit
of an unmarked group) has an SG gap (main's `unitGap_of_selOfN` at a marking). -/
theorem unitGap_of_selOfNMk (hM : G.molecule.IsMolecule) (hp : G.IsPlain) (σ : Prescription G)
    {Mk : Set (CLVine G)} {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration G d roots 0)
    (hsel : VineA.NormalizedSplice.selOf (VineA.NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base z.1)
    {u : CLBlock G} (hu : u ∈ unitBlocks G σ Mk) :
    UnitGap L γ η (fun i => base + latticePoint L (z.1 (bnodes u i))) := by
  obtain ⟨S, hS, hσ, hu'⟩ := mem_unitBlocksMk.mp hu
  by_cases hmk : markedGroup G Mk S
  · rw [groupUnitsMk_of_markedMK hmk] at hu'
    exact runGap_of_selOf hM hp σ hL γ η base roots z hsel hS hσ hmk hu'
  · have hu0 : u ∈ unitBlocks G σ := by
      refine mem_unitBlocksMk.mpr ⟨S, hS, hσ, ?_⟩
      rw [groupUnitsMk_empty]
      rwa [groupUnitsMk_of_not_marked hmk] at hu'
    exact unitGap_of_selOfN hM hp σ hL γ η base roots z hsel hu0

section Spliced
variable {S : Garden w}

/-- **G2, SG clause, for every decoration of `G_sb` at a marking** (main's `unitGap_stStN`). -/
theorem unitGap_stStNMk (hM : S.molecule.IsMolecule) (hS : S.IsPlain) (σ : Prescription S) {Mk : Set (CLVine S)}
    {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration (stSt S σ Mk).G d roots 0) (D : SplicedKernelData (stSt S σ Mk).G d)
    (hD : D.gapSpecification = VineA.NormalizedSplice.gapSpecificationMk S σ Mk)
    (hz : splicedGapIndicator (stSt S σ Mk).G D L γ η base z.1 ≠ 0) (j : Fin (unitBlocks S σ Mk).length) :
    VineB.UnitGap L γ η (fun i => base + latticePoint L (z.1 ((stShape hM σ Mk).hmom (unitBlkMk_disj hM σ Mk) j i))) := by
  obtain ⟨κ, hκ⟩ := exists_ext_of_shape (stShape hM σ Mk) hS (unitBlkMk_disj hM σ Mk) hL base roots z
  subst hκ
  have h1 := VineA.NormalizedSplice.splicedGapIndicator_eq_selOf_genMk hM hS σ hL γ η base roots κ _
    (fun y => bondIndex_stSt_odMk hM σ κ.1 y) D hD
  have hsel : VineA.NormalizedSplice.selOf (VineA.NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base
      κ.1 := by
    by_contra hn
    rw [if_neg hn] at h1
    exact hz h1
  have hu : unitBlkMk hM σ Mk j ∈ unitBlocks S σ Mk := List.get_mem _ _
  have hg := unitGap_of_selOfNMk hM hS σ hL γ η base roots κ hsel hu
  have heq : ∀ i, ((stShape hM σ Mk).resDec hS (unitBlkMk_disj hM σ Mk) κ).1
      ((stShape hM σ Mk).hmom (unitBlkMk_disj hM σ Mk) j i) = κ.1 (bnodes (unitBlkMk hM σ Mk j) i) := by
    intro i
    rw [SpliceShape.resDec_val]
    exact congrArg κ.1 ((stShape hM σ Mk).node_hmom (unitBlkMk_disj hM σ Mk) j i)
  simp only [heq]
  exact hg

/-- **G2 (`outSet` membership) at a marking** (main's `mem_outSet_of_gsbN`). -/
theorem mem_outSet_of_gsbNMk (hM : S.molecule.IsMolecule) (hS : S.IsPlain) (σ : Prescription S)
    {Mk : Set (CLVine S)} {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration (stSt S σ Mk).G d roots 0) (D : SplicedKernelData (stSt S σ Mk).G d)
    (hD : D.gapSpecification = VineA.NormalizedSplice.gapSpecificationMk S σ Mk)
    (hz : splicedGapIndicator (stSt S σ Mk).G D L γ η base z.1 ≠ 0) (j : Fin (unitBlocks S σ Mk).length)
    (c : Fin 4 → Fin d → ℤ)
    (hball : ∀ i, ‖(base + latticePoint L (z.1 ((stShape hM σ Mk).hmom (unitBlkMk_disj hM σ Mk) j i))) -
      latPt d (c i)‖ ≤ 1)
    (DS : SumintDatum d) (hw : DS.wBar = base)
    (hct : DS.centre = sumintBoundary (S.sign (unitBlkMk hM σ Mk j).upper.toNode) (fun i => latPt d (c i))) :
    sumintBoundary (S.sign (unitBlkMk hM σ Mk j).upper.toNode)
        (fun i => base + latticePoint L (z.1 ((stShape hM σ Mk).hmom (unitBlkMk_disj hM σ Mk) j i))) ∈
      outSet DS L γ η := by
  have hcore := (stShape hM σ Mk).hmom_outSet_core (unitBlkMk_disj hM σ Mk) j L base z.1 z.2.1
  have hg := (sumintBoundary_gap_iff (S.sign (unitBlkMk hM σ Mk j).upper.toNode) L γ η
    (fun i => base + latticePoint L (z.1 ((stShape hM σ Mk).hmom (unitBlkMk_disj hM σ Mk) j i)))).mpr
    (unitGap_stStNMk hM hS σ hL γ η base roots z D hD hz j)
  refine ⟨fun c' => ⟨?_, ?_⟩, hcore.2, hg.1, hg.2⟩
  · rw [hw]; exact hcore.1 c'
  · rw [hct]
    exact sumintBoundary_close _ _ _ hball c'

end Spliced

end WaveTurbulence.Flower.MkUnits
