/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnitsL.RegionL
public import WaveTurbulence.Foundations.Flower.MkUnits.WMember

/-! # MK-UNITS-L (B3-2): the weighted member identity with per-unit top filters

* `skelValW_slotFWW`, `valueSelW_modesWL`: Stage1WVine's `skelVal_slotFW`, `valueSelW_modesW` with the units' top
  weights: the value of a reconstruction with the decoration weight `fwWeight · topWt(collapse κ)` is the outer mode sum
  with the generic unit factors `unitKernelMGW (slotFWW … Wt)`.
* `member_ker_eqWMkL`, `memberRBMkL`, `member_hVWMkL`, `member_integWMkL`, `member_hsmWMkL`: B3's run-class member
  identity (`MkUnits/WMember`) with the extra weight `E`, presented on the member by the unit top filters `SU`: the
  member's unit kernels are V5W-2L's `unitRecenteredFWL p (g j₁) (SU j) y (y.2 j) …`.

Adapted from `Flower/Stage1WVine/WMember1.lean` and `Flower/MkUnits/WMember.lean` (see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.MkUnitsL
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.VineC
  WaveTurbulence.LFTwist WaveTurbulence.VineAlign WaveTurbulence.Stage1 WaveTurbulence.RepAnalytic WaveTurbulence.VineA
  WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence.Flower.V5W2L (topFilterWeightL unitRecenteredFWL)
open WaveTurbulence.VineSpaceK (nodeWeight)

/-! ## The top weights at a skeleton decoration -/

section TopWt
variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J]

end TopWt

/-! ## The weighted value of a reconstruction in mode form -/

/-! ## The member identity of a run class with per-unit top filters -/

variable {p : ℕ} {kind : Bool}

/-- The top weight of a run-class member: `topFilterWeightL (SU j)` at the top of its unit `j`. -/
abbrev memberTopW {R d : ℕ} {a : PrescribedPrimeGarden (2 * R)} {mk : Stage1Mk.MarkFn (2 * R)}
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk)))
    (SU : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → List ℝ) :
    GBranch y.1.skeleton.tree → (Fin 4 → Mom d) → ℂ :=
  topWeightOf (fun j => (y.2 j).blk.a) SU

theorem memberTopW_apply {R d : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
    (SU : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → List ℝ) (j) :
    memberTopW (d := d) y SU (y.2 j).blk.a = topFilterWeightL (SU j) :=
  topWeightOf_apply (top := fun j => (y.2 j).blk.a) (upper_injective (source_disjMk a mk y hy)) SU j

/-- For a run-class member, the generic unit factor of the weighted slot family with the member's top filters is
V5W-2L's pinned `unitRecenteredFWL` (B3's `member_ker_eqWMk` with `SU`). -/
theorem member_ker_eqWMkL {R d : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk) (L γ δ : ℝ)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (base : Mom d) (g : Fin (2 * R) → Mom d → ℂ)
    (hcan : IsCanonGC (p + 1) y.1.layered) (hlay : ∀ x, stateLayer y.1 x ≤ p)
    (SU : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → List ℝ) :
    unitKernelMGW (fun j => unitClBlock (y.2 j)) y.1.data y.1.plain
        (slotFWW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) L γ δ h p g (memberTopW y SU))
        L γ δ (stateLayer y.1) base =
      fun (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) (lam : ℤ) (t : Fin 3 → ℝ)
          (k : Fin 4 → Mom d) =>
        unitRecenteredFWL p
          (g (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper.1.1) (SU j)
          y.1 (y.2 j) L γ δ
          (unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) h j) base
          (modW lam) (t 0) (t 1) (t 2) (k 0) (k 1) (k 2) (k 3) := by
  funext j lam t k
  rw [unitKernelMG_slotFWW_eq y.1 y.2 (stateLayer y.1) (stateLayer_isLayering y.1) (stateLayer_spec y.1) L γ δ h p g
    base hcan hlay (memberTopW y SU) SU (fun j => memberTopW_apply a mk y hy SU j) j lam t k]
  have hidx := source_upper_tree_indexMk a mk y hy j
  have h1 : unitProfile (fun j => unitClBlock (y.2 j)) h j =
      unitProfile (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) h j := by
    funext q
    unfold unitProfile
    exact congrArg₂ (fun u v => h q u v) hidx hidx
  have h2 : g (y.2 j).blk.a.1.1 =
      g (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper.1.1 :=
    congrArg g hidx
  rw [h1, h2]

end WaveTurbulence.Flower.MkUnitsL
