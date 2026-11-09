/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.C.VCExport
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.Vine.C.VCSigma
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowSum
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.AssemblyTwist
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowCoh
-- L5b port of `WaveTurbulence.Foundations.Vine.C.VCSigma` (sha256 edf11f9ee7236451…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # VINE-C with the canonical per-unit data (PLAN-VINE "Canonical per-unit data")

For the representative state (skeleton `S`, data `D`, layering) and units `j : J` with chain assemblies
`B j : CLChainAssembly S (R j) (n j)` on pairwise disjoint atom sets `U j`:

* `unitsFamily`: the core family of all units, indexed by `Σ j, (assemblySourceFamily (B j)).CoreIndex` (the union of the
  core families of the units' pieces); `unitsSplit` its splitting into the units; `unitsStart` the τ-class start state
  (the representative with this family); `unitsRegion j` the chain region of the unit `j` (V5's `chainStart (B j)`).
* `unitsSplit_st`, `unitsSplit_reg`: the restricted state and region of the unit `j` are LITERALLY V5's
  `startState (B j) D hS layer hLayer` and `chainStart (B j)` (`rfl`), so the unit factors of the class product are
  `canonFinsetK p kind (startState (B j) D hS layer hLayer) (chainStart (B j))`, the objects of VINEEST.
* `classProd_bijOn_units`, `sum_tauClass_vineB_units`: the class product and the vine-case class sum in these terms.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineC
open WaveTurbulence.VineC
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.Reg.Skeleton WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.Represents WaveTurbulence.RegRed WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 TTree MeasureTheory WaveTurbulence.GammaLow.Famb.VineEstS2

variable {w : ℕ} {S : Garden w} {J : Type*} {U : J → Finset (GBranch S.tree)} {a b : J → GBranch S.tree}
  {R : ∀ j, CLRegionData S (U j) (a j) (b j)} {n : J → ℕ}

/-- The member index type of the units. -/
abbrev UnitsIndexΓ (B : ∀ j, CLChainAssemblyΓ γF S (R j) (n j)) := Σ j, (assemblySourceFamilyΓ (B j)).CoreIndex

theorem unitsAtoms_subΓ (B : ∀ j, CLChainAssemblyΓ γF S (R j) (n j)) (j : J) (k : (assemblySourceFamilyΓ (B j)).CoreIndex) :
    (assemblySourceFamilyΓ (B j)).coreFamily.atoms k ⊆ U j :=
  (chainStartΓ (B j)).atoms_sub k

/-- **The core family of all units.** -/
@[expose] noncomputable def unitsFamilyΓ (B : ∀ j, CLChainAssemblyΓ γF S (R j) (n j))
    (hdisj : ∀ j j', j ≠ j' → Disjoint (U j) (U j')) : CoreFamily S (UnitsIndexΓ B) where
  kind x := (assemblySourceFamilyΓ (B x.1)).coreFamily.kind x.2
  atoms x := (assemblySourceFamilyΓ (B x.1)).coreFamily.atoms x.2
  upper x := (assemblySourceFamilyΓ (B x.1)).coreFamily.upper x.2
  placement x := (assemblySourceFamilyΓ (B x.1)).coreFamily.placement x.2
  core x := (assemblySourceFamilyΓ (B x.1)).coreFamily.core x.2
  designated x := (assemblySourceFamilyΓ (B x.1)).coreFamily.designated x.2
  separated x y hxy := by
    obtain ⟨j, k⟩ := x
    obtain ⟨j', k'⟩ := y
    by_cases hj : j = j'
    · subst hj
      exact (assemblySourceFamilyΓ (B j)).coreFamily.separated k k' (fun h => hxy (h ▸ rfl))
    · intro v hv hv' _ _ _
      exact absurd (Finset.disjoint_left.mp (hdisj j j' hj) (unitsAtoms_subΓ B j k hv) (unitsAtoms_subΓ B j' k' hv'))
        not_false

/-- The splitting of the members into the units. -/
@[expose] def unitsSplitΓ (B : ∀ j, CLChainAssemblyΓ γF S (R j) (n j)) :
    UnitSplit (UnitsIndexΓ B) J (fun j => (assemblySourceFamilyΓ (B j)).CoreIndex) where
  unitOf := Sigma.fst
  emb j k := ⟨j, k⟩
  inj _ := fun _ _ h => eq_of_heq (Sigma.mk.inj h).2
  unitOf_emb _ _ := rfl
  surj x := ⟨x.2, rfl⟩

/-- **The τ-class start state**: the representative `(S, D, layer)` with the family of all units. -/
@[expose] noncomputable def unitsStartΓ (B : ∀ j, CLChainAssemblyΓ γF S (R j) (n j))
    (hdisj : ∀ j j', j ≠ j' → Disjoint (U j) (U j')) (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) : FamilyReconstruction w (UnitsIndexΓ B) where
  skeleton := S
  family := unitsFamilyΓ B hdisj
  plain := hS
  data := D
  layered := layeredReconstruction D hS layer hLayer
  decodes := D.garden_decodes hS

/-- **The chain region of the unit `j`** in the τ-class start state (V5's `chainStart (B j)`, disjoint from the other
units). -/
@[expose] noncomputable def unitsRegionΓ (B : ∀ j, CLChainAssemblyΓ γF S (R j) (n j))
    (hdisj : ∀ j j', j ≠ j' → Disjoint (U j) (U j')) (j : J) :
    UnitAt S (unitsFamilyΓ B hdisj) ((unitsSplitΓ B).Q j) where
  blk := ⟨U j, a j, b j, (B j).isBlock⟩
  cl := (R j).parentPattern
  atoms_sub x hx := by
    obtain ⟨j', k⟩ := x
    replace hx : j' = j := hx
    subst hx
    exact unitsAtoms_subΓ B j' k
  lower_ne x hx := by
    obtain ⟨j', k⟩ := x
    replace hx : j' = j := hx
    subst hx
    exact (chainStartΓ (B j')).lower_ne k
  disj x hx := by
    obtain ⟨j', k⟩ := x
    replace hx : ¬ j' = j := hx
    exact Finset.disjoint_of_subset_left (unitsAtoms_subΓ B j' k) (hdisj j' j hx)

variable (B : ∀ j, CLChainAssemblyΓ γF S (R j) (n j)) (hdisj : ∀ j j', j ≠ j' → Disjoint (U j) (U j'))
  (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

variable [Fintype J] [DecidableEq J]

end WaveTurbulence.GammaLow.Famb.VineC
