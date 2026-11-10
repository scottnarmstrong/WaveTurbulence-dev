/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceObj3
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a), B: the collection `C_1` of `G_sb`

For every SG group `S` of `𝒞` that is an HV, or has a skipped ingredient, `exists_obj` produces the residual
object in `G_sb` (an HV; a (CN) vine; a root (CL) vine) with the properties used for
`SubproChoices.Structural` and `hingeOutsideFirst`: allowed, supported on the image of `S`, and hinge atoms
occur in it only as joints.  `objects G σ` is the list of these objects.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

theorem groups_disjoint (hM : G.molecule.IsMolecule) :
    (maximalGroups G.molecule).Pairwise (fun S T => Disjoint S T) := by
  have hpart := partition_eq_maximalGroups (stage1Collection_isPartition hM)
  have := (stage1Collection_isPartition hM).2.1
  rwa [hpart] at this

/-- B1b (Mk-general form of `repC_mem_group`). -/
theorem repC_mem_groupMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) {z : GBranch G.tree} (hz : z ∈ S) {Mk : Set (Stage1.CLVine _)} :
    repC (stSt (Mk := Mk) G σ).cls z ∈ S := by
  by_cases h : ∃ u ∈ unitBlocks (Mk := Mk) G σ, z ∈ u.atoms
  · obtain ⟨u, hu, hzu⟩ := h
    rw [stSt_repC_memMk (Mk := Mk) hM σ hu hzu]
    obtain ⟨S'', hS''m, _, hu''⟩ := (mem_unitBlocksMk (Mk := Mk)).mp hu
    have hsub := groupUnitsMk_sub (Mk := Mk) (u := u) hu''
    by_cases hSS : S'' = S
    · subst hSS
      exact hsub u.isBlock.2.1
    · exact absurd hz (Finset.disjoint_left.mp (groups_disjoint hM hS''m hSm hSS) (hsub hzu)).elim
  · push Not at h
    rw [stSt_repC_noneMk (Mk := Mk) hM σ h]
    exact hz

/-- The crown of an atom of a group lies in the group. -/
theorem repC_mem_group (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroups G.molecule) {z : GBranch G.tree} (hz : z ∈ S) :
    repC (stSt G σ).cls z ∈ S := repC_mem_groupMk (Mk := ∅) hM σ hSm hz

/-- An SG group contributes an object to `C_1`. -/
@[expose] def HasObj (G : Garden w) (S : Finset (GBranch G.tree)) : Prop :=
  ((∃ a b, LGSpine.SourceVine.IsHV G.molecule S a b) ∧ ¬ ∃ a b, LGSpine.SourceVine.IsHVC G.molecule S a b) ∨
    ∃ sk : SkipData G S, (groupUnitsOf G S).skip = some sk

/-- The properties of the object of the group `S` in `G_sb` (B1a: for the marked vine set `Mk`). -/
structure ObjSpecMk (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree)) (Mk : Set (CLVine G))
    (O : Object (stSt G σ Mk).G.molecule) : Prop where
  allowed : AllowedCollectionObject (stSt G σ Mk).G O
  atoms_sub : ∀ v ∈ O.atoms, ∃ z ∈ S, v = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls z
  hinge : ∀ c, (stSt G σ Mk).cls ((stSt G σ Mk).M.ob c) ≠ none → c ∈ O.atoms → c = O.upper ∨ c = O.lower
  /-- SUBPRO amendment A2: the atoms of the object are exactly the image of a subset `A` of the group, and every
  unmerged atom of the group lies in `A` -/
  src : ∃ A : Finset (GBranch G.tree), A ⊆ S ∧ O.atoms = A.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) ∧
    (∀ z ∈ S, (stSt G σ Mk).cls z = none → z ∈ A) ∧
    ((((∃ a b, LGSpine.SourceVine.IsHV G.molecule S a b) ∧ ¬ ∃ a b, LGSpine.SourceVine.IsHVC G.molecule S a b) ∧
        (groupUnitsOf G S).skip = none ∧
        ∃ a b e, hvPick G S = some (a, b, e) ∧ O.upper = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a ∧
          O.lower = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls b ∧
          ∃ R : HyperLikeRealization (stSt G σ Mk).G.molecule O.atoms O.upper O.lower,
            O.shape = VineLikeObject.hyper R ∧ (stSt G σ Mk).M.od R.added = e) ∨
      ∃ sk : SkipData G S, (groupUnitsOf G S).skip = some sk ∧ A = sk.A ∧
        O.upper = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls sk.x ∧ O.lower = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls sk.y ∧
        (sk.bond = none → ∃ h, O.shape = VineLikeObject.vc h) ∧
        ∀ e, sk.bond = some e → ∃ R : HyperLikeRealization (stSt G σ Mk).G.molecule O.atoms O.upper O.lower,
          O.shape = VineLikeObject.hyper R ∧ (stSt G σ Mk).M.od R.added = e)

theorem SDecomp.nonmerged_mem {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {N : Molecule V D}
    {cls : V → Option V} {S A L0 R0 : Finset V} {a b x y : V} (H : SDecomp N cls S A L0 R0 a b x y)
    {z : V} (hz : z ∈ S) (hn : cls z = none) : z ∈ A := by
  have := H.hS
  rw [this] at hz
  rcases mem_union.mp hz with h | h
  · rcases mem_union.mp h with h | h
    · obtain ⟨r, hr, -⟩ := H.hLc z h z h
      rw [hn] at hr; cases hr
    · exact h
  · obtain ⟨r, hr, -⟩ := H.hRc z h z h
    rw [hn] at hr; cases hr

end WaveTurbulence.RedSplice
