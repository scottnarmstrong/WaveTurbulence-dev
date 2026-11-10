/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceColl` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj3
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceColl


/-!
# REDSPLICE-DEF (S2a), B: the collection `C_1` of `G_sb`

For every SG group `S` of `𝒞` that is an HV, or has a skipped ingredient, `exists_obj` produces the residual
object in `G_sb` (an HV; a (CN) vine; a root (CL) vine) with the properties used for
`Src.SubproChoices.Structural` and `hingeOutsideFirst`: allowed, supported on the image of `S`, and hinge atoms
occur in it only as joints.  `objects G σ` is the list of these objects.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

theorem groups_disjoint (hM : G.molecule.IsMolecule) :
    (maximalGroupsG γ G.molecule).Pairwise (fun S T => Disjoint S T) := by
  have hpart := partition_eq_maximalGroups (maximalGroupsG_partition (γ := γ) hM)
  have := (maximalGroupsG_partition (γ := γ) hM).2.1
  rwa [hpart] at this

/-- B1b (Mk-general form of `repC_mem_group`). -/
theorem repC_mem_groupMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {S : Finset (GBranch G.tree)}
    (hSm : S ∈ maximalGroupsG γ G.molecule) {z : GBranch G.tree} (hz : z ∈ S) {Mk : Set (CLVineG γ _)} :
    repC (stSt γ (Mk := Mk) G σ).cls z ∈ S := by
  by_cases h : ∃ u ∈ unitBlocks γ (Mk := Mk) G σ, z ∈ u.atoms
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
    (hSm : S ∈ maximalGroupsG γ G.molecule) {z : GBranch G.tree} (hz : z ∈ S) :
    repC (stSt γ G σ).cls z ∈ S := repC_mem_groupMk (Mk := ∅) hM σ hSm hz

/-- An SG group contributes an object to `C_1`. -/
@[expose] def HasObj (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree)) : Prop :=
  ((∃ a b, Src.IsHV γ G.molecule S a b) ∧ ¬ ∃ a b, Src.IsHVC γ G.molecule S a b) ∨
    ∃ sk : SkipData γ G S, (groupUnitsOf γ G S).skip = some sk

/-- The properties of the object of the group `S` in `G_sb` (B1a: for the marked vine set `Mk`). -/
structure ObjSpecMk (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (σ : Prescription G) (S : Finset (GBranch G.tree)) (Mk : Set (CLVineG γ G))
    (O : Src.Object γ (stSt γ G σ Mk).G.molecule) : Prop where
  allowed : Src.AllowedCollectionObject γ (stSt γ G σ Mk).G O
  atoms_sub : ∀ v ∈ O.atoms, ∃ z ∈ S, v = (stSt γ G σ Mk).M.pi (stSt γ G σ Mk).hcls z
  hinge : ∀ c, (stSt γ G σ Mk).cls ((stSt γ G σ Mk).M.ob c) ≠ none → c ∈ O.atoms → c = O.upper ∨ c = O.lower
  /-- SUBPRO amendment A2: the atoms of the object are exactly the image of a subset `A` of the group, and every
  unmerged atom of the group lies in `A` -/
  src : ∃ A : Finset (GBranch G.tree), A ⊆ S ∧ O.atoms = A.image ((stSt γ G σ Mk).M.pi (stSt γ G σ Mk).hcls) ∧
    (∀ z ∈ S, (stSt γ G σ Mk).cls z = none → z ∈ A) ∧
    ((((∃ a b, Src.IsHV γ G.molecule S a b) ∧ ¬ ∃ a b, Src.IsHVC γ G.molecule S a b) ∧
        (groupUnitsOf γ G S).skip = none ∧
        ∃ a b e, hvPick γ G S = some (a, b, e) ∧ O.upper = (stSt γ G σ Mk).M.pi (stSt γ G σ Mk).hcls a ∧
          O.lower = (stSt γ G σ Mk).M.pi (stSt γ G σ Mk).hcls b ∧
          ∃ R : Src.HyperLikeRealization γ (stSt γ G σ Mk).G.molecule O.atoms O.upper O.lower,
            O.shape = Src.VineLikeObject.hyper R ∧ (stSt γ G σ Mk).M.od R.added = e) ∨
      ∃ sk : SkipData γ G S, (groupUnitsOf γ G S).skip = some sk ∧ A = sk.A ∧
        O.upper = (stSt γ G σ Mk).M.pi (stSt γ G σ Mk).hcls sk.x ∧ O.lower = (stSt γ G σ Mk).M.pi (stSt γ G σ Mk).hcls sk.y ∧
        (sk.bond = none → ∃ h, O.shape = Src.VineLikeObject.vc h) ∧
        ∀ e, sk.bond = some e → ∃ R : Src.HyperLikeRealization γ (stSt γ G σ Mk).G.molecule O.atoms O.upper O.lower,
          O.shape = Src.VineLikeObject.hyper R ∧ (stSt γ G σ Mk).M.od R.added = e)

theorem SDecomp.nonmerged_mem {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {N : Molecule V D}
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

end WaveTurbulence.GammaLow.Fama
