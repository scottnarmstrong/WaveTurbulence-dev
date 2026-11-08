/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Geometry.SubproEntryMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproItems2R83
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO: `selectedSG`, `hingeSG`, `hingeJoint`, `zeroTame` for `collectionChoices G σ Mk`

Mk twins of main's `selectedSG_cc2`, `hingePair_contained`, `hingeJoint_cc2`, `hingeSG_cc2` (SubproItems2R83) for the
marked splice, with the gap specification `gapSpecificationMk` (o75 Theorem 7.5′(2), (3), (5)):
* `𝒞₁` consists of the objects of the unmarked groups, so `selectedSG` and `hingeJoint` are main's arguments;
* a hinge of an unmarked group carries main's pair; a hinge of a marked group (a run) carries the 75-F1 pair of the
  first survivor with a joint there, which is small-gap because that survivor is (`survObj_SG`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice
  WaveTurbulence.Stage1

variable {R : ℕ} {G : Garden (2 * R)}

/-- **`SubproSupportMK.selectedSG`**: the objects of `𝒞₁` are small-gap on the support. -/
theorem selectedSG_cc2Mk (σ : Prescription G) {d : ℕ} {Mk : Set (Stage1.CLVine G)}
    (D : SplicedKernelData (stSt G σ Mk).G d) (hD : D.gapSpecification = gapSpecificationMk G σ Mk)
    (L γ η : ℝ) (base : Mom d) (z : GNode (stSt G σ Mk).G.tree → (Fin d → ℤ))
    (hZ : splicedGapIndicator (stSt G σ Mk).G D L γ η base z ≠ 0)
    (hdec : SbDec G σ L base (bondIndex (stSt G σ Mk).G z)) :
    ∀ i, ((collectionChoices G σ Mk).collection i).HasGapKind L γ η base (bondIndex (stSt G σ Mk).G z)
      Molecule.GapKind.SG := by
  obtain ⟨c, hκ, hc0⟩ := hdec.c
  intro i
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  set O := (objects G σ Mk).get i with hOdef
  have hOm : O ∈ objects G σ Mk := List.get_mem _ _
  obtain ⟨S, -, hSm, hO⟩ := mem_objects'Mk hOm
  obtain ⟨-, -, hσ, -⟩ := objOf_specMk (Option.mem_def.mpr hO)
  show O.HasGapKind L γ η base (bondIndex (stSt G σ Mk).G z) _
  obtain ⟨a, ha, e, he, hk, hc1, hc2, hj⟩ := entry_objMk hM σ hSm hσ hO
  have := gapKind_of_Z (stSt G σ Mk).G D L γ η base z hZ (q := e) (by rw [hD]; exact he)
  rw [hk, hσ] at this
  exact hasGapKind_of_pair_joint (stSt G σ Mk).G L γ η base c _ hκ hc0 O hj e.at_first e.at_second hc1 hc2
    e.opposite this

/-- A hinge that is an atom of an object of `𝒞₁` is the crown of a unit of an unmarked group. -/
theorem unmarked_hinge_of_obj (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Stage1.CLVine G)}
    {v : GBranch (stSt G σ Mk).G.tree} (hv : v ∈ (stSt G σ Mk).hinges)
    {O : Object (stSt G σ Mk).G.molecule} (hOm : O ∈ objects G σ Mk) (hvO : v ∈ O.atoms) :
    ∃ S, S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧ ¬ markedGroup G Mk S ∧
      ∃ u ∈ (groupUnitsOf G S).units, (stSt G σ Mk).M.ob v = u.upper := by
  obtain ⟨S, hSm, hσ, u, hu, hcr⟩ := hinge_groupMk hM σ hv
  obtain ⟨S', hS', hnm', hsub⟩ := mem_objects_group hOm
  obtain ⟨z', hz', hvz'⟩ := hsub v hvO
  have huB : u ∈ unitBlocks G σ Mk := mem_unitBlocksMk.mpr ⟨S, hSm, hσ, hu⟩
  have hvu := pi_of_crown hM σ huB hcr u.isBlock.2.1
  have hSS : S = S' := group_eq_of_pi_eq hM σ hSm hS' (groupUnitsMk_sub hu u.isBlock.2.1) hz' (hvu.trans hvz')
  subst hSS
  exact ⟨S, hSm, hσ, hnm', u, groupUnitsMk_of_not_marked hnm' ▸ hu, hcr⟩

/-- Main's `hingePair_contained`: the hinge pair lies inside every object of `𝒞₁` having the hinge as a joint. -/
theorem hingePair_containedMk (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (Stage1.CLVine G)}
    {v : GBranch (stSt G σ Mk).G.tree} (hv : v ∈ (stSt G σ Mk).hinges) {x y : GardenDart (stSt G σ Mk).G}
    (hp : hingePair G σ v = some (x, y))
    {O : Object (stSt G σ Mk).G.molecule} (hOm : O ∈ objects G σ Mk) (hj : O.upper = v ∨ O.lower = v) :
    O.ContainsDart x ∧ O.ContainsDart y ∧ ((stSt G σ Mk).G.molecule.atom x = O.upper ∨
      (stSt G σ Mk).G.molecule.atom x = O.lower) := by
  have hvO : v ∈ O.atoms := by rcases hj with rfl | rfl; exact Object.upper_mem O; exact Object.lower_mem O
  obtain ⟨S0, hS0, hσ0, hnm0, u0, hu0, hcr0⟩ := unmarked_hinge_of_obj hM σ hv hOm hvO
  obtain ⟨x', y', hp', -, ⟨S, hSm, -, u, hu, hob, p, hsp, hx, hy⟩, -⟩ :=
    hingePair_specMk hM σ hS0 hσ0 hnm0 hu0 hcr0
  rw [hp] at hp'
  obtain ⟨rfl, rfl⟩ : x = x' ∧ y = y' := by simpa using Option.some.inj hp'
  obtain ⟨sk, hsk, hOa, hup, hlo, hsh1, hsh2⟩ := obj_skip_dataMk hM σ hOm hvO hSm hu hob
  exact hinge_dart_objMk (Mk := Mk) σ sk hsk hOa hup hlo hsh1 hsh2 hsp hx hy

/-- **`SubproSupportMK.hingeJoint`** for `collectionChoices G σ Mk`. -/
theorem hingeJoint_cc2Mk (σ : Prescription G) {Mk : Set (Stage1.CLVine G)} :
    ∀ v ∈ (collectionChoices G σ Mk).hinges, ∀ i,
      (v = ((collectionChoices G σ Mk).collection i).upper ∨ v = ((collectionChoices G σ Mk).collection i).lower) →
      HasChosenPair ((collectionChoices G σ Mk).first v) ((collectionChoices G σ Mk).second v) (fun x y =>
        ((collectionChoices G σ Mk).collection i).ContainsDart x ∧
          ((collectionChoices G σ Mk).collection i).ContainsDart y) := by
  intro v hv i hj
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  have hv' : v ∈ (stSt G σ Mk).hinges := hv
  have hOm : (objects G σ Mk).get i ∈ objects G σ Mk := List.get_mem _ _
  have hj' : ((objects G σ Mk).get i).upper = v ∨ ((objects G σ Mk).get i).lower = v := by
    rcases hj with h | h; exact Or.inl h.symm; exact Or.inr h.symm
  have hvO : v ∈ ((objects G σ Mk).get i).atoms := by
    rcases hj' with h | h
    · rw [← h]; exact Object.upper_mem _
    · rw [← h]; exact Object.lower_mem _
  obtain ⟨S0, hS0, hσ0, hnm0, u0, hu0, hcr0⟩ := unmarked_hinge_of_obj hM σ hv' hOm hvO
  obtain ⟨x, y, hp, -⟩ := hingePair_specMk hM σ hS0 hσ0 hnm0 hu0 hcr0
  have := hingePair_containedMk hM σ hv' hp hOm hj'
  exact ⟨x, y, by simp [collectionChoices, hp], by simp [collectionChoices, hp], this.1, this.2.1⟩

/-- **`SubproSupportMK.hingeSG`** for `collectionChoices G σ Mk` (o75 Theorem 7.5′(5)): every hinge pair is an SG
triple. -/
theorem hingeSG_cc2Mk (σ : Prescription G) {d : ℕ} {Mk : Set (Stage1.CLVine G)}
    (D : SplicedKernelData (stSt G σ Mk).G d) (hD : D.gapSpecification = gapSpecificationMk G σ Mk)
    (L γ η : ℝ) (base : Mom d) (z : GNode (stSt G σ Mk).G.tree → (Fin d → ℤ))
    (hZ : splicedGapIndicator (stSt G σ Mk).G D L γ η base z ≠ 0)
    (hdec : SbDec G σ L base (bondIndex (stSt G σ Mk).G z)) :
    ∀ v ∈ (collectionChoices G σ Mk).hinges, HasChosenPair ((collectionChoices G σ Mk).first v)
      ((collectionChoices G σ Mk).second v) (fun x y => TripleAt (stSt G σ Mk).G v x y ∧
        Molecule.gapKind L γ η (Molecule.gapAt L base (bondIndex (stSt G σ Mk).G z) x y) =
          Molecule.GapKind.SG) := by
  obtain ⟨c, hκ, hc0⟩ := hdec.c
  intro v hv
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  have hv' : v ∈ (stSt G σ Mk).hinges := hv
  obtain ⟨S0, hS0, hσ0, u0, hu0, hcr0⟩ := hinge_groupMk hM σ hv'
  by_cases hmk : markedGroup G Mk S0
  · -- a run hinge: the 75-F1 survivor pair
    obtain ⟨q, hq, hT, t, ht, hjv, h1, h2⟩ := hingePair_markedHinge hM σ hS0 hσ0 hmk hu0 hcr0
    have hSG := survObj_SG hM σ L γ η base z D hD hZ ⟨c, hκ, hc0⟩ ht
    refine ⟨q.1, q.2, by simp [collectionChoices, hq], by simp [collectionChoices, hq], hT, ?_⟩
    exact obj_pair_gapKind (stSt G σ Mk).G.molecule (WaveTurbulence.Mole.garden_isMolecule _) L γ η base c _ hκ
      hc0 (survObj ht) hSG hjv hT.1 hT.2.1 h1 h2 hT.2.2.2
  have hu0' : u0 ∈ (groupUnitsOf G S0).units := groupUnitsMk_of_not_marked hmk ▸ hu0
  obtain ⟨x, y, hp, hPP, -, hentry⟩ := hingePair_specMk hM σ hS0 hσ0 hmk hu0' hcr0
  have hT := hPP.1
  refine ⟨x, y, by simp [collectionChoices, hp], by simp [collectionChoices, hp], hT, ?_⟩
  by_cases hjoint : ∃ O ∈ objects G σ Mk, O.upper = v ∨ O.lower = v
  · obtain ⟨O, hOm, hj⟩ := hjoint
    obtain ⟨hc1, hc2, -⟩ := hingePair_containedMk hM σ hv' hp hOm hj
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hOm
    have hsel := selectedSG_cc2Mk σ D hD L γ η base z hZ ⟨c, hκ, hc0⟩ i
    have hsel' : O.HasGapKind L γ η base (bondIndex (stSt G σ Mk).G z) Molecule.GapKind.SG := by
      have : ((collectionChoices G σ Mk).collection i) = O := hi
      rw [← this]; exact hsel
    have hj' : v = O.upper ∨ v = O.lower := by rcases hj with h | h; exact Or.inl h.symm; exact Or.inr h.symm
    exact obj_pair_gapKind (stSt G σ Mk).G.molecule (WaveTurbulence.Mole.garden_isMolecule _) L γ η base c _ hκ hc0
      O hsel' hj' hT.1 hT.2.1 hc1 hc2 hT.2.2.2
  · obtain ⟨S, hSm, hga, hep⟩ := hentry hjoint
    have hgp : gapPair G σ S v = some (x, y) := by
      unfold gapPair; rw [if_pos hv']; exact hep
    have hspec := gapSpecificationMk_of hM σ hSm hga hgp hT
    have hk := gapKind_of_Z (stSt G σ Mk).G D L γ η base z hZ
      (q := ⟨x, y, hT.1, hT.2.1, hT.2.2.1, hT.2.2.2, σ S⟩) (by rw [hD]; exact hspec)
    obtain ⟨a, ha, hav⟩ : ∃ a, groupJoint G S Mk = some a ∧ (stSt G σ Mk).M.pi (stSt G σ Mk).hcls a = v := by
      unfold groupAtom at hga
      cases hg : groupJoint G S Mk with
      | none => rw [hg] at hga; cases hga
      | some a => rw [hg] at hga; exact ⟨a, rfl, Option.some.inj hga⟩
    have hnmS := not_marked_of_groupJoint ha
    have ha' : groupJoint G S = some a := (groupJoint_of_not_marked hnmS).symm.trans ha
    have hσ := gapSpecification_hinge_kindMk hM σ hSm (groupJoint_kind ha').1 (Mk := Mk) (hav ▸ hv')
    rw [hσ] at hk
    exact hk

/-- **`SubproSupportMK.zeroTame`** for the marked splice (main's `tame_of_eps`, generic in the garden). -/
theorem zeroTame_cc2Mk (σ : Prescription G) {d : ℕ} {Mk : Set (Stage1.CLVine G)}
    (hpl : (stSt G σ Mk).G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (z : GenDecoration (stSt G σ Mk).G d roots 0)
    (hε : splicedEpsilon (stSt G σ Mk).G (collectionChoices G σ Mk).hinges z.1 ≠ 0) :
    ∀ v, v ∉ (collectionChoices G σ Mk).hinges →
      (∃ x y, TripleAt (stSt G σ Mk).G v x y ∧ Molecule.gapAt L base (bondIndex (stSt G σ Mk).G z.1) x y = 0) →
      (stSt G σ Mk).G.molecule.IsTame L base (Finset.univ.image (fun i => base + latticePoint L (roots i)))
        (bondIndex (stSt G σ Mk).G z.1) v :=
  fun _ hv hg => tame_of_eps (stSt G σ Mk).G hpl hL base roots z hε hv hg

end WaveTurbulence.VineA.NormalizedSplice.Subpro
