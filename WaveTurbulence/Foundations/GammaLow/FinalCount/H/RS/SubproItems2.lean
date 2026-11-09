/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSplicePiece
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.SubproGap2
public import WaveTurbulence.Foundations.FinalCount.SubproTame
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.RS.SubproEntry2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
import Mathlib.Tactic
/-! **L6-HRS hand port of main `WaveTurbulence.Foundations.FinalCount.SubproItems2`** (sha256 in
`H/RS/COPIED-SHA256SUMS`; the porter did not emit it): main's text re-namespaced into `…FinalCount.H` with the
porter's carrier rewrites (`Object M` → `Src.Object Src.γL M`, `IsDV` → `Src.IsDV Src.γL`, …).

# SUBPRO (S4): `selectedSG`, `hingeSG`, `hingeJoint`, `zeroTame` for the construction (R28 base)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice
  WaveTurbulence.Stage1

variable {R : ℕ} {G : Garden (2 * R)}

/-- Decoration hypotheses of `G_sb` used by the gap-kind transport (provided by `spliced_molecule_decoration`). -/
structure SbDec (G : Garden (2 * R)) (σ : Prescription G) {d : ℕ} (L : ℝ) (base : Mom d)
    (κ : GardenDart (stSt G σ).G → (Fin d → ℤ)) : Prop where
  c : ∃ c : GBranch (stSt G σ).G.tree → Mom d, (stSt G σ).G.molecule.IsDecoration L base c κ ∧
    ∀ v ∈ (stSt G σ).G.molecule.atoms, (stSt G σ).G.molecule.deg v = 4 → c v = 0

theorem selectedSG_cc2 (σ : Prescription G) {d : ℕ}
    (D : SplicedKernelData (stSt G σ).G d) (hD : D.gapSpecification = gapSpecification G σ)
    (L γ η : ℝ) (base : Mom d) (z : GNode (stSt G σ).G.tree → (Fin d → ℤ))
    (hZ : splicedGapIndicator (stSt G σ).G D L γ η base z ≠ 0)
    (hdec : SbDec G σ L base (bondIndex (stSt G σ).G z)) :
    ∀ i, ((collectionChoices G σ).collection i).HasGapKind L γ η base (bondIndex (stSt G σ).G z)
      Molecule.GapKind.SG := by
  obtain ⟨c, hκ, hc0⟩ := hdec.c
  intro i
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  set O := (objects G σ).get i with hOdef
  have hOm : O ∈ objects G σ := List.get_mem _ _
  obtain ⟨S, -, hSm, hO⟩ := mem_objects' hOm
  obtain ⟨-, -, hσ, -⟩ := objOf_spec (Option.mem_def.mpr hO)
  show O.HasGapKind L γ η base (bondIndex (stSt G σ).G z) _
  obtain ⟨a, ha, e, he, hk, hc1, hc2, hj⟩ := entry_obj hM σ hSm hσ hO
  have := gapKind_of_Z (stSt G σ).G D L γ η base z hZ (q := e) (by rw [hD]; exact he)
  rw [hk, hσ] at this
  exact hasGapKind_of_pair_joint (stSt G σ).G L γ η base c _ hκ hc0 O hj e.at_first e.at_second hc1 hc2
    e.opposite this

/-- The hinge pair lies inside every object of `C_1` having the hinge as a joint. -/
theorem hingePair_contained (hM : G.molecule.IsMolecule) (σ : Prescription G)
    {v : GBranch (stSt G σ).G.tree} (hv : v ∈ (stSt G σ).hinges) {x y : GardenDart (stSt G σ).G}
    (hp : hingePair G σ v = some (x, y))
    {O : Src.Object Src.γL (stSt G σ).G.molecule} (hOm : O ∈ objects G σ) (hj : O.upper = v ∨ O.lower = v) :
    O.ContainsDart x ∧ O.ContainsDart y ∧ ((stSt G σ).G.molecule.atom x = O.upper ∨
      (stSt G σ).G.molecule.atom x = O.lower) := by
  obtain ⟨x', y', hp', -, ⟨S, hSm, u, hu, hob, p, hsp, hx, hy⟩, -⟩ := hingePair_spec hM σ hv
  rw [hp] at hp'
  obtain ⟨rfl, rfl⟩ : x = x' ∧ y = y' := by simpa using Option.some.inj hp'
  have hvO : v ∈ O.atoms := by rcases hj with rfl | rfl; exact Src.Object.upper_mem O; exact Src.Object.lower_mem O
  obtain ⟨sk, hsk, hOa, hup, hlo, hsh1, hsh2⟩ := obj_skip_data hM σ hOm hvO hSm hu hob
  exact hinge_dart_obj σ sk hsk hOa hup hlo hsh1 hsh2 hsp hx hy

theorem hingeJoint_cc2 (σ : Prescription G) :
    ∀ v ∈ (collectionChoices G σ).hinges, ∀ i,
      (v = ((collectionChoices G σ).collection i).upper ∨ v = ((collectionChoices G σ).collection i).lower) →
      HasChosenPair ((collectionChoices G σ).first v) ((collectionChoices G σ).second v) (fun x y =>
        ((collectionChoices G σ).collection i).ContainsDart x ∧
          ((collectionChoices G σ).collection i).ContainsDart y) := by
  intro v hv i hj
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  have hv' : v ∈ (stSt G σ).hinges := hv
  obtain ⟨x, y, hp, -⟩ := hingePair_spec hM σ hv'
  have := hingePair_contained hM σ hv' hp (List.get_mem (objects G σ) i)
    (by rcases hj with h | h; exact Or.inl h.symm; exact Or.inr h.symm)
  exact ⟨x, y, by simp [collectionChoices, hp], by simp [collectionChoices, hp], this.1, this.2.1⟩

theorem hingeSG_cc2 (σ : Prescription G) {d : ℕ}
    (D : SplicedKernelData (stSt G σ).G d) (hD : D.gapSpecification = gapSpecification G σ)
    (L γ η : ℝ) (base : Mom d) (z : GNode (stSt G σ).G.tree → (Fin d → ℤ))
    (hZ : splicedGapIndicator (stSt G σ).G D L γ η base z ≠ 0)
    (hdec : SbDec G σ L base (bondIndex (stSt G σ).G z)) :
    ∀ v ∈ (collectionChoices G σ).hinges, HasChosenPair ((collectionChoices G σ).first v)
      ((collectionChoices G σ).second v) (fun x y => TripleAt (stSt G σ).G v x y ∧
        Molecule.gapKind L γ η (Molecule.gapAt L base (bondIndex (stSt G σ).G z) x y) = Molecule.GapKind.SG) := by
  obtain ⟨c, hκ, hc0⟩ := hdec.c
  intro v hv
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  have hv' : v ∈ (stSt G σ).hinges := hv
  obtain ⟨x, y, hp, hPP, -, hentry⟩ := hingePair_spec hM σ hv'
  have hT := hPP.1
  refine ⟨x, y, by simp [collectionChoices, hp], by simp [collectionChoices, hp], hT, ?_⟩
  by_cases hjoint : ∃ O ∈ objects G σ, O.upper = v ∨ O.lower = v
  · obtain ⟨O, hOm, hj⟩ := hjoint
    obtain ⟨hc1, hc2, -⟩ := hingePair_contained hM σ hv' hp hOm hj
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hOm
    have hsel := selectedSG_cc2 σ D hD L γ η base z hZ ⟨c, hκ, hc0⟩ i
    have hsel' : O.HasGapKind L γ η base (bondIndex (stSt G σ).G z) Molecule.GapKind.SG := by
      have : ((collectionChoices G σ).collection i) = O := hi
      rw [← this]; exact hsel
    have hj' : v = O.upper ∨ v = O.lower := by rcases hj with h | h; exact Or.inl h.symm; exact Or.inr h.symm
    exact obj_pair_gapKind (stSt G σ).G.molecule (WaveTurbulence.Mole.garden_isMolecule _) L γ η base c _ hκ hc0 O
      hsel' hj' hT.1 hT.2.1 hc1 hc2 hT.2.2.2
  · obtain ⟨S, hSm, hga, hep⟩ := hentry hjoint
    have hgp : gapPair G σ S v = some (x, y) := by
      unfold gapPair; rw [if_pos hv']; exact hep
    have hspec := gapSpecification_of hM σ hSm hga hgp hT
    have hk := gapKind_of_Z (stSt G σ).G D L γ η base z hZ (q := ⟨x, y, hT.1, hT.2.1, hT.2.2.1, hT.2.2.2, σ S⟩)
      (by rw [hD]; exact hspec)
    obtain ⟨a, ha, hav⟩ : ∃ a, groupJoint G S = some a ∧ (stSt G σ).M.pi (stSt G σ).hcls a = v := by
      unfold groupAtom at hga
      cases hg : groupJoint G S with
      | none => rw [hg] at hga; cases hga
      | some a => rw [hg] at hga; exact ⟨a, rfl, Option.some.inj hga⟩
    have hσ := gapSpecification_hinge_kind hM σ hSm (groupJoint_kind ha).1 (hav ▸ hv')
    rw [hσ] at hk
    exact hk

end WaveTurbulence.GammaLow.FinalCount.H
