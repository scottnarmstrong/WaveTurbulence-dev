/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.GammaLow.Famb.TVineIso
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RealizationIso

/-!
# The cohmol groups of `𝒱_γ` under directed garden isomorphisms

`iso_famGroups`: a directed garden isomorphism `f : G ≅ H` carries the cohmol groups `famGroups γ` of a block to those
of its image: the drawn template groups by main's `VineEstS4.groups_of_corr`, the T-vine pieces by
`TVineIso.iso_tvineGroups`. The drawn types are matched in both directions through the inverse isomorphism `isoSymm`.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.Famb.VineEstS4

open WaveTurbulence.Twist WaveTurbulence.VineEstS4 Finset

variable {w : ℕ} {G H : Garden w}

/-- The inverse of a directed garden isomorphism. -/
def isoSymm (f : GardenDirectedIso G H) : GardenDirectedIso H G where
  branches := f.branches.symm
  darts := f.darts.symm
  atom_comm y := by
    have h := f.atom_comm (f.darts.symm y)
    rw [Equiv.apply_symm_apply] at h
    rw [h, Equiv.symm_apply_apply]
  mate_comm y := by
    have h := f.mate_comm (f.darts.symm y)
    rw [Equiv.apply_symm_apply] at h
    rw [h, Equiv.symm_apply_apply]
  out_comm y := by
    have h := f.out_comm (f.darts.symm y)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm

theorem isoAtoms_isoSymm (f : GardenDirectedIso G H) (S : Finset (GBranch G.tree)) :
    isoAtoms H G (isoSymm f) (isoAtoms G H f S) = S := by
  change (S.image f.branches).image f.branches.symm = S
  rw [Finset.image_image]
  simp

theorem iso_isVine_iff (f : GardenDirectedIso G H) (X : VineType) (S : Finset (GBranch G.tree))
    (a b : GBranch G.tree) :
    H.molecule.IsVine X (isoAtoms G H f S) (f.branches a) (f.branches b) ↔ G.molecule.IsVine X S a b := by
  refine ⟨fun h => ?_, iso_isVine G H f⟩
  have h' := iso_isVine H G (isoSymm f) h
  rw [isoAtoms_isoSymm] at h'
  simpa only [isoSymm, Equiv.symm_apply_apply] using h'

/-- **The cohmol groups are transported.** -/
theorem iso_famGroups (f : GardenDirectedIso G H) (γ : ℝ) {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) :
    famGroups γ H.molecule (isoAtoms G H f S) (f.branches a) (f.branches b) =
      (famGroups γ G.molecule S a b).image (Finset.image f.branches) := by
  classical
  have hI := iso_isVine_iff f .I S a b
  have hII := iso_isVine_iff f .II S a b
  by_cases h1 : G.molecule.IsVine .I S a b
  · have h1' := hI.mpr h1
    unfold famGroups
    simp only [h1, h1', ↓reduceDIte]
    exact groups_of_corr G H f (VineEstS2.chosenRealization h1) (VineEstS2.chosenRealization h1') rfl rfl rfl hB
  · have h1' : ¬ H.molecule.IsVine .I (isoAtoms G H f S) (f.branches a) (f.branches b) := fun h => h1 (hI.mp h)
    by_cases h2 : G.molecule.IsVine .II S a b
    · have h2' := hII.mpr h2
      unfold famGroups
      simp only [h1, h1', h2, h2', ↓reduceDIte]
      exact groups_of_corr G H f (VineEstS2.chosenRealization h2) (VineEstS2.chosenRealization h2') rfl rfl rfl hB
    · have h2' : ¬ H.molecule.IsVine .II (isoAtoms G H f S) (f.branches a) (f.branches b) :=
        fun h => h2 (hII.mp h)
      by_cases hγ : γ ≤ 1 / 2
      · unfold famGroups
        simp only [h1, h1', h2, h2', hγ, ↓reduceDIte, ↓reduceIte]
        exact TVineIso.iso_tvineGroups G H f S a b
      · by_cases hX : ∃ X : VineType, G.molecule.IsVine X S a b
        · have hX' : ∃ X : VineType, H.molecule.IsVine X (isoAtoms G H f S) (f.branches a) (f.branches b) :=
            ⟨hX.choose, iso_isVine G H f hX.choose_spec⟩
          unfold famGroups
          simp only [h1, h1', h2, h2', hγ, hX, hX', ↓reduceDIte, ↓reduceIte]
          exact groups_of_corr G H f (VineEstS2.chosenRealization hX.choose_spec)
            (VineEstS2.chosenRealization hX'.choose_spec) rfl rfl rfl hB
        · have hX' : ¬ ∃ X : VineType, H.molecule.IsVine X (isoAtoms G H f S) (f.branches a) (f.branches b) :=
            fun ⟨X, h⟩ => hX ⟨X, (iso_isVine_iff f X S a b).mp h⟩
          unfold famGroups
          simp only [h1, h1', h2, h2', hγ, hX, hX', ↓reduceDIte, ↓reduceIte, Finset.image_empty]

/-- Bad vines are transported in both directions. -/
theorem iso_isBadVine_iff (f : GardenDirectedIso G H) (S : Finset (GBranch G.tree)) (a b : GBranch G.tree) :
    H.molecule.IsBadVine (isoAtoms G H f S) (f.branches a) (f.branches b) ↔ G.molecule.IsBadVine S a b := by
  unfold Molecule.IsBadVine
  rw [iso_isVine_iff, iso_isVine_iff]

end WaveTurbulence.GammaLow.Famb.VineEstS4
