/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceOrdinaryJointPairs
public import WaveTurbulence.Foundations.Spine.SourceErasedConservation
/-! Literal source SG pair selection at either joint, including actual designated hyper objects. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open SourceVine WaveTurbulence.Mole

theorem source_actual_object_lower_sg_pair {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (hM : G.molecule.IsMolecule) (P : Object G.molecule) {L : ℝ} (hL : L ≠ 0) (γ η : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0)
    (hP : P.HasGapKind L γ η base (bondIndex G z.1) .SG) :
    ∃ x y, TripleAt G P.lower x y ∧ P.ContainsDart x ∧ P.ContainsDart y ∧
      Molecule.gapKind L γ η (Molecule.gapAt L base (bondIndex G z.1) x y) = .SG := by
  have hk := spliced_molecule_decoration G hp hL base roots z
  have hc : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 →
      ∑ x ∈ G.molecule.dartsAt v, G.molecule.dartSign x • Molecule.kvec L base (bondIndex G z.1) x = 0 := by
    intro v hv hdeg
    exact (hk.2 v hv).trans (gardenSource_eq_zero_of_deg_four G hp _ v hdeg)
  rcases P with ⟨S, a, b, shape⟩
  rcases hP with ⟨r, hr, hkind⟩
  cases shape with
  | vc hVC =>
    exact source_actual_block_lower_sg_pair G hp hM hVC.1 hL γ η base roots z hr hkind
  | hyper R =>
    let E := Molecule.eraseBond G.molecule R.added
    have hkE : ∀ x : {x : GardenDart G // x ≠ R.added ∧ x ≠ G.molecule.mate R.added},
        bondIndex G z.1 (E.mate x).1 = bondIndex G z.1 x.1 := fun x => hk.1 x.1
    have hcE := source_eraseBond_conservation G.molecule hM R.added
      (Molecule.kvec L base (bondIndex G z.1)) hc
    obtain ⟨r', hr', hsg⟩ := source_block_lower_SG_gap E
      (source_eraseBond_isMolecule G.molecule hM R.added) R.adjoint.1 L γ η base
      (fun x => bondIndex G z.1 x.1) hkE hcE hr hkind
    obtain ⟨x, y, hx, hy, hgx, hgy, hox, hoy, hgap⟩ := hr'
    have hgap' : r' = Molecule.gapAt L base (bondIndex G z.1) x.1 y.1 := hgap
    have hnonzero := ((Vine.gapKind_eq_SG_iff L γ η r').mp hsg).1
    have hne : y.1 ≠ G.molecule.mate x.1 := by
      intro he
      apply hnonzero
      rw [hgap', he]
      simp only [Molecule.gapAt, Molecule.kvec, hk.1 x.1, sub_self]
    refine ⟨x.1, y.1, ⟨hx, hy, hne, ?_⟩, ⟨x.2.1, x.2.2, hgx⟩, ⟨y.2.1, y.2.2, hgy⟩, ?_⟩
    · change G.molecule.out x.1 = true at hox
      change G.molecule.out y.1 = false at hoy
      rw [hox, hoy]
      decide
    · simpa only [hgap'] using hsg

theorem source_actual_object_joint_sg_pair {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (hM : G.molecule.IsMolecule) (P : Object G.molecule) {L : ℝ} (hL : L ≠ 0) (γ η : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0)
    (hP : P.HasGapKind L γ η base (bondIndex G z.1) .SG)
    (v : GBranch G.tree) (hv : v = P.upper ∨ v = P.lower) :
    ∃ x y, TripleAt G v x y ∧ P.ContainsDart x ∧ P.ContainsDart y ∧
      Molecule.gapKind L γ η (Molecule.gapAt L base (bondIndex G z.1) x y) = .SG := by
  rcases hv with rfl | rfl
  · exact source_upper_joint_sg_pair G P L γ η base (bondIndex G z.1)
      (spliced_molecule_decoration G hp hL base roots z).1 hP
  · exact source_actual_object_lower_sg_pair G hp hM P hL γ η base roots z hP

end WaveTurbulence.LGSpine
