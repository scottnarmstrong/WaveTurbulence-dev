/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourcePrimaryPairChoices
public import WaveTurbulence.Foundations.Spine.SourcePairTableEncoding
/-! The actual primary/hinge choices fit the finite incident-dart table. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open SourceVine Finset

theorem source_primary_pair_table {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (hM : G.molecule.IsMolecule) (C : SubproChoices G) (hC : C.Structural)
    {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0)
    (kFix : Finset (Mom d))
    (hs : SubproSupport G C L γ η base kFix (bondIndex G z.1)) :
    ∃ T : SourcePairTable G,
      (∀ v, atomGapKind G L γ η base (bondIndex G z.1) v = .SG →
        HasChosenPair (sourcePairFirst G T v) (sourcePairSecond G T v) (fun x y =>
          TripleAt G v x y ∧ Molecule.gapKind L γ η
            (Molecule.gapAt L base (bondIndex G z.1) x y) = .SG)) ∧
      (∀ v ∈ C.hinges, sourcePairFirst G T v = C.first v ∧
        sourcePairSecond G T v = C.second v) ∧
      (∀ i v, (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
        HasChosenPair (sourcePairFirst G T v) (sourcePairSecond G T v) (fun x y =>
          (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)) := by
  classical
  obtain ⟨first, second, hsg, hh, hj⟩ := source_primary_pair_choices G hp hM C hC hL γ η
    base roots z kFix hs
  let first' := fun v => if atomGapKind G L γ η base (bondIndex G z.1) v = .SG then first v else none
  let second' := fun v => if atomGapKind G L γ η base (bondIndex G z.1) v = .SG then second v else none
  obtain ⟨T, hTf, hTs⟩ := exists_sourcePairTable G first' second' (by
    intro v
    by_cases hv : atomGapKind G L γ η base (bondIndex G z.1) v = .SG
    · obtain ⟨x, y, hx, hy, hxy, _⟩ := hsg v hv
      exact Or.inr ⟨x, y, by simpa only [first', ite_eq_left hv] using hx,
        by simpa only [second', ite_eq_left hv] using hy,
        (Mole.mem_dartsAt G.molecule v x).mpr hxy.1,
        (Mole.mem_dartsAt G.molecule v y).mpr hxy.2.1⟩
    · exact Or.inl ⟨by simp only [first', ite_eq_right hv], by simp only [second', ite_eq_right hv]⟩)
  refine ⟨T, ?_, ?_, ?_⟩
  · intro v hv
    rw [hTf, hTs]
    simpa only [first', second', ite_eq_left hv] using hsg v hv
  · intro v hv
    have hkind : atomGapKind G L γ η base (bondIndex G z.1) v = .SG := by
      obtain ⟨x, y, _, _, hxy⟩ := hs.hingeSG v hv
      exact (source_atomGapKind_eq_SG_iff G L γ η base _ v).mpr ⟨x, y, hxy⟩
    rw [hTf, hTs]
    simpa only [first', second', ite_eq_left hkind] using hh v hv
  · intro i v hv
    have hkind := source_actual_object_joint_is_SG G hp hM (C.collection i) hL γ η
      base roots z (hs.selectedSG i) v hv
    rw [hTf, hTs]
    simpa only [first', second', ite_eq_left hkind] using hj i v hv

end WaveTurbulence.LGSpine
