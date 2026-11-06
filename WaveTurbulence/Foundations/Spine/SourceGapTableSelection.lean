/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceGapTableObjects
/-! All second-collection and atom-tag selection rules depend only on the finite local gap table. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set Finset
open scoped Classical

 theorem source_gapKind_eq_zero_iff {d : ℕ} (L γ η : ℝ) (r : Mom d) :
    Molecule.gapKind L γ η r = .ZG ↔ r = 0 := by
  unfold Molecule.gapKind
  split_ifs <;> simp_all

 theorem sourceGapTable_atomGapKind_eq {w d : ℕ} (G : Garden w) (L γ η : ℝ) (base : Mom d)
    (κ κ' : GardenDart G → (Fin d → ℤ))
    (h : sourceGapTable G L γ η base κ = sourceGapTable G L γ η base κ') (v : GBranch G.tree) :
    SourceVine.atomGapKind G L γ η base κ v = SourceVine.atomGapKind G L γ η base κ' v := by
  have hlocal (x y : GardenDart G) (ht : SourceVine.TripleAt G v x y) :=
    sourceGapTable_eq_apply G L γ η base κ κ' h x y (ht.1.trans ht.2.1.symm)
  have hSG : (∃ x y, SourceVine.TripleAt G v x y ∧
      Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) = .SG) ↔
      (∃ x y, SourceVine.TripleAt G v x y ∧
        Molecule.gapKind L γ η (Molecule.gapAt L base κ' x y) = .SG) := by
    constructor
    · rintro ⟨x, y, ht, hk⟩
      exact ⟨x, y, ht, (hlocal x y ht).symm.trans hk⟩
    · rintro ⟨x, y, ht, hk⟩
      exact ⟨x, y, ht, (hlocal x y ht).trans hk⟩
  have hZG : (∃ x y, SourceVine.TripleAt G v x y ∧ Molecule.gapAt L base κ x y = 0) ↔
      (∃ x y, SourceVine.TripleAt G v x y ∧ Molecule.gapAt L base κ' x y = 0) := by
    simp_rw [← source_gapKind_eq_zero_iff L γ η]
    constructor
    · rintro ⟨x, y, ht, hk⟩
      exact ⟨x, y, ht, (hlocal x y ht).symm.trans hk⟩
    · rintro ⟨x, y, ht, hk⟩
      exact ⟨x, y, ht, (hlocal x y ht).trans hk⟩
  unfold SourceVine.atomGapKind
  simp only [hSG, hZG]

 theorem sourceGapTable_eligibleSecond_iff {w d : ℕ} (G : Garden w) (L γ η : ℝ) (base : Mom d)
    (κ κ' : GardenDart G → (Fin d → ℤ))
    (h : sourceGapTable G L γ η base κ = sourceGapTable G L γ η base κ')
    (F : Set (GBranch G.tree)) (P : SourceVine.Object G.molecule) :
    SourceVine.eligibleSecondObject G L γ η base κ F P ↔
      SourceVine.eligibleSecondObject G L γ η base κ' F P := by
  unfold SourceVine.eligibleSecondObject
  simp only [sourceGapTable_object_kind_iff G L γ η base κ κ' h]

 theorem sourceGapTable_secondCollection_iff {w d : ℕ} (G : Garden w) (L γ η : ℝ) (base : Mom d)
    (κ κ' : GardenDart G → (Fin d → ℤ))
    (h : sourceGapTable G L γ η base κ = sourceGapTable G L γ η base κ')
    (F : Set (GBranch G.tree))
    (omitted : Set (Finset (GBranch G.tree))) (collection : Set (SourceVine.Object G.molecule)) :
    SourceVine.IsSourceSecondCollection G L γ η base κ F omitted collection ↔
      SourceVine.IsSourceSecondCollection G L γ η base κ' F omitted collection := by
  unfold SourceVine.IsSourceSecondCollection
  simp only [sourceGapTable_object_kind_iff G L γ η base κ κ' h,
    sourceGapTable_eligibleSecond_iff G L γ η base κ κ' h]

end WaveTurbulence.LGSpine
