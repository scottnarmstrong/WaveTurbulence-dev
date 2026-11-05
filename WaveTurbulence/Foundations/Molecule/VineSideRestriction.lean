/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSideBaseRestriction
import Mathlib.Tactic

/-! # The full type-VII side has exactly the literal triangular ladder bonds -/

public section
namespace WaveTurbulence.Vine

/-- Restricting the complete pinned expansion to its side labels gives
exactly the triangular side, cyan rails and doubled cyan rungs. Red and
green insertions have no retained edge, for arbitrary nonnegative counts. -/
theorem typeVII_side_restrict_bonds (kr kc kg : ℕ) :
    restrictBonds (sideLabels (11+2*kr) kc) (VineType.VII.expand [kr,kc,kg]).bonds=
      sideBonds (11+2*kr) kc := by
  let W := sideLabels (11+2*kr) kc
  let T0 := VineType.VII.template
  let Tr := insertRungs T0 ((2,7),(3,8)) kr
  let Tc := insertRungs Tr ((5,7),(6,8)) kc
  have hnr : Tr.n=11+2*kr := insertRungs_atoms T0 _ kr
  have hnc : Tc.n=11+2*kr+2*kc := by
    change (insertRungs Tr ((5,7),(6,8)) kc).n=11+2*kr+2*kc
    rw [insertRungs_atoms,hnr]
  have h2 : 2 ∉ W := by rw [mem_sideLabels_iff]; omega
  have h3 : 3 ∉ W := by rw [mem_sideLabels_iff]; omega
  have h9 : 9 ∉ W := by rw [mem_sideLabels_iff]; omega
  have h10 : 10 ∉ W := by rw [mem_sideLabels_iff]; omega
  have h5 : 5 ∈ W := by rw [mem_sideLabels_iff]; omega
  have h6 : 6 ∈ W := by rw [mem_sideLabels_iff]; omega
  have h7 : 7 ∈ W := by rw [mem_sideLabels_iff]; omega
  have h8 : 8 ∈ W := by rw [mem_sideLabels_iff]; omega
  have hR : restrictBonds W Tr.bonds=restrictBonds W T0.bonds := by
    apply restrict_insertRungs_external W T0 ((2,7),(3,8)) kr
    · exact fun h => h2 h.1
    · exact fun h => h3 h.1
    · intro i hi
      change 11+i ∉ W
      rw [mem_sideLabels_iff]
      omega
    · intro i hi
      change 11+kr+i ∉ W
      rw [mem_sideLabels_iff]
      omega
  have hbase : restrictBonds W T0.bonds=
      [(4,5),(4,5),(4,6),(4,6),(5,6),(7,8),(5,7),(6,8)] :=
    typeVII_base_side_bonds (11+2*kr) kc (by omega)
  have hC : restrictBonds W Tc.bonds=sideBonds (11+2*kr) kc := by
    by_cases hk : kc=0
    · subst kc
      change restrictBonds W Tr.bonds=sideBonds (11+2*kr) 0
      rw [hR,hbase]
      rfl
    · change restrictBonds W (insertRungs Tr ((5,7),(6,8)) kc).bonds=sideBonds (11+2*kr) kc
      rw [restrict_insertRungs_internal W Tr ((5,7),(6,8)) kc hk ⟨h5,h7,h6,h8⟩ (by
        intro i hi
        rw [hnr,mem_sideLabels_iff]
        omega) (by
        intro i hi
        rw [hnr,mem_sideLabels_iff]
        omega)]
      rw [hR,hbase]
      simp only [hnr]
      rfl
  have hG : restrictBonds W (insertRungs Tc ((7,9),(8,10)) kg).bonds=restrictBonds W Tc.bonds := by
    apply restrict_insertRungs_external W Tc ((7,9),(8,10)) kg
    · exact fun h => h9 h.2
    · exact fun h => h10 h.2
    · intro i _hi
      rw [hnc,mem_sideLabels_iff]
      omega
    · intro i _hi
      rw [hnc,mem_sideLabels_iff]
      omega
  change restrictBonds W (insertRungs Tc ((7,9),(8,10)) kg).bonds=sideBonds (11+2*kr) kc
  rw [hG,hC]

end WaveTurbulence.Vine
