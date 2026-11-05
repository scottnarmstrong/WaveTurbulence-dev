/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineInsertionDegrees
import Mathlib.Tactic

/-! # Exact degree profiles, including fresh atoms (TARGET defvine) -/

public section
namespace WaveTurbulence.Vine

/-- The two fresh name lists together contain every fresh atom once. -/
theorem fresh_counts (n k v : ℕ) :
    ((List.range k).map (n+·)).count v + ((List.range k).map (n+k+·)).count v =
      if n ≤ v ∧ v < n+2*k then 1 else 0 := by
  rw [← List.count_append,← List.range'_eq_map_range,← List.range'_eq_map_range,
    List.range'_append_1]
  rw [(List.nodup_range' 1 (by decide)).count]
  have hm : v ∈ List.range' n (k+k) ↔ n ≤ v ∧ v < n+2*k := by
    rw [List.mem_range']
    simp only [one_mul]
    constructor
    · rintro ⟨i,hi,rfl⟩; omega
    · rintro ⟨h1,h2⟩; exact ⟨v-n,by omega,by omega⟩
  simp only [hm]

/-- The exact profile of a vine template, also outside its finite atom range. -/
@[expose] def DegreeProfile (T : VineTemplate) : Prop :=
  2 ≤ T.n ∧ ∀ v, templateDegree T v = if v < T.n then (if v < 2 then 2 else 4) else 0

/-- Each pinned template has the complete degree profile. -/
theorem template_degreeProfile (X : VineType) : DegreeProfile X.template := by
  constructor
  · cases X <;> decide
  · intro v
    by_cases hv : v < X.template.n
    · simp only [hv,ite_true]
      exact template_degrees X v hv
    · simp only [hv,ite_false]
      have h1 : v ∉ X.template.bonds.map Prod.fst := by
        intro hm
        obtain ⟨e,he,hev⟩ := List.mem_map.mp hm
        exact hv (hev ▸ (template_endpoints X e he).1)
      have h2 : v ∉ X.template.bonds.map Prod.snd := by
        intro hm
        obtain ⟨e,he,hev⟩ := List.mem_map.mp hm
        exact hv (hev ▸ (template_endpoints X e he).2)
      simp only [templateDegree,List.count_eq_zero_of_not_mem h1,List.count_eq_zero_of_not_mem h2]

/-- Rung insertion preserves degree two at the joints and degree four at
all other atoms, while allocating exactly the new finite atom interval. -/
theorem insertRungs_degreeProfile (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hT : DegreeProfile T) (h1 : s.1 ∈ T.bonds) (h2 : s.2 ∈ T.bonds.erase s.1) :
    DegreeProfile (insertRungs T s k) := by
  have hn := hT.1
  refine ⟨by rw [insertRungs_atoms]; omega,?_⟩
  intro v
  rw [insertRungs_degree T s k v h1 h2,fresh_counts,hT.2,insertRungs_atoms]
  split_ifs <;> omega

end WaveTurbulence.Vine
