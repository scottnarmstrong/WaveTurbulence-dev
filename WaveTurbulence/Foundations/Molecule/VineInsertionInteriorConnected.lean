/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineInteriorPaths
public import WaveTurbulence.Foundations.Molecule.VineExpansionConnected
import Mathlib.Tactic

/-! # Rung insertion preserves connectivity of the nonjoint interior -/

public section
namespace WaveTurbulence.Vine

/-- Inserting rungs on interior rail bonds preserves the connected
nonjoint region, including when the insertion length is zero. -/
theorem insertRungs_interior_connected (T : VineTemplate) (hn : 2 ≤ T.n)
    (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ) (hc : InteriorConnected T)
    (hupper : s.1.1<T.n ∧ s.1.2<T.n ∧ s.2.1<T.n ∧ s.2.2<T.n)
    (hlower : 2 ≤ s.1.1 ∧ 2 ≤ s.2.1) :
    InteriorConnected (insertRungs T s k) := by
  intro v hv2 hvn
  rw [insertRungs_atoms] at hvn
  by_cases hvo : v<T.n
  · exact insertion_interior_path T hn s k (hc v hv2 hvo)
  · have hk : k ≠ 0 := by omega
    by_cases hu : v<T.n+k
    · have hvm : v ∈ (List.range k).map (T.n+·) :=
        List.mem_map.mpr ⟨v-T.n,List.mem_range.mpr (by omega),by omega⟩
      exact Relation.EqvGen.trans _ _ _
        (insertion_interior_path T hn s k (hc _ hlower.1 hupper.1))
        (interior_path_mono (fun _ h => first_rail_mem T s hk h)
          (interior_rail_mem_prefix _ _ _ hlower.1 (by
            intro w hw
            obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hw
            omega) hvm))
    · have hvm : v ∈ (List.range k).map (T.n+k+·) :=
        List.mem_map.mpr ⟨v-(T.n+k),List.mem_range.mpr (by omega),by omega⟩
      exact Relation.EqvGen.trans _ _ _
        (insertion_interior_path T hn s k (hc _ hlower.2 hupper.2.2.1))
        (interior_path_mono (fun _ h => second_rail_mem T s hk h)
          (interior_rail_mem_prefix _ _ _ hlower.2 (by
            intro w hw
            obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hw
            omega) hvm))

end WaveTurbulence.Vine
