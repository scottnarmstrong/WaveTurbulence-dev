/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PrefixStretch

/-! # Prefix insertion preserves the actual ancestor order -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton

/-- Inserting a common prefix below a fixed address preserves every ancestor relation. -/
theorem stretch_below_mono {w : ℕ} (a : Address w) (p : Path)
    {x y : Address w} (hxy : Below x y) : Below (stretch a p x) (stretch a p y) := by
  by_cases hx : Below a x
  · have hy : Below a y := ⟨hxy.1.trans hx.1, hx.2.trans hxy.2⟩
    obtain ⟨r,hr⟩ := below_exists_frame a x hx
    obtain ⟨s,hs⟩ := below_exists_frame x y hxy
    rw [hs, hr, addrExt_append, stretch_frame, stretch_frame]
    exact ⟨rfl, ⟨s, by simp only [addrExt, List.append_assoc]⟩⟩
  · rw [stretch_outside a p x hx]
    by_cases hy : Below a y
    · have hxa : Below x a := by
        have hi : x.1 = a.1 := hxy.1.symm.trans hy.1
        rcases List.prefix_or_prefix_of_prefix hxy.2 hy.2 with h | h
        · exact ⟨hi.symm, h⟩
        · exact (hx ⟨hi,h⟩).elim
      have ha := stretch_below a y p hy
      exact ⟨ha.1.trans hxa.1, hxa.2.trans ha.2⟩
    · rw [stretch_outside a p y hy]
      exact hxy

end WaveTurbulence.LFTwist
