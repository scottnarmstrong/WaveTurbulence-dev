/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.OpenGraphHistoryOutside

/-! # Exact uniqueness of an ambient component replacement from inside and outside matching data -/

public section
namespace WaveTurbulence.Reg.Skeleton.PortMatching

theorem eq_of_matching_on_image_and_outside {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V × Fin 4 ↪ W × Fin 4) (M N P : PortMatching W)
    (hin : ∀ x, N.mate (f x) = P.mate (f x))
    (hn : ∀ x, x ∉ Set.range f → N.mate x = M.mate x)
    (hp : ∀ x, x ∉ Set.range f → P.mate x = M.mate x) : N = P := by
  apply PortMatching.ext
  funext x
  by_cases hx : x ∈ Set.range f
  · obtain ⟨y,rfl⟩ := hx
    exact hin y
  · exact (hn x hx).trans (hp x hx).symm

end WaveTurbulence.Reg.Skeleton.PortMatching
