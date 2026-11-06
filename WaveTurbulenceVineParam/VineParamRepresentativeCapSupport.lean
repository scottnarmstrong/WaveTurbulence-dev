/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamLiftedCap
public import WaveTurbulenceVineParam.VineParamRepresentativeEndpoints
import Mathlib.Tactic

/-! # Explicit physical representatives retain geometric cap-side support -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
open Finset
variable {V β : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

/-- An admissible physical representative touches its selected side of the
old cap, now regarded in the enlarged actual atom set. -/
theorem representative_touches_selected (e : β) (side : Bool) (hs : G.AdmissibleSide e side) :
    touchesSide G.newEnds (liftedCap G.cap) (G.representative e side) side := by
  by_cases hi : e=G.i
  · subst e
    rw [G.representative_first]
    cases side <;> cases hp : G.pattern
    all_goals simp [touchesSide,liftedCap,newEnds,rungSpliceEnds,hp,RungPattern.signs,
      RungPattern.reversesPorts,orientPair,G.outer_p,G.inner_c,G.inner_d]
  · by_cases hj : e=G.j
    · subst e
      rw [G.representative_second]
      cases side <;> cases hp : G.pattern
      all_goals simp [touchesSide,liftedCap,newEnds,rungSpliceEnds,hp,RungPattern.signs,
        RungPattern.reversesPorts,orientPair,G.outer_q,G.inner_c,G.inner_d]
    · rw [G.representative_rest e hi hj]
      have hh := hs hi hj
      change side=decide ((G.ends e).1 ∈ G.cap) at hh
      cases side
      · have hn : (G.ends e).1 ∉ G.cap := by
          intro hv
          simp only [hv,decide_true] at hh
          contradiction
        change (Sum.inl (G.σ (G.ends e).1) : V ⊕ Fin 2) ∉ liftedCap G.cap ∨ _
        left
        simpa [liftedCap,G.preserves_cap] using hn
      · have ht : (G.ends e).1 ∈ G.cap := by
          by_contra hv
          simp only [hv,decide_false] at hh
          contradiction
        change (Sum.inl (G.σ (G.ends e).1) : V ⊕ Fin 2) ∈ liftedCap G.cap ∨ _
        left
        simpa [liftedCap,G.preserves_cap] using ht

end WaveTurbulence.Vine.Param.RungSpliceGeometry
