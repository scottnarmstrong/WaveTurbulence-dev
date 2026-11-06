/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamSpliceRepresentatives
import Mathlib.Tactic

/-! # Physical representatives retain the endpoint on their designated cap side -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
variable {V β : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]
variable (G : RungSpliceGeometry V β)

/-- Choosing the cap side of an actual endpoint retains that endpoint,
with the prescribed cap reflection, on the selected actual new bond. -/
theorem representative_incident (e : β) (v : V)
    (hv : (G.ends e).1=v ∨ (G.ends e).2=v) :
    (G.newEnds (G.representative e (decide (v ∈ G.cap)))).1=Sum.inl (G.σ v) ∨
      (G.newEnds (G.representative e (decide (v ∈ G.cap)))).2=Sum.inl (G.σ v) := by
  by_cases hi : e=G.i
  · subst e
    cases hp : G.pattern
    all_goals simp [G.first,hp,RungPattern.signs,orientPair] at hv
    all_goals rcases hv with h | h <;> subst v
    all_goals simp [G.representative_first,newEnds,rungSpliceEnds,hp,RungPattern.signs,RungPattern.reversesPorts,orientPair,
      G.outer_p,G.inner_c,G.fixed_p,G.port_c]
  · by_cases hj : e=G.j
    · subst e
      cases hp : G.pattern
      all_goals simp [G.second,hp,RungPattern.signs,orientPair] at hv
      all_goals rcases hv with h | h <;> subst v
      all_goals simp [G.representative_second,newEnds,rungSpliceEnds,hp,RungPattern.signs,RungPattern.reversesPorts,orientPair,
        G.outer_q,G.inner_d,G.fixed_q,G.port_d]
    · rw [G.representative_rest e hi hj]
      change (Sum.inl (G.σ (G.ends e).1) : V ⊕ Fin 2)=Sum.inl (G.σ v) ∨
        (Sum.inl (G.σ (G.ends e).2) : V ⊕ Fin 2)=Sum.inl (G.σ v)
      exact hv.imp (congrArg (fun v => (Sum.inl (G.σ v) : V ⊕ Fin 2)))
        (congrArg (fun v => (Sum.inl (G.σ v) : V ⊕ Fin 2)))

end WaveTurbulence.Vine.Param.RungSpliceGeometry
