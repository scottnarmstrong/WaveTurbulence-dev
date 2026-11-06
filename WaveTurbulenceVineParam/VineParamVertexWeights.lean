/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGraphSplice
import Mathlib.Tactic

/-! # Endpoint-supported source flow and energy terms

These identities express cut replacement vertex by vertex. A uniform cap
shift is evaluated at the endpoint supporting each term, avoiding a global
case split over repeated port names.
-/

public section
namespace WaveTurbulence.Vine.Param
variable {V E : Type*} [DecidableEq V]

/-- A label contributes only at its specified actual endpoint. -/
@[expose] def vertexWeight [Zero E] (v p : V) (x : E) : E := if p=v then x else 0

/-- Relabeling actual vertices preserves their endpoint-supported values. -/
theorem vertexWeight_relabel [Zero E] (σ : V ≃ V) (v p : V) (x : E) :
    vertexWeight (σ v) (σ p) x=vertexWeight v p x := by
  simp only [vertexWeight,σ.injective.eq_iff]

/-- The uniform cap shift may be read at the endpoint supporting a term. -/
theorem vertexWeight_cap_shift [AddCommGroup E] (C : Finset V) (v p : V) (x t : E) :
    vertexWeight v p (x-(if v ∈ C then t else 0))=
      vertexWeight v p (x-(if p ∈ C then t else 0)) := by
  by_cases h : p=v
  · subst p; rfl
  · simp only [vertexWeight,h,ite_false]

/-- One actual directed incidence row is the difference of its endpoint terms. -/
theorem flow_edge_term [AddCommGroup E] {β : Type*} (ends : β → V×V) (v : V) (j : β) (k : E) :
    (-energySign ends v j) • k=vertexWeight v (ends j).1 k-vertexWeight v (ends j).2 k := by
  simp only [energySign,neg_sub,sub_smul,vertexWeight]
  by_cases h1 : (ends j).1=v <;> by_cases h2 : (ends j).2=v <;>
    simp only [h1,h2,ite_true,ite_false,one_zsmul,zero_zsmul]

/-- A signed source edge has exactly its signed pair of endpoint flow terms. -/
theorem flow_orientedPair [AddCommGroup E] (s : ℤ) (hs : s=1 ∨ s= -1)
    (u w v : V) (k : E) :
    (-energySign (fun _ : Unit => orientPair s u w) v ()) • k=
      s • (vertexWeight v u k-vertexWeight v w k) := by
  rw [flow_edge_term]
  rcases hs with rfl | rfl <;> simp [orientPair]

/-- Negative Gamma of one actual directed edge is its two endpoint energies. -/
theorem energy_edge_term {β : Type*} (ends : β → V×V) (v : V) (j : β) (a : ℝ) :
    (energySign ends v j : ℝ)*a=vertexWeight v (ends j).2 a-vertexWeight v (ends j).1 a := by
  simp only [energySign,Int.cast_sub,vertexWeight]
  by_cases h1 : (ends j).1=v <;> by_cases h2 : (ends j).2=v <;>
    simp only [h1,h2,ite_true,ite_false,Int.cast_one,Int.cast_zero] <;> ring

/-- A signed source edge has its signed pair of endpoint energy terms. -/
theorem energy_orientedPair (s : ℤ) (hs : s=1 ∨ s= -1) (u w v : V) (a : ℝ) :
    (energySign (fun _ : Unit => orientPair s u w) v () : ℝ)*a=
      (s : ℝ)*(vertexWeight v w a-vertexWeight v u a) := by
  rw [energy_edge_term]
  rcases hs with rfl | rfl <;> simp [orientPair]

end WaveTurbulence.Vine.Param
