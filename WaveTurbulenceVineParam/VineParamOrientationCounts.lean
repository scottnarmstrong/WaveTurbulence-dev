/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Multiset.Count
import Mathlib.Tactic

/-! # Unordered bond multiplicities and one directional count determine orientation

This finite matching lemma retains every parallel occurrence. It is used
with direction counts produced from actual molecule bonds, before selecting
a profile index from the checked degree classification.
-/

public section
namespace WaveTurbulence.Vine.Param

/-- For distinct endpoints, the unordered count is the sum of both directions. -/
theorem unordered_pair_count (es : List (ℕ×ℕ)) (u v : ℕ) (hne : u ≠ v) :
    (es.map (fun e => s(e.1,e.2))).count s(u,v)=es.count (u,v)+es.count (v,u) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have hp : s(e.1,e.2)=s(u,v) ↔ e=(u,v) ∨ e=(v,u) := by
      constructor
      · intro h
        have hh := Sym2.eq_iff.mp h
        change (e.1=u ∧ e.2=v) ∨ (e.1=v ∧ e.2=u) at hh
        exact hh.elim (fun h => Or.inl (Prod.ext h.1 h.2)) (fun h => Or.inr (Prod.ext h.1 h.2))
      · rintro (rfl | rfl)
        · rfl
        · exact Sym2.eq_swap
    simp only [List.map_cons,List.count_cons,beq_iff_eq,ih,hp]
    by_cases h1 : e=(u,v) <;> by_cases h2 : e=(v,u) <;> simp_all <;> omega

/-- Conditional orientation reconstruction: the inputs are actual unordered
multiplicities, forward-direction counts and diagonal counts. The profile
classification produces these data; no directed isomorphism is assumed. -/
theorem ordered_multiset_eq_of_counts (A B : List (ℕ×ℕ))
    (hU : (A.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ))=
      (B.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ)))
    (hforward : ∀ u v,u<v → A.count (u,v)=B.count (u,v))
    (hdiag : ∀ u,A.count (u,u)=B.count (u,u)) :
    (A : Multiset (ℕ×ℕ))=(B : Multiset (ℕ×ℕ)) := by
  apply Multiset.ext.mpr
  rintro ⟨u,v⟩
  simp only [Multiset.coe_count]
  by_cases he : u=v
  · subst v; exact hdiag u
  · by_cases hlt : u<v
    · exact hforward u v hlt
    · have hvu : v<u := by omega
      have hh := congrArg (Multiset.count s(u,v)) hU
      simp only [Multiset.coe_count,unordered_pair_count _ u v he] at hh
      have hf := hforward v u hvu
      omega

end WaveTurbulence.Vine.Param
