/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrameSignCap
public import WaveTurbulence.Foundations.FinalCount.AppBTriplePermutation
import Mathlib.Tactic

/-! # A three-incidence support inside a larger removed-edge list -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The actual three outgoing representatives incident to the chosen atom.
Every other local bond has zero incidence there. -/
structure AppbTripleFrame {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) (v : V) where
  index : Fin 3 ↪ Fin P.edges.length
  incidence : ∀ j,appbIncidence M v (r.edge (index j)).val = 1
  other : ∀ i,(∀ j,index j ≠ i) → appbIncidence M v (r.edge i).val = 0

namespace AppbTripleFrame
variable {M : Molecule V D} {P : AppbPattern} {r : AppbRealization M P} {v : V}
    (t : AppbTripleFrame r v)

def project {K : Type*} (q : Fin P.edges.length → K) : Fin 3 → K := fun j => q (t.index j)

theorem sum_index {E : Type*} [AddCommMonoid E] (f : Fin P.edges.length → E)
    (hzero : ∀ i,(∀ j,t.index j ≠ i) → f i = 0) :
    (∑ i,f i) = ∑ j : Fin 3,f (t.index j) := by
  classical
  have himg : (∑ i ∈ (univ : Finset (Fin 3)).image t.index,f i) = ∑ j : Fin 3,f (t.index j) :=
    sum_image (fun a _ b _ h => t.index.injective h)
  rw [← himg]
  symm
  apply sum_subset (subset_univ _)
  intro i hi hn
  apply hzero i
  intro j he
  exact hn (mem_image.mpr ⟨j,mem_univ _,he⟩)

/-- Reindex the actual signed incidence sum onto the three-bond support. -/
theorem sum_incidence {E : Type*} [AddCommGroup E] (f : Fin P.edges.length → E) :
    (∑ i : Fin P.edges.length,
      ((if M.atom (r.edge i).val = v then f i else 0)-
        (if M.atom (M.mate (r.edge i).val) = v then f i else 0))) =
    ∑ j : Fin 3,(appbIncidenceSign M v (r.edge (t.index j)).val : ℤ) • f (t.index j) := by
  rw [t.sum_index]
  · apply sum_congr rfl
    intro j hj
    exact appb_incidence_sign_eq M v _ (t.incidence j) _
  · intro i hi
    have hh := t.other i hi
    by_cases h1 : M.atom (r.edge i).val = v <;>
      by_cases h2 : M.atom (M.mate (r.edge i).val) = v
    all_goals simp_all [appbIncidence]

/-- The source caps produce the signed triple ordering on this support. -/
theorem exists_order (hM : M.IsMolecule) (hv : v ∈ M.atoms) :
    ∃ π : Equiv.Perm (Fin 3),
      appbIncidenceSign M v (r.edge (t.index (π 0))).val =
        appbIncidenceSign M v (r.edge (t.index (π 2))).val ∧
      appbIncidenceSign M v (r.edge (t.index (π 0))).val ≠
        appbIncidenceSign M v (r.edge (t.index (π 1))).val :=
  appb_three_sign_permutation _ (r.not_all_positive_frame_signs hM t.index hv)
    (r.not_all_negative_frame_signs hM t.index hv t.incidence)

end AppbTripleFrame
end WaveTurbulence.Mole
