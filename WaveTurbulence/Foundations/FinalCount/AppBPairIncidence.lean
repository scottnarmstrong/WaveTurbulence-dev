/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceSigns
import Mathlib.Tactic

/-! # A degree-two atom inside a larger local operation -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Actual two-incidence support in the figure enumeration. These are
input graph facts, with no counting or post-operation fields. -/
structure AppbLocalPair {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) (v : V) where
  first : Fin P.edges.length
  second : Fin P.edges.length
  distinct : first ≠ second
  incidence_first : appbIncidence M v (r.edge first).val = 1
  incidence_second : appbIncidence M v (r.edge second).val = 1
  incidence_other : ∀ i,i ≠ first → i ≠ second → appbIncidence M v (r.edge i).val = 0

namespace AppbLocalPair
variable {M : Molecule V D} {P : AppbPattern} {r : AppbRealization M P} {v : V}
    (p : AppbLocalPair r v)

def project {K : Type*} (q : Fin P.edges.length → K) : K × K := (q p.first,q p.second)

/-- Only the two actual incidences contribute, with their source signs. -/
theorem sum_incidence {E : Type*} [AddCommGroup E] (f : Fin P.edges.length → E) :
    (∑ i : Fin P.edges.length,
      ((if M.atom (r.edge i).val = v then f i else 0)-
        (if M.atom (M.mate (r.edge i).val) = v then f i else 0))) =
      (appbIncidenceSign M v (r.edge p.first).val : ℤ) • f p.first+
      (appbIncidenceSign M v (r.edge p.second).val : ℤ) • f p.second := by
  rw [sum_eq_add_of_mem p.first p.second (mem_univ _) (mem_univ _) p.distinct]
  · rw [appb_incidence_sign_eq M v _ p.incidence_first,
      appb_incidence_sign_eq M v _ p.incidence_second]
  · intro i hi hne
    have hh := p.incidence_other i hne.1 hne.2
    by_cases h1 : M.atom (r.edge i).val = v <;>
      by_cases h2 : M.atom (M.mate (r.edge i).val) = v
    all_goals simp_all [appbIncidence]

theorem momentum {d : ℕ} (hv : v ∈ r.removedAtoms) (L : ℝ) (w : Mom d)
    (c : V → Mom d) (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ) :
    (appbIncidenceSign M v (r.edge p.first).val : ℤ) • Molecule.kvec L w (r.localLabels κ) p.first+
      (appbIncidenceSign M v (r.edge p.second).val : ℤ) • Molecule.kvec L w (r.localLabels κ) p.second = c v := by
  have hm := r.local_momentum L w c κ hκ hv
  rw [p.sum_incidence] at hm
  exact hm

theorem energy {d : ℕ} (hv : v ∈ r.removedAtoms) (L γ δ : ℝ) (w : Mom d)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hres : M.IsRestricted L γ δ w β k0 κ) :
    |(appbIncidenceSign M v (r.edge p.first).val : ℤ)*‖Molecule.kvec L w (r.localLabels κ) p.first‖^2+
      (appbIncidenceSign M v (r.edge p.second).val : ℤ)*‖Molecule.kvec L w (r.localLabels κ) p.second‖^2-β v| ≤
      δ⁻¹*L^(-2*γ) := by
  have he := r.local_energy L γ δ w c β k0 κ hκ hres hv
  rw [p.sum_incidence] at he
  simpa only [zsmul_eq_mul] using he

end AppbLocalPair
end WaveTurbulence.Mole
