/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.PairBondEnumeration
import Mathlib.Tactic

/-! # Complete remaining-edge enumeration after fixing a parallel bond family -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

structure BoundaryStar (M : Molecule V D) (a b : V) (k : ℕ) where
  edge : Fin k ≃ {x // x ∈ appbRemovedBonds M {a} \ parallelBonds M a b}
  neighbor : Fin k → V
  neighbor_mem : ∀ i,neighbor i ∈ M.atoms
  neighbor_ne_center : ∀ i,neighbor i ≠ a
  neighbor_ne_partner : ∀ i,neighbor i ≠ b
  endpoints : ∀ i,M.ends (edge i).val = s(a,neighbor i)

noncomputable def boundaryStarOfDegree (M : Molecule V D) (hno : AppbNoLoops M)
    {a b : V} {n k : ℕ} (hd : M.deg a = n+k) (hm : M.bondsBetween a b = n) :
    BoundaryStar M a b k := by
  classical
  have hcard : (appbRemovedBonds M {a} \ parallelBonds M a b).card = k := by
    rw [card_sdiff_of_subset (parallelBonds_subset_incident M a b),incident_card_eq_degree M hno,hd]
    change n+k-M.bondsBetween a b = k
    rw [hm]
    omega
  let e := (equivFinOfCardEq hcard).symm
  let st := starOfDegree M hno a (n+k) hd
  let j := fun i : Fin k => st.edge.symm ⟨(e i).val,(mem_sdiff.mp (e i).property).1⟩
  have he (i : Fin k) : (st.edge (j i)).val = (e i).val :=
    congrArg Subtype.val (st.edge.apply_symm_apply _)
  have hend (i : Fin k) : M.ends (e i).val = s(a,st.neighbor (j i)) := by
    rw [← he]; exact st.endpoints (j i)
  exact {
    edge := e
    neighbor := fun i => st.neighbor (j i)
    neighbor_mem i := st.neighbor_mem (j i)
    neighbor_ne_center i := st.neighbor_ne (j i)
    neighbor_ne_partner := by
      intro i hb
      apply (mem_sdiff.mp (e i).property).2
      apply mem_filter.mpr
      exact ⟨(mem_filter.mp (mem_sdiff.mp (e i).property).1).1,
        by simpa only [hb] using hend i⟩
    endpoints := hend
  }

end WaveTurbulence.Mole.AppbAlgorithm
