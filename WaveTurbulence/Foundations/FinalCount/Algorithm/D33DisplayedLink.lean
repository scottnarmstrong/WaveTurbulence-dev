/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SingleBondDirection
public import WaveTurbulence.Foundations.FinalCount.AppBD33ScaleValidity
import Mathlib.Tactic

/-! # The actual displayed link at a normal double-pair removal -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A double boundary rung and opposite old rails form the precise selected
link whose weight cancels in normal 3D3. No continuation count is assumed. -/
theorem d33_displayed_link_of_double (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (h34 : M.bondsBetween (r.vertex 3) (r.vertex 4) = 2)
    (hopp : AppbD33BoundaryOpposite M r) :
    appbD33LinkAtoms r ∈ appbLinks M := by
  classical
  let u : Fin 2 → V := ![r.vertex 1,r.vertex 3]
  let v : Fin 2 → V := ![r.vertex 2,r.vertex 4]
  let code : Fin 2 ⊕ Fin 2 → ℕ := Sum.elim ![1,3] ![2,4]
  have hcode : Function.Injective code := by decide
  have hc : ∀ i,code i ∈ AppbPatternKind.d33.pattern.vertices := by decide
  have hinj : Function.Injective (Sum.elim u v) := by
    intro i j hij
    apply hcode
    apply r.vertex_injective (hc i) (hc j)
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> exact hij
  have hm13 : M.bondsBetween (r.vertex 1) (r.vertex 3) = 1 :=
    (r.bondsBetween_vertices_eq 1 3 (by decide) (by decide)).trans (by decide)
  have hm24 : M.bondsBetween (r.vertex 2) (r.vertex 4) = 1 :=
    (r.bondsBetween_vertices_eq 2 4 (by decide) (by decide)).trans (by decide)
  have hn13 : r.vertex 1 ≠ r.vertex 3 :=
    (r.vertex_eq_iff 1 3 (by decide) (by decide)).not.mpr (by decide)
  have hn24 : r.vertex 2 ≠ r.vertex 4 :=
    (r.vertex_eq_iff 2 4 (by decide) (by decide)).not.mpr (by decide)
  have hout (i : Fin 4) : M.out (r.edge i).val = true :=
    (mem_filter.mp (mem_filter.mp (r.edge i).property).1).2
  have hd : M.Directed (r.vertex 1) (r.vertex 3) ↔ M.Directed (r.vertex 4) (r.vertex 2) := by
    rw [directed_iff_outgoing_atom M hn13 hm13 (hout 2) (r.endpoints (2 : Fin 4)),
      directed_reverse_iff_outgoing_atom_ne M hn24 hm24 (hout 3) (r.endpoints (3 : Fin 4))]
    exact hopp
  have hL : Degen.SourceLadder (m := 1) M u v := by
    refine ⟨by decide,hinj,?_,?_,?_⟩
    · intro i
      fin_cases i
      · exact ⟨r.vertex_mem 1 (by decide),r.vertex_mem 2 (by decide)⟩
      · exact ⟨r.vertex_mem 3 (by decide),r.vertex_mem 4 (by decide)⟩
    · intro i
      fin_cases i
      · exact appb_d33_internal_multiplicity M r
      · exact h34
    · intro i
      fin_cases i
      exact ⟨hm13,hm24,hd⟩
  apply (mem_appbLinks M _).mpr
  refine ⟨u,v,hL,?_⟩
  ext x
  simp [Molecule.ladderAtoms,u,v,appbD33LinkAtoms,Fin.exists_fin_two,eq_comm,or_left_comm,or_assoc]

/-- For the normal opposite-rail case, the displayed link is present
exactly when the surviving boundary pair is a double rung. -/
theorem d33_displayed_link_iff_double (M : Molecule V D) (hM : M.IsMolecule)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (hopp : AppbD33BoundaryOpposite M r) :
    appbD33LinkAtoms r ∈ appbLinks M ↔
      M.bondsBetween (r.vertex 3) (r.vertex 4) = 2 := by
  constructor
  · intro h
    obtain ⟨u,v,hL,_,_,_,h3,h4⟩ := appb_d33_link_presentation M hM r ((mem_appbLinks M _).mp h)
    have hh := hL.2.2.2.1 (1 : Fin 2)
    simpa only [h3,h4] using hh
  · exact fun h => d33_displayed_link_of_double M r h hopp

end WaveTurbulence.Mole.AppbAlgorithm
