/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBSideEquations
import Mathlib.Tactic

/-! # Gluing actual component parameter fibers -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def appbGlueParameters (M : Molecule V D) (S : Finset V) (h : AppbClosedSide M S)
    {d : ℕ} (p1 : AppbCountParameters (appbSideMolecule M S h) d)
    (p2 : AppbCountParameters (appbSideMolecule M (M.atoms \ S) h.complement) d) : AppbCountParameters M d where
  momentum := fun v => if v ∈ S then p1.momentum v else p2.momentum v
  energy := fun v => if v ∈ S then p1.energy v else p2.energy v
  center := appbGlueLabels M S p1.center p2.center
  center_mate := by
    classical
    intro x
    by_cases hx : M.atom x ∈ S
    · have hm := (h.mate_mem x).mp hx
      have hh := p1.center_mate ⟨x,hx⟩
      simpa only [appbGlueLabels,appbSideMolecule,dite_eq_left hx,dite_eq_left hm] using hh
    · have hm : M.atom (M.mate x) ∉ S := fun hh => hx ((h.mate_mem x).mpr hh)
      have hh := p2.center_mate ⟨x,mem_sdiff.mpr ⟨M.atom_mem x,hx⟩⟩
      simpa only [appbGlueLabels,appbSideMolecule,dite_eq_right hx,dite_eq_right hm] using hh

/-- Bond-constant labels glue to bond-constant labels because the side is
closed under the actual mate involution. -/
theorem appbGlueLabels_mate {K : Type*} (M : Molecule V D) (S : Finset V) (h : AppbClosedSide M S)
    (κ1 : AppbSideDart M S → K) (κ2 : AppbSideDart M (M.atoms \ S) → K)
    (h1 : ∀ x,κ1 ((appbSideMolecule M S h).mate x) = κ1 x)
    (h2 : ∀ x,κ2 ((appbSideMolecule M (M.atoms \ S) h.complement).mate x) = κ2 x) :
    ∀ x,appbGlueLabels M S κ1 κ2 (M.mate x) = appbGlueLabels M S κ1 κ2 x := by
  classical
  intro x
  by_cases hx : M.atom x ∈ S
  · have hm := (h.mate_mem x).mp hx
    simpa only [appbGlueLabels,appbSideMolecule,dite_eq_left hx,dite_eq_left hm] using h1 ⟨x,hx⟩
  · have hm : M.atom (M.mate x) ∉ S := fun hh => hx ((h.mate_mem x).mpr hh)
    simpa only [appbGlueLabels,appbSideMolecule,dite_eq_right hx,dite_eq_right hm] using h2 ⟨x,mem_sdiff.mpr ⟨M.atom_mem x,hx⟩⟩

theorem appb_isDecoration_glue (M : Molecule V D) (S : Finset V) (h : AppbClosedSide M S)
    {d : ℕ} (L : ℝ) (w : Mom d)
    (p1 : AppbCountParameters (appbSideMolecule M S h) d)
    (p2 : AppbCountParameters (appbSideMolecule M (M.atoms \ S) h.complement) d)
    (κ1 : AppbSideDart M S → (Fin d → ℤ)) (κ2 : AppbSideDart M (M.atoms \ S) → (Fin d → ℤ))
    (h1 : (appbSideMolecule M S h).IsDecoration L w p1.momentum κ1)
    (h2 : (appbSideMolecule M (M.atoms \ S) h.complement).IsDecoration L w p2.momentum κ2) :
    M.IsDecoration L w (appbGlueParameters M S h p1 p2).momentum (appbGlueLabels M S κ1 κ2) := by
  refine ⟨appbGlueLabels_mate M S h κ1 κ2 h1.1 h2.1,?_⟩
  intro v hv
  by_cases hs : v ∈ S
  · have hh := appb_side_momentum_sum M S h L w (appbGlueLabels M S κ1 κ2) hs
    rw [appbGlueLabels_left] at hh
    rw [← hh]
    exact (h1.2 v hs).trans (by simp only [appbGlueParameters,hs,ite_true])
  · have hv2 : v ∈ M.atoms \ S := mem_sdiff.mpr ⟨hv,hs⟩
    have hh := appb_side_momentum_sum M (M.atoms \ S) h.complement L w (appbGlueLabels M S κ1 κ2) hv2
    rw [appbGlueLabels_right] at hh
    rw [← hh]
    exact (h2.2 v hv2).trans (by simp only [appbGlueParameters,hs,ite_false])

theorem appb_isRestricted_glue (M : Molecule V D) (S : Finset V) (h : AppbClosedSide M S)
    {d : ℕ} (L γ δ : ℝ) (w : Mom d)
    (p1 : AppbCountParameters (appbSideMolecule M S h) d)
    (p2 : AppbCountParameters (appbSideMolecule M (M.atoms \ S) h.complement) d)
    (κ1 : AppbSideDart M S → (Fin d → ℤ)) (κ2 : AppbSideDart M (M.atoms \ S) → (Fin d → ℤ))
    (h1 : (appbSideMolecule M S h).IsRestricted L γ δ w p1.energy p1.center κ1)
    (h2 : (appbSideMolecule M (M.atoms \ S) h.complement).IsRestricted L γ δ w p2.energy p2.center κ2) :
    M.IsRestricted L γ δ w (appbGlueParameters M S h p1 p2).energy
      (appbGlueParameters M S h p1 p2).center (appbGlueLabels M S κ1 κ2) := by
  constructor
  · intro v hv
    by_cases hs : v ∈ S
    · have hh := appb_side_Gamma_eq M S h L w (appbGlueLabels M S κ1 κ2) hs
      rw [appbGlueLabels_left] at hh
      rw [← hh]
      simpa only [appbGlueParameters,hs,ite_true] using h1.1 v hs
    · have hv2 : v ∈ M.atoms \ S := mem_sdiff.mpr ⟨hv,hs⟩
      have hh := appb_side_Gamma_eq M (M.atoms \ S) h.complement L w (appbGlueLabels M S κ1 κ2) hv2
      rw [appbGlueLabels_right] at hh
      rw [← hh]
      simpa only [appbGlueParameters,hs,ite_false] using h2.1 v hv2
  · intro x
    classical
    by_cases hx : M.atom x ∈ S
    · simpa only [appbGlueParameters,appbGlueLabels,Molecule.kvec,dif_pos hx] using h1.2 ⟨x,hx⟩
    · simpa only [appbGlueParameters,appbGlueLabels,Molecule.kvec,dif_neg hx] using
        h2.2 ⟨x,mem_sdiff.mpr ⟨M.atom_mem x,hx⟩⟩

end WaveTurbulence.Mole
