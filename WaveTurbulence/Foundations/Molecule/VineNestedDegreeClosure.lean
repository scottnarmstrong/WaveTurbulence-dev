/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineNestedGaps
public import WaveTurbulence.Foundations.Molecule.VineChainConnected
import Mathlib.Tactic

/-! # Exact nested degrees make an atomic group closed within the outer group -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- If a nested group already uses every outer incidence at each of its
atoms, an outer path cannot enter or leave that group. -/
theorem nested_degree_path_barrier (M : Molecule V D) {A U : Finset V}
    (hAU : A ⊆ U) (hd : ∀ v ∈ A,M.degIn A v=M.degIn U v)
    {u v : V} (hp : (Mole.induced M U).SameComponent u v) : (u ∈ A ↔ v ∈ A) := by
  have closed {x y : V} (hx : x ∈ A) (hxy : (Mole.induced M U).Adj x y) : y ∈ A := by
    obtain ⟨⟨d,hdx,hdy⟩,hxU,hyU⟩ := (Mole.induced_adj_iff M U x y).mp hxy
    have he := internal_darts_eq_of_nested_degree M hAU x (hd x hx)
    have hdin : d ∈ (M.dartsAt x).filter (M.InGroup U) := Finset.mem_filter.mpr
      ⟨(Mole.mem_dartsAt M x d).mpr hdx,hdx.symm ▸ hxU,hdy.symm ▸ hyU⟩
    rw [← he] at hdin
    exact hdy ▸ (Finset.mem_filter.mp hdin).2.2
  induction hp with
  | rel u v huv => exact ⟨fun hu => closed hu huv,fun hv => closed hv (Mole.adj_symmetric _ huv)⟩
  | refl u => exact Iff.rfl
  | symm u v _ ih => exact ih.symm
  | trans u v w _ _ ih1 ih2 => exact ih1.trans ih2

/-- A nonempty closed nested group in a connected atomic group is the
whole group. Exact incidence equality supplies closure automatically. -/
theorem nested_degree_eq_of_connected (M : Molecule V D) {A U : Finset V}
    (hAU : A ⊆ U) (hA : A.Nonempty) (hU : GroupConnected M U)
    (hd : ∀ v ∈ A,M.degIn A v=M.degIn U v) : A=U := by
  apply Finset.Subset.antisymm hAU
  obtain ⟨u,hu⟩ := hA
  intro v hv
  exact (nested_degree_path_barrier M hAU hd (hU u (hAU hu) v hv)).mp hu

end WaveTurbulence.Vine
