/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.DipoleResidual
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SpliceEnumeration

/-! # A mini-piece contraction depends only on its unordered vertex pair -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
namespace Dipole

/-- Reverse the two vertices, retaining the same actual internal bonds. -/
def flip {V : Type*} {mate : V × Fin 4 → V × Fin 4} (D : Dipole mate)
    (hm : Function.Involutive mate) : Dipole mate where
  u := D.v
  v := D.u
  ne := D.ne.symm
  perm := D.perm.symm
  free := D.perm D.free
  active_u := D.active_v
  active_v := D.active_u
  internal j hj := by
    let i := D.perm.symm j
    have hi : i ≠ D.free := fun h => hj
      ((D.perm.apply_symm_apply j).symm.trans (congrArg D.perm h))
    have he := D.internal i hi
    have hh := hm (D.u,i)
    rw [he] at hh
    simpa only [i,Equiv.apply_symm_apply] using hh

/-- The same oriented vertex pair has the same literal four splice pairs. -/
theorem pairs_eq_of_vertices {V : Type*} {mate : V × Fin 4 → V × Fin 4}
    (D E : Dipole mate) (hm : Function.Involutive mate) (hu : D.u = E.u) (hv : D.v = E.v) :
    D.pairs = E.pairs := by
  have hp := D.perm_unique E hm hu hv
  unfold pairs
  rw [hu,hv,hp]

theorem contract_eq_of_vertices {V : Type*} [DecidableEq V] {mate : V × Fin 4 → V × Fin 4}
    (D E : Dipole mate) (hm : Function.Involutive mate) (hu : D.u = E.u) (hv : D.v = E.v) :
    D.contract = E.contract := congrArg (foldSplice mate) (D.pairs_eq_of_vertices E hm hu hv)

/-- Reversal only permutes the four pairs and swaps their endpoints. -/
theorem flip_pairs_perm {V : Type*} {mate : V × Fin 4 → V × Fin 4}
    (D : Dipole mate) (hm : Function.Involutive mate) :
    (D.pairs.map Prod.swap).Perm (D.flip hm).pairs := by
  have he := ofFn_perm_equiv D.perm (fun i => ((D.v,i),(D.u,D.perm.symm i)))
  simpa only [pairs,flip,List.map_ofFn,Function.comp_def,Prod.swap,Equiv.symm_apply_apply] using he

/-- Reversing a dipole changes no part of its contraction. -/
theorem contract_flip {V : Type*} [DecidableEq V] {mate : V × Fin 4 → V × Fin 4}
    (D : Dipole mate) (hm : Function.Involutive mate) : (D.flip hm).contract = D.contract := by
  have he := foldSplice_perm (D.flip_pairs_perm hm).symm mate hm
    (D.flip hm).pairPorts_nodup (D.flip hm).targets_active
  exact he.trans (foldSplice_map_swap D.pairs mate)

/-- Equal unordered vertex interiors are presentations of the same elementary contraction. -/
theorem contract_eq_of_unordered {V : Type*} [DecidableEq V] {mate : V × Fin 4 → V × Fin 4}
    (D E : Dipole mate) (hm : Function.Involutive mate)
    (huv : (D.u = E.u ∧ D.v = E.v) ∨ (D.u = E.v ∧ D.v = E.u)) :
    D.contract = E.contract := by
  rcases huv with h | h
  · exact D.contract_eq_of_vertices E hm h.1 h.2
  · exact (D.contract_flip hm).symm.trans ((D.flip hm).contract_eq_of_vertices E hm h.2 h.1)

end Dipole
end WaveTurbulence.Reg.Skeleton
