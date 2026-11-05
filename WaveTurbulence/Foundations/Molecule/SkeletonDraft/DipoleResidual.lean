/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Dipoles

/-! # Disjoint mini pieces survive and their contractions commute -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

theorem pairPorts_append {α : Type*} (P Q : List (α × α)) :
    pairPorts (P++Q) = pairPorts P ++ pairPorts Q := by simp only [pairPorts,List.flatMap_append]

theorem foldSplice_append {α : Type*} [DecidableEq α] (P Q : List (α × α)) (m : α → α) :
    foldSplice m (P++Q) = foldSplice (foldSplice m P) Q := by
  induction P generalizing m with
  | nil => rfl
  | cons p P ih => exact ih _

namespace Dipole

/-- The same second mini piece in the matching after deleting a disjoint first piece. -/
def residual {V : Type*} [DecidableEq V] {mate : V × Fin 4 → V × Fin 4}
    (D E : Dipole mate) (hm : Function.Involutive mate)
    (hd : D.u ≠ E.u ∧ D.u ≠ E.v ∧ D.v ≠ E.u ∧ D.v ≠ E.v) : Dipole D.contract where
  u := E.u
  v := E.v
  ne := E.ne
  perm := E.perm
  free := E.free
  active_u i := fun he => E.active_u i
    ((D.contract_fixed_iff hm (E.u,i) hd.1.symm hd.2.2.1.symm).mp he)
  active_v i := fun he => E.active_v i
    ((D.contract_fixed_iff hm (E.v,i) hd.2.1.symm hd.2.2.2.symm).mp he)
  internal i hi := by
    have he := E.internal i hi
    exact (D.contract_unaffected (E.u,i) hd.1.symm hd.2.2.1.symm
      (by rw [he]; exact hd.2.1.symm) (by rw [he]; exact hd.2.2.2.symm)).trans he

/-- The two disjoint target lists remain a disjoint list of eight-port deletions. -/
theorem append_targets_nodup {V : Type*} [DecidableEq V] {mate : V × Fin 4 → V × Fin 4}
    (D E : Dipole mate) (hd : D.u ≠ E.u ∧ D.u ≠ E.v ∧ D.v ≠ E.u ∧ D.v ≠ E.v) :
    (pairPorts (D.pairs++E.pairs)).Nodup := by
  rw [pairPorts_append]
  apply List.nodup_append.mpr
  refine ⟨D.pairPorts_nodup,E.pairPorts_nodup,?_⟩
  intro x hx y hy he
  have hh := congrArg Prod.fst he
  rcases (D.pairPorts_mem x).mp hx with hxu | hxv
  · rcases (E.pairPorts_mem y).mp hy with hyu | hyv
    · exact hd.1 (hxu.symm.trans (hh.trans hyu))
    · exact hd.2.1 (hxu.symm.trans (hh.trans hyv))
  · rcases (E.pairPorts_mem y).mp hy with hyu | hyv
    · exact hd.2.2.1 (hxv.symm.trans (hh.trans hyu))
    · exact hd.2.2.2 (hxv.symm.trans (hh.trans hyv))

/-- Disjoint whole-piece contractions commute, retaining all surviving labels. -/
theorem contract_commute {V : Type*} [DecidableEq V] {mate : V × Fin 4 → V × Fin 4}
    (D E : Dipole mate) (hm : Function.Involutive mate)
    (hd : D.u ≠ E.u ∧ D.u ≠ E.v ∧ D.v ≠ E.u ∧ D.v ≠ E.v) :
    foldSplice D.contract E.pairs = foldSplice E.contract D.pairs := by
  have hn := D.append_targets_nodup E hd
  have ha : ∀ x ∈ pairPorts (D.pairs++E.pairs), mate x ≠ x := by
    intro x hx
    rw [pairPorts_append] at hx
    rcases List.mem_append.mp hx with h | h
    · exact D.targets_active x h
    · exact E.targets_active x h
  have he := foldSplice_perm (List.perm_append_comm (l₁ := D.pairs) (l₂ := E.pairs)) mate hm hn ha
  rw [foldSplice_append,foldSplice_append] at he
  exact he

/-- The explicit residual pieces give the same common reduct. -/
theorem residual_contract_eq {V : Type*} [DecidableEq V] {mate : V × Fin 4 → V × Fin 4}
    (D E : Dipole mate) (hm : Function.Involutive mate)
    (hd : D.u ≠ E.u ∧ D.u ≠ E.v ∧ D.v ≠ E.u ∧ D.v ≠ E.v) :
    (D.residual E hm hd).contract =
      (E.residual D hm ⟨hd.1.symm,hd.2.2.1.symm,hd.2.1.symm,hd.2.2.2.symm⟩).contract :=
  D.contract_commute E hm hd

end Dipole
end WaveTurbulence.Reg.Skeleton
