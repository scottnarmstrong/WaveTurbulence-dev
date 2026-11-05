/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SplicePermutation

/-! # Label-preserving contraction data for a four-port mini piece

Three prescribed bonds join the two active vertices. The fourth is either the
pair of external attachment ports or an additional internal bond. The contraction
is the four disjoint port splices and depends on no choice of a free-index witness.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- An active three-bond piece, with its uniquely extended port permutation. -/
structure Dipole {V : Type*} (mate : V × Fin 4 → V × Fin 4) where
  u : V
  v : V
  ne : u ≠ v
  perm : Equiv.Perm (Fin 4)
  free : Fin 4
  active_u : ∀ i, mate (u,i) ≠ (u,i)
  active_v : ∀ i, mate (v,i) ≠ (v,i)
  internal : ∀ i, i ≠ free → mate (u,i) = (v,perm i)

namespace Dipole

def pairs {V : Type*} {mate : V × Fin 4 → V × Fin 4} (D : Dipole mate) :
    List ((V × Fin 4) × (V × Fin 4)) :=
  List.ofFn fun i : Fin 4 => ((D.u,i),(D.v,D.perm i))

def contract {V : Type*} [DecidableEq V] {mate : V × Fin 4 → V × Fin 4} (D : Dipole mate) :
    V × Fin 4 → V × Fin 4 := foldSplice mate D.pairs

/-- A port is deleted precisely when it belongs to one of the two vertices. -/
theorem pairPorts_mem {V : Type*} {mate : V × Fin 4 → V × Fin 4} (D : Dipole mate) (x : V × Fin 4) :
    x ∈ pairPorts D.pairs ↔ x.1 = D.u ∨ x.1 = D.v := by
  constructor
  · intro hx
    obtain ⟨p,hp,hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with h | h
    · exact Or.inl (congrArg Prod.fst h)
    · exact Or.inr (congrArg Prod.fst h)
  · intro hx
    rcases hx with h | h
    · apply List.mem_flatMap.mpr
      refine ⟨((D.u,x.2),(D.v,D.perm x.2)),List.mem_ofFn.mpr ⟨x.2,rfl⟩,?_⟩
      exact List.mem_cons.mpr (Or.inl (Prod.ext h rfl))
    · apply List.mem_flatMap.mpr
      refine ⟨((D.u,D.perm.symm x.2),(D.v,D.perm (D.perm.symm x.2))),
        List.mem_ofFn.mpr ⟨D.perm.symm x.2,rfl⟩,?_⟩
      apply List.mem_cons.mpr
      apply Or.inr
      apply List.mem_singleton.mpr
      exact Prod.ext h (D.perm.apply_symm_apply x.2).symm

/-- The four splice pairs have eight distinct targets. -/
theorem pairPorts_nodup {V : Type*} [DecidableEq V] {mate : V × Fin 4 → V × Fin 4} (D : Dipole mate) :
    (pairPorts D.pairs).Nodup := by
  change [(D.u,0),(D.v,D.perm 0),(D.u,1),(D.v,D.perm 1),
    (D.u,2),(D.v,D.perm 2),(D.u,3),(D.v,D.perm 3)].Nodup
  simp [D.ne,Ne.symm D.ne,D.perm.injective.eq_iff]

theorem targets_active {V : Type*} {mate : V × Fin 4 → V × Fin 4} (D : Dipole mate) :
    ∀ x ∈ pairPorts D.pairs, mate x ≠ x := by
  rintro ⟨s,i⟩ hx
  rcases (D.pairPorts_mem _).mp hx with h | h
  · change s = D.u at h
    subst s
    exact D.active_u i
  · change s = D.v at h
    subst s
    exact D.active_v i

/-- Whole-piece contraction preserves the exact matching, including inactive ports. -/
theorem contract_involutive {V : Type*} [DecidableEq V] {mate : V × Fin 4 → V × Fin 4}
    (D : Dipole mate) (hm : Function.Involutive mate) : Function.Involutive D.contract :=
  (foldSplice_properties D.pairs mate hm D.pairPorts_nodup D.targets_active).1

/-- Both contracted vertices become inactive, with their original labels retained. -/
theorem contract_fixed {V : Type*} [DecidableEq V] {mate : V × Fin 4 → V × Fin 4}
    (D : Dipole mate) (x : V × Fin 4) (hx : x.1 = D.u ∨ x.1 = D.v) : D.contract x = x :=
  foldSplice_target_fixed D.pairs mate x ((D.pairPorts_mem x).mpr hx)

/-- No surviving vertex loses activity under a mini-piece contraction. -/
theorem contract_fixed_iff {V : Type*} [DecidableEq V] {mate : V × Fin 4 → V × Fin 4}
    (D : Dipole mate) (hm : Function.Involutive mate) (x : V × Fin 4)
    (hu : x.1 ≠ D.u) (hv : x.1 ≠ D.v) : D.contract x = x ↔ mate x = x :=
  (foldSplice_properties D.pairs mate hm D.pairPorts_nodup D.targets_active).2 x
    (fun h => ((D.pairPorts_mem x).mp h).elim hu hv)

/-- Every edge between surviving vertices is unchanged. -/
theorem contract_unaffected {V : Type*} [DecidableEq V] {mate : V × Fin 4 → V × Fin 4}
    (D : Dipole mate) (x : V × Fin 4) (hu : x.1 ≠ D.u) (hv : x.1 ≠ D.v)
    (hmu : (mate x).1 ≠ D.u) (hmv : (mate x).1 ≠ D.v) : D.contract x = mate x :=
  foldSplice_unaffected D.pairs mate x (fun h => ((D.pairPorts_mem x).mp h).elim hu hv)
    (fun h => ((D.pairPorts_mem (mate x)).mp h).elim hmu hmv)

/-- The prescribed three bonds give the graph-level mini-piece predicate. -/
theorem threeBonds {V : Type*} [DecidableEq V] {mate : V × Fin 4 → V × Fin 4} (D : Dipole mate) :
    ThreeBonds mate D.u D.v := by
  have hs : Finset.univ.erase D.free ⊆ portsTo mate D.u D.v := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,congrArg Prod.fst (D.internal i (Finset.mem_erase.mp hi).1)⟩
  have hc := Finset.card_le_card hs
  have hn : (Finset.univ.erase D.free).card = 3 := by simp
  unfold ThreeBonds
  omega

/-- The possible fourth bond must use the same extended port permutation. -/
theorem cross {V : Type*} {mate : V × Fin 4 → V × Fin 4}
    (D : Dipole mate) (hm : Function.Involutive mate) (i : Fin 4)
    (hi : (mate (D.u,i)).1 = D.v) : mate (D.u,i) = (D.v,D.perm i) := by
  by_cases hf : i = D.free
  · let j := (mate (D.u,i)).2
    let k := D.perm.symm j
    have hk : D.perm k = j := D.perm.apply_symm_apply j
    by_cases hki : k = i
    · exact Prod.ext hi (by
        change j = D.perm i
        exact hk.symm.trans (congrArg D.perm hki))
    · have hkf : k ≠ D.free := fun h => hki (h.trans hf.symm)
      have he := D.internal k hkf
      have heq : mate (D.u,k) = mate (D.u,i) := by
        rw [he]
        exact Prod.ext hi.symm hk
      exact (hki (congrArg Prod.snd (hm.injective heq))).elim
  · exact D.internal i hf

end Dipole

/-- Bijections that agree off one point agree everywhere. -/
theorem equiv_eq_of_agree_except {α β : Type*} (p q : α ≃ β) (k : α)
    (h : ∀ i, i ≠ k → p i = q i) : p = q := by
  apply Equiv.ext
  intro i
  by_cases hi : i = k
  · subst i
    let j := q.symm (p k)
    have hj : q j = p k := q.apply_symm_apply (p k)
    by_cases hk : j = k
    · exact (congrArg q hk).symm.trans hj |>.symm
    · exact (hk (p.injective ((h j hk).trans hj))).elim
  · exact h i hi

/-- The port permutation is fixed by the actual matching, not by reduction data. -/
theorem Dipole.perm_unique {V : Type*} {mate : V × Fin 4 → V × Fin 4}
    (D E : Dipole mate) (hm : Function.Involutive mate) (hu : D.u = E.u) (hv : D.v = E.v) :
    D.perm = E.perm := by
  apply equiv_eq_of_agree_except D.perm E.perm D.free
  intro i hi
  have hd := D.internal i hi
  have he := E.cross hm i (by rw [← hu,hd]; exact hv)
  rw [← hu,← hv] at he
  exact congrArg Prod.snd (hd.symm.trans he)

end WaveTurbulence.Reg.Skeleton
