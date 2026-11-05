/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.DipoleOrientation

/-! # The labelled four-port reduction is strongly confluent

Vertices retain their labels after contraction as inactive ports. This proves
uniqueness of the surviving labelled graph, not merely an unlabelled shape.
The equivalence with source mini pieces is a separate source-facing theorem.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- A literal port matching, including the inactive ports of previously deleted vertices. -/
structure PortMatching (V : Type*) where
  mate : V × Fin 4 → V × Fin 4
  involutive : Function.Involutive mate

theorem PortMatching.ext {V : Type*} {M N : PortMatching V} (h : M.mate = N.mate) : M = N := by
  cases M
  cases N
  cases h
  rfl

namespace PortMatching

/-- One mini-piece contraction, retaining every vertex label. -/
def Step {V : Type*} [DecidableEq V] (M N : PortMatching V) : Prop :=
  ∃ D : Dipole M.mate, N.mate = D.contract

/-- No eligible mini piece remains in a terminal labelled matching. -/
def Normal {V : Type*} [DecidableEq V] (M : PortMatching V) : Prop := ∀ N, ¬ Step M N

/-- Finitely many literal labelled contractions. -/
def Reduces {V : Type*} [DecidableEq V] (M N : PortMatching V) : Prop := Relation.ReflTransGen Step M N

/-- Strong diamond: equal mini interiors give the same reduct; distinct interiors
are disjoint and their two residual contractions commute. -/
theorem step_diamond {V : Type*} [DecidableEq V] (M N P : PortMatching V)
    (hN : Step M N) (hP : Step M P) :
    ∃ Q, Relation.ReflGen Step N Q ∧ Relation.ReflGen Step P Q := by
  obtain ⟨D,hD⟩ := hN
  obtain ⟨E,hE⟩ := hP
  by_cases he : (D.u = E.u ∧ D.v = E.v) ∨ (D.u = E.v ∧ D.v = E.u)
  · have h : N = P := PortMatching.ext
      (hD.trans ((D.contract_eq_of_unordered E M.involutive he).trans hE.symm))
    subst P
    exact ⟨N,.refl,.refl⟩
  · have hd := threeBonds_interiors_disjoint M.mate M.involutive D.u D.v E.u E.v
      D.threeBonds E.threeBonds he
    let N' : PortMatching V := ⟨D.contract,D.contract_involutive M.involutive⟩
    let P' : PortMatching V := ⟨E.contract,E.contract_involutive M.involutive⟩
    have hn : N = N' := PortMatching.ext hD
    have hp : P = P' := PortMatching.ext hE
    subst N
    subst P
    let F := D.residual E M.involutive hd
    let H := E.residual D M.involutive ⟨hd.1.symm,hd.2.2.1.symm,hd.2.1.symm,hd.2.2.2.symm⟩
    let Q : PortMatching V := ⟨F.contract,F.contract_involutive (D.contract_involutive M.involutive)⟩
    refine ⟨Q,.single ⟨F,rfl⟩,.single ⟨H,?_⟩⟩
    exact D.residual_contract_eq E M.involutive hd

/-- Any two finite labelled contraction histories have a common reduct. -/
theorem church_rosser {V : Type*} [DecidableEq V] {M N P : PortMatching V}
    (hN : Reduces M N) (hP : Reduces M P) : ∃ Q, Reduces N Q ∧ Reduces P Q := by
  apply Relation.church_rosser (r := Step) ?_ hN hP
  intro A B C hB hC
  obtain ⟨D,hBD,hCD⟩ := step_diamond A B C hB hC
  refine ⟨D,hBD,?_⟩
  cases hCD with
  | refl => exact .refl
  | single h => exact .single h

/-- Terminal labelled graphs are unique, including the identities of all surviving vertices. -/
theorem normal_unique {V : Type*} [DecidableEq V] {M N P : PortMatching V}
    (hN : Normal N) (hP : Normal P) (hMN : Reduces M N) (hMP : Reduces M P) : N = P := by
  obtain ⟨Q,hNQ,hPQ⟩ := church_rosser hMN hMP
  have hn : Q = N := (Relation.reflTransGen_iff_eq hN).mp hNQ
  have hp : Q = P := (Relation.reflTransGen_iff_eq hP).mp hPQ
  exact hn.symm.trans hp

end PortMatching
end WaveTurbulence.Reg.Skeleton
