/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLinks
public import WaveTurbulence.Foundations.FinalCount.Degen.LadderDeletionGeometry
import Mathlib.Tactic

/-! # Consecutive-rung locations of selected links -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbRungInterval {m : ℕ} (u v : Fin (m+1) → V) (i : Fin m) : Finset V :=
  {u i.castSucc,u i.succ,v i.castSucc,v i.succ}

theorem appb_ladderAtoms_two (u v : Fin 2 → V) :
    Molecule.ladderAtoms u v = {u 0,u 1,v 0,v 1} := by
  ext x
  simp only [Molecule.ladderAtoms,mem_union,mem_image,mem_univ,true_and,mem_insert,mem_singleton]
  constructor
  · rintro (⟨j,rfl⟩ | ⟨j,rfl⟩) <;> fin_cases j <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl ⟨0,rfl⟩
    · exact Or.inl ⟨1,rfl⟩
    · exact Or.inr ⟨0,rfl⟩
    · exact Or.inr ⟨1,rfl⟩

/-- A selected link contained in a selected source ladder is exactly one
of its consecutive rung intervals. No induced-ladder premise is used. -/
theorem AppbLink.eq_rungInterval {M : Molecule V D} (hM : M.IsMolecule)
    {m : ℕ} {u v : Fin (m+1) → V} (hOld : Degen.SourceLadder M u v)
    {S : Finset V} (hS : AppbLink M S) (hsub : S ⊆ Molecule.ladderAtoms u v) :
    ∃ i : Fin m, S = appbRungInterval u v i := by
  obtain ⟨p,q,hNew,rfl⟩ := hS
  obtain ⟨i,hi | hi | hi | hi⟩ := Degen.sourceLadder_first_pair_alignment M hM hOld hNew hsub
  all_goals refine ⟨i,?_⟩
  all_goals rw [appb_ladderAtoms_two]
  all_goals rcases hi with ⟨h0,h1,h2,h3⟩
  all_goals change p 1 = _ at h2
  all_goals change q 1 = _ at h3
  all_goals simp only [h0,h1,h2,h3,appbRungInterval]
  all_goals ext x; simp only [mem_insert,mem_singleton]; tauto

/-- The intervals have distinct atom sets, so counting the links in a
ladder introduces no orientation or row-order multiplicity. -/
theorem appbRungInterval_injective {m : ℕ} {u v : Fin (m+1) → V}
    (hinj : Function.Injective (Sum.elim u v)) :
    Function.Injective (appbRungInterval u v) := by
  intro i j he
  have hmem : u i.castSucc ∈ appbRungInterval u v j := by
    rw [← he]
    simp [appbRungInterval]
  simp only [appbRungInterval,mem_insert,mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · have hh := hinj (show Sum.elim u v (Sum.inl i.castSucc) = Sum.elim u v (Sum.inl j.castSucc) from h)
    have hij : i.castSucc = j.castSucc := Sum.inl_injective hh
    exact Fin.ext (congrArg (fun x : Fin (m+1) => x.val) hij)
  · have hij : i.castSucc = j.succ := Sum.inl_injective (hinj h)
    have hmem' : u j.castSucc ∈ appbRungInterval u v i := by
      rw [he]
      simp [appbRungInterval]
    simp only [appbRungInterval,mem_insert,mem_singleton] at hmem'
    rcases hmem' with h' | h' | h' | h'
    · have hji : j.castSucc = i.castSucc := Sum.inl_injective (hinj h')
      have := congrArg Fin.val hij
      have := congrArg Fin.val hji
      simp only [Fin.val_castSucc,Fin.val_succ] at *
      omega
    · have hji : j.castSucc = i.succ := Sum.inl_injective (hinj h')
      have := congrArg Fin.val hij
      have := congrArg Fin.val hji
      simp only [Fin.val_castSucc,Fin.val_succ] at *
      omega
    · have hh := hinj (show Sum.elim u v (Sum.inl j.castSucc) = Sum.elim u v (Sum.inr i.castSucc) from h')
      cases hh
    · have hh := hinj (show Sum.elim u v (Sum.inl j.castSucc) = Sum.elim u v (Sum.inr i.succ) from h')
      cases hh
  · have hh := hinj (show Sum.elim u v (Sum.inl i.castSucc) = Sum.elim u v (Sum.inr j.castSucc) from h)
    cases hh
  · have hh := hinj (show Sum.elim u v (Sum.inl i.castSucc) = Sum.elim u v (Sum.inr j.succ) from h)
    cases hh

/-- Every rung interval is an actual selected link. -/
theorem appbRungInterval_link {M : Molecule V D} {m : ℕ}
    {u v : Fin (m+1) → V} (hL : Degen.SourceLadder M u v) (i : Fin m) :
    AppbLink M (appbRungInterval u v i) := by
  have hi : i.val+1 ≤ m := by omega
  let E := Degen.ladderIntervalEmbedding m i.val 1 hi
  refine ⟨(fun j => u (E j)),(fun j => v (E j)),
    Degen.sourceLadder_interval M hL i.val 1 hi (by omega),?_⟩
  rw [appb_ladderAtoms_two]
  have h0 : E 0 = i.castSucc := Fin.ext (by simp [E,Degen.ladderIntervalEmbedding])
  have h1 : E 1 = i.succ := Fin.ext (by simp [E,Degen.ladderIntervalEmbedding])
  simp only [h0,h1,appbRungInterval]

/-- Exact finite enumeration of all selected links contained in a source
ladder, with one link per consecutive rung pair. -/
theorem appbLinks_within_ladder {M : Molecule V D} (hM : M.IsMolecule) {m : ℕ}
    {u v : Fin (m+1) → V} (hL : Degen.SourceLadder M u v) :
    (appbLinks M).filter (fun S => S ⊆ Molecule.ladderAtoms u v) =
      univ.image (appbRungInterval u v) := by
  classical
  ext S
  simp only [mem_filter,mem_appbLinks,mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨hS,hsub⟩
    obtain ⟨i,rfl⟩ := hS.eq_rungInterval hM hL hsub
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    refine ⟨appbRungInterval_link hL i,?_⟩
    intro x hx
    simp only [appbRungInterval,mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    all_goals simp [Molecule.ladderAtoms]

theorem appbLinks_within_ladder_card {M : Molecule V D} (hM : M.IsMolecule) {m : ℕ}
    {u v : Fin (m+1) → V} (hL : Degen.SourceLadder M u v) :
    ((appbLinks M).filter (fun S => S ⊆ Molecule.ladderAtoms u v)).card = m := by
  rw [appbLinks_within_ladder hM hL,
    card_image_of_injective _ (appbRungInterval_injective hL.2.1),card_univ,Fintype.card_fin]

end WaveTurbulence.Mole
