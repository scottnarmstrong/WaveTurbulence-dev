/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.AddedPairCleanup
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33ReinsertTripleExclusion
public import WaveTurbulence.Foundations.FinalCount.AppBD33ReinsertMolecule
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertNoLoops
import Mathlib.Tactic

/-! # The optional source 3D3 reinsertion cleanup is an actual TB realization -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 algorithm three(c-ii): zero or one literal TB cleanup restores the
no-triple invariant after the defective-pair reinsertion. -/
theorem d33_cleanup_selection (M : Molecule V D) (hM : M.IsMolecule)
    (hno : AppbNoLoops M) (hnt : AppbNoTripleBonds M)
    (r : AppbRealization M AppbPatternKind.d33.pattern) (hg : AppbD33BoundaryOpposite M r)
    (hconn : ∀ a ∈ M.atoms,∀ b ∈ M.atoms,M.SameComponent a b)
    (hb : ∀ e : D,¬Degen.IsBridge M e) (hc : ¬D33Continues r)
    (ht : ¬HasD33ResidualCommon r) (hd : AppbD33ResidualDefect M r) :
    AppbNoTripleBonds (r.directedPostWithBond 3 4 ⟨2,by decide⟩) ∨
      ∃ k ∈ ([AppbPatternKind.tb1,.tb2] : List _),
        ∃ t : AppbRealization (r.directedPostWithBond 3 4 ⟨2,by decide⟩) k.pattern,
          AppbNoTripleBonds t.post := by
  have hN := appb_d33_reinsert_isMolecule M hM r hconn hb hg hd
  have hNL := r.directedPostWithBond_noLoops 3 4 ⟨2,by decide⟩ hno (by decide) (by decide) (by decide)
  have hNT : AppbNoTripleBonds r.post := appb_eraseAtoms_noTripleBonds M r.removedAtoms hnt
  have hm3 := r.vertex_mem_post 3 (by decide) (by decide)
  have hm4 := r.vertex_mem_post 4 (by decide) (by decide)
  have hne : r.vertex 3 ≠ r.vertex 4 := (r.vertex_eq_iff 3 4 (by decide) (by decide)).not.mpr (by decide)
  have hdN : (r.directedPostWithBond 3 4 ⟨2,by decide⟩).bondsBetween (r.vertex 3) (r.vertex 4) = 3 →
      ¬((r.directedPostWithBond 3 4 ⟨2,by decide⟩).deg (r.vertex 3) = 4 ∧
        (r.directedPostWithBond 3 4 ⟨2,by decide⟩).deg (r.vertex 4) = 4) :=
    fun hm => d33_reinsert_triple_not_both_four M hM hno r hg hc ht hm
  by_cases hdir : M.atom (r.edge ⟨2,by decide⟩).val = r.vertex 3
  · have he : r.directedPostWithBond 3 4 ⟨2,by decide⟩ = addBond r.post (r.vertex 3) (r.vertex 4) := by
      unfold AppbRealization.directedPostWithBond
      exact if_pos hdir
    rw [he] at hN hNL hdN ⊢
    rcases addedPair_cleanup r.post hNT hm3 hm4 hne hN hNL hdN with hh | ⟨k,hk,t,ha,hb,ht⟩
    · exact Or.inl hh
    · exact Or.inr ⟨k,hk,t,ht⟩
  · have he : r.directedPostWithBond 3 4 ⟨2,by decide⟩ = addBond r.post (r.vertex 4) (r.vertex 3) := by
      unfold AppbRealization.directedPostWithBond
      exact if_neg hdir
    rw [he] at hN hNL hdN ⊢
    have hdN' : (addBond r.post (r.vertex 4) (r.vertex 3)).bondsBetween (r.vertex 4) (r.vertex 3) = 3 →
        ¬((addBond r.post (r.vertex 4) (r.vertex 3)).deg (r.vertex 4) = 4 ∧
          (addBond r.post (r.vertex 4) (r.vertex 3)).deg (r.vertex 3) = 4) := by
      intro hm h
      apply hdN ((bondsBetween_symm _ (r.vertex 3) (r.vertex 4)).trans hm)
      exact ⟨h.2,h.1⟩
    rcases addedPair_cleanup r.post hNT hm4 hm3 hne.symm hN hNL hdN' with hh | ⟨k,hk,t,ha,hb,ht⟩
    · exact Or.inl hh
    · exact Or.inr ⟨k,hk,t,ht⟩

end WaveTurbulence.Mole.AppbAlgorithm
