/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.AddedPairCleanup
public import WaveTurbulence.Foundations.FinalCount.AppBS33ReinsertMolecule
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertNoLoops
import Mathlib.Tactic

/-! # The optional source 3S3 reinsertion cleanup is an actual TB realization -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 algorithm two(c): zero or one literal TB cleanup restores the
no-triple invariant after the defective-pair reinsertion. -/
theorem s33_cleanup_selection (M : Molecule V D) (hM : M.IsMolecule)
    (hno : AppbNoLoops M) (hnt : AppbNoTripleBonds M)
    (r : AppbRealization M AppbPatternKind.s33.pattern) (hg : AppbS33SplitGeometry M r)
    (hd : ¬(M.deg (r.vertex 3) = 4 ∧ M.deg (r.vertex 5) = 4)) :
    AppbNoTripleBonds (r.directedPostWithBond 3 5 ⟨1,by decide⟩) ∨
      ∃ k ∈ ([AppbPatternKind.tb1,.tb2] : List _),
        ∃ t : AppbRealization (r.directedPostWithBond 3 5 ⟨1,by decide⟩) k.pattern,
          AppbNoTripleBonds t.post := by
  have hN := appb_s33_reinsert_isMolecule M hM r hg hd
  have hNL := r.directedPostWithBond_noLoops 3 5 ⟨1,by decide⟩ hno (by decide) (by decide) (by decide)
  have hNT : AppbNoTripleBonds r.post := appb_eraseAtoms_noTripleBonds M r.removedAtoms hnt
  have hm3 := r.vertex_mem_post 3 (by decide) (by decide)
  have hm5 := r.vertex_mem_post 5 (by decide) (by decide)
  have hne : r.vertex 3 ≠ r.vertex 5 := (r.vertex_eq_iff 3 5 (by decide) (by decide)).not.mpr (by decide)
  have hdeg3 : (r.directedPostWithBond 3 5 ⟨1,by decide⟩).deg (r.vertex 3) = M.deg (r.vertex 3) := by
    have hh := appb_s33_reinsert_survivor_degree M r 3 (by decide)
    norm_num at hh
    exact hh
  have hdeg5 : (r.directedPostWithBond 3 5 ⟨1,by decide⟩).deg (r.vertex 5) = M.deg (r.vertex 5) := by
    have hh := appb_s33_reinsert_survivor_degree M r 5 (by decide)
    norm_num at hh
    exact hh
  have hdN : ¬((r.directedPostWithBond 3 5 ⟨1,by decide⟩).deg (r.vertex 3) = 4 ∧
      (r.directedPostWithBond 3 5 ⟨1,by decide⟩).deg (r.vertex 5) = 4) := by
    simpa only [hdeg3,hdeg5] using hd
  by_cases hdir : M.atom (r.edge ⟨1,by decide⟩).val = r.vertex 3
  · have he : r.directedPostWithBond 3 5 ⟨1,by decide⟩ = addBond r.post (r.vertex 3) (r.vertex 5) := by
      unfold AppbRealization.directedPostWithBond
      exact if_pos hdir
    rw [he] at hN hNL hdN ⊢
    rcases addedPair_cleanup r.post hNT hm3 hm5 hne hN hNL (fun _ => hdN) with hh | ⟨k,hk,t,ha,hb,ht⟩
    · exact Or.inl hh
    · exact Or.inr ⟨k,hk,t,ht⟩
  · have he : r.directedPostWithBond 3 5 ⟨1,by decide⟩ = addBond r.post (r.vertex 5) (r.vertex 3) := by
      unfold AppbRealization.directedPostWithBond
      exact if_neg hdir
    rw [he] at hN hNL hdN ⊢
    have hdN' : ¬((addBond r.post (r.vertex 5) (r.vertex 3)).deg (r.vertex 5) = 4 ∧
        (addBond r.post (r.vertex 5) (r.vertex 3)).deg (r.vertex 3) = 4) := fun h => hdN ⟨h.2,h.1⟩
    rcases addedPair_cleanup r.post hNT hm5 hm3 hne.symm hN hNL (fun _ => hdN') with hh | ⟨k,hk,t,ha,hb,ht⟩
    · exact Or.inl hh
    · exact Or.inr ⟨k,hk,t,ht⟩

end WaveTurbulence.Mole.AppbAlgorithm
