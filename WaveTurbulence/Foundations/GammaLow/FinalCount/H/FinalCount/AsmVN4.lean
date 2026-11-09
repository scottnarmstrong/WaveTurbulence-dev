/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmVN4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmVN4`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (VineNodeExists, part 4): the removed atom set of a vine cut is determined by its darts.**
The atoms of `K.C` are exactly the component of the upper joint in the doubly cut molecule (`vineCut_atoms_comp`): the complement is
closed, and the group connectivity of the block (the adjoint for a hyper object) uses only `ContainsDart` darts, which the cuts keep.
So two vine cuts with the same four darts and the same fresh atoms remove the same atoms (`vineCut_atoms_determined`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem _root_.WaveTurbulence.GammaLow.FinalCount.Step1.VineCut.pairU (K : Step1.VineCut Src.γL M) : SourceObjectJointPair K.C K.C.upper K.x₂ K.x₁ :=
  ⟨K.Mx₂, K.Mx₁, K.in_a.2, K.in_a.1, K.Mout₂, K.Mout₁⟩

theorem _root_.WaveTurbulence.GammaLow.FinalCount.Step1.VineCut.pairL (K : Step1.VineCut Src.γL M) : SourceObjectJointPair K.C K.C.lower K.y₂ K.y₁ :=
  ⟨K.My₂, K.My₁, K.in_b.2, K.in_b.1, K.Mouty₂, K.Mouty₁⟩

/-- The group-connectivity of an object uses only `ContainsDart` darts. -/
theorem object_groupConnected (O : Src.Object Src.γL M) : ∀ u ∈ O.atoms, ∀ v ∈ O.atoms,
    Relation.EqvGen (fun a b => ∃ x, O.ContainsDart x ∧ M.atom x = a ∧ M.atom (M.mate x) = b) u v := by
  rcases O with ⟨S, a, b, sh⟩
  cases sh with
  | vc h =>
    intro u hu v hv
    have := h.1.2.2.2.2.2.2.2.2.2 u hu v hv
    exact Relation.EqvGen.mono (fun p q ⟨x, hx, h1, h2⟩ => ⟨x, hx, h1, h2⟩) _ _ this
  | hyper R =>
    intro u hu v hv
    have := R.adjoint.1.2.2.2.2.2.2.2.2.2 u hu v hv
    exact Relation.EqvGen.mono (fun p q ⟨x, hx, h1, h2⟩ => ⟨x.1, ⟨x.2.1, x.2.2, hx⟩, h1, h2⟩) _ _ this

theorem vineCut_atoms_comp (K : Step1.VineCut Src.γL M) (v : V) :
    v ∈ K.C.atoms ↔ v ∈ K.cutMol.atoms ∧ K.cutMol.SameComponent K.C.upper v := by
  have hb := (object_oh K.C).basic
  have key := cut2_atom_mem_iff K.C
  constructor
  · intro hv
    refine ⟨?_, ?_⟩
    · show v ∈ insert K.fb (insert K.fa M.atoms)
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hb.1 hv))
    · have hG := object_groupConnected K.C K.C.upper K.a_mem v hv
      refine Relation.EqvGen.mono ?_ _ _ hG
      intro p q ⟨x, hx, h1, h2⟩
      have e1 := cut2_atom_eq_of_cd K.C K.fa K.fb K.pairU K.pairL x hx
      have e2 := cut2_atom_eq_of_cd K.C K.fa K.fb K.pairU K.pairL (M.mate x) (containsDart_mate K.C hx)
      exact ⟨x, e1.trans h1, e2.trans h2⟩
  · rintro ⟨-, hc⟩
    have hP : ∀ u u', K.cutMol.Adj u u' → (u ∈ K.C.atoms ↔ u' ∈ K.C.atoms) := by
      rintro u u' ⟨x, hx1, hx2⟩
      have h1 := K.closed x
      have h2 := K.closed (K.cutMol.mate x)
      change K.cutMol.atom x ∉ K.C.atoms → K.cutMol.atom (K.cutMol.mate x) ∉ K.C.atoms at h1
      change K.cutMol.atom (K.cutMol.mate x) ∉ K.C.atoms → K.cutMol.atom (K.cutMol.mate (K.cutMol.mate x)) ∉ K.C.atoms at h2
      rw [K.cutMol.mate_mate] at h2
      rw [← hx1, ← hx2]
      constructor
      · intro hu; by_contra hu'; exact (h2 hu') hu
      · intro hu'; by_contra hu; exact (h1 hu) hu'
    have : ∀ u u', Relation.EqvGen K.cutMol.Adj u u' → (u ∈ K.C.atoms ↔ u' ∈ K.C.atoms) := by
      intro u u' h
      induction h with
      | rel _ _ h => exact hP _ _ h
      | refl _ => exact Iff.rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
    exact (this _ _ hc).mp K.a_mem

theorem vineCut_atoms_determined (K K' : Step1.VineCut Src.γL M) (e1 : K.x₁ = K'.x₁) (e2 : K.x₂ = K'.x₂) (e3 : K.y₁ = K'.y₁)
    (e4 : K.y₂ = K'.y₂) (e5 : K.fa = K'.fa) (e6 : K.fb = K'.fb) : K.C.atoms = K'.C.atoms := by
  have hu : K'.C.upper = K.C.upper := by rw [← K'.Mx₁, ← K.Mx₁, e1]
  have hl : K'.C.lower = K.C.lower := by rw [← K'.My₁, ← K.My₁, e3]
  have hc : K'.cutMol = K.cutMol := by
    unfold Step1.VineCut.cutMol
    rw [hu, hl, ← e1, ← e2, ← e3, ← e4, ← e5, ← e6]
  ext v
  rw [vineCut_atoms_comp K, vineCut_atoms_comp K', hc, hu]

end WaveTurbulence.GammaLow.FinalCount.H
