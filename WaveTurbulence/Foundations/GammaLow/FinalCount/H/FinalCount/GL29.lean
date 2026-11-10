/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL29
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Step5c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineF
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.GL5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.GL29`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **G3-LOWDEG (R48), part 29: `hnew` of `HStepD1` holds for every Step 1 at an object with a degree-`2` joint** (TARGET excessprop1 (3):
the isolated half of the degree-`2` joint is a new component).  `vineCut_F_lt`: if `deg upper = 2` or `deg lower = 2`, the removal of
the vine-like object creates at least one new component: `F(M) < F(K.post)`.  Together with `vine_F_le_succ`: `F(K.post) = F(M) + 1`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine.SourceVine
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- A dartless atom of `K.post` is in a component by itself. -/
theorem post_sc_dartless (K : Step1.VineCut Src.γL M) {a : V} (ha : K.cutMol.dartsAt a = ∅) {b : V}
    (h : K.post.SameComponent a b) : b = a := by
  have key : ∀ u v : V, Relation.EqvGen K.post.Adj u v → (u = a ↔ v = a) := by
    intro u v huv
    induction huv with
    | rel x y hxy =>
      obtain ⟨z, hz1, hz2⟩ := hxy
      have h1 : x ≠ a := by
        rintro rfl
        have : z.1 ∈ K.cutMol.dartsAt x := (mem_dartsAt' K.cutMol x z.1).2 hz1
        rw [ha] at this; exact absurd this (Finset.notMem_empty _)
      have h2 : y ≠ a := by
        rintro rfl
        have : (K.post.mate z).1 ∈ K.cutMol.dartsAt y := (mem_dartsAt' K.cutMol y _).2 hz2
        rw [ha] at this; exact absurd this (Finset.notMem_empty _)
      exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  exact ((key a b h).1 rfl).symm ▸ rfl

/-- **The removal of a vine-like object with a joint of degree `2` creates a new component** (`F(M) < F(K.post)`). -/
theorem vineCut_F_lt (K : Step1.VineCut Src.γL M) (hd : M.deg K.C.upper = 2 ∨ M.deg K.C.lower = 2) :
    M.numComponents < K.post.numComponents := by
  have hfa : K.fa ∈ K.post.atoms := by
    rw [post_atoms_eq, Finset.mem_filter]
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), fun h => K.fa_fresh (Step1.objectAtoms_sub K.C h)⟩
  have hfb : K.fb ∈ K.post.atoms := by
    rw [post_atoms_eq, Finset.mem_filter]
    exact ⟨Finset.mem_insert_self _ _, fun h => K.fb_fresh (Step1.objectAtoms_sub K.C h)⟩
  let f : Quot (fun u w : K.post.atoms => K.post.Adj u.1 w.1) → Quot (fun u w : M.atoms => M.Adj u.1 w.1) :=
    Quot.map (fun a : K.post.atoms => (⟨piVine K a.1, piVine_mem K a.2⟩ : M.atoms)) (by
      intro a b h
      obtain ⟨z, hz1, hz2⟩ := h
      refine ⟨z.1, ?_, ?_⟩
      · show M.atom z.1 = piVine K a.1
        rw [← hz1]; exact (piVine_atom K z.1).symm
      · show M.atom (M.mate z.1) = piVine K b.1
        rw [← hz2]; exact (piVine_atom K (K.cutMol.mate z.1)).symm)
  have hsurj : Function.Surjective f := by
    intro q
    induction q using Quot.ind with
    | mk a =>
      obtain ⟨a, ha⟩ := a
      by_cases hC : a ∈ K.C.atoms
      · refine ⟨Quot.mk _ ⟨K.fa, hfa⟩, ?_⟩
        show Quot.mk _ (⟨piVine K K.fa, _⟩ : M.atoms) = Quot.mk _ ⟨a, ha⟩
        rw [quot_mk_eq_iff M _ _ _ ha]
        have : piVine K K.fa = K.C.upper := by simp [piVine]
        rw [this]
        exact vine_obj_sc K K.a_mem hC
      · have hp : a ∈ K.post.atoms := by
          rw [post_atoms_eq, Finset.mem_filter]
          exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha), hC⟩
        refine ⟨Quot.mk _ ⟨a, hp⟩, ?_⟩
        show Quot.mk _ (⟨piVine K a, _⟩ : M.atoms) = Quot.mk _ ⟨a, ha⟩
        have h1 : a ≠ K.fa := fun e => K.fa_fresh (e ▸ ha)
        have h2 : a ≠ K.fb := fun e => K.fb_fresh (e ▸ ha)
        simp only [piVine, h1, h2, if_false]
  have hfeq : f (Quot.mk _ ⟨K.fa, hfa⟩) = f (Quot.mk _ ⟨K.fb, hfb⟩) := by
    show Quot.mk _ (⟨piVine K K.fa, _⟩ : M.atoms) = Quot.mk _ ⟨piVine K K.fb, _⟩
    have e1 : piVine K K.fa = K.C.upper := by simp [piVine]
    have e2 : piVine K K.fb = K.C.lower := by simp [piVine, K.fa_ne_fb.symm]
    rw [quot_mk_eq_iff M _ _ (piVine_mem K hfa) (piVine_mem K hfb), e1, e2]
    exact vine_obj_sc K K.a_mem K.b_mem
  have hne : (Quot.mk _ ⟨K.fa, hfa⟩ : Quot (fun u w : K.post.atoms => K.post.Adj u.1 w.1)) ≠ Quot.mk _ ⟨K.fb, hfb⟩ := by
    intro h
    have hsc := (quot_mk_eq_iff K.post K.fa K.fb hfa hfb).1 h
    rcases hd with hd | hd
    · exact K.fa_ne_fb (post_sc_dartless K (vineCut_fa_dartless K hd) hsc).symm
    · have := post_sc_dartless K (vineCut_fb_dartless K hd) (Relation.EqvGen.symm _ _ hsc)
      exact K.fa_ne_fb this
  have hninj : ¬ Function.Injective f := fun hinj => hne (hinj hfeq)
  unfold Molecule.numComponents
  haveI := Fintype.ofFinite (Quot (fun u w : K.post.atoms => K.post.Adj u.1 w.1))
  haveI := Fintype.ofFinite (Quot (fun u w : M.atoms => M.Adj u.1 w.1))
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_surjective_not_injective f hsurj hninj

universe u
variable {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

end WaveTurbulence.GammaLow.FinalCount.H
