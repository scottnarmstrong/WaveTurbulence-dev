/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Step5a
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineF
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3Step5a`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3 (step 5a): a vine removal creates no new component iff its two fresh joints stay connected** (TARGET L2167,
`subsetvc` L2128 last sentence: "`U₂` still remains connected after removing `U₁` or the VC which `U₁` is the adjoint of").

* `vine_F_le_of_sc`: `K.post.SameComponent K.fa K.fb → K.post.numComponents ≤ M.numComponents` (converse of `vine_sc_fafb`).
* `vine_fafb_of_outside`: if the joints are joined by a chain of bonds of `M` that avoid the interior atoms of the removed object and
  the darts `G ⊇ {x₁, x₂, y₁, y₂}` of its own bonds (exactly the adjacency of the universe's `removeBlocks M U₂ [P]`), then `fa ~ fb`
  in `K.post`.
* `doubleShape_F_le`, `vineCut_F_le_of_outside`: the statement for the Step-1 VC (the `DoubleShape` case is the one needed; the proof does not
  use the shape).  The statement is FALSE without the connectivity hypothesis (dumbbell `A - a=x=b - B`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine.SourceVine

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D]

section lemmaA
variable {M : Molecule V D} (K : Step1.VineCut Src.γL M)

/-- The collapse of an atom of `M` onto the post-molecule: atoms of the object go to `fa`. -/
def gPost (t : V) : V := if t ∈ K.C.atoms then K.fa else t

theorem post_sc_gpi (h : K.post.SameComponent K.fa K.fb) {u : V} (hu : u ∈ K.post.atoms) :
    K.post.SameComponent u (gPost K (piVine K u)) := by
  have hu' := hu
  rw [post_atoms_eq, Finset.mem_filter] at hu'
  obtain ⟨hu1, hu2⟩ := hu'
  by_cases e1 : u = K.fa
  · subst e1
    have : piVine K K.fa = K.C.upper := by simp [piVine]
    rw [this]; unfold gPost; rw [if_pos K.a_mem]; exact Relation.EqvGen.refl _
  by_cases e2 : u = K.fb
  · subst e2
    have : piVine K K.fb = K.C.lower := by simp [piVine, K.fa_ne_fb.symm]
    rw [this]; unfold gPost; rw [if_pos K.b_mem]; exact Relation.EqvGen.symm _ _ h
  · have : piVine K u = u := by simp [piVine, e1, e2]
    rw [this]; unfold gPost; rw [if_neg hu2]; exact Relation.EqvGen.refl _

theorem post_sc_adj (h : K.post.SameComponent K.fa K.fb) {s t : V} (hst : M.Adj s t) :
    K.post.SameComponent (gPost K s) (gPost K t) := by
  obtain ⟨z, hz1, hz2⟩ := hst
  have hs : piVine K (K.cutMol.atom z) = s := by rw [piVine_atom]; exact hz1
  have ht : piVine K (K.cutMol.atom (K.cutMol.mate z)) = t := by
    rw [piVine_atom]; exact hz2
  have hmm : K.cutMol.mate (K.cutMol.mate z) = z := K.cutMol.mate_mate z
  have hcl := K.closed
  by_cases hs' : K.cutMol.atom z ∈ K.C.atoms
  · -- both endpoints in the object
    have ht' : K.cutMol.atom (K.cutMol.mate z) ∈ K.C.atoms := by
      by_contra hn
      have h2 : K.cutMol.atom (K.cutMol.mate (K.cutMol.mate z)) ∉ K.C.atoms := hcl (K.cutMol.mate z) hn
      rw [hmm] at h2
      exact h2 hs'
    have e1 : K.cutMol.atom z ≠ K.fa := fun e => K.fa_fresh (Step1.objectAtoms_sub K.C (e ▸ hs'))
    have e2 : K.cutMol.atom z ≠ K.fb := fun e => K.fb_fresh (Step1.objectAtoms_sub K.C (e ▸ hs'))
    have e3 : K.cutMol.atom (K.cutMol.mate z) ≠ K.fa := fun e => K.fa_fresh (Step1.objectAtoms_sub K.C (e ▸ ht'))
    have e4 : K.cutMol.atom (K.cutMol.mate z) ≠ K.fb := fun e => K.fb_fresh (Step1.objectAtoms_sub K.C (e ▸ ht'))
    have hs2 : s = K.cutMol.atom z := by rw [← hs]; simp [piVine, e1, e2]
    have ht2 : t = K.cutMol.atom (K.cutMol.mate z) := by rw [← ht]; simp [piVine, e3, e4]
    unfold gPost
    rw [if_pos (hs2 ▸ hs'), if_pos (ht2 ▸ ht')]
    exact Relation.EqvGen.refl _
  · have ht' : K.cutMol.atom (K.cutMol.mate z) ∉ K.C.atoms := hcl z hs'
    have hpa : K.post.Adj (K.cutMol.atom z) (K.cutMol.atom (K.cutMol.mate z)) :=
      ⟨⟨z, hs'⟩, rfl, rfl⟩
    have hm1 : K.cutMol.atom z ∈ K.post.atoms := K.post.atom_mem ⟨z, hs'⟩
    have hm2 : K.cutMol.atom (K.cutMol.mate z) ∈ K.post.atoms := K.post.atom_mem (K.post.mate ⟨z, hs'⟩)
    rw [← hs, ← ht]
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (post_sc_gpi K h hm1))
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ hpa) (post_sc_gpi K h hm2))

theorem post_sc_of_M_sc (h : K.post.SameComponent K.fa K.fb) {s t : V} (hst : M.SameComponent s t) :
    K.post.SameComponent (gPost K s) (gPost K t) := by
  unfold Molecule.SameComponent at hst
  induction hst with
  | rel x y hxy => exact post_sc_adj K h hxy
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- **No new component iff the joints stay connected** (converse of `vine_sc_fafb`). -/
theorem vine_F_le_of_sc (h : K.post.SameComponent K.fa K.fb) : K.post.numComponents ≤ M.numComponents := by
  have hfa : K.fa ∈ K.post.atoms := by
    rw [post_atoms_eq, Finset.mem_filter]
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
      fun h => K.fa_fresh (Step1.objectAtoms_sub K.C h)⟩
  let f : Quot (fun u w : K.post.atoms => K.post.Adj u.1 w.1) → Quot (fun u w : M.atoms => M.Adj u.1 w.1) :=
    Quot.map (fun a : K.post.atoms => (⟨piVine K a.1, piVine_mem K a.2⟩ : M.atoms)) (by
      intro a b h
      obtain ⟨z, hz1, hz2⟩ := h
      refine ⟨z.1, ?_, ?_⟩
      · show M.atom z.1 = piVine K a.1
        rw [← hz1]; exact (piVine_atom K z.1).symm
      · show M.atom (M.mate z.1) = piVine K b.1
        rw [← hz2]; exact (piVine_atom K (K.cutMol.mate z.1)).symm)
  have hinj : Function.Injective f := by
    intro q1 q2
    induction q1 using Quot.ind with
    | mk a =>
    induction q2 using Quot.ind with
    | mk b =>
      obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      intro hab
      have hab' : (Quot.mk _ (⟨piVine K a, piVine_mem K ha⟩ : M.atoms)) = Quot.mk _ (⟨piVine K b, piVine_mem K hb⟩ : M.atoms) := hab
      rw [quot_mk_eq_iff M _ _ _ _] at hab'
      have h1 := post_sc_of_M_sc K h hab'
      have h2 := Relation.EqvGen.trans _ _ _ (post_sc_gpi K h ha)
        (Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.symm _ _ (post_sc_gpi K h hb)))
      exact (quot_mk_eq_iff K.post a b ha hb).2 h2
  exact Nat.card_le_card_of_injective f hinj

end lemmaA

end WaveTurbulence.GammaLow.FinalCount.H
