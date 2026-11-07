/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Step5b
/-! **FINALCOUNT-G3 (step 5c): a vine removal creates at most one new component** (`ΔF ≤ 1`; with `vine_F_ge` and the failure of
`vine_F_le_of_sc`, `ΔF = 1` exactly in the new-component case of TARGET `excessprop1` (2)).  The collapse map
`Q_post → Q_pre` identifies at most the classes of `fa` and `fb`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine.SourceVine

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (K : VineCut M)

/-- Representative: the classes of `fa` and `fb` are merged. -/
noncomputable def phiP (u : V) : V :=
  if K.post.SameComponent u K.fa ∨ K.post.SameComponent u K.fb then K.fa else u

/-- The coarse equivalence `E` (post components, with `[fa]` and `[fb]` merged). -/
def EP (u v : V) : Prop := K.post.SameComponent (phiP K u) (phiP K v)

theorem EP_refl (u : V) : EP K u u := Relation.EqvGen.refl _
theorem EP_symm {u v : V} (h : EP K u v) : EP K v u := Relation.EqvGen.symm _ _ h
theorem EP_trans {u v w : V} (h1 : EP K u v) (h2 : EP K v w) : EP K u w := Relation.EqvGen.trans _ _ _ h1 h2

theorem EP_of_sc {u v : V} (h : K.post.SameComponent u v) : EP K u v := by
  unfold EP phiP
  by_cases a : K.post.SameComponent u K.fa ∨ K.post.SameComponent u K.fb
  · have b : K.post.SameComponent v K.fa ∨ K.post.SameComponent v K.fb := by
      rcases a with a | a
      · exact Or.inl (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) a)
      · exact Or.inr (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) a)
    rw [if_pos a, if_pos b]; exact Relation.EqvGen.refl _
  · have b : ¬ (K.post.SameComponent v K.fa ∨ K.post.SameComponent v K.fb) := by
      rintro (b | b)
      · exact a (Or.inl (Relation.EqvGen.trans _ _ _ h b))
      · exact a (Or.inr (Relation.EqvGen.trans _ _ _ h b))
    rw [if_neg a, if_neg b]; exact h

theorem EP_fafb : EP K K.fa K.fb := by
  unfold EP phiP
  have h1 : K.post.SameComponent K.fa K.fa ∨ K.post.SameComponent K.fa K.fb := Or.inl (Relation.EqvGen.refl _)
  have h2 : K.post.SameComponent K.fb K.fa ∨ K.post.SameComponent K.fb K.fb := Or.inr (Relation.EqvGen.refl _)
  rw [if_pos h1, if_pos h2]; exact Relation.EqvGen.refl _

theorem sc_of_EP {u v : V} (hu : ¬ K.post.SameComponent u K.fb) (hv : ¬ K.post.SameComponent v K.fb)
    (h : EP K u v) : K.post.SameComponent u v := by
  unfold EP phiP at h
  by_cases a1 : K.post.SameComponent u K.fa <;> by_cases a2 : K.post.SameComponent v K.fa
  · exact Relation.EqvGen.trans _ _ _ a1 (Relation.EqvGen.symm _ _ a2)
  · simp only [a1, hu, or_false, if_true, a2, hv, if_false, or_self] at h <;>
      first | exact absurd (Relation.EqvGen.symm _ _ h) a2 | skip
  · simp only [a1, hu, or_self, if_false, a2, hv, or_false, if_true] at h <;>
      first | exact absurd h a1 | skip
  · simp only [a1, hu, or_self, if_false, a2, hv] at h
    exact h

theorem EP_gpi {u : V} (hu : u ∈ K.post.atoms) : EP K u (gPost K (piVine K u)) := by
  have hu' := hu
  rw [post_atoms_eq, Finset.mem_filter] at hu'
  obtain ⟨hu1, hu2⟩ := hu'
  by_cases e1 : u = K.fa
  · subst e1
    have : piVine K K.fa = K.C.upper := by simp [piVine]
    rw [this]; unfold gPost; rw [if_pos K.a_mem]; exact EP_refl K _
  by_cases e2 : u = K.fb
  · subst e2
    have : piVine K K.fb = K.C.lower := by simp [piVine, K.fa_ne_fb.symm]
    rw [this]; unfold gPost; rw [if_pos K.b_mem]; exact EP_symm K (EP_fafb K)
  · have : piVine K u = u := by simp [piVine, e1, e2]
    rw [this]; unfold gPost; rw [if_neg hu2]; exact EP_refl K _

theorem EP_adj {s t : V} (hst : M.Adj s t) : EP K (gPost K s) (gPost K t) := by
  obtain ⟨z, hz1, hz2⟩ := hst
  have hs : piVine K (K.cutMol.atom z) = s := by rw [piVine_atom]; exact hz1
  have ht : piVine K (K.cutMol.atom (K.cutMol.mate z)) = t := by
    rw [piVine_atom]; exact hz2
  have hmm : K.cutMol.mate (K.cutMol.mate z) = z := K.cutMol.mate_mate z
  have hcl := K.closed
  by_cases hs' : K.cutMol.atom z ∈ K.C.atoms
  · have ht' : K.cutMol.atom (K.cutMol.mate z) ∈ K.C.atoms := by
      by_contra hn
      have h2 : K.cutMol.atom (K.cutMol.mate (K.cutMol.mate z)) ∉ K.C.atoms := hcl (K.cutMol.mate z) hn
      rw [hmm] at h2
      exact h2 hs'
    have e1 : K.cutMol.atom z ≠ K.fa := fun e => K.fa_fresh (objectAtoms_sub K.C (e ▸ hs'))
    have e2 : K.cutMol.atom z ≠ K.fb := fun e => K.fb_fresh (objectAtoms_sub K.C (e ▸ hs'))
    have e3 : K.cutMol.atom (K.cutMol.mate z) ≠ K.fa := fun e => K.fa_fresh (objectAtoms_sub K.C (e ▸ ht'))
    have e4 : K.cutMol.atom (K.cutMol.mate z) ≠ K.fb := fun e => K.fb_fresh (objectAtoms_sub K.C (e ▸ ht'))
    have hs2 : s = K.cutMol.atom z := by rw [← hs]; simp [piVine, e1, e2]
    have ht2 : t = K.cutMol.atom (K.cutMol.mate z) := by rw [← ht]; simp [piVine, e3, e4]
    unfold gPost
    rw [if_pos (hs2 ▸ hs'), if_pos (ht2 ▸ ht')]
    exact EP_refl K _
  · have ht' : K.cutMol.atom (K.cutMol.mate z) ∉ K.C.atoms := hcl z hs'
    have hpa : K.post.Adj (K.cutMol.atom z) (K.cutMol.atom (K.cutMol.mate z)) :=
      ⟨⟨z, hs'⟩, rfl, rfl⟩
    have hm1 : K.cutMol.atom z ∈ K.post.atoms := K.post.atom_mem ⟨z, hs'⟩
    have hm2 : K.cutMol.atom (K.cutMol.mate z) ∈ K.post.atoms := K.post.atom_mem (K.post.mate ⟨z, hs'⟩)
    rw [← hs, ← ht]
    exact EP_trans K (EP_symm K (EP_gpi K hm1))
      (EP_trans K (EP_of_sc K (Relation.EqvGen.rel _ _ hpa)) (EP_gpi K hm2))

theorem EP_of_M_sc {s t : V} (hst : M.SameComponent s t) : EP K (gPost K s) (gPost K t) := by
  unfold Molecule.SameComponent at hst
  induction hst with
  | rel x y hxy => exact EP_adj K hxy
  | refl x => exact EP_refl K _
  | symm x y _ ih => exact EP_symm K ih
  | trans x y z _ _ ih1 ih2 => exact EP_trans K ih1 ih2

/-- **`ΔF ≤ 1`** for a vine removal. -/
theorem vine_F_le_succ : K.post.numComponents ≤ M.numComponents + 1 := by
  have hfb : K.fb ∈ K.post.atoms := by
    rw [post_atoms_eq, Finset.mem_filter]
    exact ⟨Finset.mem_insert_self _ _, fun h => K.fb_fresh (objectAtoms_sub K.C h)⟩
  let f : Quot (fun u w : K.post.atoms => K.post.Adj u.1 w.1) → Quot (fun u w : M.atoms => M.Adj u.1 w.1) :=
    Quot.map (fun a : K.post.atoms => (⟨piVine K a.1, piVine_mem K a.2⟩ : M.atoms)) (by
      intro a b h
      obtain ⟨z, hz1, hz2⟩ := h
      refine ⟨z.1, ?_, ?_⟩
      · show M.atom z.1 = piVine K a.1
        rw [← hz1]; exact (piVine_atom K z.1).symm
      · show M.atom (M.mate z.1) = piVine K b.1
        rw [← hz2]; exact (piVine_atom K (K.cutMol.mate z.1)).symm)
  let qb : Quot (fun u w : K.post.atoms => K.post.Adj u.1 w.1) := Quot.mk _ ⟨K.fb, hfb⟩
  let f' : Quot (fun u w : K.post.atoms => K.post.Adj u.1 w.1) →
      Option (Quot (fun u w : M.atoms => M.Adj u.1 w.1)) := fun q => if q = qb then none else some (f q)
  have hinj : Function.Injective f' := by
    intro q1 q2 h
    by_cases h1 : q1 = qb <;> by_cases h2 : q2 = qb
    · rw [h1, h2]
    · simp [f', h1, h2] at h
    · simp [f', h1, h2] at h
    · have hf : f q1 = f q2 := by simpa [f', h1, h2] using h
      induction q1 using Quot.ind with
      | mk a =>
      induction q2 using Quot.ind with
      | mk b =>
        obtain ⟨a, ha⟩ := a
        obtain ⟨b, hb⟩ := b
        have hab' : (Quot.mk _ (⟨piVine K a, piVine_mem K ha⟩ : M.atoms)) =
            Quot.mk _ (⟨piVine K b, piVine_mem K hb⟩ : M.atoms) := hf
        rw [quot_mk_eq_iff M _ _ _ _] at hab'
        have e1 := EP_of_M_sc K hab'
        have e2 := EP_trans K (EP_gpi K ha) (EP_trans K e1 (EP_symm K (EP_gpi K hb)))
        have na : ¬ K.post.SameComponent a K.fb := fun hh => h1 ((quot_mk_eq_iff K.post a K.fb ha hfb).2 hh)
        have nb : ¬ K.post.SameComponent b K.fb := fun hh => h2 ((quot_mk_eq_iff K.post b K.fb hb hfb).2 hh)
        exact (quot_mk_eq_iff K.post a b ha hb).2 (sc_of_EP K na nb e2)
  have := Nat.card_le_card_of_injective f' hinj
  rwa [Finite.card_option] at this

end WaveTurbulence.FinalCountG3
