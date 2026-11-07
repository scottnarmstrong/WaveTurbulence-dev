/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3NewComp1
/-! **FINALCOUNT-G3 (step 5b, part 2): `NewCompFixed` for a vine removal that creates a new component** (TARGET L2174-L2175).

When `fa ≁ fb` in `K.post`, the new component hangs at the upper joint: `A = {upper} ∪ {v ∉ K.C : v ~ fa in K.post}` has boundary
exactly `{x₁, x₂}` (`newComp_boundary`), so `NewCompFixedUp` holds with `ν' = |A|` (`newCompFixedUp_of_boundary`), and
`newCompFixed_of_upper` gives `NewCompFixed` with `ν = |A| + (m - 2) ≤ |M.atoms|` (`newCompFixed_exists`; `|M.atoms| ≤ n_sb ≤ (log L)^{C₂}`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.VineCount WaveTurbulence.LGSpine.SourceVine

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ} {M : Molecule V D}

/-- The atoms of the new component, seen in `M` (the upper joint stands for `fa`). -/
noncomputable def newCompAtoms (K : VineCut M) : Finset V :=
  insert K.C.upper ((M.atoms \ K.C.atoms).filter fun v => K.post.SameComponent v K.fa)

theorem mem_newCompAtoms (K : VineCut M) {v : V} :
    v ∈ newCompAtoms K ↔ v = K.C.upper ∨ (v ∈ M.atoms ∧ v ∉ K.C.atoms ∧ K.post.SameComponent v K.fa) := by
  unfold newCompAtoms
  simp [Finset.mem_insert, Finset.mem_filter, Finset.mem_sdiff, and_assoc]

theorem newCompAtoms_sub (K : VineCut M) : newCompAtoms K ⊆ M.atoms := by
  intro v hv
  rcases (mem_newCompAtoms K).1 hv with rfl | h
  · exact objectAtoms_sub K.C K.a_mem
  · exact h.1

theorem inGroup_of_contains (K : VineCut M) {x : D} (h : K.C.ContainsDart x) : M.InGroup K.C.atoms x := by
  unfold Object.ContainsDart at h
  rcases hsh : K.C.shape with _ | R
  · rw [hsh] at h; exact h
  · rw [hsh] at h; exact h.2.2

/-- A dart of the post molecule leaving a vertex joined to `fa` stays in the new component. -/
theorem newComp_step (K : VineCut M) (hnc : ¬ K.post.SameComponent K.fa K.fb) {x : D}
    (hx : K.cutMol.atom x ∉ K.C.atoms) (hsc : K.post.SameComponent (K.cutMol.atom x) K.fa) :
    M.atom (M.mate x) ∈ newCompAtoms K := by
  have ht' : K.cutMol.atom (K.cutMol.mate x) ∉ K.C.atoms := K.closed x hx
  have hadj : K.post.Adj (K.cutMol.atom x) (K.cutMol.atom (K.cutMol.mate x)) := ⟨⟨x, hx⟩, rfl, rfl⟩
  have hsc2 : K.post.SameComponent (K.cutMol.atom (K.cutMol.mate x)) K.fa :=
    Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hadj)) hsc
  have hpi : piVine K (K.cutMol.atom (K.cutMol.mate x)) = M.atom (M.mate x) := piVine_atom K (M.mate x)
  have hmem : K.cutMol.atom (K.cutMol.mate x) ∈ K.post.atoms := K.post.atom_mem (K.post.mate ⟨x, hx⟩)
  by_cases e1 : K.cutMol.atom (K.cutMol.mate x) = K.fa
  · rw [e1] at hpi
    have : piVine K K.fa = K.C.upper := by simp [piVine]
    rw [this] at hpi
    rw [← hpi]; exact (mem_newCompAtoms K).2 (Or.inl rfl)
  by_cases e2 : K.cutMol.atom (K.cutMol.mate x) = K.fb
  · exfalso
    rw [e2] at hsc2
    exact hnc (Relation.EqvGen.symm _ _ hsc2)
  · have : piVine K (K.cutMol.atom (K.cutMol.mate x)) = K.cutMol.atom (K.cutMol.mate x) := by
      simp [piVine, e1, e2]
    rw [this] at hpi
    rw [post_atoms_eq, Finset.mem_filter] at hmem
    have hM : K.cutMol.atom (K.cutMol.mate x) ∈ M.atoms := by
      have := hmem.1
      simp only [Finset.mem_insert] at this
      rcases this with h | h | h
      · exact absurd h e2
      · exact absurd h e1
      · exact h
    rw [← hpi]
    exact (mem_newCompAtoms K).2 (Or.inr ⟨hM, hmem.2, hsc2⟩)

theorem newComp_boundary (K : VineCut M) (hnc : ¬ K.post.SameComponent K.fa K.fb) {x : D}
    (hs : M.atom x ∈ newCompAtoms K) (ht : M.atom (M.mate x) ∉ newCompAtoms K) : x = K.x₁ ∨ x = K.x₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hn1, hn2⟩ := hcon
  have hG : ∀ z ∈ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset D), z ∈ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset D) :=
    fun _ h => h
  rcases (mem_newCompAtoms K).1 hs with h | ⟨hsM, hsC, hsc⟩
  · -- the upper joint
    have hx : x ∉ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset D) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨hn1, hn2, fun e => ?_, fun e => ?_⟩
      · rw [e, K.My₁] at h; exact K.ab_ne h.symm
      · rw [e, K.My₂] at h; exact K.ab_ne h.symm
    have e1 := cutMol_atom_outside K hG hx
    have e2 : hPost K (M.atom x) = K.fa := by simp [hPost, h]
    rw [e2] at e1
    exact ht (newComp_step K hnc (by rw [e1]; exact fun h => K.fa_fresh (objectAtoms_sub K.C h))
      (by rw [e1]; exact Relation.EqvGen.refl _))
  · have hx : x ∉ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset D) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro e; rw [e, K.Mx₁] at hsC; exact hsC K.a_mem
      · intro e; rw [e, K.Mx₂] at hsC; exact hsC K.a_mem
      · intro e; rw [e, K.My₁] at hsC; exact hsC K.b_mem
      · intro e; rw [e, K.My₂] at hsC; exact hsC K.b_mem
    have e1 := cutMol_atom_outside K hG hx
    have e2 : hPost K (M.atom x) = M.atom x := by
      have h1 : M.atom x ≠ K.C.upper := fun e => hsC (e ▸ K.a_mem)
      have h2 : M.atom x ≠ K.C.lower := fun e => hsC (e ▸ K.b_mem)
      simp [hPost, h1, h2]
    rw [e2] at e1
    exact ht (newComp_step K hnc (by rw [e1]; exact hsC) (by rw [e1]; exact hsc))

/-- `NewCompFixed` (TARGET L2174) for a vine removal creating a new component, with `ν ≤ |M.atoms|`. -/
theorem newCompFixed_exists (hd : 0 < d) (K : VineCut M) (hnc : ¬ K.post.SameComponent K.fa K.fb)
    (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hM : ∀ v ∈ M.atoms, M.deg v ≤ 4)
    (hB : M.IsBlock K.C.atoms K.C.upper K.C.lower) {L γ δ : ℝ} (hL : L ≠ 0) {w : Mom d}
    {Adm : (D → (Fin d → ℤ)) → Prop} (hgap : ∀ κ, Adm κ → κ K.x₁ ≠ κ K.x₂) :
    ∃ ν : ℝ, 1 ≤ ν ∧ ν ≤ (M.atoms.card : ℝ) ∧ NewCompFixed M K L γ δ ν w Adm := by
  set A := newCompAtoms K with hA
  have hupA : K.C.upper ∈ A := (mem_newCompAtoms K).2 (Or.inl rfl)
  have hCA : ∀ v ∈ A, v ∈ K.C.atoms → v = K.C.upper := by
    intro v hv hvC
    rcases (mem_newCompAtoms K).1 hv with h | h
    · exact h
    · exact absurd hvC h.2.1
  have g1 : M.InGroup K.C.atoms K.x₁ := inGroup_of_contains K K.in_a.1
  have g2 : M.InGroup K.C.atoms K.x₂ := inGroup_of_contains K K.in_a.2
  have hup : M.atom K.x₁ ∈ A ∧ M.atom (M.mate K.x₁) ∉ A := by
    refine ⟨K.Mx₁ ▸ hupA, fun h => ?_⟩
    have := hCA _ h g1.2
    exact hnl K.x₁ (by rw [K.Mx₁, this])
  have hup2 : M.atom K.x₂ ∈ A ∧ M.atom (M.mate K.x₂) ∉ A := by
    refine ⟨K.Mx₂ ▸ hupA, fun h => ?_⟩
    have := hCA _ h g2.2
    exact hnl K.x₂ (by rw [K.Mx₂, this])
  have hfix := newCompFixedUp_of_boundary hd K hL A (newCompAtoms_sub K)
    (fun x h1 h2 => newComp_boundary K hnc h1 h2) hup hup2 hgap (Adm := Adm) (γ := γ) (δ := δ) (w := w)
  have hfix2 := newCompFixed_of_upper K hB hM hfix
  refine ⟨(A.card : ℝ) + (((K.C.atoms.erase K.C.upper).erase K.C.lower).card : ℝ), ?_, ?_, hfix2⟩
  · have : 1 ≤ A.card := Finset.card_pos.2 ⟨_, hupA⟩
    have : (1 : ℝ) ≤ A.card := by exact_mod_cast this
    have : (0 : ℝ) ≤ (((K.C.atoms.erase K.C.upper).erase K.C.lower).card : ℝ) := Nat.cast_nonneg _
    linarith
  · have hdis : Disjoint A ((K.C.atoms.erase K.C.upper).erase K.C.lower) := by
      rw [Finset.disjoint_left]
      intro v hv hv2
      have h1 : v ≠ K.C.lower := (Finset.mem_erase.1 hv2).1
      have h2 := Finset.mem_erase.1 (Finset.mem_erase.1 hv2).2
      exact h2.1 (hCA v hv h2.2)
    have hsub : A ∪ ((K.C.atoms.erase K.C.upper).erase K.C.lower) ⊆ M.atoms := by
      intro v hv
      rcases Finset.mem_union.1 hv with h | h
      · exact newCompAtoms_sub K h
      · exact objectAtoms_sub K.C (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis] at this
    exact_mod_cast this

end WaveTurbulence.FinalCountG3
