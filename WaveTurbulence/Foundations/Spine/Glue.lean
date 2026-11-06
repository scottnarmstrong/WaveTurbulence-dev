/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RestInv
/-! # Gluing decorations along disjoint ladders (S3c) -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay Finset
open scoped Classical

variable {w d : ℕ} {G : Garden w} {ι : Type} [Fintype ι] [DecidableEq ι]

lemma rootPairCompat (L : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration G d roots 0) : Mole.RootPairCompatible G (rootVec L base roots) :=
  Mole.rootPairCompatible_of_labels G _ (fun a => base + latticePoint L (z.1 a))
    (fun i => by rw [z.2.2.1 i]; rfl) (isDecoration_coset L base z.2.1).2

lemma bondIndex_mate {roots : Fin w → (Fin d → ℤ)} (z : GenDecoration G d roots 0) (x : GardenDart G) :
    bondIndex G z.1 (G.molecule.mate x) = bondIndex G z.1 x := by
  rw [bondIndex_eq_restrict]
  exact Mole.restrictLabels_mate G z.1 (fun l => z.2.1.2 l) x

/-- **Gluing.** Decorations `y i`, agreeing with `z₀` on the boundary darts of the atoms of `S i`,
can be combined with `z₀` into a decoration equal to `y i` at the darts of the atoms of `S i`. -/
theorem exists_glue (hP : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (z₀ : GenDecoration G d roots 0)
    (S : ι → Finset (GBranch G.tree)) (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (y : ι → GenDecoration G d roots 0)
    (hy : ∀ i x, G.molecule.atom x ∈ S i → ¬ G.molecule.InGroup (S i) x →
      bondIndex G (y i).1 x = bondIndex G z₀.1 x) :
    ∃ z : GenDecoration G d roots 0,
      (∀ i x, G.molecule.atom x ∈ S i → bondIndex G z.1 x = bondIndex G (y i).1 x) ∧
      (∀ x, G.molecule.atom x ∉ Uni S → bondIndex G z.1 x = bondIndex G z₀.1 x) := by
  have hn := rootPairCompat L base roots z₀
  -- the glued labelling
  let lab : GardenDart G → (Fin d → ℤ) := fun x =>
    if h : ∃ i, G.molecule.atom x ∈ S i then bondIndex G (y (Classical.choose h)).1 x
    else bondIndex G z₀.1 x
  have lab_in : ∀ i x, G.molecule.atom x ∈ S i → lab x = bondIndex G (y i).1 x := by
    intro i x hx
    have h : ∃ i, G.molecule.atom x ∈ S i := ⟨i, hx⟩
    have hc : Classical.choose h = i := by
      by_contra hne
      exact Finset.disjoint_left.mp (hS _ _ hne) (Classical.choose_spec h) hx
    simp only [lab, dif_pos h, hc]
  have lab_out : ∀ x, G.molecule.atom x ∉ Uni S → lab x = bondIndex G z₀.1 x := by
    intro x hx
    have h : ¬ ∃ i, G.molecule.atom x ∈ S i := fun ⟨i, hi⟩ => hx (mem_biUnion.mpr ⟨i, mem_univ _, hi⟩)
    simp only [lab, dif_neg h]
  have lab_bd : ∀ i x, G.molecule.atom x ∈ S i → ¬ G.molecule.InGroup (S i) x → lab x = bondIndex G z₀.1 x :=
    fun i x hx hn' => by rw [lab_in i x hx]; exact hy i x hx hn'
  -- cross-atom comparison: for any dart whose atom or mate atom is not both in the same ladder
  have lab_z0 : ∀ x, ¬ IntDart S x → lab x = bondIndex G z₀.1 x := by
    intro x hx
    by_cases ha : G.molecule.atom x ∈ Uni S
    · obtain ⟨i, -, hi⟩ := mem_biUnion.mp ha
      exact lab_bd i x hi (fun hh => hx ⟨i, hh⟩)
    · exact lab_out x ha
  have lab_mate : ∀ x, lab (G.molecule.mate x) = lab x := by
    intro x
    by_cases hx : IntDart S x
    · obtain ⟨i, hi⟩ := hx
      have hm : G.molecule.InGroup (S i) (G.molecule.mate x) := by
        exact ⟨hi.2, by rw [G.molecule.mate_mate]; exact hi.1⟩
      rw [lab_in i x hi.1, lab_in i (G.molecule.mate x) hm.1, bondIndex_mate]
    · have hx' : ¬ IntDart S (G.molecule.mate x) := by
        rintro ⟨i, hi⟩
        apply hx
        have hi' : G.molecule.atom (G.molecule.mate x) ∈ S i ∧
          G.molecule.atom (G.molecule.mate (G.molecule.mate x)) ∈ S i := hi
        rw [G.molecule.mate_mate] at hi'
        exact ⟨i, hi'.2, hi'.1⟩
      rw [lab_z0 x hx, lab_z0 _ hx', bondIndex_mate]
  -- the molecule decoration property
  have hdec : G.molecule.IsDecoration L base (Mole.gardenSource G hP (rootVec L base roots)) lab := by
    refine ⟨lab_mate, ?_⟩
    intro v hv
    by_cases hvU : v ∈ Uni S
    · obtain ⟨i, -, hi⟩ := mem_biUnion.mp hvU
      have hy' : ∑ x ∈ G.molecule.dartsAt v, G.molecule.dartSign x •
          Molecule.kvec L base (bondIndex G (y i).1) x = Mole.gardenSource G hP (rootVec L base roots) v :=
        (spliced_molecule_decoration G hP hL base roots (y i)).2 v hv
      refine Eq.trans ?_ hy'
      refine Finset.sum_congr rfl (fun x hx => ?_)
      have hxv : G.molecule.atom x = v := by simpa [Molecule.dartsAt] using hx
      simp only [Molecule.kvec]
      rw [lab_in i x (by rw [hxv]; exact hi)]
    · have hz' : ∑ x ∈ G.molecule.dartsAt v, G.molecule.dartSign x •
          Molecule.kvec L base (bondIndex G z₀.1) x = Mole.gardenSource G hP (rootVec L base roots) v :=
        (spliced_molecule_decoration G hP hL base roots z₀).2 v hv
      refine Eq.trans ?_ hz'
      refine Finset.sum_congr rfl (fun x hx => ?_)
      have hxv : G.molecule.atom x = v := by simpa [Molecule.dartsAt] using hx
      simp only [Molecule.kvec]
      rw [lab_out x (by rw [hxv]; exact hvU)]
  set e := decEquiv L base roots hP hL hn with he
  have hb : bondIndex G (e.symm ⟨lab, hdec⟩).1 = lab := by
    have := congrArg Subtype.val (e.apply_symm_apply ⟨lab, hdec⟩)
    exact this
  refine ⟨e.symm ⟨lab, hdec⟩, ?_, ?_⟩
  · intro i x hx
    rw [hb, lab_in i x hx]
  · intro x hx
    rw [hb, lab_out x hx]

end WaveTurbulence.CoarseSpliced
