/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.SourceGroupConnectivity
public import WaveTurbulence.Foundations.Molecule.MoleculeBlockConcatenation
/-! Intersecting with a block whose only accessible boundary joint is fixed preserves connectivity. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

theorem source_groupConnected_inter_of_one_joint {V D : Type*} [DecidableEq V] [Fintype D]
    (M : Molecule V D) (hM : M.IsMolecule) {A B : Finset V} {b₁ b₂ : V}
    (hA : M.GroupConnected A) (hB : M.IsBlock B b₁ b₂)
    (hb₂ : b₂ ∉ A) : M.GroupConnected (A ∩ B) := by
  classical
  let f : V → V := fun v => if v ∈ B then v else b₁
  let E : V → V → Prop := fun a b => ∃ x, M.InGroup (A ∩ B) x ∧
    M.atom x = a ∧ M.atom (M.mate x) = b
  have hedge : ∀ a b, (∃ x, M.InGroup A x ∧ M.atom x = a ∧ M.atom (M.mate x) = b) →
      Relation.EqvGen E (f a) (f b) := by
    rintro a b ⟨x, hg, rfl, rfl⟩
    by_cases ha : M.atom x ∈ B
    · by_cases hb : M.atom (M.mate x) ∈ B
      · simp only [f, ite_eq_left ha, ite_eq_left hb]
        exact Relation.EqvGen.rel _ _ ⟨x, ⟨Finset.mem_inter.mpr ⟨hg.1, ha⟩,
          Finset.mem_inter.mpr ⟨hg.2, hb⟩⟩, rfl, rfl⟩
      · have he : M.atom x = b₁ := by
          rcases Mole.block_entry_is_joint M hM hB hb ha
            (Mole.adj_symmetric M ⟨x, rfl, rfl⟩) with he | he
          · exact he
          · exact False.elim (hb₂ (he ▸ hg.1))
        simp only [f, ite_eq_right hb, he, ite_self]
        exact Relation.EqvGen.refl _
    · by_cases hb : M.atom (M.mate x) ∈ B
      · have he : M.atom (M.mate x) = b₁ := by
          rcases Mole.block_entry_is_joint M hM hB ha hb ⟨x, rfl, rfl⟩ with he | he
          · exact he
          · exact False.elim (hb₂ (he ▸ hg.2))
        simp only [f, ite_eq_right ha, he, ite_self]
        exact Relation.EqvGen.refl _
      · simp only [f, ite_eq_right ha, ite_eq_right hb]
        exact Relation.EqvGen.refl _
  have map_path : ∀ u v, Relation.EqvGen (fun a b => ∃ x, M.InGroup A x ∧
      M.atom x = a ∧ M.atom (M.mate x) = b) u v → Relation.EqvGen E (f u) (f v) := by
    intro u v hp
    induction hp with
    | rel a b hab => exact hedge a b hab
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  intro u hu v hv
  have hmap := map_path u v (hA u (Finset.mem_inter.mp hu).1 v (Finset.mem_inter.mp hv).1)
  simpa only [f, ite_eq_left (Finset.mem_inter.mp hu).2,
    ite_eq_left (Finset.mem_inter.mp hv).2] using hmap

end WaveTurbulence.LGSpine
