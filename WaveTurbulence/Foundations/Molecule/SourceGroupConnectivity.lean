/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.Molecules
public import Mathlib.Logic.Relation
/-! Induced connectivity of two actual atomic groups meeting at an atom. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

theorem source_groupConnected_union {V D : Type*} [DecidableEq V]
    (M : Molecule V D) {A B : Finset V} {c : V}
    (hA : M.GroupConnected A) (hB : M.GroupConnected B) (hcA : c ∈ A) (hcB : c ∈ B) :
    M.GroupConnected (A ∪ B) := by
  have lift (S : Finset V) (hs : S ⊆ A ∪ B) {u v : V}
      (hp : Relation.EqvGen (fun a b => ∃ x, M.InGroup S x ∧
        M.atom x = a ∧ M.atom (M.mate x) = b) u v) :
      Relation.EqvGen (fun a b => ∃ x, M.InGroup (A ∪ B) x ∧
        M.atom x = a ∧ M.atom (M.mate x) = b) u v := by
    apply Relation.EqvGen.mono (r := fun a b => ∃ x, M.InGroup S x ∧
      M.atom x = a ∧ M.atom (M.mate x) = b) ?_ u v hp
    rintro a b ⟨x, hg, ha, hb⟩
    exact ⟨x, ⟨hs hg.1, hs hg.2⟩, ha, hb⟩
  intro u hu v hv
  have huc := (Finset.mem_union.mp hu).elim
    (fun hu => lift A Finset.subset_union_left (hA u hu c hcA))
    (fun hu => lift B Finset.subset_union_right (hB u hu c hcB))
  have hcv := (Finset.mem_union.mp hv).elim
    (fun hv => lift A Finset.subset_union_left (hA c hcA v hv))
    (fun hv => lift B Finset.subset_union_right (hB c hcB v hv))
  exact Relation.EqvGen.trans _ _ _ huc hcv

end WaveTurbulence.LGSpine
