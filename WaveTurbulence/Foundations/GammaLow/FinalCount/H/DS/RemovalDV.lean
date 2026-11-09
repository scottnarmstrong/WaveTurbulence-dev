/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.Removal
public import WaveTurbulence.Foundations.Molecule.VineRemovalLocalPaths
/-! # H-DS: the removal clause of TARGET `subsetvc` in a DV′ (packet L6-HDS; hand-written)

A DV′ of the low family is `S ∪ T` with T-vine branches `S`, `T` (`σ(a, b) = 1`, `S ∩ T = {a, b}`). Main removes vines (V)
from DVs along the drawn templates. Here:
* `DV_split_removal_connected`: every removed piece lies in one branch and is disjoint from the other: N3 Cor 1.16′(3) in
  each branch (`removal_connected_of_objects`), glued at the joint `a` (main's `removal_local_path_lift`);
* `DV_branch_removal_connected`: one piece is a whole branch `S`, the others lie in `T` and avoid the joints: N3 Lemma P
  in `T` (`removal_connected_avoiding`; the removal of `S` kills, among the bonds of `T`, only the joint bond,
  `pair_group_darts`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H.DS
open Finset WaveTurbulence.Vine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- Removal in a DV′ of pieces each inside one branch and disjoint from the other. -/
theorem DV_split_removal_connected (hM : M.IsMolecule) {S T : Finset V} {a b : V} (hS : M.IsTVine S a b)
    (hT : M.IsTVine T a b) (ps : List (RemovalPiece V D)) (hO : ∀ P ∈ ps, ∃ O : Src.Object Src.γL M, Realizes O P)
    (hinside : ∀ P ∈ ps, ∀ x ∈ P.darts, M.InGroup P.atoms x)
    (hparts : ∀ P ∈ ps, (P.atoms ⊆ S ∧ Disjoint P.atoms T) ∨ (P.atoms ⊆ T ∧ Disjoint P.atoms S))
    (hdis : ∀ P ∈ ps, ∀ Q ∈ ps, P ≠ Q → Disjoint P.atoms Q.atoms) :
    ∀ u ∈ remainingAtoms (S ∪ T) ps, ∀ v ∈ remainingAtoms (S ∪ T) ps, (removeBlocks M (S ∪ T) ps).SameComponent u v := by
  classical
  let qs := ps.filter (fun P => P.atoms ⊆ S)
  let ts := ps.filter (fun P => P.atoms ⊆ T)
  have hqs (P : RemovalPiece V D) (hP : P ∈ qs) : P ∈ ps ∧ P.atoms ⊆ S :=
    ⟨(List.mem_filter.mp hP).1, by simpa using (List.mem_filter.mp hP).2⟩
  have hts (P : RemovalPiece V D) (hP : P ∈ ts) : P ∈ ps ∧ P.atoms ⊆ T :=
    ⟨(List.mem_filter.mp hP).1, by simpa using (List.mem_filter.mp hP).2⟩
  have hqsParts : ∀ P ∈ ps, P ∈ qs ∨ Disjoint P.atoms S := by
    intro P hP
    rcases hparts P hP with ⟨hPS, _⟩ | ⟨_, hPS⟩
    · exact Or.inl (List.mem_filter.mpr ⟨hP, by simpa using hPS⟩)
    · exact Or.inr hPS
  have htsParts : ∀ P ∈ ps, P ∈ ts ∨ Disjoint P.atoms T := by
    intro P hP
    rcases hparts P hP with ⟨_, hPT⟩ | ⟨hPT, _⟩
    · exact Or.inr hPT
    · exact Or.inl (List.mem_filter.mpr ⟨hP, by simpa using hPT⟩)
  have hne (P : RemovalPiece V D) (hP : P ∈ ps) : P.atoms ≠ S ∧ P.atoms ≠ T := by
    constructor
    · intro h
      rcases hparts P hP with ⟨_, hd⟩ | ⟨_, hd⟩
      · exact disjoint_left.mp hd (h ▸ hS.1.2.1) hT.1.2.1
      · exact disjoint_left.mp hd (h ▸ hS.1.2.1) hS.1.2.1
    · intro h
      rcases hparts P hP with ⟨_, hd⟩ | ⟨_, hd⟩
      · exact disjoint_left.mp hd (h ▸ hT.1.2.1) hT.1.2.1
      · exact disjoint_left.mp hd (h ▸ hT.1.2.1) hS.1.2.1
  have hconnS := removal_connected_of_objects hM (Src.isSomeVine_of_T hS) qs (fun P hP => hO P (hqs P hP).1)
    (fun P hP => Finset.ssubset_iff_subset_ne.mpr ⟨(hqs P hP).2, (hne P (hqs P hP).1).1⟩)
    (fun P hP Q hQ h => hdis P (hqs P hP).1 Q (hqs Q hQ).1 h)
  have hconnT := removal_connected_of_objects hM (Src.isSomeVine_of_T hT) ts (fun P hP => hO P (hts P hP).1)
    (fun P hP => Finset.ssubset_iff_subset_ne.mpr ⟨(hts P hP).2, (hne P (hts P hP).1).2⟩)
    (fun P hP Q hQ h => hdis P (hts P hP).1 Q (hts Q hQ).1 h)
  have hpartsAtom : ∀ (B : Finset V) (rs : List (RemovalPiece V D)), (∀ P ∈ rs, P ∈ ps) →
      (∀ P ∈ ps, P ∈ rs ∨ Disjoint P.atoms B) →
      ∀ w ∈ remainingAtoms (S ∪ T) ps, w ∈ B → w ∈ remainingAtoms B rs := by
    intro B rs hrs _ w hw hwB
    exact mem_filter.mpr ⟨hwB, fun P hP => (mem_filter.mp hw).2 P (hrs P hP)⟩
  have hjS : a ∈ remainingAtoms S qs := by
    refine mem_filter.mpr ⟨hS.1.2.1, fun P hP hai => ?_⟩
    rcases hparts P (hqs P hP).1 with ⟨_, hd⟩ | ⟨_, hd⟩
    · exact disjoint_left.mp hd (mem_sdiff.mp hai).1 hT.1.2.1
    · exact disjoint_left.mp hd (mem_sdiff.mp hai).1 hS.1.2.1
  have hjT : a ∈ remainingAtoms T ts := by
    refine mem_filter.mpr ⟨hT.1.2.1, fun P hP hai => ?_⟩
    rcases hparts P (hts P hP).1 with ⟨_, hd⟩ | ⟨_, hd⟩
    · exact disjoint_left.mp hd (mem_sdiff.mp hai).1 hT.1.2.1
    · exact disjoint_left.mp hd (mem_sdiff.mp hai).1 hS.1.2.1
  have reach (u : V) (hu : u ∈ remainingAtoms (S ∪ T) ps) : (removeBlocks M (S ∪ T) ps).SameComponent u a := by
    rcases mem_union.mp (mem_filter.mp hu).1 with huS | huT
    · exact removal_local_path_lift M (show S ⊆ S ∪ T from subset_union_left) qs ps hqsParts hinside
        (hconnS u (hpartsAtom S qs (fun P hP => (hqs P hP).1) hqsParts u hu huS) a hjS)
    · exact removal_local_path_lift M (show T ⊆ S ∪ T from subset_union_right) ts ps htsParts hinside
        (hconnT u (hpartsAtom T ts (fun P hP => (hts P hP).1) htsParts u hu huT) a hjT)
  intro u hu v hv
  exact Relation.EqvGen.trans _ _ _ (reach u hu) (Relation.EqvGen.symm _ _ (reach v hv))

/-- Removal in a DV′ of one whole branch `S` (its block removal) and of pieces inside the other branch avoiding the
joints: N3 Lemma P in `T`. -/
theorem DV_branch_removal_connected (hM : M.IsMolecule) {S T : Finset V} {a b : V} (hσ : M.sigma a b = 1)
    (hT : M.IsTVine T a b) (hi : S ∩ T = {a, b}) (ps : List (RemovalPiece V D)) (P0 : RemovalPiece V D)
    (hP0 : P0 ∈ ps) (hP0a : P0.atoms = S) (hP0j : (P0.left = a ∧ P0.right = b) ∨ (P0.left = b ∧ P0.right = a))
    (hP0D : P0.darts = univ.filter (M.InGroup S))
    (hO : ∀ P ∈ ps, P ≠ P0 → ∃ O : Src.Object Src.γL M, Realizes O P)
    (hothers : ∀ P ∈ ps, P ≠ P0 → P.atoms ⊆ T ∧ a ∉ P.atoms ∧ b ∉ P.atoms)
    (hdis : ∀ P ∈ ps, ∀ Q ∈ ps, P ≠ Q → Disjoint P.atoms Q.atoms) :
    ∀ u ∈ remainingAtoms (S ∪ T) ps, ∀ v ∈ remainingAtoms (S ∪ T) ps, (removeBlocks M (S ∪ T) ps).SameComponent u v := by
  classical
  obtain ⟨f, hf⟩ := exists_joint_bond hσ
  let qs := ps.filter (fun P => P ≠ P0)
  have hqs (P : RemovalPiece V D) (hP : P ∈ qs) : P ∈ ps ∧ P ≠ P0 :=
    ⟨(List.mem_filter.mp hP).1, by simpa using (List.mem_filter.mp hP).2⟩
  have hqs' (P : RemovalPiece V D) (hP : P ∈ ps) (hne : P ≠ P0) : P ∈ qs :=
    List.mem_filter.mpr ⟨hP, by simpa using hne⟩
  have hpath := removal_connected_avoiding hM (Src.isSomeVine_of_T hT) hσ hf qs
    (fun P hP => hO P (hqs P hP).1 (hqs P hP).2) (fun P hP => (hothers P (hqs P hP).1 (hqs P hP).2).1)
    (fun P hP => (hothers P (hqs P hP).1 (hqs P hP).2).2)
    (fun P hP Q hQ hne => hdis P (hqs P hP).1 Q (hqs Q hQ).1 hne)
  have hint0 : P0.interior = S \ {a, b} := by
    unfold RemovalPiece.interior
    rw [hP0a]
    rcases hP0j with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, pair_comm]
  have hmemT : ∀ w ∈ remainingAtoms (S ∪ T) ps, w ∈ remainingAtoms T qs := by
    intro w hw
    obtain ⟨hwU, hwP⟩ := mem_filter.mp hw
    have hwT : w ∈ T := by
      rcases mem_union.mp hwU with hwS | hwT
      · by_contra hwT
        apply hwP P0 hP0
        rw [hint0, mem_sdiff]
        refine ⟨hwS, fun hab => hwT ?_⟩
        rcases mem_insert.mp hab with h | h
        · rw [h]; exact hT.1.2.1
        · rw [mem_singleton.mp h]; exact hT.1.2.2.1
      · exact hwT
    exact mem_filter.mpr ⟨hwT, fun P hP => hwP P (hqs P hP).1⟩
  have hrem : ∀ w, w ∈ remainingAtoms T qs → w ∈ remainingAtoms (S ∪ T) ps := by
    intro w hw
    obtain ⟨hwT, hwP⟩ := mem_filter.mp hw
    refine mem_filter.mpr ⟨mem_union_right _ hwT, fun P hP => ?_⟩
    by_cases hPP : P = P0
    · subst hPP
      rw [hint0, mem_sdiff, not_and, not_not]
      intro hwS
      have : w ∈ S ∩ T := mem_inter.mpr ⟨hwS, hwT⟩
      rwa [hi] at this
    · exact hwP P (hqs' P hP hPP)
  have hk : ∀ x, KeepDart M T qs x → x ≠ f → x ≠ M.mate f → KeepDart M (S ∪ T) ps x := by
    intro x hx hxf hxmf
    obtain ⟨h1, h2, h3⟩ := hx
    have hT1 := (mem_filter.mp h1).1
    have hT2 := (mem_filter.mp h2).1
    have hnotS : ¬ M.InGroup S x := by
      intro hxS
      have hab : M.InGroup {a, b} x := by
        refine ⟨?_, ?_⟩
        · have : M.atom x ∈ S ∩ T := mem_inter.mpr ⟨hxS.1, hT1⟩
          rwa [hi] at this
        · have : M.atom (M.mate x) ∈ S ∩ T := mem_inter.mpr ⟨hxS.2, hT2⟩
          rwa [hi] at this
      rcases pair_group_darts hT.1 hσ hf hab with h | h
      · exact hxf h
      · exact hxmf h
    refine ⟨hrem _ h1, hrem _ h2, fun P hP => ?_⟩
    by_cases hPP : P = P0
    · subst hPP
      rw [hP0D]
      exact ⟨fun h => hnotS (mem_filter.mp h).2, fun h => hnotS (inGroup_mate.mp (mem_filter.mp h).2)⟩
    · exact h3 P (hqs' P hP hPP)
  intro u hu v hv
  exact avoiding_lift hk (hpath u (hmemT u hu) v (hmemT v hv))

end WaveTurbulence.GammaLow.FinalCount.H.DS
