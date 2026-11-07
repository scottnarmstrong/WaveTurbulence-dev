/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineGroupPickCarrier
public import WaveTurbulence.Foundations.Vine.A.VineNormalizationNames
public import Mathlib.Data.Finset.Sort
/-! R83 pure-DV keys: the complete normalized constituent support and its joints. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Mole WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)}

/-- A DV candidate constituent and both its joints lie in the whole group. -/
theorem DVCandidate.support {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (h : DVCandidate G S t) : t.1 ⊆ S ∧ t.2.1 ∈ S ∧ t.2.2 ∈ S := by
  obtain ⟨B, hA, _, _, hS⟩ := h
  have hsub : t.1 ⊆ S := by rw [hS]; exact Finset.subset_union_left
  exact ⟨hsub, hsub hA.1.2.1, hsub hA.1.2.2.1⟩

/-- An ordered list of every normalized atom in a support. -/
noncomputable def coarseSupportWord (G : Garden w) (A : Finset (GBranch G.tree)) : List (List ℕ) := by
  classical
  exact (A.image (coarseAtomWord G)).sort (· ≤ ·)

/-- Untouched supports are determined by their complete normalized words. -/
theorem coarseSupportWord_inj_of_none {A B : Finset (GBranch G.tree)}
    (hA : ∀ a ∈ A, (coarseSplice G).cls a = none)
    (hB : ∀ b ∈ B, (coarseSplice G).cls b = none)
    (he : coarseSupportWord G A = coarseSupportWord G B) : A = B := by
  classical
  have himg : A.image (coarseAtomWord G) = B.image (coarseAtomWord G) := by
    simpa only [coarseSupportWord, Finset.sort_toFinset] using congrArg List.toFinset he
  ext v
  constructor
  · intro hv
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp (himg ▸ Finset.mem_image_of_mem (coarseAtomWord G) hv)
    exact (coarseAtomWord_inj_of_none (hB b hb) (hA v hv) he) ▸ hb
  · intro hv
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp (himg.symm ▸ Finset.mem_image_of_mem (coarseAtomWord G) hv)
    exact (coarseAtomWord_inj_of_none (hA a ha) (hB v hv) he) ▸ ha

/-- Lexicographic comparison of the sorted constituent support, then its two joints. -/
noncomputable def dvGroupKey (G : Garden w) (t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) :
    List (List (List ℕ)) :=
  [coarseSupportWord G t.1, [coarseAtomWord G t.2.1], [coarseAtomWord G t.2.2]]

/-- On pure-DV candidates the full normalized key is injective. -/
theorem dvGroupKey_injective (hS : PureDVGroup G S) :
    Function.Injective (fun t : {t // DVCandidate G S t} => dvGroupKey G t.1) := by
  intro x y he
  have ha := (List.cons.inj he).1
  have hb := (List.cons.inj (List.cons.inj (List.cons.inj he).2).1).1
  have hc := (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj he).2).2).1).1
  have hea : x.1.1 = y.1.1 := coarseSupportWord_inj_of_none
    (fun a ha => hS.cls_none (x.2.support.1 ha))
    (fun a ha => hS.cls_none (y.2.support.1 ha)) ha
  have heb : x.1.2.1 = y.1.2.1 := coarseAtomWord_inj_of_none
    (hS.cls_none x.2.support.2.1) (hS.cls_none y.2.support.2.1) hb
  have hec : x.1.2.2 = y.1.2.2 := coarseAtomWord_inj_of_none
    (hS.cls_none x.2.support.2.2) (hS.cls_none y.2.support.2.2) hc
  exact Subtype.ext (Prod.ext hea (Prod.ext heb hec))

/-- The pure-DV normalized candidate set has exactly one least triple. -/
theorem dvGroupKey_existsUnique (hS : PureDVGroup G S) :
    ∃! t : {t // DVCandidate G S t}, ∀ u : {t // DVCandidate G S t},
      dvGroupKey G t.1 ≤ dvGroupKey G u.1 := by
  let : Nonempty {t // DVCandidate G S t} := hS.candidate
  exact existsUnique_least_key _ (dvGroupKey_injective hS)

/-- R83's pure-DV constituent choice, made without a prescription. -/
noncomputable def dvGroupPick (G : Garden w) (S : Finset (GBranch G.tree)) :
    Option (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) := by
  classical
  exact if hS : PureDVGroup G S then some (dvGroupKey_existsUnique hS).choose.1 else none

/-- The chosen DV triple is valid and least among all normalized candidates. -/
theorem dvGroupPick_spec {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (h : dvGroupPick G S = some t) : PureDVGroup G S ∧ DVCandidate G S t ∧
      ∀ u : {u // DVCandidate G S u}, dvGroupKey G t ≤ dvGroupKey G u.1 := by
  classical
  unfold dvGroupPick at h
  split_ifs at h with hS
  · have he := Option.some.inj h
    subst t
    exact ⟨hS, (dvGroupKey_existsUnique hS).choose.property, (dvGroupKey_existsUnique hS).choose_spec.1⟩

end WaveTurbulence.VineA
